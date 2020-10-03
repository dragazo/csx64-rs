use std::iter::Peekable;
use std::str::CharIndices;
use std::collections::VecDeque;
use std::borrow::Cow;
use std::cell;
use rug::Float;

use super::*;
use super::expr::{ExprData, OP, Value, ValueVariants, PRECISION};
use super::caseless::Caseless;

macro_rules! err {
    ($self:expr, kind:$kind:ident, pos:$pos:expr) => {
        Err(AsmError {
            kind: AsmErrorKind::$kind,
            line_num: $self.line_num,
            pos: $pos,
            line: $self.line.clone(),
        })
    };
}

// advances the cursor iterator to the specified character index.
// end_pos is the exclusive upper bound index of cursor.
fn advance_cursor(cursor: &mut Peekable<CharIndices>, to: usize, end_pos: usize) {
    loop {
        match cursor.peek().copied() {
            None => return assert_eq!(to, end_pos),
            Some((p, _)) => {
                if p < to { cursor.next(); }
                else if p == to { return }
                else { panic!() }
            }
        }
    }
}
#[test]
fn test_advance_cursor() {
    let mut cursor = "hello world".char_indices().peekable();
    assert_eq!(cursor.peek().unwrap().0, 0);
    advance_cursor(&mut cursor, 5, 11);
    assert_eq!(cursor.peek().unwrap().0, 5);
    advance_cursor(&mut cursor, 5, 11);
    assert_eq!(cursor.peek().unwrap().0, 5);
    advance_cursor(&mut cursor, 10, 11);
    assert_eq!(cursor.peek().unwrap().0, 10);
    advance_cursor(&mut cursor, 11, 11);
    assert_eq!(cursor.peek(), None);
    advance_cursor(&mut cursor, 11, 11);
    assert_eq!(cursor.peek(), None);
}

#[must_use]
fn is_valid_symbol_name(name: &str) -> bool {
    let mut chars = name.chars();
    match chars.next() {
        None => return false, // empty symbol name not allowed
        Some(c) => match c {
            '_' | '.' | 'a'..='z' | 'A'..='Z' => (), // first char
            _ => return false,
        }
    }
    for c in chars {
        match c {
            '_' | '.' | 'a'..='z' | 'A'..='Z' | '0'..='9' => (), // other chars
            _ => return false,
        }
    }
    true
}
#[test]
fn test_valid_symname() {
    assert!(is_valid_symbol_name("foo"));
    assert!(is_valid_symbol_name("Foo"));
    assert!(is_valid_symbol_name(".foo"));
    assert!(is_valid_symbol_name("_foo"));
    assert!(is_valid_symbol_name("._foo"));
    assert!(is_valid_symbol_name(".7_foo"));
    assert!(is_valid_symbol_name(".foo_bAR7"));
    assert!(is_valid_symbol_name(".Boo_Bar_7"));
    assert!(!is_valid_symbol_name("12"));
    assert!(!is_valid_symbol_name("12.4"));
    assert!(!is_valid_symbol_name("7up"));
    assert!(is_valid_symbol_name("_7up"));
    assert!(!is_valid_symbol_name(" _7up"));
    assert!(!is_valid_symbol_name("_7up "));
    assert!(!is_valid_symbol_name("_7u p"));
    assert!(!is_valid_symbol_name("$foo"));
}

/// Grabs the first whitespace-separated token and returns it, along with the index just after it.
/// If no token is present, returns empty string and the index of one past the end of the input string.
fn grab_whitespace_sep_token(raw_line: &str, raw_start: usize, raw_stop: usize) -> (&str, usize) {
    let token_start = match raw_line[raw_start..raw_stop].find(|c: char| !c.is_whitespace()) {
        None => raw_stop,
        Some(p) => raw_start + p,
    };
    let token_stop = match raw_line[token_start..raw_stop].find(|c: char| c.is_whitespace()) {
        None => raw_stop,
        Some(p) => token_start + p,
    };
    (&raw_line[token_start..token_stop], token_stop)
}
#[test]
fn test_grab_ws_sep_token() {
    assert_eq!(grab_whitespace_sep_token("   \t hello world  ", 3, 18), ("hello", 10));
    assert_eq!(grab_whitespace_sep_token("    \t  ", 1, 7), ("", 7));
    assert_eq!(grab_whitespace_sep_token("", 0, 0), ("", 0));
}

/// Trims all leading whitespace characters and returns the result and the index of the starting portion.
/// If the string is empty or whitespace, returns empty string and one past the end of the input string.
fn trim_start_with_pos(raw_line: &str, raw_start: usize, raw_stop: usize) -> (&str, usize) {
    match raw_line[raw_start..raw_stop].find(|c: char| !c.is_whitespace()) {
        Some(p) => (&raw_line[raw_start + p..raw_stop], raw_start + p),
        None => ("", raw_stop),
    }
}
#[test]
fn test_trim_start_with_pos() {
    assert_eq!(trim_start_with_pos("   \t hello world  ", 3, 18), ("hello world  ", 5));
    assert_eq!(trim_start_with_pos("    \t  ", 1, 7), ("", 7));
    assert_eq!(trim_start_with_pos("", 0, 0), ("", 0));
}

fn parse_size_str(val: &str, success: usize, failure: usize) -> (Option<Size>, usize) {
    match SIZE_KEYWORDS.get(&Caseless(val)) {
        Some(size) => (Some(*size), success),
        None => (None, failure),
    }
}

pub(super) struct TimesInfo {
    pub(super) total_count: usize,
    pub(super) current: usize,
}

pub(super) struct AssembleArgs {
    pub(super) file: ObjectFile,
    
    pub(super) current_seg: AsmSegment,
    pub(super) done_segs: AsmSegment,

    pub(super) line: String,
    pub(super) line_num: usize,
    pub(super) line_pos_in_seg: usize,

    pub(super) last_nonlocal_label: Option<String>,
    pub(super) label_def: String,

    pub(super) times: Option<TimesInfo>,

    pub(super) op: String,
    pub(super) args: Vec<String>,
}
impl AssembleArgs {
    pub(super) fn update_line_pos(&mut self) {
        // update current line pos based on segment
        match self.current_seg {
            AsmSegment::TEXT => self.line_pos_in_seg = self.file.text.len(),
            AsmSegment::RODATA => self.line_pos_in_seg = self.file.rodata.len(),
            AsmSegment::DATA => self.line_pos_in_seg = self.file.data.len(),
            AsmSegment::BSS => self.line_pos_in_seg = self.file.bss_len,

            _ => (), // default does nothing - nothing to update
        }
    }

    // attempt to mutate a symbol name from the line, transforming local symbols names to their full name.
    fn mutate_name(&self, raw_line: &str, raw_start: usize, raw_stop: usize) -> Result<String, AsmError> {
        let name = &raw_line[raw_start..raw_stop];
        if name.starts_with('.') {
            match &self.last_nonlocal_label {
                None => return err!(self, kind: LocalSymbolBeforeNonlocal, pos: raw_start),
                Some(nonlocal) => Ok(format!("{}.{}", nonlocal, name)),
            }
        }
        else {
            Ok(name.into())
        }
    }

    // attempts to read a binary op from the string, allowing leading whitespace.
    // if a binary op is present, returns the op and the character index just after it, otherwise returns None.
    fn extract_binary_op(&self, raw_line: &str, raw_start: usize, raw_stop: usize) -> Option<(OP, usize)> {
        let mut pos = raw_line[raw_start..raw_stop].char_indices();

        loop {
            match pos.next() {
                None => return None,
                Some((p, c)) => {
                    if c.is_whitespace() { continue; }

                    let val = &raw_line[raw_start + p..];
                    for (repr, op) in BINARY_OP_STR.iter() {
                        if val.starts_with(repr) {
                            return Some((*op, raw_start + p + repr.len()));
                        }
                    }
                    return None;
                }
            }
        }
    }

    // attempts to read a delimited string literal from the string, allowing leading whitespace.
    // if a string is present, returns Ok with the binary string contents and the character index just after its ending quote, otherwise returns Err.
    pub(super) fn extract_string(&self, raw_line: &str, raw_start: usize, raw_stop: usize) -> Result<(Vec<u8>, usize), AsmError> {
        // find the next starting quote char
        let mut pos = raw_line[raw_start..raw_stop].char_indices();
        let (quote_pos, quote_char) = loop {
            match pos.next() {
                None => return err!(self, kind: ExpectedString, pos: raw_stop),
                Some((p, ch)) => {
                    if ['\'', '"'].contains(&ch) {
                        break (p, ch);
                    }
                    else if !ch.is_whitespace() {
                        return err!(self, kind: ExpectedString, pos: raw_start + p);
                    }
                }
            }
        };

        let mut res = vec![];
        let mut buf = [0u8; 4];

        // consume the entire string, applying escape sequences as needed
        loop {
            match pos.next() {
                None => return err!(self, kind: IncompleteString, pos: raw_start + quote_pos),
                Some((p, ch)) => {
                    if ch == quote_char {
                        return Ok((res, raw_start + p + 1));
                    }
                    else if ch == '\\' {
                        match pos.next() {
                            None => return err!(self, kind: IncompleteEscape, pos: raw_start + p),
                            Some((_, esc)) => {
                                if let Some(mapped) = match esc {
                                    '\\' => Some('\\'),
                                    '\'' => Some('\''),
                                    '"' => Some('"'),
                                    'n' => Some('\n'),
                                    't' => Some('\t'),
                                    'r' => Some('\r'),
                                    '0' => Some('\0'),
                                    'x' => {
                                        let mut vals = [0; 2];
                                        for val in vals.iter_mut() {
                                            *val = match pos.next().map(|(_, x)| x.to_digit(16)).flatten() {
                                                None => return err!(self, kind: IncompleteEscape, pos: raw_start + p),
                                                Some(v) => v,
                                            };
                                        }
                                        let val = vals[0] * 16 + vals[1];
                                        res.push(val as u8);
                                        None
                                    }
                                    _ => return err!(self, kind: InvalidEscape, pos: raw_start + p),
                                } {
                                    res.extend(mapped.encode_utf8(&mut buf).as_bytes());
                                }
                            }
                        }
                    }
                    else {
                        res.extend(ch.encode_utf8(&mut buf).as_bytes());
                    }
                }
            }
        }
    }

    // attempts to parse a sequence of 1+ comma-separated expressions.
    fn parse_comma_sep_exprs(&mut self, raw_line: &str, raw_start: usize, raw_stop: usize) -> Result<Vec<Expr>, AsmError> {
        let mut args = vec![];
        
        let mut pos = raw_start;
        loop {
            // extract an expr and add it to args
            let (expr, aft) = self.extract_expr(raw_line, pos, raw_stop)?;
            args.push(expr);

            // check if we have another arg after this one (comma)
            let mut tail = raw_line[aft..raw_stop].char_indices();
            loop {
                match tail.next() {
                    None => return Ok(args), // nothing after expr means we're done
                    Some((p, c)) => {
                        if c.is_whitespace() { continue; } // skip whitespace
                        else if c == ',' { pos = aft + p + 1; break; } // if we have a comma, we expect another arg
                        else { return err!(self, kind: ExpectedCommaBeforeToken, pos: aft + p); }
                    }
                }
            }
        }
    }

    // attempts to extract an expression from the string, allowing leading whitespace.
    // if a well-formed expression is found, returns Ok with it and the character index just after it, otherwise returns Err.
    pub(super) fn extract_expr(&mut self, raw_line: &str, raw_start: usize, raw_stop: usize) -> Result<(Expr, usize), AsmError> {
        let mut parsing_pos = raw_start;

        let mut unary_stack: Vec<OP> = Vec::with_capacity(8);
        let mut binary_stack: Vec<OP> = Vec::with_capacity(8);

        let mut output_stack: Vec<Expr> = Vec::with_capacity(8);

        loop {
            let mut chars = raw_line[parsing_pos..raw_stop].char_indices().peekable();

            // consume all unary ops up to a token and push onto unary stack
            debug_assert!(unary_stack.is_empty());
            let (term_start, numeric) = loop {
                match chars.peek().copied() {
                    None => return err!(self, kind: ExpectedExprTerm, pos: raw_stop),
                    Some((_, x)) if x.is_whitespace() || x == '+' => (), // whitespace and unary plus do nothing
                    Some((_, '-')) => unary_stack.push(OP::Neg),         // push unary ops onto the stack
                    Some((_, '!')) => unary_stack.push(OP::Not),
                    Some((p, c)) => break (parsing_pos + p, c.is_digit(10)), // otherwise is a token, which also means end of term
                }
                chars.next(); // if we get here, we consumed it
            };

            // move to next logical separator (white space, open paren, or binary op - but only at depth 0)
            // bin_op holds op and aft, token_stop holds one past end of token
            let mut paren_depth = 0usize;
            let (term_stop, bin_op) = loop {
                let end_content = chars.peek().cloned();
                match end_content {
                    // if there's not a next character we're either done (depth 0), or failed
                    None => {
                        if paren_depth == 0 { break (raw_stop, None); }
                        else { return err!(self, kind: MissingCloseParen, pos: raw_stop); }
                    }
                    // otherwise account for important characters
                    Some((p, ch)) => match ch {
                        '(' => {
                            if numeric {
                                return err!(self, kind: UnexpectedOpenParen, pos: p);
                            }
                            paren_depth += 1;
                        }
                        ')' => match paren_depth {
                            0 => return err!(self, kind: UnexpectedCloseParen, pos: p),
                            1 => match self.extract_binary_op(raw_line, parsing_pos + p + 1, raw_stop) { // this would drop down to level 0, so end of term
                                Some((op, aft)) => break (parsing_pos + p + 1, Some((op, aft))),
                                None => break (parsing_pos + p + 1, None),
                            }
                            _ => paren_depth -= 1,
                        }
                        '"' | '\'' => {
                            if numeric {
                                return err!(self, kind: UnexpectedString, pos: p);
                            }

                            let (_, aft) = self.extract_string(raw_line, p, raw_stop)?;  // if we run into a string, refer to the string extractor to get aft
                            advance_cursor(&mut chars, aft - 1, raw_stop); // jump to just before aft position (the end quote)
                            debug_assert_ne!(chars.peek().unwrap().0, p);
                            debug_assert_eq!(chars.peek().unwrap().1, ch); // sanity check: should not be same position, but should be same char
                        }
                        'e' | 'E' if numeric => {
                            if let Some((_, x)) = chars.clone().nth(1) {  // look at next char
                                if x == '+' || x == '-' { chars.next(); } // make sure an exponent sign won't be parsed as binary + or - by skipping it
                            }
                        }
                        _ => {
                            if paren_depth == 0 {
                                if let Some((op, aft)) = self.extract_binary_op(raw_line, parsing_pos + p, raw_stop) {
                                    break (parsing_pos + p, Some((op, aft))); // if we find a binary op, we're done
                                }
                                else if ch.is_whitespace() || ch == ',' || ch == ']' {
                                    break (parsing_pos + p, None); // otherwise if we're on a term-breaking char we're done (but we have no binary op)
                                }
                            }
                        }
                    }
                }
                chars.next(); // if we get here, we consumed the char
            };
            drop(chars); // we're done with this now and it's not guaranteed to be in correct position - drop it so it can't accidentally be used again

            // grab the term we just found
            let term = &raw_line[term_start..term_stop];
            debug_assert_eq!(term, term.trim());
            if term.is_empty() {
                return err!(self, kind: ExpectedExprTerm, pos: term_start);
            }

            let term_expr = match term.chars().next().unwrap() {
                '(' => { // if it's a sub-expression (paren grouped expr)
                    debug_assert_eq!(term.chars().rev().next().unwrap(), ')'); // last char of term should be a closing paren
                    let (expr, aft) = self.extract_expr(raw_line, term_start + 1, term_stop - 1)?; // parse interior as an expr
                    if !raw_line[aft..term_stop-1].trim_start().is_empty() {
                        return err!(self, kind: ParenInteriorNotExpr, pos: term_start); // we should be able to consume the whole interior
                    }
                    expr
                }
                '$' => match term { // if it's a user-level macro
                    "$" => { // current line macro
                        match SEG_OFFSETS.get(&self.current_seg) {
                            None => return err!(self, kind: IllegalInCurrentSegment, pos: term_start),
                            Some(ident) => (OP::Add, ExprData::Ident(ident.to_string()), self.line_pos_in_seg as i64).into(),
                        }
                    }
                    "$$" => { // start of seg macro
                        match SEG_ORIGINS.get(&self.current_seg) {
                            None => return err!(self, kind: IllegalInCurrentSegment, pos: term_start),
                            Some(ident) => ExprData::Ident(ident.to_string()).into(),
                        }
                    }
                    "$i" => { // times iter macro
                         match &self.times {
                            None => return err!(self, kind: TimesIterOutisideOfTimes, pos: term_start),
                            Some(info) => (info.current as u64).into(),
                         }
                    }
                    _ => { // otherwise it is either invalid or function-like - assume it's function-like
                        let paren_pos = match term.find('(') {
                            None => return err!(self, kind: UnrecognizedMacroInvocation, pos: term_start),
                            Some(p) => p,
                        };
                        if term.chars().rev().next() != Some(')') {
                            return err!(self, kind: UnrecognizedMacroInvocation, pos: term_start);
                        }
                        let func = &term[..paren_pos];
                        let args = self.parse_comma_sep_exprs(raw_line, term_start + paren_pos + 1, term_stop - 1)?;

                        match func {
                            "$ptr" => { // pointer macro - interns a binary value in the rodata segment and returns a pointer to its eventual location
                                if args.len() != 1 {
                                    return err!(self, kind: IncorrectArgCount, pos: term_start);
                                }
                                let arg = args.into_iter().next().unwrap();

                                let x = match arg.eval(&self.file.symbols) {
                                    Err(_) => return err!(self, kind: FailedCriticalExpression, pos: term_start),
                                    Ok(mut val) => match val.take_or_borrow().binary() {
                                        None => return err!(self, kind: ExpectedBinaryValue, pos: term_start),
                                        Some(content) => {
                                            if content.is_empty() {
                                                return err!(self, kind: EmptyBinaryValue, pos: term_start);
                                            }
                                            let idx = self.file.binary_set.add(content);
                                            ExprData::Ident(format!("{}{:x}", BINARY_LITERAL_SYMBOL_PREFIX, idx)).into()
                                        }
                                    }
                                };
                                x
                            }
                            "$if" => {
                                if args.len() != 3 {
                                    return err!(self, kind: IncorrectArgCount, pos: term_start);
                                }
                                let mut args = args.into_iter();
                                let cond = args.next().unwrap();
                                let left = args.next().unwrap();
                                let right = args.next().unwrap();
                                (OP::Condition, cond, Expr::from((OP::Pair, left, right))).into()
                            }
                            _ => match UNARY_FUNCTION_OPERATOR_TO_OP.get(func).copied() {
                                Some(op) => {
                                    if args.len() != 1 {
                                        return err!(self, kind: IncorrectArgCount, pos: term_start);
                                    }
                                    (op, args.into_iter().next().unwrap()).into()
                                }
                                None => {
                                    return err!(self, kind: UnrecognizedMacroInvocation, pos: term_start);
                                }
                            }
                        }
                    }
                }
                '\'' | '"' => { // if it's a string literal
                    debug_assert_eq!(term.chars().rev().next().unwrap(), term.chars().next().unwrap()); // first and last char should be the same
                    let (content, _) = self.extract_string(raw_line, term_start, term_stop)?;
                    ExprData::Value(Value::Binary(content)).into()
                }
                '0'..='9' => { // if it's a numeric constant
                    let (term_fix, signed) = match term { // check if signed/unsigned suffix and remove it if present
                        x if x.ends_with('u') => (&x[..x.len()-1], false),
                        x => (x, true),
                    };
                    let (term_fix, radix) = match term_fix { // check for radix prefix and remove it if present
                        x if x.starts_with("0x") => (&x[2..], 16),
                        x if x.starts_with("0o") => (&x[2..], 8),
                        x if x.starts_with("0b") => (&x[2..], 2),
                        x => (x, 10),
                    };
                    let term_fix = term_fix.replace('_', ""); // remove all underscores (allowed as group separators)

                    // terms should not have signs - this is handled by unary ops (and prevents e.g. 0x-5 instead of proper -0x5)
                    if term_fix.starts_with('+') || term_fix.starts_with('-') {
                        return err!(self, kind: IllFormedNumericLiteral, pos: term_start);
                    }

                    // parse it as correct type and propagate any errors
                    match signed {
                        false => match u64::from_str_radix(&term_fix, radix) {
                            Err(_) => return err!(self, kind: IllFormedNumericLiteral, pos: term_start), // failed unsigned is failure
                            Ok(v) => v.into(),
                        }
                        true => match i64::from_str_radix(&term_fix, radix) {
                            Err(_) => match Float::parse(term_fix) { // failed signed (int) could just mean that it's (signed) float
                                Err(_) => return err!(self, kind: IllFormedNumericLiteral, pos: term_start), // but if that fails too, it's a bust
                                Ok(v) => Float::with_val(PRECISION, v).into(),
                            }
                            Ok(v) => v.into(),
                        }
                    }
                }
                _ => match term { // otherwise it must be an keyword/identifier
                    "true" | "TRUE" => true.into(),
                    "false" | "FALSE" => false.into(),
                    "null" | "NULL" => Value::Pointer(0).into(),
                    _ => { // if none of above, must be an identifier
                        let mutated = self.mutate_name(raw_line, term_start, term_stop)?;
                        if !is_valid_symbol_name(&mutated) {
                            return err!(self, kind: InvalidSymbolName, pos: term_start); // we just need to make sure it's a valid name
                        }
                        ExprData::Ident(mutated).into()
                    }
                }
            };

            // update parsing pos - either after term (no bin op) or after bin op
            parsing_pos = match bin_op {
                None => term_stop,
                Some((_, aft)) => aft,
            };

            // add the term to the output
            output_stack.push(term_expr);

            // apply any unary ops to the term before we begin
            while let Some(op) = unary_stack.pop() {
                let last = output_stack.pop().unwrap();
                output_stack.push((op, last).into());
            }

            // handle the bin op (if present)
            match bin_op {
                Some((op, _)) => { // if there's an op, we need to handle precedence logic (shunting-yard algorithm)
                    // handle any required ops that are still on the stack
                    let op_prec = *PRECEDENCE.get(&op).unwrap();
                    loop {
                        let top = match binary_stack.last() {
                            None => break,
                            Some(op) => *op,
                        };
                        let top_prec = *PRECEDENCE.get(&top).unwrap();
                        if top_prec.0 >= op_prec.0 && (top_prec.0 != op_prec.0 || op_prec.1 != Associativity::Left) {
                            break;
                        }

                        // pop off op stack and put on output stack (but resolve the tree structure immediately)
                        binary_stack.pop();
                        let right = output_stack.pop().unwrap();
                        let left = output_stack.pop().unwrap();
                        output_stack.push((top, left, right).into()); // plop it back onto the output queue
                    }

                    // push this op onto the stack
                    binary_stack.push(op);
                }
                None => {
                    break; // if there wasn't a bin op, we're done parsing
                }
            }
        }

        // pop any remaining binary ops off the stack
        while let Some(op) = binary_stack.pop() {
            let right = output_stack.pop().unwrap();
            let left = output_stack.pop().unwrap();
            output_stack.push((op, left, right).into()); // plop it back onto the output queue
        }

        // there should now be only one thing in output, which is the result
        debug_assert_eq!(output_stack.len(), 1);
        let res = self.apply_ptrdiff(output_stack.into_iter().next().unwrap());

        Ok((res, parsing_pos))
    }

    fn get_ptr_offset<'a>(&'a self, expr: &'a Expr, base: &str) -> Option<Expr> {
        let target = match &*expr.data.borrow() {
            ExprData::Value(_) => return None,
            ExprData::Ident(ident) => {
                if ident == base { return Some(Value::Signed(0).into()); } // if this is the base itself, offset is zero (signed because we want the offset value)
                match self.file.symbols.get(ident) {
                    None => return None,
                    Some(symbol) => symbol,
                }
            }
            ExprData::Uneval { op: _, left: _, right: _ } => expr,
        };
        match &*target.data.borrow() {
            ExprData::Uneval { op: OP::Add, left, right } => match &*left.as_ref().unwrap().data.borrow() { // unwraps are ok cause we know we generated the value just before
                ExprData::Ident(ident) if ident == base => match &*right.as_ref().unwrap().data.borrow() {
                    ExprData::Value(Value::Signed(v)) => Some((*v).into()), // rhs of address should always be a signed constant (never needs to be evaluated)
                    _ => panic!("address improperly constructed"),
                }
                _ => None,
            }
            _ => None,
        }
    }
    // applies ptrdiff logic (e.g. $-$ == 0) to an expr and returns the resulting expression.
    // if no ptrdiff logic can be performed, returns the original expression,
    // otherwise returns a modified expression which is guaranteed to yield the same value.
    fn apply_ptrdiff(&self, expr: Expr) -> Expr {
        let (mut add, mut sub) = expr.break_add_sub();
        for base in PTRDIFF_IDS { // look for add/sub pairs that have a common base
            let a = add.iter_mut().filter_map(|x| self.get_ptr_offset(x, base).map(|r| (x, r)));
            let b = sub.iter_mut().filter_map(|x| self.get_ptr_offset(x, base).map(|r| (x, r)));
            for (a, b) in a.zip(b) {
                *a.0 = a.1; // every time we get a pair, replace them with their offset values
                *b.0 = b.1;
            }
        }

        // recurse to non-leaf children
        let recurse = |x: Expr| match x.data.into_inner() {
            x @ ExprData::Value(_) => Expr::from(x),
            x @ ExprData::Ident(_) => Expr::from(x),
            ExprData::Uneval { op, left, right } => {
                let left = left.map(|x| Box::new(self.apply_ptrdiff(*x)));
                let right = right.map(|x| Box::new(self.apply_ptrdiff(*x)));
                ExprData::Uneval { op, left, right }.into()
            }
        };
        let add = add.into_iter().map(recurse).collect();
        let sub = sub.into_iter().map(recurse).collect();

        Expr::chain_add_sub(add, sub).unwrap() // assemble the result
    }

    pub(super) fn extract_imm(&mut self, raw_line: &str, raw_start: usize, raw_stop: usize) -> Result<(Imm, usize), AsmError> {
        // check if we had an explicit size and get the expr start position (after size if present)
        let (token, token_stop) = grab_whitespace_sep_token(raw_line, raw_start, raw_stop);
        let (size, expr_start) = parse_size_str(token, token_stop, raw_start);

        // and finally, read the expr
        let (expr, aft) = self.extract_expr(raw_line, expr_start, raw_stop)?;
        Ok((Imm { expr, size }, aft))
    }
    pub(super) fn extract_address(&mut self, raw_line: &str, raw_start: usize, raw_stop: usize) -> Result<(Address, usize), AsmError> {
        // check if we had an explicit size and get the expr start position (after size if present)
        let (token, token_stop) = grab_whitespace_sep_token(raw_line, raw_start, raw_stop);
        if token.is_empty() {
            return err!(self, kind: ExpectedAddress, pos: raw_stop);
        }
        if let Some(p) = token.find('[') {
            let token_fix = &token[..p];
            if Caseless(token_fix) == Caseless("PTR") {
                return err!(self, kind: AddressPtrSpecWithoutSize, pos: token_stop - token.len());
            }
            if p != 0 { // if token has an open bracket that's not the first char then we have something bad
                if parse_size_str(token_fix, 0, 0).0.is_some() { // if we can parse it as a size, then we're missing ptr spec
                    return err!(self, kind: AddressSizeMissingPtr, pos: token_stop - token.len() + p);
                }
                else { // otherwise we have an unknown size
                    return err!(self, kind: AddressSizeNotRecognized, pos: token_stop - token.len());
                }
            }
        }
        if Caseless(token) == Caseless("PTR") {
            return err!(self, kind: AddressPtrSpecWithoutSize, pos: token_stop - token.len());
        }
        let (pointed_size, mut next_start) = parse_size_str(token, token_stop, raw_start);
        match pointed_size {
            Some(_) => { // explicit size requires the ptr specifier
                let (mut token, mut token_stop) = grab_whitespace_sep_token(raw_line, next_start, raw_stop);
                if let Some(p) = token.find('[') {
                    token_stop -= token.len() - p; // chop off at an open bracket if we have one
                    token = &token[..p];
                }
                if Caseless(token) == Caseless("PTR") { next_start = token_stop; }
                else { return err!(self, kind: AddressSizeMissingPtr, pos: token_stop - token.len()); }
            }
            None => { // if we failed to parse the size, we must start with an open bracket (just the address component)
                if token.chars().next() != Some('[') {
                    return err!(self, kind: AddressSizeNotRecognized, pos: token_stop - token.len());
                }
            }
        }

        // after the size part, we need to find the start of the core address component [expr]
        let address_start = match raw_line[next_start..raw_stop].find(|c: char| !c.is_whitespace()) {
            None => return err!(self, kind: ExpectedAddress, pos: raw_stop),
            Some(p) => next_start + p,
        };
        if raw_line[address_start..].chars().next().unwrap() != '[' {
            return err!(self, kind: ExpectedAddress, pos: address_start);
        }
        let (mut imm, imm_aft) = self.extract_imm(raw_line, address_start + 1, raw_stop)?;
        let (tail, tail_start) = trim_start_with_pos(raw_line, imm_aft, raw_stop);
        match tail.chars().next() {
            Some(']') => (),
            None => return err!(self, kind: UnterminatedAddress, pos: raw_stop),
            Some(_) => return err!(self, kind: AddressInteriorNotSingleExpr, pos: tail_start),
        }
        if let Some(size) = imm.size {
            match size {
                Size::Word | Size::Dword | Size::Qword => (),
                _ => return err!(self, kind: AddressSizeUnsupported, pos: address_start),
            }
        }

        // now we need to handle all the register arithmetic stuff
        let mut r1: Option<(u8, u8)> = None; // reg id and multiplier
        let mut r2: Option<u8> = None; // reg id
        for reg in CPU_REGISTER_INFO.iter() {
            if let Some(mult) = self.get_reg_mult(*reg.0, &imm.expr, address_start)? { // see if this register is present in the expression
                if reg.1.high { // first of all, high registers are not allowed (this is just for better error messages)
                    return err!(self, kind: AddressUseOfHighRegister, pos: address_start);
                }

                let mut mult = match mult.eval(&self.file.symbols) { // if it is then it must be a critical expression
                    Ok(mut val) => match &*val.take_or_borrow() {
                        Value::Signed(v) => *v,
                        _ => return err!(self, kind: AddressRegMultNotSignedInt, pos: address_start),
                    },
                    Err(_) => return err!(self, kind: AddressRegMultNotCriticalExpr, pos: address_start),
                };
                if mult == 0 { continue; } // if it's zero then it canceled out and we don't need it

                match imm.size { 
                    None => imm.size = Some(reg.1.size), // if we don't already have a required size, set it to this register size
                    Some(size) => if size != reg.1.size { // otherwise enforce pre-existing value
                        return err!(self, kind: AddressConflictingSizes, pos: address_start);
                    }
                }

                // if the multiplier is trivial or has a trivial component (of 1)
                if mult & 1 != 0 {
                    mult &= !1; // remove the trivial component
                    if r2.is_none() { r2 = Some(reg.1.id); } // prioritize putting it in r2 since r2 can't have a multiplier (other than 1)
                    else if r1.is_none() { r1 = Some((reg.1.id, 0)); } // otherwise we have to put it in r1 and give it a multiplier of 1 (mult code 0)
                    else { return err!(self, kind: AddressTooManyRegs, pos: address_start); } // if we don't have anywhere to put it, failure
                }
                // now, if a (non-trivial) component is present
                if mult != 0 {
                    let multcode = match mult { // decode the multiplier into its sizecode equivalent
                        1 => 0,
                        2 => 1,
                        4 => 2,
                        8 => 3,
                        _ => return err!(self, kind: AddressRegInvalidMult, pos: address_start),
                    };

                    if r1.is_none() { r1 = Some((reg.1.id, multcode)); }
                    else { return err!(self, kind: AddressTooManyRegs, pos: address_start); }
                }
            }
        }

        let size = match imm.size {
            None => Size::Qword, // if we still don't have an explicit address size, use 64-bit
            Some(size) => match size {
                Size::Word | Size::Dword | Size::Qword => size,
                _ => return err!(self, kind: AddressSizeUnsupported, pos: address_start), // unsupported addressing modes
            }
        };
        let base = {
            let present = match imm.expr.eval(&self.file.symbols) {
                Ok(v) => match &*v {
                    Value::Signed(v) => *v != 0, // if it's nonzero we have to keep it
                    _ => return err!(self, kind: AddressTypeUnsupported, pos: address_start), // if it's some other type it's invalid
                }
                Err(_) => true, // failure to evaluate means we can't statically elide it, so we assume it's present
            };
            if present { Some(imm.expr) } else { None }
        };

        //TODO: move this logic into the address writer insted of pre-computing it here
        // [1: base][1:][2: mult_1][2: size][1: r1][1: r2]   ([4: r1][4: r2])   ([size: base])
        // let a = (if base.is_some() { 0x80 } else { 0 }) | (r1.unwrap_or((0, 0)).1 << 4) | (size << 2) | (if r1.is_some() { 2 } else { 0 }) | (if r2.is_some() { 1 } else { 0 });
        // let b = (r1.unwrap_or((0, 0)).0 << 4) | r2.unwrap_or(0);
        Ok((Address { size, r1, r2, base, pointed_size }, imm_aft + 1))
    }
    fn get_reg_mult(&self, reg: Caseless<'_>, expr: &Expr, err_pos: usize) -> Result<Option<Expr>, AsmError> {
        let handle = &mut *expr.data.borrow_mut();
        match handle {
            ExprData::Value(_) => Ok(None),
            ExprData::Ident(ident) => {
                if Caseless(ident) == reg {
                    *handle = 0i64.into(); // if we got a register, replace it with zero
                    Ok(Some(1i64.into())) // report a multiplier of 1
                }
                else {
                    Ok(None)
                }
            }
            ExprData::Uneval { op, left, right } => {
                let a = match left.as_ref() {
                    None => return err!(self, kind: IllFormedExpr, pos: err_pos),
                    Some(x) => self.get_reg_mult(reg, x, err_pos)?,
                };
                match op {
                    OP::Neg => {
                        if let Some(_) = right.as_ref() { return err!(self, kind: IllFormedExpr, pos: err_pos); }
                        Ok(a.map(|t| (OP::Neg, t).into())) // just return the negative if we had something
                    }
                    OP::Add | OP::Sub => {
                        let b = match right.as_ref() {
                            None => return err!(self, kind: IllFormedExpr, pos: err_pos),
                            Some(x) => self.get_reg_mult(reg, x, err_pos)?,
                        };
                        
                        // if neither existed, return None, otherwise combine them with defaults of 0 if either is not present
                        if a.is_none() && b.is_none() { Ok(None) }
                        else { Ok(Some((*op, a.unwrap_or(0i64.into()), b.unwrap_or(0i64.into())).into())) }
                    }
                    OP::Mul => match a { // reg must not be present in both branches - this is done by allowing either as wildcard, which will always fail to evaluate
                        Some(a) => Ok(Some((OP::Mul, a, (**right.as_ref().unwrap()).clone()).into())), // return what we got times the other side (currently unmodified due to not recursing to it)
                        None => {
                            let b = match right.as_ref() {
                                None => return err!(self, kind: IllFormedExpr, pos: err_pos),
                                Some(x) => self.get_reg_mult(reg, x, err_pos)?,
                            };
                            match b {
                                Some(b) => Ok(Some((OP::Mul, (**left.as_ref().unwrap()).clone(), b).into())), // return what we got times the other side (currently unmodified do to left returning None)
                                None => Ok(None), // if we got nothing for both, report nothing
                            }
                        }
                    }
                    _ => { // for any other (unsuported) operation, just ensure that the register was not present
                        if let Some(_) = a {
                            return err!(self, kind: AddressRegIllegalOp, pos: err_pos);
                        }
                        if let Some(v) = right.as_ref() {
                            if let Some(_) = self.get_reg_mult(reg, v, err_pos)? {
                                return err!(self, kind: AddressRegIllegalOp, pos: err_pos);
                            }
                        }
                        Ok(None)
                    }
                }
            }
        }
    }

    /// Attempts to extract an argument from the string, be it a register, address, or imm.
    /// On success, returns the extracted argument and the index just after it.
    /// On failure, the returned error is from imm extraction due to being the most general.
    pub(super) fn extract_arg(&mut self, raw_line: &str, raw_start: usize, raw_stop: usize) -> Result<(Argument, usize), AsmError> {
        // first, try address, since they could parse as an expr if given explicit size
        if let Ok((addr, aft)) = self.extract_address(raw_line, raw_start, raw_stop) {
            return Ok((Argument::Address(addr), aft));
        }
        // then parse as imm - all registers are parseable as imm, then we extract them separately
        let (imm, aft) = self.extract_imm(raw_line, raw_start, raw_stop)?;
        // if it was only an identifier, it might be a register
        if let ExprData::Ident(ident) = &*imm.expr.data.borrow() {
            let res = if let Some(reg) = CPU_REGISTER_INFO.get(&Caseless(ident)) { Some(Argument::CPURegister(*reg)) }
            else if let Some(reg) = FPU_REGISTER_INFO.get(&Caseless(ident)) { Some(Argument::FPURegister(*reg)) }
            else if let Some(reg) = VPU_REGISTER_INFO.get(&Caseless(ident)) { Some(Argument::VPURegister(*reg)) }
            else { None };

            if let Some(res) = res {
                if let Some(_) = imm.size { // if it is indeed a register, we should not have a size specifier
                    return err!(self, kind: RegisterWithSizeSpec, pos: aft - ident.len());
                }
                return Ok((res, aft));
            }
        }
        // otherwise it was an expression
        Ok((Argument::Imm(imm), aft))
    }
}

#[cfg(test)]
fn create_context() -> AssembleArgs {
    AssembleArgs {
        file: ObjectFile {
            global_symbols: Default::default(),
            extern_symbols: Default::default(),

            symbols: Default::default(),

            text_align: Default::default(),
            rodata_align: Default::default(),
            data_align: Default::default(),
            bss_align: Default::default(),

            text_holes: Default::default(),
            rodata_holes: Default::default(),
            data_holes: Default::default(),

            text: Default::default(),
            rodata: Default::default(),
            data: Default::default(),
            bss_len: Default::default(),

            binary_set: Default::default(),
        },
    
        current_seg: AsmSegment::TEXT,
        done_segs: AsmSegment::RODATA,

        line: Default::default(),
        line_num: Default::default(),
        line_pos_in_seg: Default::default(),

        last_nonlocal_label: Default::default(),
        label_def: Default::default(),

        times: Default::default(),

        op: Default::default(),
        args: Default::default(),
    }
}

#[test]
fn test_extr_bin_op() {
    let c = create_context();

    match c.extract_binary_op("+", 0, 1) {
        Some((op ,aft)) => {
            assert_eq!(op, OP::Add);
            assert_eq!(aft, 1);
        }
        None => panic!(),
    }
    match c.extract_binary_op("    +  ", 2, 7) {
        Some((op, aft)) => {
            assert_eq!(op, OP::Add);
            assert_eq!(aft, 5);
        }
        None => panic!(),
    }
    match c.extract_binary_op("    a  ", 2, 7) {
        Some(_) => panic!(),
        None => (),
    }
}

#[test]
fn test_extr_string() {
    let c = create_context();

    match c.extract_string("'hello world'", 0, 13) {
        Ok((res, aft)) => {
            assert_eq!(res, "hello world".as_bytes());
            assert_eq!(aft, 13);
        }
        Err(_) => panic!(),
    }
    match c.extract_string("hello      ' wo rld'  ", 5, 22) {
        Ok((res, aft)) => {
            assert_eq!(res, " wo rld".as_bytes());
            assert_eq!(aft, 20);
        }
        Err(_) => panic!(),
    }
    match c.extract_string("hello      ' wo rld' b ", 12, 22) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.kind, AsmErrorKind::ExpectedString);
            assert_eq!(e.pos, 13);
        }
    }
    match c.extract_string("hello      ' wo rld'y ", 5, 19) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.kind, AsmErrorKind::IncompleteString);
            assert_eq!(e.pos, 11);
        }
    }
    match c.extract_string("hello      ' wo rld'  ", 5, 11) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.kind, AsmErrorKind::ExpectedString);
            assert_eq!(e.pos, 11);
        }
    }
    match c.extract_string("hello      ' wo rld'  ", 5, 12) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.kind, AsmErrorKind::IncompleteString);
            assert_eq!(e.pos, 11);
        }
    }
    match c.extract_string("\"\\\\\\'\\\"'\\n\\t\\r\\0\\x12\\xfe\"\t ", 0, 25) {
        Ok((res, aft)) => {
            assert_eq!(res, &[92, 39, 34, 39, 10, 9, 13, 0, 0x12, 0xfe]);
            assert_eq!(aft, 25);
        }
        Err(_) => panic!(),
    }
    match c.extract_string("'\\\\\\'\\\"\"\\n\\t\\r\\0\\x12\\xfe'\t ", 0, 25) {
        Ok((res, aft)) => {
            assert_eq!(res, &[92, 39, 34, 34, 10, 9, 13, 0, 0x12, 0xfe]);
            assert_eq!(aft, 25);
        }
        Err(_) => panic!(),
    }
    match c.extract_string("  'hello world' 'another string' ", 1, 33) {
        Ok((res, aft)) => {
            assert_eq!(res, "hello world".as_bytes());
            assert_eq!(aft, 15);
        }
        Err(_) => panic!(),
    }
    match c.extract_string("  'hello world' 'another string' ", 14, 33) {
        Ok((res, aft)) => {
            assert_eq!(res, " ".as_bytes());
            assert_eq!(aft, 17);
        }
        Err(_) => panic!(),
    }
    match c.extract_string("  '\\y'y", 2, 7) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.kind, AsmErrorKind::InvalidEscape);
            assert_eq!(e.pos, 3);
        }
    }
    match c.extract_string("  '\\x'", 1, 6) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.kind, AsmErrorKind::IncompleteEscape);
            assert_eq!(e.pos, 3);
        }
    }
    match c.extract_string("  '\\x5'", 1, 7) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.kind, AsmErrorKind::IncompleteEscape);
            assert_eq!(e.pos, 3);
        }
    }
    match c.extract_string("  '\\x5g'", 2, 8) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.kind, AsmErrorKind::IncompleteEscape);
            assert_eq!(e.pos, 3);
        }
    }
    match c.extract_string("  '\\x", 2, 5) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.kind, AsmErrorKind::IncompleteEscape);
            assert_eq!(e.pos, 3);
        }
    }
    match c.extract_string("  '\\x4", 1, 6) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.kind, AsmErrorKind::IncompleteEscape);
            assert_eq!(e.pos, 3);
        }
    }
    match c.extract_string("  '\\x4b", 2, 7) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.kind, AsmErrorKind::IncompleteString);
            assert_eq!(e.pos, 2);
        }
    }
    match c.extract_string("  '\\", 1, 4) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.kind, AsmErrorKind::IncompleteEscape);
            assert_eq!(e.pos, 3);
        }
    }
}

#[test]
fn test_extr_expr() {
    let mut c = create_context();
    match c.extract_expr("true", 0, 4) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 4);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Logical(val)) => assert_eq!(val, true),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("false", 0, 5) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 5);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Logical(val)) => assert_eq!(val, false),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("5", 0, 1) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 1);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 5),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("7u", 0, 2) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 2);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Unsigned(val)) => assert_eq!(val, 7),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("3.14", 0, 4) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 4);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Floating(val)) => assert!(Float::from(val - 3.14).abs() < 0.00000001),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("5+8", 0, 3) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 3);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 13),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("5+8*2-1", 0, 7) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 7);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 20),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("(5+1)*(5-1) g", 0, 13) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 11);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 24),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("  (  5-3 )     *--+ -(5 -1)f  ", 1, 30) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 27);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, -8),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("$if(true,6 / -2,3 << 2)", 0, 23) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 23);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, -3),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("   $if(  false == true  ,    6 / -  2 ,  3 << 2   )  ", 1, 53) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 51);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 12),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
}
#[test]
fn test_ptriff() {
    let mut c = create_context();
    c.file.symbols.define("foo".into(), (OP::Add, Expr::from(ExprData::Ident("#t".into())), 10i64).into()).unwrap();
    c.file.symbols.define("bar".into(), (OP::Add, Expr::from(ExprData::Ident("#t".into())), 14i64).into()).unwrap();
    match c.extract_expr("$-$", 0, 3) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 3);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 0),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("    $ + 3  + 3 - 1 - 2  - -- $ - 2 + 1  ", 2, 40) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 38);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 2),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("5*(($ + 8)-($ - 3))", 0, 19) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 19);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 55),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("foo-foo", 0, 7) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 7);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 0),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("foo-$", 0, 5) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 5);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 10),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("$-foo", 0, 5) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 5);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, -10),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("bar-foo", 0, 7) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 7);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 4),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
}
#[test]
fn test_numeric_formats() {
    let mut c = create_context();
    match c.extract_expr("0x2Ff4", 0, 6) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 6);
            match expr.eval(&c.file.symbols) {
                Ok(v) => match &*v {
                    Value::Signed(v) => assert_eq!(*v, 0x2Ff4),
                    x => panic!("unexpected type: {:?}", x),
                }
                Err(e) => panic!("{:?}", e),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("0x2Ff4u", 0, 7) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 7);
            match expr.eval(&c.file.symbols) {
                Ok(v) => match &*v {
                    Value::Unsigned(v) => assert_eq!(*v, 0x2Ff4),
                    x => panic!("unexpected type: {:?}", x),
                }
                Err(e) => panic!("{:?}", e),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("0o23_34", 0, 7) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 7);
            match expr.eval(&c.file.symbols) {
                Ok(v) => match &*v {
                    Value::Signed(v) => assert_eq!(*v, 0o23_34),
                    x => panic!("unexpected type: {:?}", x),
                }
                Err(e) => panic!("{:?}", e),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("0o23_34_u", 0, 9) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 9);
            match expr.eval(&c.file.symbols) {
                Ok(v) => match &*v {
                    Value::Unsigned(v) => assert_eq!(*v, 0o23_34),
                    x => panic!("unexpected type: {:?}", x),
                }
                Err(e) => panic!("{:?}", e),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("0b1011_0010", 0, 11) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 11);
            match expr.eval(&c.file.symbols) {
                Ok(v) => match &*v {
                    Value::Signed(v) => assert_eq!(*v, 0b1011_0010),
                    x => panic!("unexpected type: {:?}", x),
                }
                Err(e) => panic!("{:?}", e),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("0b1011_0010u", 0, 12) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 12);
            match expr.eval(&c.file.symbols) {
                Ok(v) => match &*v {
                    Value::Unsigned(v) => assert_eq!(*v, 0b1011_0010),
                    x => panic!("unexpected type: {:?}", x),
                }
                Err(e) => panic!("{:?}", e),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
}
#[test]
fn test_address_parser() {
    let mut c = create_context();
    match c.extract_address("   dword     ptr  [0x2334]  ", 2, 28) {
        Ok((addr, aft)) => {
            assert_eq!(aft, 26);
            assert_eq!(addr.size, Size::Qword);
            assert_eq!(addr.r1, None);
            assert_eq!(addr.r2, None);
            assert_eq!(addr.pointed_size, Some(Size::Dword));
            match addr.base.as_ref().unwrap().eval(&c.file.symbols) {
                Ok(v) => match &*v {
                    Value::Signed(v) => assert_eq!(*v, 0x2334),
                    x => panic!("unexpected type {:?}", x),
                }
                Err(e) => panic!("{:?}", e),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_address(".  tword     ptr  [4*eax] _", 2, 27) {
        Ok((addr, aft)) => {
            assert_eq!(aft, 25);
            assert_eq!(addr.size, Size::Dword);
            assert_eq!(addr.r1, Some((0, 2)));
            assert_eq!(addr.r2, None);
            assert_eq!(addr.pointed_size, Some(Size::Tword));
            assert!(addr.base.is_none());
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_address(".  tword     ptr  [3*eax + EaX] _", 2, 33) {
        Ok((addr, aft)) => {
            assert_eq!(aft, 31);
            assert_eq!(addr.size, Size::Dword);
            assert_eq!(addr.r1, Some((0, 2)));
            assert_eq!(addr.r2, None);
            assert_eq!(addr.pointed_size, Some(Size::Tword));
            assert!(addr.base.is_none());
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_address("   tword     ptr  [ax+bx]  ", 2, 27) {
        Ok((addr, aft)) => {
            assert_eq!(aft, 25);
            assert_eq!(addr.size, Size::Word);
            assert_eq!(addr.r1.unwrap().1, 0);
            assert_eq!(addr.r1.unwrap().0 + addr.r2.unwrap(), 1);
            assert_eq!(addr.pointed_size, Some(Size::Tword));
            assert!(addr.base.is_none());
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_address("   zmMword     ptr  [4*(r8d + 7)]   ", 2, 36) {
        Ok((addr, aft)) => {
            assert_eq!(aft, 33);
            assert_eq!(addr.size, Size::Dword);
            assert_eq!(addr.r1, Some((8, 2)));
            assert_eq!(addr.r2, None);
            assert_eq!(addr.pointed_size, Some(Size::Zmmword));
            match addr.base.as_ref().unwrap().eval(&c.file.symbols) {
                Ok(v) => match &*v {
                    Value::Signed(v) => assert_eq!(*v, 28),
                    x => panic!("unexpected type {:?}", x),
                }
                Err(e) => panic!("{:?}", e),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_address("  [4*(4 * (2 + r8) + (7 + -r8 * (1 + 1 * 1))) + R8] g ", 2, 54) {
        Ok((addr, aft)) => {
            assert_eq!(aft, 51);
            assert_eq!(addr.size, Size::Qword);
            assert_eq!(addr.r1, Some((8, 3)));
            assert_eq!(addr.r2, Some(8));
            assert_eq!(addr.pointed_size, None);
            match addr.base.as_ref().unwrap().eval(&c.file.symbols) {
                Ok(v) => match &*v {
                    Value::Signed(v) => assert_eq!(*v, 60),
                    x => panic!("unexpected type {:?}", x),
                }
                Err(e) => panic!("{:?}", e),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_address("[5*ax] extra stuff after", 0, 24) {
        Ok((addr, aft)) => {
            assert_eq!(aft, 6);
            assert_eq!(addr.size, Size::Word);
            assert_eq!(addr.r1, Some((0, 2)));
            assert_eq!(addr.r2, Some(0));
            assert_eq!(addr.pointed_size, None);
            assert!(addr.base.is_none());
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_address("   5 * ax]  ", 2, 12) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 3);
            assert_eq!(e.kind, AsmErrorKind::AddressSizeNotRecognized);
        }
    }
    match c.extract_address("   [5 * ax  ", 2, 12) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 12);
            assert_eq!(e.kind, AsmErrorKind::UnterminatedAddress);
        }
    }
    match c.extract_address("   word [5 * ax  ", 2, 17) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 8);
            assert_eq!(e.kind, AsmErrorKind::AddressSizeMissingPtr);
        }
    }
    match c.extract_address("   wOrd[5 * ax  ", 2, 16) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 7);
            assert_eq!(e.kind, AsmErrorKind::AddressSizeMissingPtr);
        }
    }
    match c.extract_address("   WORD ptr[5 * ax  ", 2, 20) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 20);
            assert_eq!(e.kind, AsmErrorKind::UnterminatedAddress);
        }
    }
    match c.extract_address("   word ptr[9 * ax]  ", 2, 21) {
        Ok((addr, aft)) => {
            assert_eq!(aft, 19);
            assert_eq!(addr.size, Size::Word);
            assert_eq!(addr.r1, Some((0, 3)));
            assert_eq!(addr.r2, Some(0));
            assert_eq!(addr.pointed_size, Some(Size::Word));
            assert!(addr.base.is_none());
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_address("  word pTr[   ]  ", 1, 17) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 14);
            assert_eq!(e.kind, AsmErrorKind::ExpectedExprTerm);
        }
    }
    match c.extract_address("  word ptr[]  ", 1, 14) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 11);
            assert_eq!(e.kind, AsmErrorKind::ExpectedExprTerm);
        }
    }
    match c.extract_address("  word ptr[a b]  ", 1, 17) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 13);
            assert_eq!(e.kind, AsmErrorKind::AddressInteriorNotSingleExpr);
        }
    }
    match c.extract_address("  ptr[45]  ", 1, 11) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 2);
            assert_eq!(e.kind, AsmErrorKind::AddressPtrSpecWithoutSize);
        }
    }
    match c.extract_address("  ptr [45]  ", 1, 12) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 2);
            assert_eq!(e.kind, AsmErrorKind::AddressPtrSpecWithoutSize);
        }
    }
    match c.extract_address("  sefsfsd[45]  ", 1, 11) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 2);
            assert_eq!(e.kind, AsmErrorKind::AddressSizeNotRecognized);
        }
    }
    match c.extract_address("  sefsfsd [45]  ", 1, 12) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 2);
            assert_eq!(e.kind, AsmErrorKind::AddressSizeNotRecognized);
        }
    }
    match c.extract_address("          ", 1, 10) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 10);
            assert_eq!(e.kind, AsmErrorKind::ExpectedAddress);
        }
    }
    match c.extract_address("  [  byte 45]   ", 1, 16) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 2);
            assert_eq!(e.kind, AsmErrorKind::AddressSizeUnsupported);
        }
    }
    match c.extract_address("  [tword 45]   ", 1, 15) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 2);
            assert_eq!(e.kind, AsmErrorKind::AddressSizeUnsupported);
        }
    }
    match c.extract_address("  [ xmmword 45]   ", 1, 18) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 2);
            assert_eq!(e.kind, AsmErrorKind::AddressSizeUnsupported);
        }
    }
    match c.extract_address("  [ ymmword 45]   ", 1, 18) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 2);
            assert_eq!(e.kind, AsmErrorKind::AddressSizeUnsupported);
        }
    }
    match c.extract_address("  [ zmmword 45]   ", 1, 18) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 2);
            assert_eq!(e.kind, AsmErrorKind::AddressSizeUnsupported);
        }
    }
    match c.extract_address("  word ptr [al]   ", 1, 18) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 11);
            assert_eq!(e.kind, AsmErrorKind::AddressSizeUnsupported);
        }
    }
    match c.extract_address("  [ah]   ", 1, 9) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 2);
            assert_eq!(e.kind, AsmErrorKind::AddressUseOfHighRegister);
        }
    }
    match c.extract_address("  [ax*bx]   ", 1, 12) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 2);
            assert_eq!(e.kind, AsmErrorKind::AddressRegMultNotCriticalExpr);
        }
    }
    match c.extract_address("  [ax*ax]   ", 1, 12) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, 2);
            assert_eq!(e.kind, AsmErrorKind::AddressRegMultNotCriticalExpr);
        }
    }
}
#[test]
fn test_parse_arg() {
    let mut c = create_context();
    match c.extract_arg("g RaX g", 1, 7).unwrap() {
        (Argument::CPURegister(CPURegisterInfo { id: 0, size: Size::Qword, high: false }), 5) => (),
        e => panic!("wrong value: {:?}", e),
    }
    match c.extract_arg("g sT0 g", 1, 7).unwrap() {
        (Argument::FPURegister(FPURegisterInfo { id: 0 }), 5) => (),
        e => panic!("wrong value: {:?}", e),
    }
    match c.extract_arg("g XmM0 g", 1, 8).unwrap() {
        (Argument::VPURegister(VPURegisterInfo { id: 0, size: Size::Xmmword }), 6) => (),
        e => panic!("wrong value: {:?}", e),
    }
    match c.extract_arg("g bYte PtR [20+rax] g", 1, 21).unwrap() {
        (Argument::Address(Address { .. }), 19) => (),
        e => panic!("wrong value: {:?}", e),
    }
    match c.extract_arg("g foo + bar g", 1, 13).unwrap() {
        (Argument::Imm(Imm { .. }), 11) => (),
        e => panic!("wrong value: {:?}", e),
    }
    match c.extract_arg("       ", 1, 7) {
        Ok(x) => panic!("{:?}", x),
        Err(e) => {
            assert_eq!(e.pos, 7);
            assert_eq!(e.kind, AsmErrorKind::ExpectedExprTerm);
        }
    }
}