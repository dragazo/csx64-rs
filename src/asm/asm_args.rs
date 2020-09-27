use std::iter::Peekable;
use std::str::CharIndices;
use std::collections::VecDeque;
use std::borrow::Cow;
use std::cell;

use super::*;
use super::expr::{ExprData, OP, Value, ValueVariants};

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

pub(super) struct Imm {
    pub(super) expr: Expr,
    pub(super) sizecode: Option<u8>,

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
                        else { println!("{}..{}", raw_start, raw_stop); return err!(self, kind: MissingCloseParen, pos: raw_stop); }
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
                                else if ch.is_whitespace() || ch == ',' {
                                    break (parsing_pos + p, None); // otherwise if we're on whitespace or comma we're done (but we have no binary op)
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
                            Err(_) => match term_fix.parse::<f64>() { // failed signed (int) could just mean that it's (signed) float
                                Err(_) => return err!(self, kind: IllFormedNumericLiteral, pos: term_start), // but if that fails too, it's a bust
                                Ok(v) => v.into(),
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
                if ident == base { return Some(Value::Pointer(0).into()); } // if this is the base itself, offset is zero
                match self.file.symbols.get(ident) {
                    None => return None,
                    Some(symbol) => symbol,
                }
            }
            ExprData::Uneval { op: _, left: _, right: _ } => expr,
        };
        match &*target.data.borrow() {
            ExprData::Uneval { op: OP::Add, left, right } => match &*left.as_ref().unwrap().data.borrow() {
                ExprData::Ident(ident) if ident == base => Some((**right.as_ref().unwrap()).clone()),
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
        // extract the first whitespace separated thing (done like this cause we need index
        let token_start = match raw_line[raw_start..raw_stop].find(|c: char| !c.is_whitespace()) {
            None => return err!(self, kind: ExpectedExprTerm, pos: raw_stop),
            Some(p) => raw_start + p,
        };
        let token_stop = match raw_line[token_start..raw_stop].find(|c: char| c.is_whitespace()) {
            None => raw_stop,
            Some(p) => token_start + p,
        };

        // check if we had an explicit size and get the expr start position (after size if present)
        let (sizecode, expr_start) = match &raw_line[token_start..token_stop] {
            "byte" => (Some(0), token_stop),
            "word" => (Some(1), token_stop),
            "dword" => (Some(2), token_stop),
            "qword" => (Some(3), token_stop),
            _ => (None, token_start),
        };

        // and finally, read the expr
        let (expr, aft) = self.extract_expr(raw_line, expr_start, raw_stop)?;
        Ok((Imm { expr, sizecode }, aft))
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
    match c.extract_string("hello      ' wo rld'  ", 12, 22) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.kind, AsmErrorKind::ExpectedString);
            assert_eq!(e.pos, 13);
        }
    }
    match c.extract_string("hello      ' wo rld'  ", 5, 19) {
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
    match c.extract_string("  '\\y'", 2, 6) {
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
    let s = SymbolTable::new();

    match c.extract_expr("true", 0, 4) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 4);
            match expr.eval(&s).unwrap().take_or_borrow() {
                Cow::Owned(Value::Logical(val)) => assert_eq!(val, true),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("false", 0, 5) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 5);
            match expr.eval(&s).unwrap().take_or_borrow() {
                Cow::Owned(Value::Logical(val)) => assert_eq!(val, false),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("5", 0, 1) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 1);
            match expr.eval(&s).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 5),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("7u", 0, 2) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 2);
            match expr.eval(&s).unwrap().take_or_borrow() {
                Cow::Owned(Value::Unsigned(val)) => assert_eq!(val, 7),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("3.14", 0, 4) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 4);
            match expr.eval(&s).unwrap().take_or_borrow() {
                Cow::Owned(Value::Floating(val)) => assert!((val - 3.14).abs() < 0.00000001),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }

    match c.extract_expr("5+8", 0, 3) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 3);
            match expr.eval(&s).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 13),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("5+8*2-1", 0, 7) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 7);
            match expr.eval(&s).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 20),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("(5+1)*(5-1)", 0, 11) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 11);
            match expr.eval(&s).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 24),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("  (  5-3 )     *--+ -(5 -1)  ", 1, 29) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 27);
            match expr.eval(&s).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, -8),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("$if(true,6 / -2,3 << 2)", 0, 23) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 23);
            match expr.eval(&s).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, -3),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("   $if(  false == true  ,    6 / -  2 ,  3 << 2   )  ", 1, 53) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 51);
            match expr.eval(&s).unwrap().take_or_borrow() {
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
    let s = SymbolTable::new();

    match c.extract_expr("$-$", 0, 3) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 3);
            match expr.eval(&s).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 0),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("    $ + 3  + 3 - 1 - 2  - -- $ - 2 + 1  ", 2, 40) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 38);
            match expr.eval(&s).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 2),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("5*(($ + 8)-($ - 3))", 0, 19) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 19);
            match expr.eval(&s).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 55),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
}