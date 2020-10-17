use std::iter::{self, Peekable};
use std::str::CharIndices;
use rug::Float;

use super::*;
use super::expr::{ExprData, OP, Value, ValueVariants, PRECISION};
use super::caseless::Caseless;

#[cfg(test)]
use std::borrow::Cow;

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

fn parse_size_str(val: &str, success: usize, failure: usize) -> (Option<Size>, usize) {
    match SIZE_KEYWORDS.get(&Caseless(val)) {
        Some(size) => (Some(*size), success),
        None => (None, failure),
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) struct TimesInfo {
    pub(super) total_count: u64,
    pub(super) current: u64,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Locality {
    Local,
    Nonlocal,
}

pub(super) struct AssembleArgs<'a> {
    pub(super) file_name: &'a str,
    pub(super) file: ObjectFile,
    
    pub(super) current_seg: Option<AsmSegment>,
    pub(super) done_segs: Vec<AsmSegment>,

    pub(super) line_num: usize,
    pub(super) line_pos_in_seg: usize,

    pub(super) last_nonlocal_label: Option<String>,
    pub(super) label_def: Option<(String, Locality)>,

    pub(super) times: Option<TimesInfo>,
}
impl AssembleArgs<'_> {
    /// Updates the segment positioning info.
    /// This must be called prior to parsing a line (includingthe header), and once before each first-order assembly action (times iter).
    pub(super) fn update_line_pos_in_seg(&mut self) {
        match self.current_seg {
            None => (),
            Some(AsmSegment::Text) => self.line_pos_in_seg = self.file.text.len(),
            Some(AsmSegment::Rodata) => self.line_pos_in_seg = self.file.rodata.len(),
            Some(AsmSegment::Data) => self.line_pos_in_seg = self.file.data.len(),
            Some(AsmSegment::Bss) => self.line_pos_in_seg = self.file.bss_len,
        }
    }

    // attempt to mutate a symbol name from the line, transforming local symbols names to their full name.
    fn mutate_name(&self, name: &str, err_pos: usize) -> Result<(String, Locality), AsmError> {
        if name.starts_with('.') {
            // local can't be empty after dot or be followed by a digit (ambig floating point)
            if name.len() <= 1 || name.chars().nth(1).unwrap().is_digit(10) { return Err(AsmError { kind: AsmErrorKind::InvalidSymbolName, line_num: self.line_num, pos: Some(err_pos), inner_err: None }); }
            match &self.last_nonlocal_label {
                None => return Err(AsmError { kind: AsmErrorKind::LocalSymbolBeforeNonlocal, line_num: self.line_num, pos: Some(err_pos), inner_err: None }),
                Some(nonlocal) => {
                    let mutated = format!("{}{}", nonlocal, name);
                    if !is_valid_symbol_name(&mutated) { return Err(AsmError { kind: AsmErrorKind::InvalidSymbolName, line_num: self.line_num, pos: Some(err_pos), inner_err: None }); }
                    Ok((mutated, Locality::Local))
                }
            }
        }
        else {
            if !is_valid_symbol_name(name) { return Err(AsmError { kind: AsmErrorKind::InvalidSymbolName, line_num: self.line_num, pos: Some(err_pos), inner_err: None }); }
            Ok((name.into(), Locality::Nonlocal))
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
    fn extract_string(&self, raw_line: &str, raw_start: usize, raw_stop: usize) -> Result<(Vec<u8>, usize), AsmError> {
        // find the next starting quote char
        let mut pos = raw_line[raw_start..raw_stop].char_indices();
        let (quote_pos, quote_char) = loop {
            match pos.next() {
                None => return Err(AsmError { kind: AsmErrorKind::ExpectedString, line_num: self.line_num, pos: Some(raw_stop), inner_err: None }),
                Some((p, ch)) => {
                    if ['\'', '"'].contains(&ch) {
                        break (p, ch);
                    }
                    else if !ch.is_whitespace() {
                        return Err(AsmError { kind: AsmErrorKind::ExpectedString, line_num: self.line_num, pos: Some(raw_start + p), inner_err: None });
                    }
                }
            }
        };

        let mut res = vec![];
        let mut buf = [0u8; 4];

        // consume the entire string, applying escape sequences as needed
        loop {
            match pos.next() {
                None => return Err(AsmError { kind: AsmErrorKind::IncompleteString, line_num: self.line_num, pos: Some(raw_start + quote_pos), inner_err: None }),
                Some((p, ch)) => {
                    if ch == quote_char {
                        return Ok((res, raw_start + p + 1));
                    }
                    else if ch == '\\' {
                        match pos.next() {
                            None => return Err(AsmError { kind: AsmErrorKind::IncompleteEscape, line_num: self.line_num, pos: Some(raw_start + p), inner_err: None }),
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
                                                None => return Err(AsmError { kind: AsmErrorKind::IncompleteEscape, line_num: self.line_num, pos: Some(raw_start + p), inner_err: None }),
                                                Some(v) => v,
                                            };
                                        }
                                        let val = vals[0] * 16 + vals[1];
                                        res.push(val as u8);
                                        None
                                    }
                                    _ => return Err(AsmError { kind: AsmErrorKind::InvalidEscape, line_num: self.line_num, pos: Some(raw_start + p), inner_err: None }),
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
                        else { return Err(AsmError { kind: AsmErrorKind::ExpectedCommaBeforeToken, line_num: self.line_num, pos: Some(aft + p, ), inner_err: None }); }
                    }
                }
            }
        }
    }

    // attempts to extract an expression from the string, allowing leading whitespace.
    // if a well-formed expression is found, returns Ok with it and the character index just after it, otherwise returns Err.
    fn extract_expr(&mut self, raw_line: &str, raw_start: usize, raw_stop: usize) -> Result<(Expr, usize), AsmError> {
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
                    None => return Err(AsmError { kind: AsmErrorKind::ExpectedExprTerm, line_num: self.line_num, pos: Some(raw_stop), inner_err: None }),
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
                        else { return Err(AsmError { kind: AsmErrorKind::MissingCloseParen, line_num: self.line_num, pos: Some(raw_stop), inner_err: None }); }
                    }
                    // otherwise account for important characters
                    Some((p, ch)) => match ch {
                        '(' => {
                            if numeric { return Err(AsmError { kind: AsmErrorKind::UnexpectedOpenParen, line_num: self.line_num, pos: Some(p), inner_err: None }); }
                            paren_depth += 1;
                        }
                        ')' => match paren_depth {
                            0 => return Err(AsmError { kind: AsmErrorKind::UnexpectedCloseParen, line_num: self.line_num, pos: Some(p), inner_err: None }),
                            1 => match self.extract_binary_op(raw_line, parsing_pos + p + 1, raw_stop) { // this would drop down to level 0, so end of term
                                Some((op, aft)) => break (parsing_pos + p + 1, Some((op, aft))),
                                None => break (parsing_pos + p + 1, None),
                            }
                            _ => paren_depth -= 1,
                        }
                        '"' | '\'' => {
                            if numeric { return Err(AsmError { kind: AsmErrorKind::UnexpectedString, line_num: self.line_num, pos: Some(p), inner_err: None }); }
                            let (_, aft) = self.extract_string(raw_line, p, raw_stop)?;  // if we run into a string, refer to the string extractor to get aft
                            advance_cursor(&mut chars, aft - 1 - raw_start, raw_stop); // jump to just before aft position (the end quote) (account for base index change)
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
                                else if ch.is_whitespace() || ch == ',' || ch == ']' || ch == COMMENT_CHAR {
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
            if term.is_empty() { return Err(AsmError { kind: AsmErrorKind::ExpectedExprTerm, line_num: self.line_num, pos: Some(term_start), inner_err: None }); }

            let term_expr = match term.chars().next().unwrap() {
                '(' => { // if it's a sub-expression (paren grouped expr)
                    debug_assert_eq!(term.chars().rev().next().unwrap(), ')'); // last char of term should be a closing paren
                    let (expr, aft) = self.extract_expr(raw_line, term_start + 1, term_stop - 1)?; // parse interior as an expr
                    match raw_line[aft..term_stop-1].trim_start().chars().next() {
                        None => (),
                        Some(x) if x == COMMENT_CHAR => return Err(AsmError { kind: AsmErrorKind::MissingCloseParen, line_num: self.line_num, pos: Some(aft), inner_err: None }),
                        Some(_) => return Err(AsmError { kind: AsmErrorKind::ParenInteriorNotExpr, line_num: self.line_num, pos: Some(term_start), inner_err: None }), // we should be able to consume the whole interior
                    }
                    expr
                }
                '$' => match term { // if it's a user-level macro
                    "$" => match self.current_seg { // current line macro
                        None => return Err(AsmError { kind: AsmErrorKind::IllegalInCurrentSegment, line_num: self.line_num, pos: Some(term_start), inner_err: None }),
                        Some(seg) => (OP::Add, ExprData::Ident(get_seg_offset_str(seg).into()), self.line_pos_in_seg as i64).into(),
                    }
                    "$$" => match self.current_seg { // start of seg macro
                        None => return Err(AsmError { kind: AsmErrorKind::IllegalInCurrentSegment, line_num: self.line_num, pos: Some(term_start), inner_err: None }),
                        Some(seg) => ExprData::Ident(get_seg_origin_str(seg).into()).into(),
                    }
                    "$file" => Value::Binary(self.file_name.as_bytes().into()).into(),
                    "$i" => match &self.times { // times iter macro
                        None => return Err(AsmError { kind: AsmErrorKind::TimesIterOutisideOfTimes, line_num: self.line_num, pos: Some(term_start), inner_err: None }),
                        Some(info) => (info.current as u64).into(),
                    }
                    _ => { // otherwise it is either invalid or function-like - assume it's function-like
                        let paren_pos = match term.find('(') {
                            None => return Err(AsmError { kind: AsmErrorKind::UnrecognizedMacroInvocation, line_num: self.line_num, pos: Some(term_start), inner_err: None }),
                            Some(p) => p,
                        };
                        if term.chars().rev().next() != Some(')') {
                            return Err(AsmError { kind: AsmErrorKind::UnrecognizedMacroInvocation, line_num: self.line_num, pos: Some(term_start), inner_err: None });
                        }
                        let func = &term[..paren_pos];
                        let args = self.parse_comma_sep_exprs(raw_line, term_start + paren_pos + 1, term_stop - 1)?;

                        match func {
                            "$ptr" => { // pointer macro - interns a binary value in the rodata segment and returns a pointer to its eventual location
                                if args.len() != 1 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(1), line_num: self.line_num, pos: Some(term_start), inner_err: None }); }
                                let arg = args.into_iter().next().unwrap();

                                let x = match arg.eval(&self.file.symbols) {
                                    Err(e) => return Err(AsmError { kind: AsmErrorKind::FailedCriticalExpression(e), line_num: self.line_num, pos: Some(term_start), inner_err: None }),
                                    Ok(mut val) => match val.take_or_borrow().binary() {
                                        None => return Err(AsmError { kind: AsmErrorKind::ExpectedBinaryValue, line_num: self.line_num, pos: Some(term_start), inner_err: None }),
                                        Some(content) => {
                                            if content.is_empty() { return Err(AsmError { kind: AsmErrorKind::EmptyBinaryValue, line_num: self.line_num, pos: Some(term_start), inner_err: None }); }
                                            let idx = self.file.binary_set.add(content);
                                            ExprData::Ident(format!("{}{:x}", BINARY_LITERAL_SYMBOL_PREFIX, idx)).into()
                                        }
                                    }
                                };
                                x
                            }
                            "$if" => {
                                if args.len() != 3 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(3), line_num: self.line_num, pos: Some(term_start), inner_err: None }); }
                                let mut args = args.into_iter();
                                let cond = args.next().unwrap();
                                let left = args.next().unwrap();
                                let right = args.next().unwrap();
                                (OP::Condition, cond, Expr::from((OP::Pair, left, right))).into()
                            }
                            _ => match UNARY_FUNCTION_OPERATOR_TO_OP.get(func).copied() {
                                Some(op) => {
                                    if args.len() != 1 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(1), line_num: self.line_num, pos: Some(term_start), inner_err: None }); }
                                    (op, args.into_iter().next().unwrap()).into()
                                }
                                None => return Err(AsmError { kind: AsmErrorKind::UnrecognizedMacroInvocation, line_num: self.line_num, pos: Some(term_start), inner_err: None }),
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
                        x => {
                            if x.len() > 1 && x.starts_with('0') { // disambig from C-style octal literals, which we do not support
                                return Err(AsmError { kind: AsmErrorKind::NumericLiteralWithZeroPrefix, line_num: self.line_num, pos: Some(term_start), inner_err: None });
                            }
                            (x, 10)
                        }
                    };
                    let term_fix = term_fix.replace('_', ""); // remove all underscores (allowed as group separators)

                    // terms should not have signs - this is handled by unary ops (and prevents e.g. 0x-5 instead of proper -0x5)
                    if term_fix.starts_with('+') || term_fix.starts_with('-') {
                        return Err(AsmError { kind: AsmErrorKind::IllFormedNumericLiteral, line_num: self.line_num, pos: Some(term_start), inner_err: None });
                    }

                    // parse it as correct type and propagate any errors
                    match signed {
                        false => match u64::from_str_radix(&term_fix, radix) {
                            Err(_) => return Err(AsmError { kind: AsmErrorKind::IllFormedNumericLiteral, line_num: self.line_num, pos: Some(term_start), inner_err: None }), // failed unsigned is failure
                            Ok(v) => v.into(),
                        }
                        true => match i64::from_str_radix(&term_fix, radix) {
                            Err(_) => match Float::parse(term_fix) { // failed signed (int) could just mean that it's (signed) float
                                Err(_) => return Err(AsmError { kind: AsmErrorKind::IllFormedNumericLiteral, line_num: self.line_num, pos: Some(term_start), inner_err: None }), // but if that fails too, it's a bust
                                Ok(v) => Float::with_val(PRECISION, v).into(),
                            }
                            Ok(v) => v.into(),
                        }
                    }
                }
                _ => { // otherwise it must be an keyword/identifier - keywords are always case insensitive
                    if Caseless(term) == Caseless("TRUE") { true.into() }
                    else if Caseless(term) == Caseless("FALSE") { false.into() }
                    else if Caseless(term) == Caseless("NULL") { Value::Pointer(0).into() }
                    else { // if none of above, must be an identifier
                        let (mutated, _) = self.mutate_name(term, term_start)?;
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
                    Some((symbol, _)) => symbol,
                }
            }
            ExprData::Uneval { .. } => expr,
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

    fn extract_imm(&mut self, raw_line: &str, raw_start: usize, raw_stop: usize) -> Result<(Imm, usize), AsmError> {
        // check if we had an explicit size and get the expr start position (after size if present)
        let (token, token_stop) = grab_whitespace_sep_token(raw_line, raw_start, raw_stop);
        let (size, expr_start) = parse_size_str(token, token_stop, raw_start);

        // and finally, read the expr
        let (expr, aft) = self.extract_expr(raw_line, expr_start, raw_stop)?;
        Ok((Imm { expr, size }, aft))
    }
    fn extract_address(&mut self, raw_line: &str, raw_start: usize, raw_stop: usize) -> Result<(Address, usize), AsmError> {
        // check if we had an explicit size and get the expr start position (after size if present)
        let (token, token_stop) = grab_whitespace_sep_token(raw_line, raw_start, raw_stop);
        if token.is_empty() {
            return Err(AsmError { kind: AsmErrorKind::ExpectedAddress, line_num: self.line_num, pos: Some(raw_stop), inner_err: None });
        }
        if let Some(p) = token.find('[') {
            let token_fix = &token[..p];
            if Caseless(token_fix) == Caseless("PTR") {
                return Err(AsmError { kind: AsmErrorKind::AddressPtrSpecWithoutSize, line_num: self.line_num, pos: Some(token_stop - token.len()), inner_err: None });
            }
            if p != 0 { // if token has an open bracket that's not the first char then we have something bad
                if parse_size_str(token_fix, 0, 0).0.is_some() { // if we can parse it as a size, then we're missing ptr spec
                    return Err(AsmError { kind: AsmErrorKind::AddressSizeMissingPtr, line_num: self.line_num, pos: Some(token_stop - token.len() + p), inner_err: None });
                }
                else { // otherwise we have an unknown size
                    return Err(AsmError { kind: AsmErrorKind::AddressSizeNotRecognized, line_num: self.line_num, pos: Some(token_stop - token.len()), inner_err: None });
                }
            }
        }
        if Caseless(token) == Caseless("PTR") {
            return Err(AsmError { kind: AsmErrorKind::AddressPtrSpecWithoutSize, line_num: self.line_num, pos: Some(token_stop - token.len()), inner_err: None });
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
                else { return Err(AsmError { kind: AsmErrorKind::AddressSizeMissingPtr, line_num: self.line_num, pos: Some(token_stop - token.len()), inner_err: None }); }
            }
            None => { // if we failed to parse the size, we must start with an open bracket (just the address component)
                if token.chars().next() != Some('[') {
                    return Err(AsmError { kind: AsmErrorKind::AddressSizeNotRecognized, line_num: self.line_num, pos: Some(token_stop - token.len()), inner_err: None });
                }
            }
        }

        // after the size part, we need to find the start of the core address component [expr]
        let address_start = match raw_line[next_start..raw_stop].find(|c: char| !c.is_whitespace()) {
            None => return Err(AsmError { kind: AsmErrorKind::ExpectedAddress, line_num: self.line_num, pos: Some(raw_stop), inner_err: None }),
            Some(p) => next_start + p,
        };
        if raw_line[address_start..].chars().next().unwrap() != '[' {
            return Err(AsmError { kind: AsmErrorKind::ExpectedAddress, line_num: self.line_num, pos: Some(address_start), inner_err: None });
        }
        let (mut imm, imm_aft) = self.extract_imm(raw_line, address_start + 1, raw_stop)?;
        let (tail, tail_start) = trim_start_with_pos(raw_line, imm_aft, raw_stop);
        match tail.chars().next() {
            Some(']') => (),
            None => return Err(AsmError { kind: AsmErrorKind::UnterminatedAddress, line_num: self.line_num, pos: Some(tail_start), inner_err: None }),
            Some(_) => return Err(AsmError { kind: AsmErrorKind::AddressInteriorNotSingleExpr, line_num: self.line_num, pos: Some(tail_start), inner_err: None }),
        }
        if let Some(size) = imm.size {
            match size {
                Size::Word | Size::Dword | Size::Qword => (),
                _ => return Err(AsmError { kind: AsmErrorKind::AddressSizeUnsupported, line_num: self.line_num, pos: Some(address_start), inner_err: None }),
            }
        }

        // now we need to handle all the register arithmetic stuff
        let mut r1: Option<(u8, u8)> = None; // reg id and multiplier
        let mut r2: Option<u8> = None; // reg id
        for reg in CPU_REGISTER_INFO.iter() {
            if let Some(mult) = self.get_reg_mult(*reg.0, &imm.expr, raw_line, address_start)? { // see if this register is present in the expression
                if reg.1.high { // first of all, high registers are not allowed (this is just for better error messages)
                    return Err(AsmError { kind: AsmErrorKind::AddressUseOfHighRegister, line_num: self.line_num, pos: Some(address_start), inner_err: None });
                }

                let mut mult = match mult.eval(&self.file.symbols) { // if it is then it must be a critical expression
                    Ok(mut val) => match &*val.take_or_borrow() {
                        Value::Signed(v) => *v,
                        _ => return Err(AsmError { kind: AsmErrorKind::AddressRegMultNotSignedInt, line_num: self.line_num, pos: Some(address_start), inner_err: None }),
                    },
                    Err(_) => return Err(AsmError { kind: AsmErrorKind::AddressRegMultNotCriticalExpr, line_num: self.line_num, pos: Some(address_start), inner_err: None }),
                };
                if mult == 0 { continue; } // if it's zero then it canceled out and we don't need it

                match imm.size { 
                    None => imm.size = Some(reg.1.size), // if we don't already have a required size, set it to this register size
                    Some(size) => if size != reg.1.size { // otherwise enforce pre-existing value
                        return Err(AsmError { kind: AsmErrorKind::AddressConflictingSizes, line_num: self.line_num, pos: Some(address_start), inner_err: None });
                    }
                }

                // if the multiplier is trivial or has a trivial component (of 1)
                if mult & 1 != 0 {
                    mult &= !1; // remove the trivial component
                    if r2.is_none() { r2 = Some(reg.1.id); } // prioritize putting it in r2 since r2 can't have a multiplier (other than 1)
                    else if r1.is_none() { r1 = Some((reg.1.id, 0)); } // otherwise we have to put it in r1 and give it a multiplier of 1 (mult code 0)
                    else { return Err(AsmError { kind: AsmErrorKind::AddressTooManyRegs, line_num: self.line_num, pos: Some(address_start), inner_err: None }); } // if we don't have anywhere to put it, failure
                }
                // now, if a (non-trivial) component is present
                if mult != 0 {
                    let multcode = match mult { // decode the multiplier into its sizecode equivalent
                        1 => 0,
                        2 => 1,
                        4 => 2,
                        8 => 3,
                        _ => return Err(AsmError { kind: AsmErrorKind::AddressRegInvalidMult, line_num: self.line_num, pos: Some(address_start), inner_err: None }),
                    };

                    if r1.is_none() { r1 = Some((reg.1.id, multcode)); }
                    else { return Err(AsmError { kind: AsmErrorKind::AddressTooManyRegs, line_num: self.line_num, pos: Some(address_start), inner_err: None }); }
                }
            }
        }

        let address_size = match imm.size {
            None => Size::Qword, // if we still don't have an explicit address size, use 64-bit
            Some(size) => match size {
                Size::Word | Size::Dword | Size::Qword => size,
                _ => return Err(AsmError { kind: AsmErrorKind::AddressSizeUnsupported, line_num: self.line_num, pos: Some(address_start), inner_err: None }), // unsupported addressing modes
            }
        };
        let base = {
            let present = match imm.expr.eval(&self.file.symbols) {
                Ok(v) => match &*v {
                    Value::Signed(v) => *v != 0, // if it's nonzero we have to keep it
                    _ => return Err(AsmError { kind: AsmErrorKind::AddressTypeUnsupported, line_num: self.line_num, pos: Some(address_start), inner_err: None }), // if it's some other type it's invalid
                }
                Err(_) => true, // failure to evaluate means we can't statically elide it, so we assume it's present
            };
            if present { Some(imm.expr) } else { None }
        };

        Ok((Address { address_size, r1, r2, base, pointed_size }, imm_aft + 1))
    }
    fn get_reg_mult(&self, reg: Caseless, expr: &Expr, raw_line: &str, err_pos: usize) -> Result<Option<Expr>, AsmError> {
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
                    None => return Err(AsmError { kind: AsmErrorKind::IllFormedExpr, line_num: self.line_num, pos: Some(err_pos), inner_err: None }),
                    Some(x) => self.get_reg_mult(reg, x, raw_line, err_pos)?,
                };
                match op {
                    OP::Neg => {
                        if let Some(_) = right.as_ref() { return Err(AsmError { kind: AsmErrorKind::IllFormedExpr, line_num: self.line_num, pos: Some(err_pos), inner_err: None }); }
                        Ok(a.map(|t| (OP::Neg, t).into())) // just return the negative if we had something
                    }
                    OP::Add | OP::Sub => {
                        let b = match right.as_ref() {
                            None => return Err(AsmError { kind: AsmErrorKind::IllFormedExpr, line_num: self.line_num, pos: Some(err_pos), inner_err: None }),
                            Some(x) => self.get_reg_mult(reg, x, raw_line, err_pos)?,
                        };
                        
                        // if neither existed, return None, otherwise combine them with defaults of 0 if either is not present
                        if a.is_none() && b.is_none() { Ok(None) }
                        else { Ok(Some((*op, a.unwrap_or(0i64.into()), b.unwrap_or(0i64.into())).into())) }
                    }
                    OP::Mul => match a { // reg must not be present in both branches - this is done by allowing either as wildcard, which will always fail to evaluate
                        Some(a) => Ok(Some((OP::Mul, a, (**right.as_ref().unwrap()).clone()).into())), // return what we got times the other side (currently unmodified due to not recursing to it)
                        None => {
                            let b = match right.as_ref() {
                                None => return Err(AsmError { kind: AsmErrorKind::IllFormedExpr, line_num: self.line_num, pos: Some(err_pos), inner_err: None }),
                                Some(x) => self.get_reg_mult(reg, x, raw_line, err_pos)?,
                            };
                            match b {
                                Some(b) => Ok(Some((OP::Mul, (**left.as_ref().unwrap()).clone(), b).into())), // return what we got times the other side (currently unmodified do to left returning None)
                                None => Ok(None), // if we got nothing for both, report nothing
                            }
                        }
                    }
                    _ => { // for any other (unsuported) operation, just ensure that the register was not present
                        if let Some(_) = a {
                            return Err(AsmError { kind: AsmErrorKind::AddressRegIllegalOp, line_num: self.line_num, pos: Some(err_pos), inner_err: None });
                        }
                        if let Some(v) = right.as_ref() {
                            if let Some(_) = self.get_reg_mult(reg, v, raw_line, err_pos)? {
                                return Err(AsmError { kind: AsmErrorKind::AddressRegIllegalOp, line_num: self.line_num, pos: Some(err_pos), inner_err: None });
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
    fn extract_arg(&mut self, raw_line: &str, raw_start: usize, raw_stop: usize) -> Result<(Argument, usize), AsmError> {
        // first try named items since we can do this without copying anything
        let (token, token_aft) = grab_alnum_token(raw_line, raw_start, raw_stop);
        if let Some(reg) = CPU_REGISTER_INFO.get(&Caseless(token)) { return Ok((Argument::CPURegister(*reg), token_aft)); }
        if let Some(reg) = FPU_REGISTER_INFO.get(&Caseless(token)) { return Ok((Argument::FPURegister(*reg), token_aft)); }
        if let Some(reg) = VPU_REGISTER_INFO.get(&Caseless(token)) { return Ok((Argument::VPURegister(*reg), token_aft)); }
        if let Some(seg) = SEGMENTS.get(&Caseless(token)) { return Ok((Argument::Segment(*seg), token_aft)); }

        // next, try address, since it could parse as an expr if given explicit size
        if let Ok((addr, aft)) = self.extract_address(raw_line, raw_start, raw_stop) { return Ok((Argument::Address(addr), aft)); }

        // otherwise parse as imm
        let (imm, aft) = self.extract_imm(raw_line, raw_start, raw_stop)?;
        Ok((Argument::Imm(imm), aft))
    }
    
    /// Attempts to extract the header of the given line.
    /// This includes label_def, times, and instruction.
    /// On success, returns the parsed instruction (if present) and one past the index of the last character extracted.
    pub(super) fn extract_header(&mut self, raw_line: &str) -> Result<(Option<(Option<(Prefix, usize)>, (Instruction, usize))>, usize), AsmError> {
        self.label_def = None;
        self.times = None;

        // grab a token - if it's empty or starts a comment, we're done
        let mut token = grab_whitespace_sep_token(raw_line, 0, raw_line.len());
        if token.0.is_empty() { return Ok((None, 0)); }
        if token.0.ends_with(LABEL_DEF_CHAR) { // if we got a label, set it and grab another token
            let mutated = self.mutate_name(&token.0[..token.0.len()-1], token.1 - token.0.len())?;
            if is_reserved_symbol_name(&mutated.0) { return Err(AsmError { kind: AsmErrorKind::ReservedSymbolName, line_num: self.line_num, pos: Some(token.1 - token.0.len()), inner_err: None }); }
            self.label_def = Some(mutated);

            let new_token = grab_whitespace_sep_token(raw_line, token.1, raw_line.len());
            if new_token.0.is_empty() { return Ok((None, token.1)); }
            token = new_token;
        }
        if Caseless(token.0) == Caseless("TIMES") { // if we got a TIMES prefix, extract its part and grab another token
            let err_pos = token.1 - token.0.len();
            let (arg, aft) = match self.extract_arg(raw_line, token.1, raw_line.len()) {
                Err(e) => return Err(AsmError { kind: AsmErrorKind::TimesMissingCount, line_num: self.line_num, pos: e.pos, inner_err: None }),
                Ok(x) => x,
            };
            let count = match arg {
                Argument::Imm(imm) => {
                    if imm.size.is_some() { return Err(AsmError { kind: AsmErrorKind::TimesCountHadSizeSpec, line_num: self.line_num, pos: Some(err_pos), inner_err: None }); }
                    match imm.expr.eval(&self.file.symbols) {
                        Err(_) => return Err(AsmError { kind: AsmErrorKind::TimesCountNotCriticalExpression, line_num: self.line_num, pos: Some(err_pos), inner_err: None }),
                        Ok(val) => match &*val {
                            Value::Signed(v) => {
                                if *v < 0 { return Err(AsmError { kind: AsmErrorKind::TimesCountWasNegative, line_num: self.line_num, pos: Some(err_pos), inner_err: None }); }
                                *v as u64
                            }
                            Value::Unsigned(v) => *v,
                            _ => return Err(AsmError { kind: AsmErrorKind::TimesCountNotInteger, line_num: self.line_num, pos: Some(err_pos), inner_err: None }),
                        }
                    }
                }
                _ => return Err(AsmError { kind: AsmErrorKind::TimesCountNotImm, line_num: self.line_num, pos: Some(err_pos), inner_err: None }),
            };
            self.times = Some(TimesInfo { total_count: count, current: 0 });

            token = grab_whitespace_sep_token(raw_line, aft, raw_line.len());
            if token.0.is_empty() { return Err(AsmError { kind: AsmErrorKind::TimesUsedOnEmptyLine, line_num: self.line_num, pos: Some(err_pos), inner_err: None }); }
        }
        else if Caseless(token.0) == Caseless("IF") { // if we got an IF prefix, extract its part and grab another token
            let err_pos = token.1 - token.0.len();
            let (arg, aft) = match self.extract_arg(raw_line, token.1, raw_line.len()) {
                Err(e) => return Err(AsmError { kind: AsmErrorKind::IfMissingExpr, line_num: self.line_num, pos: e.pos, inner_err: None }),
                Ok(x) => x,
            };
            let cond = match arg {
                Argument::Imm(imm) => {
                    if imm.size.is_some() { return Err(AsmError { kind: AsmErrorKind::IfExprHadSizeSpec, line_num: self.line_num, pos: Some(err_pos), inner_err: None }); }
                    match imm.expr.eval(&self.file.symbols) {
                        Err(_) => return Err(AsmError { kind: AsmErrorKind::IfExprNotCriticalExpression, line_num: self.line_num, pos: Some(err_pos), inner_err: None }),
                        Ok(val) => match &*val {
                            Value::Logical(v) => *v,
                            _ => return Err(AsmError { kind: AsmErrorKind::IfExprNotLogical, line_num: self.line_num, pos: Some(err_pos), inner_err: None }),
                        }
                    }
                }
                _ => return Err(AsmError { kind: AsmErrorKind::IfExprNotImm, line_num: self.line_num, pos: Some(err_pos), inner_err: None }),
            };
            self.times = Some(TimesInfo { total_count: if cond { 1 } else { 0 }, current: 0 });

            token = grab_whitespace_sep_token(raw_line, aft, raw_line.len());
            if token.0.is_empty() { return Err(AsmError { kind: AsmErrorKind::IfUsedOnEmptyLine, line_num: self.line_num, pos: Some(err_pos), inner_err: None }); }
        }

        // check if we got a prefix
        let prefix = match PREFIXES.get(&Caseless(token.0)) {
            None => None,
            Some(prefix) => {
                let err_pos = token.1 - token.0.len();
                token = grab_whitespace_sep_token(raw_line, token.1, raw_line.len());
                if token.0.is_empty() { return Err(AsmError { kind: AsmErrorKind::PrefixWithoutInstruction, line_num: self.line_num, pos: Some(err_pos), inner_err: None }); }
                Some((*prefix, err_pos))
            }
        };

        // the token we have at this point should be the instruction - parse it
        let ins_pos = token.1 - token.0.len();
        match INSTRUCTIONS.get(&Caseless(token.0)) {
            None => return Err(AsmError { kind: AsmErrorKind::UnrecognizedInstruction, line_num: self.line_num, pos: Some(ins_pos), inner_err: None }),
            Some(ins) => Ok((Some((prefix, (*ins, ins_pos))), token.1)),
        }
    }
    pub(super) fn extract_arguments(&mut self, raw_line: &str, raw_start: usize) -> Result<Vec<Argument>, AsmError> {
        let mut args = vec![];

        // parse the rest of the line as comma-separated arguments
        let (tail, mut pos) = trim_start_with_pos(raw_line, raw_start, raw_line.len());
        if !tail.is_empty() { // check if we're done with line or entering a comment section (no args)
            loop { // parse one or more comma-separated arguments
                let (arg, aft) = self.extract_arg(raw_line, pos, raw_line.len())?;
                args.push(arg);

                let (tail, tail_pos) = trim_start_with_pos(raw_line, aft, raw_line.len());
                if tail.chars().next() != Some(',') { // if we're not followed by a comma we're done
                    pos = aft;
                    break;
                } 
                pos = tail_pos + 1;
            }

            // make sure we consumed the entire line
            let (tail, tail_pos) = trim_start_with_pos(raw_line, pos, raw_line.len());
            if !tail.is_empty() { return Err(AsmError { kind: AsmErrorKind::ExtraContentAfterArgs, line_num: self.line_num, pos: Some(tail_pos), inner_err: None }); }
        }

        Ok(args)
    }

    /// Gets the current segment for writing. Returns the segment, the symbol table, and the set of holes.
    /// Fails if not currently in a segment or if in a non-writable segment (like bss).
    pub(super) fn get_current_segment_for_writing(&mut self) -> Result<(&mut Vec<u8>, &dyn SymbolTableCore, &mut Vec<Hole>), AsmError> {
        Ok(match self.current_seg {
            None => return Err(AsmError { kind: AsmErrorKind::WriteOutsideOfSegment, line_num: self.line_num, pos: None, inner_err: None }),
            Some(seg) => match seg {
                AsmSegment::Text => (&mut self.file.text, &self.file.symbols, &mut self.file.text_holes),
                AsmSegment::Rodata => (&mut self.file.rodata, &self.file.symbols, &mut self.file.rodata_holes),
                AsmSegment::Data => (&mut self.file.data, &self.file.symbols, &mut self.file.data_holes),
                AsmSegment::Bss => return Err(AsmError { kind: AsmErrorKind::WriteInBssSegment, line_num: self.line_num, pos: None, inner_err: None }),
            }
        })
    }
    /// Appends a byte to the current segment, if valid.
    pub(super) fn append_byte(&mut self, val: u8) -> Result<(), AsmError> {
        let (seg, _, _) = self.get_current_segment_for_writing()?;
        seg.push(val);
        Ok(())
    }
    /// Appends a value to the current segment, if valid.
    /// If it is immediately evaluatable, appends the value, otherwise writes a placeholder and generates a hole entry to be patched later.
    pub(super) fn append_val(&mut self, size: Size, expr: Expr, allowed_type: HoleType) -> Result<(), AsmError> {
        let line_num = self.line_num;
        let (seg, symbols, holes) = self.get_current_segment_for_writing()?;
        let hole = Hole { // generate the hole info
            address: seg.len(),
            size, expr, allowed_type, line_num,
        };
        seg.extend(iter::once(0xffu8).cycle().take(size.size())); // make room for the value (all 1's is arbitrary)
        match patch_hole(seg, &hole, symbols) {
            Ok(_) => (), // on success we're golden - hole was patched immediately
            Err(e) => match e.kind {
                PatchErrorKind::Illegal(r) => return Err(AsmError { kind: AsmErrorKind::IllegalPatch(r), line_num: e.line_num, pos: None, inner_err: None }), // anything illegal is a hard pass
                PatchErrorKind::NotPatched(_) => holes.push(hole), // an eval error just means we need to add it to the list of holes for this segment
            }
        }
        Ok(())
    }
    /// Appends an address to the current segment, if valid.
    fn append_address(&mut self, addr: Address) -> Result<(), AsmError> {
        let a = (if addr.base.is_some() { 0x80 } else { 0 }) | (addr.r1.unwrap_or((0, 0)).1 << 4) | (addr.address_size.basic_sizecode().unwrap() << 2) | (if addr.r1.is_some() { 2 } else { 0 }) | (if addr.r2.is_some() { 1 } else { 0 });
        let b = (addr.r1.unwrap_or((0, 0)).0 << 4) | addr.r2.unwrap_or(0);

        self.append_byte(a)?;
        if a & 3 != 0 { self.append_byte(b)?; }
        if a & 0x80 != 0 { self.append_val(addr.address_size, addr.base.unwrap(), HoleType::Integral)? }
        Ok(())
    }

    /// Handles instructions which take no arguments.
    /// Writes `op`, followed by `ext_op` (if valid).
    pub(super) fn process_no_arg_op(&mut self, args: Vec<Argument>, op: Option<u8>, ext_op: Option<u8>) -> Result<(), AsmError> {
        if self.current_seg != Some(AsmSegment::Text) { return Err(AsmError { kind: AsmErrorKind::InstructionOutsideOfTextSegment, line_num: self.line_num, pos: None, inner_err: None }); }
        if args.len() != 0 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(0), line_num: self.line_num, pos: None, inner_err: None }); }
        if let Some(ext) = op { self.append_byte(ext)? }
        if let Some(ext) = ext_op { self.append_byte(ext)? }
        Ok(())
    }
    /// Attempts to assemble an operation which uses the binary op format.
    /// `force_b_imm_size` can be set to artificially force the size of an imm - e.g. the BTx series of instructions always have use imm8.
    pub(super) fn process_binary_op(&mut self, args: Vec<Argument>, op: u8, ext_op: Option<u8>, allowed_type: HoleType, allowed_sizes: &[Size], force_b_imm_size: Option<Size>) -> Result<(), AsmError> {
        if self.current_seg != Some(AsmSegment::Text) { return Err(AsmError { kind: AsmErrorKind::InstructionOutsideOfTextSegment, line_num: self.line_num, pos: None, inner_err: None }); }
        if args.len() != 2 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(2), line_num: self.line_num, pos: None, inner_err: None }); }
        let mut args = args.into_iter();
        let arg1 = args.next().unwrap();
        let arg2 = args.next().unwrap();

        self.append_byte(op)?;
        if let Some(ext) = ext_op { self.append_byte(ext)?; }

        match (arg1, arg2) {
            (Argument::CPURegister(dest), Argument::CPURegister(src)) => {
                if dest.size != src.size { return Err(AsmError { kind: AsmErrorKind::OperandsHadDifferentSizes, line_num: self.line_num, pos: None, inner_err: None }); }
                if !allowed_sizes.contains(&dest.size) { return Err(AsmError { kind: AsmErrorKind::UnsupportedOperandSize, line_num: self.line_num, pos: None, inner_err: None }); }
                self.append_byte((dest.id << 4) | (dest.size.basic_sizecode().unwrap() << 2) | (if dest.high { 2 } else { 0 }) | (if src.high { 1 } else { 0 }))?;
                self.append_byte(src.id)?;
            }
            (Argument::CPURegister(dest), Argument::Address(src)) => {
                if let Some(size) = src.pointed_size {
                    if size != dest.size { return Err(AsmError { kind: AsmErrorKind::OperandsHadDifferentSizes, line_num: self.line_num, pos: None, inner_err: None }); }
                }
                if !allowed_sizes.contains(&dest.size) { return Err(AsmError { kind: AsmErrorKind::UnsupportedOperandSize, line_num: self.line_num, pos: None, inner_err: None }); }
                self.append_byte((dest.id << 4) | (dest.size.basic_sizecode().unwrap() << 2) | (if dest.high { 2 } else { 0 }))?;
                self.append_byte(2 << 4)?;
                self.append_address(src)?;
            }
            (Argument::CPURegister(dest), Argument::Imm(mut src)) => {
                match force_b_imm_size {
                    None => match src.size {
                        Some(size) => if size != dest.size { return Err(AsmError { kind: AsmErrorKind::OperandsHadDifferentSizes, line_num: self.line_num, pos: None, inner_err: None }); },
                        None => src.size = Some(dest.size),
                    }
                    Some(forced_size) => match src.size {
                        Some(_) => return Err(AsmError { kind: AsmErrorKind::SizeSpecOnForcedSize, line_num: self.line_num, pos: None, inner_err: None }),
                        None => src.size = Some(forced_size),
                    }
                }
                if !allowed_sizes.contains(&dest.size) { return Err(AsmError { kind: AsmErrorKind::UnsupportedOperandSize, line_num: self.line_num, pos: None, inner_err: None }); }
                self.append_byte((dest.id << 4) | (dest.size.basic_sizecode().unwrap() << 2) | (if dest.high { 2 } else { 0 }))?;
                self.append_byte(1 << 4)?;
                self.append_val(src.size.unwrap(), src.expr, allowed_type)?;
            }
            (Argument::Address(dest), Argument::CPURegister(src)) => {
                if let Some(size) = dest.pointed_size {
                    if size != src.size { return Err(AsmError { kind: AsmErrorKind::OperandsHadDifferentSizes, line_num: self.line_num, pos: None, inner_err: None }); }
                }
                if !allowed_sizes.contains(&src.size) { return Err(AsmError { kind: AsmErrorKind::UnsupportedOperandSize, line_num: self.line_num, pos: None, inner_err: None }); }
                self.append_byte((src.size.basic_sizecode().unwrap() << 2) | (if src.high { 1 } else { 0 }))?;
                self.append_byte((3 << 4) | src.id)?;
                self.append_address(dest)?;
            }
            (Argument::Address(mut dest), Argument::Imm(mut src)) => {
                match force_b_imm_size {
                    None => match (dest.pointed_size, src.size) {
                        (Some(a), Some(b)) => if a != b { return Err(AsmError { kind: AsmErrorKind::OperandsHadDifferentSizes, line_num: self.line_num, pos: None, inner_err: None }); },
                        (None, Some(b)) => dest.pointed_size = Some(b),
                        (Some(a), None) => src.size = Some(a),
                        (None, None) => return Err(AsmError { kind: AsmErrorKind::CouldNotDeduceOperandSize, line_num: self.line_num, pos: None, inner_err: None }),
                    }
                    Some(forced_size) => {
                        if src.size.is_some() { return Err(AsmError { kind: AsmErrorKind::SizeSpecOnForcedSize, line_num: self.line_num, pos: None, inner_err: None }); }
                        src.size = Some(forced_size);
                        if dest.pointed_size.is_none() { return Err(AsmError { kind: AsmErrorKind::CouldNotDeduceOperandSize, line_num: self.line_num, pos: None, inner_err: None }); }
                    }
                }
                if !allowed_sizes.contains(&dest.pointed_size.unwrap()) { return Err(AsmError { kind: AsmErrorKind::UnsupportedOperandSize, line_num: self.line_num, pos: None, inner_err: None }); }
                self.append_byte(dest.pointed_size.unwrap().basic_sizecode().unwrap() << 2)?;
                self.append_byte(4 << 4)?;
                self.append_address(dest)?;
                self.append_val(src.size.unwrap(), src.expr, allowed_type)?;
            }
            _ => return Err(AsmError { kind: AsmErrorKind::BinaryOpUnsupportedSrcDestTypes, line_num: self.line_num, pos: None, inner_err: None }),
        }

        Ok(())
    }

    fn verify_legal_expr(&self, expr: &Expr, line_num: usize) -> Result<(), AsmError> {
        match &*expr.data.borrow() {
            ExprData::Value(_) => (),
            ExprData::Ident(ident) => if !self.file.symbols.is_defined(ident) && !self.file.extern_symbols.contains_key(ident) && !ident.starts_with('#') {
                return Err(AsmError { kind: AsmErrorKind::UnknownSymbol, line_num, pos: None, inner_err: None });
            }
            ExprData::Uneval { op: _, left, right } => {
                self.verify_legal_expr(left.as_ref().unwrap(), line_num)?;
                if let Some(right) = right { self.verify_legal_expr(right, line_num)?; }
            }
        }
        Ok(())
    }
    fn verify_legal_global(&self, expr: &Expr, line_num: usize) -> Result<(), AsmError> {
        match &*expr.data.borrow() {
            ExprData::Value(_) => (),
            ExprData::Ident(ident) => if let Some(_) = self.file.extern_symbols.get(ident) {
                return Err(AsmError { kind: AsmErrorKind::GlobalUsesExtern { extern_sym: ident.to_owned() }, line_num, pos: None, inner_err: None });
            }
            ExprData::Uneval { left, right, .. } => {
                if let Some(left) = left { self.verify_legal_global(left, line_num)? } // although children might not be globals themselves, same logic applies
                if let Some(right) = right { self.verify_legal_global(right, line_num)? }
            }
        }
        Ok(())
    }
    pub(super) fn finalize(self) -> Result<ObjectFile, AsmError> {
        // make sure all globals are defined
        for (global, &line_num) in self.file.global_symbols.iter() {
            if !self.file.symbols.is_defined(global) {
                return Err(AsmError { kind: AsmErrorKind::GlobalSymbolWasNotDefined, line_num, pos: None, inner_err: None });
            }
        }
        // this has to happen after the previous because it assumes globals are defined
        for (global, _) in self.file.global_symbols.iter() {
            let line_num = self.file.symbols.get(global).unwrap().1; // error message point to definition, not declaration
            self.verify_legal_global(&self.file.symbols.get(global).unwrap().0, line_num)?;
        }

        for (_, (expr, line_num)) in self.file.symbols.iter() { self.verify_legal_expr(expr, *line_num)?; }

        for hole in self.file.text_holes.iter() { self.verify_legal_expr(&hole.expr, hole.line_num)?; }
        for hole in self.file.rodata_holes.iter() { self.verify_legal_expr(&hole.expr, hole.line_num)?; }
        for hole in self.file.data_holes.iter() { self.verify_legal_expr(&hole.expr, hole.line_num)?; }

        Ok(self.file) // if we're ok, return the final result
    }
}

#[cfg(test)]
fn create_context() -> AssembleArgs<'static> {
    AssembleArgs {
        file_name: "test.asm",
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
    
        current_seg: Some(AsmSegment::Text),
        done_segs: Default::default(),

        line_num: Default::default(),
        line_pos_in_seg: Default::default(),

        last_nonlocal_label: Default::default(),
        label_def: Default::default(),

        times: Default::default(),
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
            assert!(matches!(e.kind, AsmErrorKind::ExpectedString));
            assert_eq!(e.pos, Some(13));
        }
    }
    match c.extract_string("hello      ' wo rld'y ", 5, 19) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::IncompleteString));
            assert_eq!(e.pos, Some(11));
        }
    }
    match c.extract_string("hello      ' wo rld'  ", 5, 11) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::ExpectedString));
            assert_eq!(e.pos, Some(11));
        }
    }
    match c.extract_string("hello      ' wo rld'  ", 5, 12) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::IncompleteString));
            assert_eq!(e.pos, Some(11));
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
    match c.extract_string("  'hello;world' 'another string' ", 1, 33) {
        Ok((res, aft)) => {
            assert_eq!(res, "hello;world".as_bytes());
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
            assert!(matches!(e.kind, AsmErrorKind::InvalidEscape));
            assert_eq!(e.pos, Some(3));
        }
    }
    match c.extract_string("  '\\x'", 1, 6) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::IncompleteEscape));
            assert_eq!(e.pos, Some(3));
        }
    }
    match c.extract_string("  '\\x5'", 1, 7) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::IncompleteEscape));
            assert_eq!(e.pos, Some(3));
        }
    }
    match c.extract_string("  '\\x5g'", 2, 8) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::IncompleteEscape));
            assert_eq!(e.pos, Some(3));
        }
    }
    match c.extract_string("  '\\x", 2, 5) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::IncompleteEscape));
            assert_eq!(e.pos, Some(3));
        }
    }
    match c.extract_string("  '\\x4", 1, 6) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::IncompleteEscape));
            assert_eq!(e.pos, Some(3));
        }
    }
    match c.extract_string("  '\\x4b", 2, 7) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::IncompleteString));
            assert_eq!(e.pos, Some(2));
        }
    }
    match c.extract_string("  '\\", 1, 4) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::IncompleteEscape));
            assert_eq!(e.pos, Some(3));
        }
    }
}

#[test]
fn test_extr_expr() {
    let mut c = create_context();
    match c.extract_expr("trUe;", 0, 5) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 4);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Logical(val)) => assert_eq!(val, true),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("faLse", 0, 5) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 5);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Logical(val)) => assert_eq!(val, false),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("nuLl", 0, 4) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 4);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Pointer(val)) => assert_eq!(val, 0),
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
    match c.extract_expr("  010  ", 1, 7) {
        Ok(r) => panic!("{:?}", r),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::NumericLiteralWithZeroPrefix));
        }
    }
    match c.extract_expr("0", 0, 1) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 1);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 0),
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
    match c.extract_expr("  .14  ", 1, 7) {
        Ok(v) => panic!("{:?}", v),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::InvalidSymbolName));
        }
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
    match c.extract_expr("(5+1)*;(5-1) g", 0, 13) {
        Ok(r) => panic!("{:?}", r),
        Err(e) => {
            assert_eq!(e.pos, Some(6));
            assert!(matches!(e.kind, AsmErrorKind::ExpectedExprTerm));
        }
    }
    match c.extract_expr("(5+1);*(5-1) g", 0, 13) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 5);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, 6),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("(5;+1)", 0, 6) {
        Ok(r) => panic!("{:?}", r),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::MissingCloseParen));
        }
    }
    match c.extract_expr(";(5;+1)", 0, 7) {
        Ok(r) => panic!("{:?}", r),
        Err(e) => {
            assert_eq!(e.pos, Some(0));
            assert!(matches!(e.kind, AsmErrorKind::ExpectedExprTerm));
        }
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
    match c.extract_expr("  'hello world'  ", 1, 17) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 15);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Binary(val)) => assert_eq!(val, "hello world".as_bytes()),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("  'hello;world'  ", 1, 17) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 15);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Binary(val)) => assert_eq!(val, "hello;world".as_bytes()),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("  'hello;world\"  ", 1, 17) {
        Ok(r) => panic!("{:?}", r),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::IncompleteString));
        }
    }
    match c.extract_expr("$if(TrUe,6 / -2,3 << 2)", 0, 23) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 23);
            match expr.eval(&c.file.symbols).unwrap().take_or_borrow() {
                Cow::Owned(Value::Signed(val)) => assert_eq!(val, -3),
                _ => panic!(),
            }
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_expr("   $if(  False == true  ,    6 / -  2 ,  3 << 2   )  ", 1, 53) {
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
    c.file.symbols.define("foo".into(), (OP::Add, Expr::from(ExprData::Ident("#t".into())), 10i64).into(), 0).unwrap();
    c.file.symbols.define("bar".into(), (OP::Add, Expr::from(ExprData::Ident("#t".into())), 14i64).into(), 0).unwrap();
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
    match c.extract_expr("foo-$;comment", 0, 5) {
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
    match c.extract_expr("0x2Ff4;comment", 0, 6) {
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
    match c.extract_expr("0x02Ff4u", 0, 8) {
        Ok((expr, aft)) => {
            assert_eq!(aft, 8);
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
            assert_eq!(addr.address_size, Size::Qword);
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
            assert_eq!(addr.address_size, Size::Dword);
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
            assert_eq!(addr.address_size, Size::Dword);
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
            assert_eq!(addr.address_size, Size::Word);
            assert_eq!(addr.r1.unwrap().1, 0);
            assert_eq!(addr.r1.unwrap().0 + addr.r2.unwrap(), 1);
            assert_eq!(addr.pointed_size, Some(Size::Tword));
            assert!(addr.base.is_none());
        }
        Err(e) => panic!("{:?}", e),
    }
    match c.extract_address("   zWord     ptr  [4*(r8d + 7)]   ", 2, 34) {
        Ok((addr, aft)) => {
            assert_eq!(aft, 31);
            assert_eq!(addr.address_size, Size::Dword);
            assert_eq!(addr.r1, Some((8, 2)));
            assert_eq!(addr.r2, None);
            assert_eq!(addr.pointed_size, Some(Size::Zword));
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
            assert_eq!(addr.address_size, Size::Qword);
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
            assert_eq!(addr.address_size, Size::Word);
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
            assert_eq!(e.pos, Some(3));
            assert!(matches!(e.kind, AsmErrorKind::AddressSizeNotRecognized));
        }
    }
    match c.extract_address("   [5 * ax  ", 2, 12) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(12));
            assert!(matches!(e.kind, AsmErrorKind::UnterminatedAddress));
        }
    }
    match c.extract_address("   word [5 * ax  ", 2, 17) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(8));
            assert!(matches!(e.kind, AsmErrorKind::AddressSizeMissingPtr));
        }
    }
    match c.extract_address("   wOrd[5 * ax  ", 2, 16) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(7));
            assert!(matches!(e.kind, AsmErrorKind::AddressSizeMissingPtr));
        }
    }
    match c.extract_address("   WORD ptr[5 * ax  ", 2, 20) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(20));
            assert!(matches!(e.kind, AsmErrorKind::UnterminatedAddress));
        }
    }
    match c.extract_address("   word ptr[9 * ax]  ", 2, 21) {
        Ok((addr, aft)) => {
            assert_eq!(aft, 19);
            assert_eq!(addr.address_size, Size::Word);
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
            assert_eq!(e.pos, Some(14));
            assert!(matches!(e.kind, AsmErrorKind::ExpectedExprTerm));
        }
    }
    match c.extract_address("  word ptr[]  ", 1, 14) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(11));
            assert!(matches!(e.kind, AsmErrorKind::ExpectedExprTerm));
        }
    }
    match c.extract_address("  word ptr[a b]  ", 1, 17) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(13));
            assert!(matches!(e.kind, AsmErrorKind::AddressInteriorNotSingleExpr));
        }
    }
    match c.extract_address("  ptr[45]  ", 1, 11) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::AddressPtrSpecWithoutSize));
        }
    }
    match c.extract_address("  ptr [45]  ", 1, 12) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::AddressPtrSpecWithoutSize));
        }
    }
    match c.extract_address("  sefsfsd[45]  ", 1, 11) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::AddressSizeNotRecognized));
        }
    }
    match c.extract_address("  sefsfsd [45]  ", 1, 12) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::AddressSizeNotRecognized));
        }
    }
    match c.extract_address("          ", 1, 10) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(10));
            assert!(matches!(e.kind, AsmErrorKind::ExpectedAddress));
        }
    }
    match c.extract_address("  [  byte 45]   ", 1, 16) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::AddressSizeUnsupported));
        }
    }
    match c.extract_address("  [tword 45]   ", 1, 15) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::AddressSizeUnsupported));
        }
    }
    match c.extract_address("  [ xwoRd 45]   ", 1, 16) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::AddressSizeUnsupported));
        }
    }
    match c.extract_address("  [ yword 45]   ", 1, 16) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::AddressSizeUnsupported));
        }
    }
    match c.extract_address("  [ ZWORD 45]   ", 1, 16) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::AddressSizeUnsupported));
        }
    }
    match c.extract_address("  word ptr [al]   ", 1, 18) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(11));
            assert!(matches!(e.kind, AsmErrorKind::AddressSizeUnsupported));
        }
    }
    match c.extract_address("  [ah]   ", 1, 9) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::AddressUseOfHighRegister));
        }
    }
    match c.extract_address("  [ax*bx]   ", 1, 12) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::AddressRegMultNotCriticalExpr));
        }
    }
    match c.extract_address("  [ax*ax]   ", 1, 12) {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::AddressRegMultNotCriticalExpr));
        }
    }
    match c.extract_address("  [ax;*ax]   ", 1, 12) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::UnterminatedAddress));
            assert_eq!(e.pos, Some(5));
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
        (Argument::VPURegister(VPURegisterInfo { id: 0, size: Size::Xword }), 6) => (),
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
            assert_eq!(e.pos, Some(7));
            assert!(matches!(e.kind, AsmErrorKind::ExpectedExprTerm));
        }
    }
}
#[test]
fn test_extract_header() {
    let mut c = create_context();
    
    assert_eq!(c.extract_header("").unwrap(), (None, 0));
    assert_eq!(c.label_def, None);
    assert_eq!(c.times, None);

    assert_eq!(c.extract_header(" \t   ").unwrap(), (None, 0));
    assert_eq!(c.label_def, None);
    assert_eq!(c.times, None);

    assert_eq!(c.extract_header(" \t  ; this is a comment ").unwrap(), (None, 0));
    assert_eq!(c.label_def, None);
    assert_eq!(c.times, None);

    assert_eq!(c.extract_header("  label:    ; this is a comment ").unwrap(), (None, 8));
    assert_eq!(c.label_def.as_ref().unwrap().0, "label");
    assert_eq!(c.label_def.as_ref().unwrap().1, Locality::Nonlocal);
    assert_eq!(c.times, None);

    match c.extract_header("  label%^:    ; this is a comment ") {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::InvalidSymbolName));
        }
    }

    match c.extract_header("  .top:    ; this is a comment ") {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::LocalSymbolBeforeNonlocal));
        }
    }
    c.last_nonlocal_label = Some("thingy".into());
    assert_eq!(c.extract_header("  .top:    ; this is a comment ").unwrap(), (None, 7));
    assert_eq!(c.label_def.as_ref().unwrap().0, "thingy.top");
    assert_eq!(c.label_def.as_ref().unwrap().1, Locality::Local);
    assert_eq!(c.times, None);

    assert_eq!(c.extract_header("  times 45 nop  ; this is a comment ").unwrap(), (Some((None, (Instruction::NOP, 11))), 14));
    assert_eq!(c.label_def, None);
    assert_eq!(c.times, Some(TimesInfo { total_count: 45, current: 0 }));

    match c.extract_header("  times 45     ; this is a comment ") {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::TimesUsedOnEmptyLine));
        }
    }
    match c.extract_header("  times abc     ; this is a comment ") {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::TimesCountNotCriticalExpression));
        }
    }
    match c.extract_header("  times -45     ; this is a comment ") {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::TimesCountWasNegative));
        }
    }

    match c.extract_header("  times 5 UNKNOWN_COMMAND    ; this is a comment ") {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(10));
            assert!(matches!(e.kind, AsmErrorKind::UnrecognizedInstruction));
        }
    }
    match c.extract_header("   UNKNOWN_COMMAND    ; this is a comment ") {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(3));
            assert!(matches!(e.kind, AsmErrorKind::UnrecognizedInstruction));
        }
    }

    assert_eq!(c.extract_header("  label: tiMEs 5 NoP  ; this is a comment ").unwrap(), (Some((None, (Instruction::NOP, 17))), 20));
    assert_eq!(c.label_def.as_ref().unwrap().0, "label");
    assert_eq!(c.label_def.as_ref().unwrap().1, Locality::Nonlocal);
    assert_eq!(c.times, Some(TimesInfo { total_count: 5, current: 0 }));

    assert_eq!(c.extract_header("  label: tiMEs 0 NoP  ; this is a comment ").unwrap(), (Some((None, (Instruction::NOP, 17))), 20));
    assert_eq!(c.label_def.as_ref().unwrap().0, "label");
    assert_eq!(c.label_def.as_ref().unwrap().1, Locality::Nonlocal);
    assert_eq!(c.times, Some(TimesInfo { total_count: 0, current: 0 }));

    assert_eq!(c.extract_header("  merp: NoP  ; this is a comment ").unwrap(), (Some((None, (Instruction::NOP, 8))), 11));
    assert_eq!(c.label_def.as_ref().unwrap().0, "merp");
    assert_eq!(c.label_def.as_ref().unwrap().1, Locality::Nonlocal);
    assert_eq!(c.times, None);

    assert_eq!(c.extract_header("  NoP  ; this is a comment ").unwrap(), (Some((None, (Instruction::NOP, 2))), 5));
    assert_eq!(c.label_def, None);
    assert_eq!(c.times, None);

    assert_eq!(c.extract_header("  NoP; this is a comment ").unwrap(), (Some((None, (Instruction::NOP, 2))), 5));
    assert_eq!(c.label_def, None);
    assert_eq!(c.times, None);

    assert_eq!(c.extract_header(" lab: if true nop ' ; this is a comment ").unwrap(), (Some((None, (Instruction::NOP, 14))), 17));
    assert_eq!(c.label_def.as_ref().unwrap().0, "lab");
    assert_eq!(c.label_def.as_ref().unwrap().1, Locality::Nonlocal);
    assert_eq!(c.times, Some(TimesInfo { total_count: 1, current: 0 }));

    assert_eq!(c.extract_header(" .lab2: if false nop ' ; this is a comment ").unwrap(), (Some((None, (Instruction::NOP, 17))), 20));
    assert_eq!(c.label_def.as_ref().unwrap().0, "thingy.lab2");
    assert_eq!(c.label_def.as_ref().unwrap().1, Locality::Local);
    assert_eq!(c.times, Some(TimesInfo { total_count: 0, current: 0 }));

    match c.extract_header("   rax:    ; this is a comment ") {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(3));
            assert!(matches!(e.kind, AsmErrorKind::ReservedSymbolName));
        }
    }

    assert_eq!(c.extract_header("  reP NoP  ").unwrap(), (Some((Some((Prefix::REP, 2)), (Instruction::NOP, 6))), 9));
    assert_eq!(c.label_def, None);
    assert_eq!(c.times, None);

    match c.extract_header("  reP  ") {
        Ok(_) => panic!(),
        Err(e) => {
            assert_eq!(e.pos, Some(2));
            assert!(matches!(e.kind, AsmErrorKind::PrefixWithoutInstruction));
        }
    }
}