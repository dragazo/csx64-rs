use std::iter::Peekable;
use std::str::CharIndices;

use super::*;
use super::expr::{ExprData, OP};

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

    pub(super) last_nonlocal_label: String,
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
/*
    // attempts to parse a function call syntax, returning the function name and a list of (trimmed) arguments.
    fn parse_function_call(&self, raw_line: &str, raw_start: usize, raw_stop: usize) -> Result<(&str, Vec<Expr>), AsmError> {
        let paren_pos = match raw_line[raw_start..raw_stop].find('(') {
            None => return err!(self, kind: ExpectedOpenParen, pos: raw_stop),
            Some(p) => raw_start + p,
        };
        debug_assert_eq!(raw_line.chars().rev().next().unwrap(), ')'); // should end in a closing quote

        let func = &raw_line[raw_start..paren_pos];
        let mut args = vec![];
        
        let mut paren_depth = 0;
        let mut pos = paren_pos + 1;
        let mut chars = raw_line[pos..raw_stop-1].char_indices(); // iterate through the rest of the 
        loop {
            match chars.next() {
                None => {
                    if paren_depth != 0 {
                        return err!(self, 
                    }
                    args.push(raw_line[pos..raw_stop-1].trim()); // if we run out of chars, push the tail onto args and quit
                    break;
                }
                Some((p, c)) => {

                }
            }
        }
    }

    // attempts to extract an expression from the string, allowing leading whitespace.
    // if a well-formed expression is found, returns Ok with it and the character index just after it, otherwise returns Err.
    pub(super) fn extract_expr(&self, raw_line: &str, raw_start: usize, raw_stop: usize) -> Result<(Expr, usize), AsmError> {
        let mut parsing_pos = raw_start;
        let mut unary_stack: Vec<OP> = Vec::with_capacity(8);

        loop {
            let mut chars = raw_line[parsing_pos..raw_stop].char_indices().peekable();

            // consume all unary ops up to a token and push onto unary stack
            debug_assert!(unary_stack.is_empty());
            let (term_start, numeric) = loop {
                match chars.peek().copied() {
                    None => return err!(self, kind: ExpectedExprTerm, pos: raw_stop),
                    Some((_, x)) if x.is_whitespace() || x == '+' => (), // whitespace and unary plus do nothing
                    Some((_, '-')) => unary_stack.push(OP::Neg),         // push unary ops onto the stack
                    Some((_, '~')) => unary_stack.push(OP::BitNot),
                    Some((_, '!')) => unary_stack.push(OP::LogNot),
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
                            1 => match self.extract_binary_op(raw_line, p + 1, raw_stop) { // this would drop down to level 0, so end of term
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
                        _ if paren_depth == 0 => {
                            if let Some((op, aft)) = self.extract_binary_op(raw_line, p, raw_stop) {
                                break (parsing_pos + p, Some((op, aft))); // if we find a binary op, we're done
                            }
                            else if ch.is_whitespace() {
                                break (parsing_pos + p, None); // otherwise if we're on whitespace we're done (but no binary op)
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

            let mut term_expr = match term.chars().next().unwrap() {
                '(' => { // if it's a sub-expression (paren grouped expr)
                    debug_assert_eq!(term.chars().rev().next().unwrap(), ')'); // last char of term should be a closing paren
                    let (expr, aft) = self.extract_expr(raw_line, term_start + 1, term_stop - 1)?; // parse interior as an expr
                    if !raw_line[aft..term_stop-1].trim_start().is_empty() {
                        return err!(self, kind: ParenInteriorNotExpr, pos: term_start); // we should be able to consume the whole interior
                    }
                    expr
                }
                '$' => match term.to_uppercase().as_str() { // if it's a macro token (parse as case insensitive)
                    CURRENT_LINE_MACRO => match SEG_OFFSETS.get(&self.current_seg) {
                        None => return err!(self, kind: IllegalInCurrentSegment, pos: term_start),
                        Some(ident) => (OP::Add, ExprData::Ident(ident.to_string()), self.line_pos_in_seg as u64).into(),
                    }
                    START_OF_SEG_MACRO => match SEG_ORIGINS.get(&self.current_seg) {
                        None => return err!(self, kind: IllegalInCurrentSegment, pos: term_start),
                        Some(ident) => ExprData::Ident(ident.to_string()).into(),
                    }
                    TIMES_ITER_MACRO => match self.times {
                        None => return err!(self, kinf: TimesIterOutisideOfTimes, pos: term_start),
                        Some(info) => (info.current as u64).into(),
                    }
                    term_upper @ STRING_LITERAL_MACRO | BINARY_LITERAL_MACRO => {
                        
                    }
                }
            };
        }
    }
    */
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

            binary_literals: Default::default(),
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
