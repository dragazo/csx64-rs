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

pub(super) struct TimesInfo {
    total_count: usize,
    current: usize,
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

    // attempts to read a binary op from start of string - on success returns OP and parsed operator (in bytes)
    fn extract_binary_op(&self, src: &str) -> Option<(OP, usize)> {
        for (repr, op) in BINARY_OP_STR.iter() {
            if src.starts_with(repr) {
                return Some((*op, repr.len()));
            }
        }
        None
    }

    pub(super) fn extract_string(&self, raw_line: &str, raw_start: usize, raw_stop: usize) -> Result<(Vec<u8>, usize), AsmError> {
        let src = &raw_line[raw_start..raw_stop];

        // find the next starting quote char
        let mut pos = src.char_indices();
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
                        return Ok((res, match pos.next() {
                            None => raw_stop,
                            Some((a, _)) => raw_start + a,
                        }));
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
    pub(super) fn extract_expr(&self, raw_line: &str, raw_start: usize, raw_stop: usize) -> Result<(Expr, usize), AsmError> {
        let mut pos = raw_start;
        let mut src = &raw_line[raw_start..raw_stop];

        let mut unary_stack: Vec<char> = Vec::with_capacity(8);

        loop {
            let mut chars = src.char_indices().peekable();

            // consume all unary ops up to a token and push onto unary stack
            'unary: loop {
                match chars.peek() {
                    // if there's not a next character we have a missing token
                    None => return err!(self, kind: ExprParse, pos: raw_stop, "expected expr token"),
                    Some((_, x)) if x.is_whitespace() || *x == '+' => (),                // whitespace and unary plus do nothing
                    Some((_, x)) if ['-', '~', '!'].contains(x) => unary_stack.push(*x), // push unary ops onto stack
                    Some(_) => break 'unary, // otherwise is a token, which also means end of term
                }
                chars.next(); // if we get here, we consumed it
            }

            let first_token_char = chars.peek().unwrap().1;
            let numeric = first_token_char.is_digit(10);

            let mut depth: usize = 0;           // parens depth - initially 0
            let mut quote: Option<char> = None; // current quote char - initially none

            // move end to next logical separator (white space, open paren, or binary op - but only at depth 0)
            let mut end = chars.clone();
            if first_token_char == '(' { // if starting with parens, go to depth 1 and skip the char
                depth += 1;
                end.next();
            }
            let end = 'separator: loop {
                let end_content = end.peek().cloned();
                match end_content {
                    // if there's not a next character we're either done (depth 0), or failed
                    None => {
                        if depth == 0 && quote.is_none() {
                            break 'separator (None, raw_stop);
                        }
                        else if depth != 0 {
                            return err!(self, kind: ExprParse, pos: raw_stop, "missing close paren");
                        }
                        else {
                            return err!(self, kind: ExprParse, pos: raw_stop, "missing close quote");
                        }
                    }
                    Some((p, ch)) => match quote {
                        None => {
                            // account for important characters
                            if ch == '(' && depth != 0 {
                                depth += 1; 
                            }
                            else if ch == ')' {
                                if depth > 0 { depth -= 1; }             // if depth > 0 drop down a level
                                else { break 'separator (None, p + 1); } // otherwise this marks the logical separator
                            }
                            else if numeric && (ch == 'e' || ch == 'E') && match end.clone().next() { Some((_, x)) if x == '+' || x == '-' => true, _ => false } {
                                end.next(); // make sure an exponent sign won't be parsed as binary + or - by skipping it
                            }
                            else if ['"', '\'', '`'].contains(&ch) {
                                quote = Some(ch); // enter quote mode
                            }
                            else if depth == 0 {
                                if ch.is_whitespace() || ch == '(' { break 'separator (None, p); }
                                match self.extract_binary_op(&src[p..]) {
                                    Some((op, len)) => {
                                        end.nth(len - 1); // skip end ahead len places
                                        break 'separator (Some(op), p);
                                    }
                                    None => (),
                                }
                            }
                        }
                        Some(quote_ch) => {
                            if ch == quote_ch { quote = None; } // if we have a matching quote, end quote mode
                        }
                    }
                }
                end.next(); // if we get here, we consumed it
            };

            let token_pos = chars.peek().unwrap().0;
            let token = &src[token_pos..end.1]; // grab the token we just found
            if token.is_empty() {
                return err!(self, kind: ExprParse, pos: token_pos, "empty token encountered");
            }
            let token_first_char = token.chars().next().unwrap();

            let mut expr_tree: Option<Expr> =
                if token_first_char == '(' { // if it's a sub-expression
                    match self.extract_expr(raw_line, pos + token_pos + 1, pos + end.1 - 1)? {
                        (expr, aft) => {
                            if aft != pos + end.1 {
                                return err!(self, kind: ExprParse, pos: aft, "interior of sub-expression was more than one expression");
                            }
                            Some(expr)
                        }
                    }
                }
                else if token_first_char == '$' { // if it's a user-level assembler token
                    let token_upper = token.to_uppercase();

                    if token_upper == CURRENT_LINE_MACRO {
                        if self.current_seg.is_empty() {
                            return err!(self, kind: ExprParse, pos: token_pos, "attempt to use {} macro outside of any segment", token_upper);
                        }

                        Some(ExprData::Uneval {
                            op: OP::Add,
                            left: Some(Box::new(ExprData::Ident(SEG_OFFSETS.get(&self.current_seg).unwrap().to_string()).into())),
                            right: Some(Box::new((self.line_pos_in_seg as u64).into())),
                        }.into())
                    }
                    else if token_upper == START_OF_SEG_MACRO {
                        if self.current_seg.is_empty() {
                            return err!(self, kind: ExprParse, pos: token_pos, "attempt to use {} macro outside of any segment", token_upper);
                        }

                        match self.times {
                            None => return err!(self, kinf: ExprParse, pos: token_pos, "attempt to use {} macro outside of a TIMES directive", token_upper);
                            Some(info) {
                                Some((info.current as u64).into())
                            }
                        }
                    }
                    else if token_upper == STRING_LITERAL_MACRO || token_upper == BINARY_LITERAL_MACRO {
                        // get the index of the next paren
                        
                    }
                }
                else {

                };
        }
    }
    */
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
