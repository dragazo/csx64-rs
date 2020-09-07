use super::*;

pub(super) struct AssembleArgs {
    pub(super) file: ObjectFile,
    
    pub(super) current_seg: AsmSegment,
    pub(super) done_segs: AsmSegment,

    pub(super) line: usize,
    pub(super) line_pos_in_seg: usize,

    pub(super) last_nonlocal_label: String,
    pub(super) label_def: String,

    pub(super) times: i64,
    pub(super) times_i: i64,

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

    // pub(super) fn extract_expr(&self, src: &str) -> Result<(Expr, usize), AssembleError> {
        
    // }
}
