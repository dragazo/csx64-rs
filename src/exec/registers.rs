//! Various types of emulated hardware registers.

use rug::float::Round;

/// A 64-bit general-purpose CPU register with standard partitioning.
#[derive(Default, Clone, Copy)]
pub struct CPURegister(pub u64);
impl CPURegister {
    /// Gets the full 64-bit value.
    pub const fn get_x64(self) -> u64 {
        self.0
    }
    /// Sets the full 64-bit value.
    pub fn set_x64(&mut self, val: u64) {
        self.0 = val;
    }

    /// Gets the low 32-bits.
    pub const fn get_x32(self) -> u32 {
        self.0 as u32
    }
    /// Sets the low 32-bits to `val` and zeros the high 32-bits.
    pub fn set_x32(&mut self, val: u32) {
        self.0 = val as u64;
    }

    /// Gets the low 16-bits.
    pub const fn get_x16(self) -> u16 {
        self.0 as u16
    }
    /// Sets the low 16-bits (without modifying any other bits).
    pub fn set_x16(&mut self, val: u16) {
        self.0 = (self.0 & 0xffffffffffff0000) | (val as u64);
    }

    /// Gets the low 8-bits.
    pub const fn get_x8(self) -> u8 {
        self.0 as u8
    }
    /// Sets the low 8-bits (without modifying any other bits).
    pub fn set_x8(&mut self, val: u8) {
        self.0 = (self.0 & 0xffffffffffffff00) | (val as u64);
    }

    /// Gets bits 8-15.
    pub const fn get_x8h(self) -> u8 {
        (self.0 >> 8) as u8
    }
    /// Sets bits 8-15 (without modifying any other bits).
    pub fn set_x8h(&mut self, val: u8) {
        self.0 = (self.0 & 0xffffffffffff00ff) | ((val as u64) << 8);
    }

    /// Gets the value with the given size, zero extended to 64-bit.
    /// Panics if sizecode is invalid.
    pub(super) fn raw_get(self, sizecode: u8) -> u64 {
        match sizecode {
            0 => self.get_x8() as u64,
            1 => self.get_x16() as u64,
            2 => self.get_x32() as u64,
            3 => self.get_x64(),
            _ => panic!(),
        }
    }
    /// Writes the value with the given size, truncating it if too large.
    /// Panics if sizecode is invalid.
    pub(super) fn raw_set(&mut self, sizecode: u8, value: u64) {
        match sizecode {
            0 => self.set_x8(value as u8),
            1 => self.set_x16(value as u16),
            2 => self.set_x32(value as u32),
            3 => self.set_x64(value),
            _ => panic!(),
        }
    }
}

#[test]
fn test_cpu_register() {
    let mut r = CPURegister::default();
    assert_eq!(r.get_x64(), 0);

    r.set_x64(0x2049381758392734);
    assert_eq!(r.get_x64(), 0x2049381758392734);
    assert_eq!(r.get_x32(), 0x58392734);
    assert_eq!(r.get_x16(), 0x2734);
    assert_eq!(r.get_x8(), 0x34);
    assert_eq!(r.get_x8h(), 0x27);

    r.set_x16(0x8692);
    assert_eq!(r.get_x64(), 0x2049381758398692);
    assert_eq!(r.get_x32(), 0x58398692);
    assert_eq!(r.get_x16(), 0x8692);
    assert_eq!(r.get_x8(), 0x92);
    assert_eq!(r.get_x8h(), 0x86);

    r.set_x8(0xf5);
    assert_eq!(r.get_x64(), 0x20493817583986f5);
    assert_eq!(r.get_x32(), 0x583986f5);
    assert_eq!(r.get_x16(), 0x86f5);
    assert_eq!(r.get_x8(), 0xf5);
    assert_eq!(r.get_x8h(), 0x86);

    r.set_x8h(0x12);
    assert_eq!(r.get_x64(), 0x20493817583912f5);
    assert_eq!(r.get_x32(), 0x583912f5);
    assert_eq!(r.get_x16(), 0x12f5);
    assert_eq!(r.get_x8(), 0xf5);
    assert_eq!(r.get_x8h(), 0x12);

    r.set_x32(0x59288643);
    assert_eq!(r.get_x64(), 0x59288643);
    assert_eq!(r.get_x32(), 0x59288643);
    assert_eq!(r.get_x16(), 0x8643);
    assert_eq!(r.get_x8(), 0x43);
    assert_eq!(r.get_x8h(), 0x86);
}

/// Represents a 512-bit ZMM (vector) register.
/// 
/// Values are held as an array of 64 bytes, which is suitably aligned for use in any simd operations.
/// Multi-byte values must be stored little-endian to facilitate the correct index behavior.
/// The provided element accessors automatically do this, but care should be taken if accessing the data directly (e.g. for simd operations).
#[derive(Clone, Copy)]
#[repr(align(64))]
pub struct ZMMRegister(pub [u8; 64]);
impl Default for ZMMRegister {
    fn default() -> Self {
        Self([0; 64]) // arrays this large don't impl Default on their own - new releases of rust might fix this
    }
}
macro_rules! zmm_impl {
    ($get:ident : $set:ident => $t:ident) => {
        pub fn $get(&self, index: usize) -> $t {
            $t::from_le(bytemuck::cast_slice(&self.0)[index])
        }
        pub fn $set(&mut self, index: usize, value: $t) {
            bytemuck::cast_slice_mut(&mut self.0)[index] = value.to_le()
        }
    };
    (signed $get:ident : $set:ident => $i:ident : $u:ident : $raw_get:ident : $raw_set:ident) => {
        pub fn $get(&self, index: usize) -> $i {
            self.$raw_get(index) as $i
        }
        pub fn $set(&mut self, index: usize, value: $i) {
            self.$raw_set(index, value as $u)
        }
    };
    (float $get:ident : $set:ident => $t:ident : $raw_get:ident : $raw_set:ident) => {
        pub fn $get(&self, index: usize) -> $t {
            $t::from_bits(self.$raw_get(index))
        }
        pub fn $set(&mut self, index: usize, value: $t) {
            self.$raw_set(index, value.to_bits())
        }
    };
}
impl ZMMRegister {
    pub fn get_u8(&self, index: usize) -> u8 {
        self.0[index]
    }
    pub fn set_u8(&mut self, index: usize, value: u8) {
        self.0[index] = value
    }

    zmm_impl! { get_u16 : set_u16 => u16 }
    zmm_impl! { get_u32 : set_u32 => u32 }
    zmm_impl! { get_u64 : set_u64 => u64 }

    zmm_impl! { signed get_i64 : set_i64 => i64 : u64 : get_u64 : set_u64 }
    zmm_impl! { signed get_i32 : set_i32 => i32 : u32 : get_u32 : set_u32 }
    zmm_impl! { signed get_i16 : set_i16 => i16 : u16 : get_u16 : set_u16 }
    zmm_impl! { signed get_i8 : set_i8 => i8 : u8 : get_u8 : set_u8 }

    zmm_impl! { float get_f64 : set_f64 => f64 : get_u64 : set_u64 }
    zmm_impl! { float get_f32 : set_f32 => f32 : get_u32 : set_u32 }

    pub(crate) fn get(&self, index: usize, size: u8) -> u64 {
        match size {
            0 => self.get_u8(index) as u64,
            1 => self.get_u16(index) as u64,
            2 => self.get_u32(index) as u64,
            3 => self.get_u64(index),
            _ => panic!(),
        }
    }
    pub(crate) fn set(&mut self, index: usize, size: u8, value: u64) {
        match size {
            0 => self.set_u8(index, value as u8),
            1 => self.set_u16(index, value as u16),
            2 => self.set_u32(index, value as u32),
            3 => self.set_u64(index, value),
            _ => panic!(),
        }
    }
}

#[test]
fn test_zmm_register() {
    assert_eq!(std::mem::align_of::<ZMMRegister>(), 64);
    assert_eq!(std::mem::size_of::<ZMMRegister>(), 64);
    
    let mut r = ZMMRegister::default();

    for i in 0..64 {
        r.set_u8(i, i as u8);
    }
    for i in 0..32 {
        assert_eq!(r.get_u16(i), u16::from_le_bytes([i as u8 * 2, i as u8 * 2 + 1]));
    }
}

macro_rules! impl_flag {
    ($mask_name:ident, $set:ident, $clear:ident, $flip:ident, $get:ident, $assign:ident => $from:ty [ $mask:literal ]) => {
        pub const $mask_name: $from = $mask;
        pub fn $set(&mut self) { self.0 |= $mask }
        pub fn $clear(&mut self) { self.0 &= !$mask }
        pub fn $flip(&mut self) { self.0 ^= $mask }
        pub const fn $get(self) -> bool { (self.0 & $mask) != 0 }
        pub fn $assign(&mut self, value: bool) {
            if value { self.$set() } else { self.$clear() }
        }
    }
}
macro_rules! impl_field {
    ($mask_name:ident, $get:ident, $assign:ident => $from:ty [ $shift:literal => $mask:literal ] $to:ty) => {
        pub const $mask_name: $from = $mask << $shift;
        pub const fn $get(self) -> $to {
            ((self.0 >> $shift) & $mask) as $to
        }
        pub fn $assign(&mut self, val: $to) {
            assert_eq!(val, val & $mask);
            self.0 = (self.0 & !($mask << $shift)) | ((val as $from) << $shift);
        }
    }
}

/// The CPU flags register.
#[derive(Default, Clone, Copy)]
pub struct Flags(pub u64);
impl Flags {
    impl_flag! { MASK_CF, set_cf, clear_cf, flip_cf, get_cf, assign_cf       => u64 [0x0000000000000001] }
    impl_flag! { MASK_PF, set_pf, clear_pf, flip_pf, get_pf, assign_pf       => u64 [0x0000000000000004] }
    impl_flag! { MASK_AF, set_af, clear_af, flip_af, get_af, assign_af       => u64 [0x0000000000000010] }
    impl_flag! { MASK_ZF, set_zf, clear_zf, flip_zf, get_zf, assign_zf       => u64 [0x0000000000000040] }
    impl_flag! { MASK_SF, set_sf, clear_sf, flip_sf, get_sf, assign_sf       => u64 [0x0000000000000080] }
    impl_flag! { MASK_TF, set_tf, clear_tf, flip_tf, get_tf, assign_tf       => u64 [0x0000000000000100] }
    impl_flag! { MASK_IF, set_if, clear_if, flip_if, get_if, assign_if       => u64 [0x0000000000000200] }
    impl_flag! { MASK_DF, set_df, clear_df, flip_df, get_df, assign_df       => u64 [0x0000000000000400] }
    impl_flag! { MASK_OF, set_of, clear_of, flip_of, get_of, assign_of       => u64 [0x0000000000000800] }
    impl_flag! { MASK_NT, set_nt, clear_nt, flip_nt, get_nt, assign_nt       => u64 [0x0000000000004000] }
    impl_flag! { MASK_RF, set_rf, clear_rf, flip_rf, get_rf, assign_rf       => u64 [0x0000000000010000] }
    impl_flag! { MASK_VM, set_vm, clear_vm, flip_vm, get_vm, assign_vm       => u64 [0x0000000000020000] }
    impl_flag! { MASK_AC, set_ac, clear_ac, flip_ac, get_ac, assign_ac       => u64 [0x0000000000040000] }
    impl_flag! { MASK_VIF, set_vif, clear_vif, flip_vif, get_vif, assign_vif => u64 [0x0000000000080000] }
    impl_flag! { MASK_VIP, set_vip, clear_vip, flip_vip, get_vip, assign_vip => u64 [0x0000000000100000] }
    impl_flag! { MASK_ID, set_id, clear_id, flip_id, get_id, assign_id       => u64 [0x0000000000200000] }

    impl_field! { MASK_IOPL, get_iopl, assign_iopl => u64 [ 12 => 0b11 ] u8 }

    // -------------------------------------------------------------------------------------

    impl_flag! { MASK_OTS, set_ots, clear_ots, flip_ots, get_ots, assign_ots => u64 [0x0000000100000000] }

    // -------------------------------------------------------------------------------------

    /// Checks the "below" condition.
    pub const fn condition_b(self) -> bool { self.get_cf() }
    /// Checks the "below or equal" condition.
    pub const fn condition_be(self) -> bool { self.get_cf() || self.get_zf() }
    /// Checks the "above" condition.
    pub const fn condition_a(self) -> bool { !self.condition_be() }
    /// Checks the "above or equal" condition.
    pub const fn condition_ae(self) -> bool { !self.condition_b() }

    // -------------------------------------------------------------------------------------

    /// Checks the "less than" condition.
    pub const fn condition_l(self) -> bool { self.get_sf() != self.get_of() }
    /// Checks the "less or equal" condition.
    pub const fn condition_le(self) -> bool { self.get_zf() || (self.get_sf() != self.get_of()) }
    /// Checks the "greater than" condition.
    pub const fn condition_g(self) -> bool { !self.condition_le() }
    /// Checks the "greater or equal" condition.
    pub const fn condition_ge(self) -> bool { !self.condition_l() }
}

/// The MXCSR register.
#[derive(Default, Clone, Copy)]
pub struct MXCSR(pub u16);
impl MXCSR {

}

/// The FPU control word.
#[derive(Clone, Copy)]
pub struct Control(pub u16);
impl Control {
    impl_flag! { MASK_IM, set_im, clear_im, flip_im, get_im, assign_im       => u16 [0x0001] }
    impl_flag! { MASK_DM, set_dm, clear_dm, flip_dm, get_dm, assign_dm       => u16 [0x0002] }
    impl_flag! { MASK_ZM, set_zm, clear_zm, flip_zm, get_zm, assign_zm       => u16 [0x0004] }
    impl_flag! { MASK_OM, set_om, clear_om, flip_om, get_om, assign_om       => u16 [0x0008] }
    impl_flag! { MASK_UM, set_um, clear_um, flip_um, get_um, assign_um       => u16 [0x0010] }
    impl_flag! { MASK_PM, set_pm, clear_pm, flip_pm, get_pm, assign_pm       => u16 [0x0020] }
    impl_flag! { MASK_IEM, set_iem, clear_iem, flip_iem, get_iem, assign_iem => u16 [0x0080] }
    impl_flag! { MASK_IC, set_ic, clear_ic, flip_ic, get_ic, assign_ic       => u16 [0x1000] }

    impl_field! { MASK_PC, get_pc, assign_pc => u16 [ 8 => 0b11 ] u8 }
    impl_field! { MASK_RC, get_rc, assign_rc => u16 [ 10 => 0b11 ] u8 }

    /// Gets the rounding control field and interprets it as a rounding mode enum for program use.
    pub fn get_rc_enum(self) -> Round {
        match self.get_rc() {
            0 => Round::Nearest,
            1 => Round::Down,
            2 => Round::Up,
            3 => Round::Zero,
            _ => unreachable!(),
        }
    }
    /// Gets the precision control field value in terms of the number of bits.
    /// Fails only for `0b01`, which is reserved.
    pub fn get_pc_val(self) -> Result<u32, ()> {
        match self.get_pc() {
            0 => Ok(24),
            1 => Err(()),
            2 => Ok(53),
            3 => Ok(64),
            _ => unreachable!(),
        }
    }
}

/// The FPU status word.
#[derive(Clone, Copy)]
pub struct Status(pub u16);
impl Status {
    impl_flag! { MASK_I, set_i, clear_i, flip_i, get_i, assign_i       => u16 [0x0001] }
    impl_flag! { MASK_D, set_d, clear_d, flip_d, get_d, assign_d       => u16 [0x0002] }
    impl_flag! { MASK_Z, set_z, clear_z, flip_z, get_z, assign_z       => u16 [0x0004] }
    impl_flag! { MASK_O, set_o, clear_o, flip_o, get_o, assign_o       => u16 [0x0008] }
    impl_flag! { MASK_U, set_u, clear_u, flip_u, get_u, assign_u       => u16 [0x0010] }
    impl_flag! { MASK_P, set_p, clear_p, flip_p, get_p, assign_p       => u16 [0x0020] }
    impl_flag! { MASK_SF, set_sf, clear_sf, flip_sf, get_sf, assign_sf => u16 [0x0040] }
    impl_flag! { MASK_IR, set_ir, clear_ir, flip_ir, get_ir, assign_ir => u16 [0x0080] }
    impl_flag! { MASK_C0, set_c0, clear_c0, flip_c0, get_c0, assign_c0 => u16 [0x0100] }
    impl_flag! { MASK_C1, set_c1, clear_c1, flip_c1, get_c1, assign_c1 => u16 [0x0200] }
    impl_flag! { MASK_C2, set_c2, clear_c2, flip_c2, get_c2, assign_c2 => u16 [0x0400] }
    impl_flag! { MASK_C3, set_c3, clear_c3, flip_c3, get_c3, assign_c3 => u16 [0x4000] }
    impl_flag! { MASK_B, set_b, clear_b, flip_b, get_b, assign_b       => u16 [0x8000] }

    impl_field! { MASK_TOP, get_top, assign_top => u16 [ 11 => 0b111 ] u8 }
}

/// The FPU tag word.
#[derive(Clone, Copy)]
pub struct Tag(pub u16);
impl Tag {
    pub fn get_physical(self, index: u8) -> u8 {
        ((self.0 >> (2 * index)) & 3) as u8
    }
    pub fn set_physical(&mut self, index: u8, value: TagValue) {
        assert!(index < 8);
        let s = 2 * index;
        self.0 = (self.0 & !(3 << s)) | ((value as u16) << s);
    }
}

/// The valid values for an fpu register tag.
#[repr(u8)]
pub enum TagValue {
    NonZero = 0,
    Zero = 1,
    Special = 2,
    Empty = 3,
}