//! Various types of emulated hardware registers.

use rug::float::Round;

/// A 64-bit general-purpose CPU register with standard partitioning.
#[derive(Default, Clone, Copy)]
pub struct CPURegister(pub u64);
impl CPURegister {
    /// Gets the full 64-bit value.
    pub const fn x64(self) -> u64 {
        self.0
    }
    /// Sets the full 64-bit value.
    pub fn set_x64(&mut self, val: u64) {
        self.0 = val;
    }

    /// Gets the low 32-bits.
    pub const fn x32(self) -> u32 {
        self.0 as u32
    }
    /// Sets the low 32-bits to `val` and zeros the high 32-bits.
    pub fn set_x32(&mut self, val: u32) {
        self.0 = val as u64;
    }

    /// Gets the low 16-bits.
    pub const fn x16(self) -> u16 {
        self.0 as u16
    }
    /// Sets the low 16-bits (without modifying any other bits).
    pub fn set_x16(&mut self, val: u16) {
        self.0 = (self.0 & 0xffffffffffff0000) | (val as u64);
    }

    /// Gets the low 8-bits.
    pub const fn x8(self) -> u8 {
        self.0 as u8
    }
    /// Sets the low 8-bits (without modifying any other bits).
    pub fn set_x8(&mut self, val: u8) {
        self.0 = (self.0 & 0xffffffffffffff00) | (val as u64);
    }

    /// Gets bits 8-15.
    pub const fn x8h(self) -> u8 {
        (self.0 >> 8) as u8
    }
    /// Sets bits 8-15 (without modifying any other bits).
    pub fn set_x8h(&mut self, val: u8) {
        self.0 = (self.0 & 0xffffffffffff00ff) | ((val as u64) << 8);
    }
}

#[test]
fn test_cpu_register() {
    let mut r = CPURegister::default();
    assert_eq!(r.x64(), 0);

    r.set_x64(0x2049381758392734);
    assert_eq!(r.x64(), 0x2049381758392734);
    assert_eq!(r.x32(), 0x58392734);
    assert_eq!(r.x16(), 0x2734);
    assert_eq!(r.x8(), 0x34);
    assert_eq!(r.x8h(), 0x27);

    r.set_x16(0x8692);
    assert_eq!(r.x64(), 0x2049381758398692);
    assert_eq!(r.x32(), 0x58398692);
    assert_eq!(r.x16(), 0x8692);
    assert_eq!(r.x8(), 0x92);
    assert_eq!(r.x8h(), 0x86);

    r.set_x8(0xf5);
    assert_eq!(r.x64(), 0x20493817583986f5);
    assert_eq!(r.x32(), 0x583986f5);
    assert_eq!(r.x16(), 0x86f5);
    assert_eq!(r.x8(), 0xf5);
    assert_eq!(r.x8h(), 0x86);

    r.set_x8h(0x12);
    assert_eq!(r.x64(), 0x20493817583912f5);
    assert_eq!(r.x32(), 0x583912f5);
    assert_eq!(r.x16(), 0x12f5);
    assert_eq!(r.x8(), 0xf5);
    assert_eq!(r.x8h(), 0x12);

    r.set_x32(0x59288643);
    assert_eq!(r.x64(), 0x59288643);
    assert_eq!(r.x32(), 0x59288643);
    assert_eq!(r.x16(), 0x8643);
    assert_eq!(r.x8(), 0x43);
    assert_eq!(r.x8h(), 0x86);
}

/// Represents a 512-bit ZMM (vector) register.
/// 
/// Values are held as an array of 64 bytes, which is suitably aligned for use in any simd operations.
/// Multi-byte values must be stored little-endian to facilitate the correct index behavior.
/// The provided element accessors automatically do this, but care should be taken if accessing the data directly (e.g. for simd operations).
#[derive(Clone, Copy)]
#[repr(align(64))]
pub struct ZMMRegister {
    pub data: [u8; 64],
}
impl Default for ZMMRegister {
    fn default() -> Self {
        Self { data: [0; 64] } // arrays this large don't impl Default on their own - new releases of rust might fix this
    }
}
macro_rules! zmm_impl {
    ($get:ident : $set:ident => $t:ident) => {
        pub fn $get(&self, index: usize) -> $t {
            $t::from_le(bytemuck::cast_slice(&self.data)[index])
        }
        pub fn $set(&mut self, index: usize, value: $t) {
            bytemuck::cast_slice_mut(&mut self.data)[index] = value.to_le()
        }
    }
}
impl ZMMRegister {
    pub fn get_u8(&self, index: usize) -> u8 {
        self.data[index]
    }
    pub fn set_u8(&mut self, index: usize, value: u8) {
        self.data[index] = value
    }

    zmm_impl! { get_u16 : set_u16 => u16 }
    zmm_impl! { get_u32 : set_u32 => u32 }
    zmm_impl! { get_u64 : set_u64 => u64 }
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
    ($get:ident : $set:ident : $flip:ident => [$mask:expr]) => {
        pub fn $get(self) -> bool {
            (self.0 & $mask) != 0
        }
        pub fn $set(&mut self, value: bool) {
            if value { self.0 |= $mask; } else { self.0 &= !$mask; }
        }
        pub fn $flip(&mut self) {
            self.0 ^= $mask;
        }
    }
}
macro_rules! impl_field {
    ($get:ident : $set:ident => $from:ty [ $shift:expr => $mask:expr ] $to:ty) => {
        pub fn $get(self) -> $to {
            ((self.0 >> $shift) & $mask) as $to
        }
        pub fn $set(&mut self, val: $to) {
            assert_eq!(val, val & $mask);
            self.0 = (self.0 & !($mask << $shift)) | ((val as $from) << $shift);
        }
    }
}

/// The FPU control word.
#[derive(Clone, Copy)]
pub struct Control(pub u16);
impl Control {
    impl_flag! { get_im : set_im : flip_im => [1] }
    impl_flag! { get_dm : set_dm : flip_dm => [2] }
    impl_flag! { get_zm : set_zm : flip_zm => [4] }
    impl_flag! { get_om : set_om : flip_om => [8] }
    impl_flag! { get_um : set_um : flip_um => [16] }
    impl_flag! { get_pm : set_pm : flip_pm => [32] }
    impl_flag! { get_iem : set_iem : flip_iem => [128] }
    impl_flag! { get_ic : set_ic : flip_ic => [4096] }

    impl_field! { get_pc : set_pc => u16 [ 8 => 3 ] u8 }
    impl_field! { get_rc : set_rc => u16 [ 10 => 3 ] u8 }

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
    impl_flag! { get_i : set_i : flip_i => [1] }
    impl_flag! { get_d : set_d : flip_d => [2] }
    impl_flag! { get_z : set_z : flip_z => [4] }
    impl_flag! { get_o : set_o : flip_o => [8] }
    impl_flag! { get_u : set_u : flip_u => [16] }
    impl_flag! { get_p : set_p : flip_p => [32] }
    impl_flag! { get_sf : set_sf : flip_sf => [64] }
    impl_flag! { get_ir : set_ir : flip_ir => [128] }
    impl_flag! { get_c0 : set_c0 : flip_c0 => [256] }
    impl_flag! { get_c1 : set_c1 : flip_c1 => [512] }
    impl_flag! { get_c2 : set_c2 : flip_c2 => [1024] }
    impl_flag! { get_c3 : set_c3 : flip_c3 => [16384] }
    impl_flag! { get_b : set_b : flip_b => [32768] }

    impl_field! { get_top : set_top => u16 [ 11 => 7 ] u8 }
}

/// The FPU tag word.
#[derive(Clone, Copy)]
pub struct Tag(pub u16);
impl Tag {
    pub fn get_physical(self, index: u8) -> u8 {
        ((self.0 >> (2 * index)) & 3) as u8
    }
    pub fn set_physical(&mut self, index: u8, value: TagValue) {
        assert!(index <= 7);
        let s = 2 * index;
        self.0 = (self.0 & !(3 << s)) | ((value as u16) << s);
    }
}

/// The valid values for a register tag.
#[repr(u8)]
pub enum TagValue {
    NonZero = 0,
    Zero = 1,
    Special = 2,
    Empty = 3,
}