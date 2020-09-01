//! Various types of emulated hardware registers.

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
