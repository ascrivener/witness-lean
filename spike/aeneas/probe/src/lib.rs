//! Common Rust features, to see what Aeneas translates.

pub enum Error { Short, Overflow }

pub struct Reader<'a> { buf: &'a [u8], pos: usize }

impl<'a> Reader<'a> {
    pub fn new(buf: &'a [u8]) -> Self { Reader { buf, pos: 0 } }

    /// A byte, or `Short`.
    pub fn u8(&mut self) -> Result<u8, Error> {
        let b = *self.buf.get(self.pos).ok_or(Error::Short)?;
        self.pos += 1;
        Ok(b)
    }

    /// A little-endian u16, using `?`.
    pub fn u16_le(&mut self) -> Result<u16, Error> {
        let lo = self.u8()? as u16;
        let hi = self.u8()? as u16;
        Ok(lo | (hi << 8))
    }
}

/// Sum with checked arithmetic, using a `for` loop over a slice iterator.
pub fn checked_sum(xs: &[u32]) -> Option<u32> {
    let mut acc: u32 = 0;
    for x in xs {
        acc = acc.checked_add(*x)?;
    }
    Some(acc)
}

/// A `for` loop over a range.
pub fn count_zeros(xs: &[u8]) -> usize {
    let mut n = 0;
    for i in 0..xs.len() {
        if xs[i] == 0 { n += 1; }
    }
    n
}

/// Building a `Vec`.
pub fn encode_u32(mut v: u32) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 { out.push(byte); return out; }
        out.push(byte | 0x80);
    }
}

/// A trait with a generic function.
pub trait Checksum { fn add(&mut self, b: u8); fn get(&self) -> u32; }
pub struct Adler { a: u32, b: u32 }
impl Checksum for Adler {
    fn add(&mut self, x: u8) {
        self.a = (self.a + x as u32) % 65521;
        self.b = (self.b + self.a) % 65521;
    }
    fn get(&self) -> u32 { (self.b << 16) | self.a }
}
pub fn checksum<C: Checksum>(c: &mut C, data: &[u8]) -> u32 {
    let mut i = 0;
    while i < data.len() { c.add(data[i]); i += 1; }
    c.get()
}

