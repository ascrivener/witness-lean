//! Unsigned LEB128, the variable-length integer encoding in WebAssembly, DWARF and protobuf.

/// Decodes an unsigned LEB128 `u32` from the start of `buf`: the value and the number of bytes
/// it took, or `None` if `buf` ends first or the value doesn't fit 32 bits.
pub fn decode_u32(buf: &[u8]) -> Option<(u32, usize)> {
    let mut value: u32 = 0;
    let mut shift: u32 = 0;
    let mut i: usize = 0;
    while i < buf.len() && i < 5 {
        let byte = buf[i];
        let low = (byte & 0x7f) as u32;
        if shift == 28 && low > 0x0f {
            return None;
        }
        value |= low << shift;
        i += 1;
        if byte & 0x80 == 0 {
            return Some((value, i));
        }
        shift += 7;
    }
    None
}
