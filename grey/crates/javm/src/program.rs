//! PVM program loading and initialization (JAR v0.8.0).
//!
//! Includes `deblob` for parsing program blobs and linear memory
//! initialization with basic block prevalidation.

use alloc::{vec, vec::Vec};

use crate::instruction::Opcode;
use crate::vm::Pvm;
use crate::{Gas, PVM_PAGE_SIZE};

/// Parse a program blob into (code, bitmask, jump_table) (eq A.2).
///
/// deblob(p) = (c, k, j) where:
///   p = E(|j|) ⌢ E₁(z) ⌢ E(|c|) ⌢ E_z(j) ⌢ E(c) ⌢ E(k), |k| = |c|
pub fn deblob(blob: &[u8]) -> Option<(Vec<u8>, Vec<u8>, Vec<u32>)> {
    let mut offset = 0;

    // Read |j| (jump table length) as variable-length natural
    let (jt_len, n) = decode_natural(blob, offset)?;
    offset += n;

    // Read z (encoding size for jump table entries) as 1 byte
    if offset >= blob.len() {
        return None;
    }
    let z = blob[offset] as usize;
    offset += 1;

    // Read |c| (code length) as variable-length natural
    let (code_len, n) = decode_natural(blob, offset)?;
    offset += n;

    // Read jump table: jt_len entries, each z bytes LE
    let mut jump_table = Vec::with_capacity(jt_len);
    for _ in 0..jt_len {
        if offset + z > blob.len() {
            return None;
        }
        let mut val: u32 = 0;
        for i in 0..z {
            val |= (blob[offset + i] as u32) << (i * 8);
        }
        jump_table.push(val);
        offset += z;
    }

    // Read code: code_len bytes
    if offset + code_len > blob.len() {
        return None;
    }
    let code = blob[offset..offset + code_len].to_vec();
    offset += code_len;

    // Read bitmask: packed bitfield, ceil(code_len/8) bytes (eq C.9)
    let bitmask_bytes = (code_len + 7) / 8;
    if offset + bitmask_bytes > blob.len() {
        return None;
    }
    let packed_bitmask = &blob[offset..offset + bitmask_bytes];

    // Unpack packed bits to one byte per instruction (LSB first per byte)
    let mut bitmask = vec![0u8; code_len];
    // Process 8 bits at a time for the bulk of the bitmask
    let full_bytes = code_len / 8;
    for i in 0..full_bytes {
        let b = packed_bitmask[i];
        let out = &mut bitmask[i * 8..i * 8 + 8];
        out[0] = b & 1;
        out[1] = (b >> 1) & 1;
        out[2] = (b >> 2) & 1;
        out[3] = (b >> 3) & 1;
        out[4] = (b >> 4) & 1;
        out[5] = (b >> 5) & 1;
        out[6] = (b >> 6) & 1;
        out[7] = (b >> 7) & 1;
    }
    // Handle remaining bits
    for i in full_bytes * 8..code_len {
        bitmask[i] = (packed_bitmask[i / 8] >> (i % 8)) & 1;
    }

    Some((code, bitmask, jump_table))
}

// ---------------------------------------------------------------------------
// PolkaVM blob parser (PVM\x00 format from polkavm-common)
// ---------------------------------------------------------------------------

/// Parsed PolkaVM program blob.
pub struct PolkaVMProgram {
    pub ro_data_size: u32,
    pub rw_data_size: u32,
    pub stack_size: u32,
    pub ro_data: Vec<u8>,
    pub rw_data: Vec<u8>,
    pub code: Vec<u8>,
    pub bitmask: Vec<u8>,
    pub jump_table: Vec<u32>,
}

const PVM_MAGIC: &[u8] = b"PVM\x00";

/// Read a polkavm varint: leading 1-bits determine byte count.
fn read_pvm_varint(data: &[u8], offset: &mut usize) -> Option<u32> {
    if *offset >= data.len() { return None; }
    let first = data[*offset];
    let leading = first.leading_ones() as usize;
    match leading {
        0 => { *offset += 1; Some(first as u32) }
        1 => {
            if *offset + 1 >= data.len() { return None; }
            let val = ((first & 0x3f) as u32) << 8 | data[*offset + 1] as u32;
            *offset += 2; Some(val)
        }
        2 => {
            if *offset + 2 >= data.len() { return None; }
            let val = ((first & 0x1f) as u32) << 16
                | (data[*offset + 1] as u32)
                | ((data[*offset + 2] as u32) << 8);
            *offset += 3; Some(val)
        }
        3 => {
            if *offset + 3 >= data.len() { return None; }
            let val = ((first & 0x0f) as u32) << 24
                | (data[*offset + 1] as u32)
                | ((data[*offset + 2] as u32) << 8)
                | ((data[*offset + 3] as u32) << 16);
            *offset += 4; Some(val)
        }
        _ => {
            if *offset + 4 >= data.len() { return None; }
            let val = u32::from_le_bytes([
                data[*offset + 1], data[*offset + 2],
                data[*offset + 3], data[*offset + 4],
            ]);
            *offset += 5; Some(val)
        }
    }
}

/// Parse a PolkaVM blob (PVM\x00 magic, section-based format).
/// Returns the parsed program or None if invalid.
pub fn parse_polkavm_blob(blob: &[u8]) -> Option<PolkaVMProgram> {
    if blob.len() < 14 || &blob[0..4] != PVM_MAGIC {
        return None;
    }
    let mut offset = 4; // skip magic
    let _version = blob[offset]; offset += 1;
    offset += 8; // skip blob length

    let mut prog = PolkaVMProgram {
        ro_data_size: 0, rw_data_size: 0, stack_size: 0,
        ro_data: Vec::new(), rw_data: Vec::new(),
        code: Vec::new(), bitmask: Vec::new(), jump_table: Vec::new(),
    };

    while offset < blob.len() {
        let section_type = blob[offset]; offset += 1;
        if section_type == 0x00 { break; } // end of file

        let section_len = read_pvm_varint(blob, &mut offset)? as usize;
        let section_end = offset + section_len;
        if section_end > blob.len() { return None; }

        match section_type {
            0x01 => { // memory config
                prog.ro_data_size = read_pvm_varint(blob, &mut offset)?;
                prog.rw_data_size = read_pvm_varint(blob, &mut offset)?;
                prog.stack_size = read_pvm_varint(blob, &mut offset)?;
                offset = section_end;
            }
            0x02 => { // ro data
                prog.ro_data = blob[offset..section_end].to_vec();
                offset = section_end;
            }
            0x03 => { // rw data
                prog.rw_data = blob[offset..section_end].to_vec();
                offset = section_end;
            }
            0x04 => { offset = section_end; } // imports (skip for now)
            0x05 => { offset = section_end; } // exports (skip for now)
            0x06 => { // code + jump table + bitmask
                let jt_count = read_pvm_varint(blob, &mut offset)? as usize;
                if offset >= blob.len() { return None; }
                let jt_entry_size = blob[offset] as usize; offset += 1;
                let code_len = read_pvm_varint(blob, &mut offset)? as usize;

                // Jump table (before code)
                for _ in 0..jt_count {
                    if offset + jt_entry_size > blob.len() { return None; }
                    let mut val = 0u32;
                    for j in 0..jt_entry_size {
                        val |= (blob[offset + j] as u32) << (8 * j);
                    }
                    prog.jump_table.push(val);
                    offset += jt_entry_size;
                }

                // Code
                if offset + code_len > blob.len() { return None; }
                prog.code = blob[offset..offset + code_len].to_vec();
                offset += code_len;

                // Bitmask (packed bits)
                let bitmask_bytes = (code_len + 7) / 8;
                if offset + bitmask_bytes <= blob.len() {
                    let packed = &blob[offset..offset + bitmask_bytes];
                    prog.bitmask = vec![0u8; code_len];
                    for i in 0..code_len {
                        prog.bitmask[i] = (packed[i / 8] >> (i % 8)) & 1;
                    }
                    offset += bitmask_bytes;
                }
                offset = section_end.max(offset);
            }
            t if t & 0x80 != 0 => { offset = section_end; } // optional, skip
            _ => { return None; } // unknown required section
        }
    }

    if prog.code.is_empty() { return None; }
    Some(prog)
}

/// Strip corevm metadata wrapper (length-prefixed metadata before PVM blob).
pub fn strip_corevm_metadata(data: &[u8]) -> &[u8] {
    // corevm format: [metadata_len: u16 LE] [metadata bytes] [PVM\x00 blob]
    if data.len() > 4 && &data[0..4] == PVM_MAGIC {
        return data; // already a raw polkavm blob
    }
    // Try to find PVM magic
    if let Some(pos) = data.windows(4).position(|w| w == PVM_MAGIC) {
        return &data[pos..];
    }
    data
}

/// Initialize a PVM from a polkavm blob (PVM\x00 format).
/// Handles both raw .polkavm and wrapped .corevm files.
pub fn initialize_from_polkavm(blob: &[u8], arguments: &[u8], gas: Gas) -> Option<Pvm> {
    let raw = strip_corevm_metadata(blob);
    let prog = parse_polkavm_blob(raw)?;

    if !validate_basic_blocks(&prog.code, &prog.bitmask, &prog.jump_table) {
        return None;
    }

    let page_round = |x: u32| -> u32 {
        ((x + PVM_PAGE_SIZE - 1) / PVM_PAGE_SIZE) * PVM_PAGE_SIZE
    };

    let stack_pages = page_round(prog.stack_size);
    let args_len = arguments.len() as u32;
    let args_pages = page_round(args_len);
    let ro_pages = page_round(prog.ro_data_size);
    let rw_pages = page_round(prog.rw_data_size);
    // Doom needs ~22MB address space. Allocate generously.
    let heap_pages = 8192 * PVM_PAGE_SIZE; // 32MB heap

    let total_mapped = stack_pages + args_pages + ro_pages + rw_pages + heap_pages;
    let mut mem = vec![0u8; total_mapped as usize];

    let mut cursor = stack_pages as usize;
    // Arguments
    let args_end = cursor + args_len as usize;
    if args_end <= mem.len() {
        mem[cursor..args_end].copy_from_slice(arguments);
    }
    cursor = (stack_pages + args_pages) as usize;

    // RO data
    let ro_end = cursor + prog.ro_data.len().min(prog.ro_data_size as usize);
    if ro_end <= mem.len() {
        mem[cursor..ro_end].copy_from_slice(&prog.ro_data[..ro_end - cursor]);
    }
    cursor = (stack_pages + args_pages + ro_pages) as usize;

    // RW data
    let rw_end = cursor + prog.rw_data.len().min(prog.rw_data_size as usize);
    if rw_end <= mem.len() {
        mem[cursor..rw_end].copy_from_slice(&prog.rw_data[..rw_end - cursor]);
    }

    let heap_base = (stack_pages + args_pages + ro_pages + rw_pages) as u32;

    let mut registers = [0u64; crate::PVM_REGISTER_COUNT];
    registers[1] = stack_pages as u64; // SP
    registers[7] = stack_pages as u64; // A0 = start of args
    registers[8] = args_len as u64;    // A1 = args length

    let mut pvm = Pvm::new(prog.code, prog.bitmask, prog.jump_table, registers, mem, gas);
    pvm.heap_base = heap_base;
    pvm.heap_top = heap_base;
    Some(pvm)
}

/// Program initialization with JAR v0.8.0 linear memory layout.
///
/// Contiguous layout: [stack | args | roData | rwData | heap | unmapped...]
/// All mapped pages are read-write. No guard zones.
pub fn initialize_program(program_blob: &[u8], arguments: &[u8], gas: Gas) -> Option<Pvm> {
    let blob = skip_metadata(program_blob);

    // Parse the standard program blob header:
    // E₃(|o|) ⌢ E₃(|w|) ⌢ E₂(z) ⌢ E₃(s) ⌢ o ⌢ w ⌢ E₄(|c|) ⌢ c
    if blob.len() < 15 {
        return None;
    }

    let mut offset = 0;

    let ro_size = read_le_u24(blob, &mut offset)? as u32;
    let rw_size = read_le_u24(blob, &mut offset)? as u32;
    let heap_pages = read_le_u16(blob, &mut offset)? as u32;
    let stack_size = read_le_u24(blob, &mut offset)? as u32;

    // Read read-only data
    if offset + ro_size as usize > blob.len() {
        return None;
    }
    let ro_data = &blob[offset..offset + ro_size as usize];
    offset += ro_size as usize;

    // Read read-write data
    if offset + rw_size as usize > blob.len() {
        return None;
    }
    let rw_data = &blob[offset..offset + rw_size as usize];
    offset += rw_size as usize;

    // Read E₄(|c|) — 4-byte LE code blob length
    let code_len = read_le_u32(blob, &mut offset)? as usize;
    if offset + code_len > blob.len() {
        return None;
    }
    let program_data = &blob[offset..offset + code_len];
    let (code, bitmask, jump_table) = deblob(program_data)?;

    // JAR v0.8.0: basic block prevalidation
    if !validate_basic_blocks(&code, &bitmask, &jump_table) {
        return None;
    }

    let page_round = |x: u32| -> u32 {
        ((x + PVM_PAGE_SIZE - 1) / PVM_PAGE_SIZE) * PVM_PAGE_SIZE
    };

    // Linear layout: stack | args | roData | rwData | heap
    let s = page_round(stack_size);              // stack: [0, s)
    let arg_start = s;                            // args:  [s, s + P(|a|))
    let ro_start = arg_start + page_round(arguments.len() as u32);
    let rw_start = ro_start + page_round(ro_size);
    let heap_start = rw_start + page_round(rw_size);
    let heap_end = heap_start + heap_pages * PVM_PAGE_SIZE;
    let mem_size = heap_end;

    // Check total fits in 32-bit address space
    if (mem_size as u64) > (1u64 << 32) {
        return None;
    }

    // Build flat memory buffer
    let mut flat_mem = vec![0u8; mem_size as usize];
    if !arguments.is_empty() {
        flat_mem[arg_start as usize..arg_start as usize + arguments.len()].copy_from_slice(arguments);
    }
    if !ro_data.is_empty() {
        flat_mem[ro_start as usize..ro_start as usize + ro_data.len()].copy_from_slice(ro_data);
    }
    if !rw_data.is_empty() {
        flat_mem[rw_start as usize..rw_start as usize + rw_data.len()].copy_from_slice(rw_data);
    }

    // Registers (JAR v0.8.0 linear)
    let mut registers = [0u64; 13];
    let halt_addr: u64 = (1u64 << 32) - (1u64 << 16); // 0xFFFF0000
    registers[0] = halt_addr;                 // φ[0]: RA (halt address for top-level return)
    registers[1] = s as u64;                  // φ[1]: SP (top of stack)
    registers[7] = arg_start as u64;          // φ[7]: argument base
    registers[8] = arguments.len() as u64;    // φ[8]: argument length

    tracing::info!(
        "PVM init (linear): stack=[0,{:#x}), args={:#x}+{}, ro={:#x}+{}, rw={:#x}+{}, heap={:#x}..{:#x}, SP={:#x}, RA={:#x}",
        s, arg_start, arguments.len(), ro_start, ro_size, rw_start, rw_size, heap_start, heap_end, registers[1], registers[0]
    );

    let mut pvm = Pvm::new(code, bitmask, jump_table, registers, flat_mem, gas);
    pvm.heap_base = heap_start;
    pvm.heap_top = heap_end;

    Some(pvm)
}

/// Memory layout offsets for direct flat-buffer writes.
pub struct DataLayout {
    pub mem_size: u32,
    pub arg_start: u32,
    pub arg_data: Vec<u8>,
    pub ro_start: u32,
    pub ro_data: Vec<u8>,
    pub rw_start: u32,
    pub rw_data: Vec<u8>,
}

/// Parsed program data without interpreter pre-decoding.
pub struct ParsedProgram {
    pub code: Vec<u8>,
    pub bitmask: Vec<u8>,
    pub jump_table: Vec<u32>,
    pub registers: [u64; crate::PVM_REGISTER_COUNT],
    pub heap_base: u32,
    pub heap_top: u32,
    /// Layout info for direct flat-buffer writes.
    pub layout: Option<DataLayout>,
}

/// Parse a program blob into raw components without building a full Pvm.
pub fn parse_program_blob(program_blob: &[u8], arguments: &[u8], _gas: Gas) -> Option<ParsedProgram> {
    let blob = skip_metadata(program_blob);

    if blob.len() < 15 {
        return None;
    }

    let mut offset = 0;
    let ro_size = read_le_u24(blob, &mut offset)? as u32;
    let rw_size = read_le_u24(blob, &mut offset)? as u32;
    let heap_pages = read_le_u16(blob, &mut offset)? as u32;
    let stack_size = read_le_u24(blob, &mut offset)? as u32;

    if offset + ro_size as usize > blob.len() { return None; }
    let ro_data = &blob[offset..offset + ro_size as usize];
    offset += ro_size as usize;

    if offset + rw_size as usize > blob.len() { return None; }
    let rw_data = &blob[offset..offset + rw_size as usize];
    offset += rw_size as usize;

    let code_len = read_le_u32(blob, &mut offset)? as usize;
    if offset + code_len > blob.len() { return None; }
    let program_data = &blob[offset..offset + code_len];
    let (code, bitmask, jump_table) = deblob(program_data)?;

    if !validate_basic_blocks(&code, &bitmask, &jump_table) {
        return None;
    }

    let page_round = |x: u32| -> u32 {
        ((x + PVM_PAGE_SIZE - 1) / PVM_PAGE_SIZE) * PVM_PAGE_SIZE
    };

    let s = page_round(stack_size);
    let arg_start = s;
    let ro_start = arg_start + page_round(arguments.len() as u32);
    let rw_start = ro_start + page_round(ro_size);
    let heap_start = rw_start + page_round(rw_size);
    let heap_end = heap_start + heap_pages * PVM_PAGE_SIZE;
    let mem_size = heap_end;

    if (mem_size as u64) > (1u64 << 32) { return None; }

    let layout = DataLayout {
        mem_size,
        arg_start,
        arg_data: arguments.to_vec(),
        ro_start,
        ro_data: ro_data.to_vec(),
        rw_start,
        rw_data: rw_data.to_vec(),
    };

    let mut registers = [0u64; crate::PVM_REGISTER_COUNT];
    let halt_addr: u64 = (1u64 << 32) - (1u64 << 16); // 0xFFFF0000
    registers[0] = halt_addr;                 // φ[0]: RA
    registers[1] = s as u64;                  // φ[1]: SP
    registers[7] = arg_start as u64;
    registers[8] = arguments.len() as u64;

    Some(ParsedProgram {
        code, bitmask, jump_table, registers,
        heap_base: heap_start,
        heap_top: heap_end,
        layout: Some(layout),
    })
}

/// JAR v0.8.0 basic block prevalidation.
/// 1. Last instruction must be a terminator
/// 2. All jump table entries must point to valid instruction boundaries
fn validate_basic_blocks(code: &[u8], bitmask: &[u8], jump_table: &[u32]) -> bool {
    if code.is_empty() {
        return false;
    }
    // Find the last instruction start (scan backwards through bitmask)
    let mut last = code.len() - 1;
    while last > 0 && (last >= bitmask.len() || bitmask[last] != 1) {
        last -= 1;
    }
    // Check it's a valid terminator
    if last >= bitmask.len() || bitmask[last] != 1 {
        return false;
    }
    match Opcode::from_byte(code[last]) {
        Some(op) if op.is_terminator() => {}
        _ => return false,
    }
    // All jump table entries must point to instruction boundaries
    for &target in jump_table {
        let t = target as usize;
        if t != 0 && (t >= bitmask.len() || bitmask[t] != 1) {
            return false;
        }
    }
    true
}


/// Decode a variable-length natural number (JAM codec format).
/// Returns (value, bytes_consumed) or None.
fn decode_natural(data: &[u8], offset: usize) -> Option<(usize, usize)> {
    if offset >= data.len() {
        return None;
    }

    let first = data[offset];
    if first < 128 {
        // Single byte
        Some((first as usize, 1))
    } else if first < 192 {
        // Two bytes
        if offset + 2 > data.len() {
            return None;
        }
        let val = ((first as usize & 0x3F) << 8) | data[offset + 1] as usize;
        Some((val, 2))
    } else if first < 224 {
        // Three bytes: remaining 2 bytes in LE order
        if offset + 3 > data.len() {
            return None;
        }
        let val = ((first as usize & 0x1F) << 16)
            | ((data[offset + 2] as usize) << 8)
            | data[offset + 1] as usize;
        Some((val, 3))
    } else {
        // Four bytes: remaining 3 bytes in LE order
        if offset + 4 > data.len() {
            return None;
        }
        let val = ((first as usize & 0x0F) << 24)
            | ((data[offset + 3] as usize) << 16)
            | ((data[offset + 2] as usize) << 8)
            | data[offset + 1] as usize;
        Some((val, 4))
    }
}



fn read_le_u16(data: &[u8], offset: &mut usize) -> Option<u16> {
    if *offset + 2 > data.len() {
        return None;
    }
    let val = u16::from_le_bytes([data[*offset], data[*offset + 1]]);
    *offset += 2;
    Some(val)
}

/// Skip metadata prefix from polkavm-linker output.
/// Detects metadata by checking if the first 3 bytes as E3(ro_size) would be too large.
fn skip_metadata(blob: &[u8]) -> &[u8] {
    if blob.len() < 14 {
        return blob;
    }
    // Try parsing as standard program header (first 3 bytes = E3(ro_size) LE)
    let ro_size = blob[0] as u32 | ((blob[1] as u32) << 8) | ((blob[2] as u32) << 16);
    if (ro_size as usize) + 14 <= blob.len() {
        // Looks like a valid standard program header
        return blob;
    }
    // Assume metadata: varint(length) prefix + metadata bytes
    if let Some((meta_len, consumed)) = decode_natural(blob, 0) {
        let skip = consumed + meta_len;
        if skip < blob.len() {
            return &blob[skip..];
        }
    }
    blob
}

fn read_le_u32(data: &[u8], offset: &mut usize) -> Option<u32> {
    if *offset + 4 > data.len() {
        return None;
    }
    let val = u32::from_le_bytes([
        data[*offset],
        data[*offset + 1],
        data[*offset + 2],
        data[*offset + 3],
    ]);
    *offset += 4;
    Some(val)
}

fn read_le_u24(data: &[u8], offset: &mut usize) -> Option<u32> {
    if *offset + 3 > data.len() {
        return None;
    }
    let val = data[*offset] as u32 | ((data[*offset + 1] as u32) << 8) | ((data[*offset + 2] as u32) << 16);
    *offset += 3;
    Some(val)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_deblob_simple() {
        // Build a simple blob: |j|=0, z=1, |c|=3, code=[0,1,0], bitmask packed
        let mut blob = Vec::new();
        blob.push(0); // |j| = 0 (single byte natural)
        blob.push(1); // z = 1
        blob.push(3); // |c| = 3
        // no jump table entries
        blob.extend_from_slice(&[0, 1, 0]); // code: trap, fallthrough, trap
        blob.push(0x07); // packed bitmask: bits 0,1,2 set = 0b00000111
        let (code, bitmask, jt) = deblob(&blob).unwrap();
        assert_eq!(code, vec![0, 1, 0]);
        assert_eq!(bitmask, vec![1, 1, 1]);
        assert!(jt.is_empty());
    }

    #[test]
    fn test_deblob_with_jump_table() {
        let mut blob = Vec::new();
        blob.push(2); // |j| = 2
        blob.push(2); // z = 2 (2-byte entries)
        blob.push(2); // |c| = 2
        blob.extend_from_slice(&[0, 0]); // j[0] = 0
        blob.extend_from_slice(&[1, 0]); // j[1] = 1
        blob.extend_from_slice(&[0, 1]); // code: trap, fallthrough
        blob.push(0x03); // packed bitmask: bits 0,1 set = 0b00000011
        let (code, bitmask, jt) = deblob(&blob).unwrap();
        assert_eq!(code, vec![0, 1]);
        assert_eq!(bitmask, vec![1, 1]);
        assert_eq!(jt, vec![0, 1]);
    }

    #[test]
    fn test_invalid_blob() {
        assert!(deblob(&[]).is_none());
        assert!(deblob(&[0]).is_none()); // missing z
    }
}
