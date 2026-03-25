//! Basic block trace + memory access log for verifiable execution.
//!
//! Captures PVM state at basic block boundaries and records every
//! memory access for the grand product permutation proof.
//!
//! # Usage
//!
//! ```ignore
//! let mut pvm = Pvm::new(...);
//! pvm.block_tracing_enabled = true;
//! let (exit, gas_used) = pvm.run();
//! let trace = pvm.take_block_trace();
//! // trace.blocks: block boundary states (for Merkle commitment)
//! // trace.memory_accesses: access log (for Ligerito polynomial)
//! ```

use alloc::vec::Vec;
use crate::PVM_REGISTER_COUNT;

/// State snapshot at a point in PVM execution.
#[derive(Clone, Debug)]
pub struct PvmSnapshot {
    /// Program counter (ı).
    pub pc: u32,
    /// Register file (13 registers).
    pub registers: [u64; PVM_REGISTER_COUNT],
    /// Remaining gas (ϱ).
    pub gas: u64,
}

/// A single basic block execution record.
///
/// Given `entry` state AND memory read values from the access log,
/// the `exit` state is deterministic. Note: refinement CAN have host
/// calls (GP §14.3), so determinism requires memory values as input.
#[derive(Clone, Debug)]
pub struct BlockStep {
    /// PVM state at block entry.
    pub entry: PvmSnapshot,
    /// PVM state at block exit (after the terminator executes).
    pub exit: PvmSnapshot,
    /// Number of instructions in this block.
    pub instruction_count: u32,
    /// Range of memory access seq numbers belonging to this block.
    /// `access_seq_start..access_seq_end` indexes into the memory
    /// access log. Enables ELVES auditors to extract the subset of
    /// accesses for a specific block without re-executing from block 0.
    pub access_seq_start: u32,
    pub access_seq_end: u32,
}

impl BlockStep {
    /// Gas consumed by this block (derived from entry/exit).
    pub fn gas_cost(&self) -> u64 {
        self.entry.gas.saturating_sub(self.exit.gas)
    }
}

/// Access width in bytes. Matches PVM load/store instruction widths.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum AccessWidth {
    Byte1 = 1,
    Byte2 = 2,
    Byte4 = 4,
    Byte8 = 8,
}

impl AccessWidth {
    /// Convert from raw byte count. Returns None for invalid widths.
    pub fn from_bytes(n: u8) -> Option<Self> {
        match n {
            1 => Some(Self::Byte1),
            2 => Some(Self::Byte2),
            4 => Some(Self::Byte4),
            8 => Some(Self::Byte8),
            _ => None,
        }
    }

    /// Raw byte count (1, 2, 4, or 8).
    pub fn as_u32(self) -> u32 {
        self as u32
    }
}

/// A single memory access during PVM execution.
/// Recorded for the grand product permutation proof.
#[derive(Clone, Debug)]
pub struct MemoryAccess {
    /// Memory address accessed.
    pub address: u32,
    /// Value read or written (up to 8 bytes, LE).
    pub value: u64,
    /// Monotonic sequence number (execution order, 0-based).
    /// The polynomial constrains seq_i == i for uniqueness.
    pub seq: u32,
    /// Width of access (1, 2, 4, or 8 bytes).
    pub width: AccessWidth,
    /// True if store, false if load.
    pub is_write: bool,
}

impl MemoryAccess {
    /// Encode this access as 6 GF(2^32) elements for the polynomial.
    /// Layout: [addr, value_lo, value_hi, seq, width, flags]
    /// This is the canonical encoding — both prover and verifier use it.
    pub fn to_field_elements(&self) -> [u32; 6] {
        [
            self.address,
            self.value as u32,         // value_lo: low 32 bits
            (self.value >> 32) as u32, // value_hi: high 32 bits
            self.seq,
            self.width.as_u32(),       // 1, 2, 4, or 8
            if self.is_write { 1 } else { 0 },
        ]
    }
}

/// Complete trace for a single work report execution.
#[derive(Clone, Debug)]
pub struct BlockTrace {
    /// Basic block records, in execution order.
    /// For Merkle commitment (trace_root). NOT in the polynomial.
    pub blocks: Vec<BlockStep>,
    /// Memory access log, in execution order.
    /// For the Ligerito grand product polynomial.
    pub memory_accesses: Vec<MemoryAccess>,
    /// Total instructions executed across all blocks.
    pub total_instructions: u64,
    /// Next memory access sequence number (monotonic counter).
    next_seq: u32,
}

impl Default for BlockTrace {
    fn default() -> Self {
        Self::new()
    }
}

impl BlockTrace {
    /// Create an empty trace.
    pub fn new() -> Self {
        Self {
            blocks: Vec::new(),
            memory_accesses: Vec::new(),
            total_instructions: 0,
            next_seq: 0,
        }
    }

    /// Record a memory access. Called by the VM during execution.
    ///
    /// Returns false if the sequence counter would overflow (>2^32
    /// accesses). Callers should treat this as a trace abort.
    pub fn record_memory_access(
        &mut self, address: u32, value: u64, width: AccessWidth, is_write: bool,
    ) -> bool {
        if self.next_seq == u32::MAX {
            return false; // overflow: trace is full
        }
        self.memory_accesses.push(MemoryAccess {
            address,
            value,
            seq: self.next_seq,
            width,
            is_write,
        });
        self.next_seq += 1;
        true
    }

    /// Current sequence number (next access will get this seq).
    pub fn current_seq(&self) -> u32 {
        self.next_seq
    }

    /// Number of memory accesses recorded.
    pub fn num_memory_accesses(&self) -> usize {
        self.memory_accesses.len()
    }

    /// Number of basic blocks traced.
    pub fn num_blocks(&self) -> usize {
        self.blocks.len()
    }

    /// Polynomial size in GF(2^32) elements for the grand product.
    ///
    /// The polynomial contains ONLY memory access logs (block
    /// boundaries are in the Merkle tree, not the polynomial).
    ///
    /// Per access: addr(1) + value_lo(1) + value_hi(1) + seq(1) + width(1) + flags(1) = 6
    /// Two copies (original + sorted) = 12 elements per access.
    pub fn polynomial_elements(&self) -> usize {
        self.memory_accesses.len() * 12
    }

    /// Merkle tree leaf count (one leaf per basic block boundary).
    pub fn merkle_leaf_count(&self) -> usize {
        self.blocks.len()
    }

    /// Log₂ of the polynomial size for the grand product proof.
    /// Minimum 14 (Ligerito needs logSize-6 >= 4+1), maximum 24.
    pub fn log_size(&self) -> u32 {
        let n = self.polynomial_elements().next_power_of_two();
        // next_power_of_two(0) = 1, trailing_zeros(1) = 0
        n.trailing_zeros().max(14).min(24)
    }

    /// Verify internal consistency: each block's exit matches the
    /// next block's entry (register-level continuity).
    pub fn verify_continuity(&self) -> bool {
        for i in 1..self.blocks.len() {
            let prev_exit = &self.blocks[i - 1].exit;
            let curr_entry = &self.blocks[i].entry;
            if prev_exit.pc != curr_entry.pc
                || prev_exit.registers != curr_entry.registers
                || prev_exit.gas != curr_entry.gas
            {
                return false;
            }
        }
        true
    }

    /// Get the initial state (first block entry).
    pub fn initial_state(&self) -> Option<&PvmSnapshot> {
        self.blocks.first().map(|b| &b.entry)
    }

    /// Get the final state (last block exit).
    pub fn final_state(&self) -> Option<&PvmSnapshot> {
        self.blocks.last().map(|b| &b.exit)
    }
}
