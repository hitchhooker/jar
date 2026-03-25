//! Basic block trace for execution proofs.
//!
//! Captures PVM state at basic block boundaries — entry and exit of each
//! straight-line instruction sequence. This is the "downsampled" trace:
//! 20x smaller than per-instruction traces, but equally sound because
//! basic blocks are deterministic (given entry state, exit state is unique).
//!
//! # Usage
//!
//! ```ignore
//! let mut pvm = Pvm::new(...);
//! pvm.block_tracing_enabled = true;
//! let (exit, gas_used) = pvm.run();
//! let trace = pvm.take_block_trace();
//! // trace.blocks contains entry/exit state for each basic block
//! ```

use alloc::vec::Vec;
use crate::PVM_REGISTER_COUNT;

/// State snapshot at a point in PVM execution.
#[derive(Clone, Debug)]
pub struct PvmSnapshot {
    /// Program counter.
    pub pc: u32,
    /// Register file (13 registers).
    pub registers: [u64; PVM_REGISTER_COUNT],
    /// Remaining gas.
    pub gas: u64,
}

/// A single basic block execution record.
///
/// A basic block is a straight-line sequence of instructions with no
/// branches (except at the end). Given `entry`, the `exit` state is
/// deterministic — there is exactly one possible outcome.
#[derive(Clone, Debug)]
pub struct BlockStep {
    /// Block index (sequential, 0-based).
    pub index: u32,
    /// PVM state at block entry.
    pub entry: PvmSnapshot,
    /// PVM state at block exit (after the terminator executes).
    pub exit: PvmSnapshot,
    /// Number of instructions in this block.
    pub instruction_count: u32,
    /// Gas consumed by this block (entry.gas - exit.gas).
    pub gas_cost: u64,
}

/// A single memory access during PVM execution.
/// Recorded for the grand product consistency proof.
#[derive(Clone, Debug)]
pub struct MemoryAccess {
    /// Memory address accessed.
    pub address: u32,
    /// Value read or written (up to 8 bytes, LE).
    pub value: u64,
    /// Monotonic seq (execution order). Must be strictly
    /// increasing. Used by the grand product to bind access ordering.
    pub seq: u32,
    /// Width of access in bytes (1, 2, 4, or 8).
    pub width: u8,
    /// True if store, false if load.
    pub is_write: bool,
}

/// Complete basic block trace for an execution.
///
/// Contains one `BlockStep` per basic block, in execution order.
/// For a 1M-instruction program with ~50K basic blocks, this is
/// ~5M field elements — fits in a 2^23 polynomial for BaseFold.
#[derive(Clone, Debug)]
pub struct BlockTrace {
    /// Basic block records, in execution order.
    pub blocks: Vec<BlockStep>,
    /// Memory access log, in execution order.
    /// Timestamps are strictly increasing (monotonic counter).
    pub memory_accesses: Vec<MemoryAccess>,
    /// Total instructions executed.
    pub total_instructions: u64,
    /// Next memory access seq (monotonic counter).
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
    pub fn record_memory_access(&mut self, address: u32, value: u64, width: u8, is_write: bool) {
        self.memory_accesses.push(MemoryAccess {
            address,
            value,
            seq: self.next_seq,
            width,
            is_write,
        });
        self.next_seq += 1;
    }

    /// Number of memory accesses recorded.
    pub fn num_memory_accesses(&self) -> usize {
        self.memory_accesses.len()
    }

    /// Number of basic blocks traced.
    pub fn num_blocks(&self) -> usize {
        self.blocks.len()
    }

    /// Estimated polynomial size in GF(2^32) elements for the grand
    /// product permutation proof.
    ///
    /// The polynomial contains ONLY memory access logs (not block
    /// boundaries — those go in the Merkle tree via trace_root).
    ///
    /// Per access: addr(1) + value_lo(1) + value_hi(1) + seq(1) + flags(1) = 5
    /// Two copies: original + sorted = 10 elements per access
    pub fn polynomial_elements(&self) -> usize {
        self.memory_accesses.len() * 10  // original + sorted logs
    }

    /// Estimated Merkle tree leaf count (block boundaries).
    /// Each boundary: pc(4B) + 13 regs×8B(104B) + gas(8B) = 116 bytes per leaf.
    pub fn merkle_leaf_count(&self) -> usize {
        self.blocks.len()
    }

    /// Log₂ of the polynomial size for the grand product proof.
    pub fn log_size(&self) -> u32 {
        let n = self.polynomial_elements().next_power_of_two();
        if n == 0 { 20 } else { n.trailing_zeros().max(20) }
    }

    /// Verify internal consistency: each block's exit matches the next
    /// block's entry.
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
