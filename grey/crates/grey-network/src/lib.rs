//! P2P networking for JAM block propagation using libp2p gossipsub.
//!
//! This crate handles:
//! - Block announcement and propagation via gossipsub
//! - Peer discovery and connection management
//! - GRANDPA-like finality vote propagation

pub mod safe_tip;
pub mod service;

/// Re-export signing contexts from grey-types (single source of truth).
pub use grey_types::signing_contexts;
