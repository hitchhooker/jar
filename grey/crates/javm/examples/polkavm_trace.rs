use std::time::Instant;

fn main() {
    let path = std::env::args().nth(1).unwrap_or_else(|| {
        eprintln!("usage: polkavm_trace <blob.corevm|blob.polkavm> [gas]");
        std::process::exit(1);
    });
    let gas: u64 = std::env::args().nth(2)
        .and_then(|s| s.parse().ok())
        .unwrap_or(10_000_000);

    let blob = std::fs::read(&path).expect("cannot read blob");
    println!("Loaded {} ({} bytes), gas={}", path, blob.len(), gas);

    // Try polkavm format first, then standard GP format
    let make_pvm = |tracing: bool| -> Option<javm::Pvm> {
        let mut pvm = javm::program::initialize_from_polkavm(&blob, &[], gas)
            .or_else(|| javm::program::initialize_program(&blob, &[], gas))?;
        pvm.block_tracing_enabled = tracing;
        Some(pvm)
    };

    let Some(mut pvm) = make_pvm(false) else {
        eprintln!("Failed to parse blob (neither polkavm nor GP format)");
        return;
    };
    println!("Parsed: code={} bitmask={}", pvm.code.len(), pvm.bitmask.len());

    // Run without trace
    let start = Instant::now();
    let mut host_calls = 0u32;
    loop {
        let (exit, _) = pvm.run();
        match exit {
            javm::ExitReason::Halt => break,
            javm::ExitReason::HostCall(_) => { host_calls += 1; continue; }
            javm::ExitReason::OutOfGas => { println!("out of gas"); break; }
            javm::ExitReason::Panic => { println!("panic"); break; }
            other => { println!("exit: {:?}", other); break; }
        }
    }
    let t1 = start.elapsed();
    let gas_used = gas - pvm.gas;
    println!("NO TRACE:   {:.1}ms  gas_used={}  host_calls={}", t1.as_secs_f64()*1000.0, gas_used, host_calls);

    // Run with trace
    let mut pvm2 = make_pvm(true).unwrap();
    let start = Instant::now();
    host_calls = 0;
    loop {
        let (exit, _) = pvm2.run();
        match exit {
            javm::ExitReason::Halt => break,
            javm::ExitReason::HostCall(_) => { host_calls += 1; continue; }
            javm::ExitReason::OutOfGas => break,
            javm::ExitReason::Panic => break,
            other => { println!("exit: {:?}", other); break; }
        }
    }
    let t2 = start.elapsed();
    let trace = pvm2.take_block_trace();
    let gas_used2 = gas - pvm2.gas;
    println!("WITH TRACE: {:.1}ms  gas_used={}  blocks={}  mem_accesses={}  host_calls={}",
        t2.as_secs_f64()*1000.0, gas_used2, trace.num_blocks(), trace.num_memory_accesses(), host_calls);
    println!("OVERHEAD:   {:.2}x", t2.as_secs_f64() / t1.as_secs_f64());
}
