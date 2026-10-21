// u128 variant for j = 39..40 (3y+1 overflows u64 past j = 38).
// with the odd-count band decomposition E_{j,a} and normalized values E_{j,a}/sqrt(C(j,a)).
use std::thread;
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let j0: u32 = args[1].parse().unwrap(); let j1: u32 = args[2].parse().unwrap();
    let nth = thread::available_parallelism().map(|n| n.get()).unwrap_or(8);
    for j in j0..=j1 {
        let t0 = std::time::Instant::now();
        let total: u64 = 1u64 << j; let chunk = total / nth as u64;
        let handles: Vec<_> = (0..nth as u64).map(|t| {
            thread::spawn(move || {
                let lo = t * chunk; let hi = if t == nth as u64 - 1 { total } else { lo + chunk };
                let mut bands = vec![0i64; (j + 1) as usize];
                for r in lo..hi {
                    let mut y = r as u128; let mut a = 0u32;
                    for _ in 0..j { if y & 1 == 1 { y = (3 * y + 1) >> 1; a += 1 } else { y >>= 1 } }
                    bands[a as usize] += if y & 1 == 0 { 1 } else { -1 };
                }
                bands
            })
        }).collect();
        let mut bands = vec![0i64; (j + 1) as usize];
        for h in handles { for (i, v) in h.join().unwrap().iter().enumerate() { bands[i] += v; } }
        let e: i64 = bands.iter().sum();
        let (mut ee, mut eo) = (0i64, 0i64);
        for (a, v) in bands.iter().enumerate() { if a % 2 == 0 { ee += v } else { eo += v } }
        // normalized bands
        let mut c = 1f64; let mut norm = Vec::new(); let (mut pos, mut neg) = (0, 0);
        for a in 0..=j { if a >= 2 && a + 2 <= j { let v = bands[a as usize] as f64 / c.sqrt(); norm.push(v); if v > 0.0 { pos += 1 } else if v < 0.0 { neg += 1 } }
            c = c * (j - a) as f64 / (a + 1) as f64; }
        let mean = norm.iter().sum::<f64>() / norm.len() as f64;
        println!("j={} E={} E/2^(j/2)={:.3} E%4={} E[a even]={} E[a odd]={} bands(a=2..j-2) +{} -{} mean={:+.2} ({:.0}s, {} threads)",
            j, e, e as f64 / 2f64.powf(j as f64 / 2.0), e.rem_euclid(4), ee, eo, pos, neg, mean, t0.elapsed().as_secs_f64(), nth);
        println!("  bands: {}", bands.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(","));
        println!("  norm:  {}", norm.iter().map(|v| format!("{:+.2}", v)).collect::<Vec<_>>().join(" "));
    }
}
