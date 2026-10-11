//! Independent check of the lattice solver behind ArcSolverInclusion, written from the Lean spec
//! (`stepOpen`, `roundIn`), not ported from experiments/arc_trap_k.py.
//!
//! Residue form.  P[r] is a sorted list of disjoint closed intervals in [0, 1], on the 1/N grid.  A start
//! a at residue r is kept when some NONDEGENERATE interval of moves u lies inside [a, a + l/3], each move
//! keeps its window [u, u + 2l/3] inside an arc lift [m + s, m + s + t], and c = 3u/2 + d (d = (r mod 2)/2)
//! has fract c in P[base] and P[base + 2^(k-1)], base = ((3r - r mod 2)/2 + floor c) mod 2^(k-1).
//! Rounding keeps the 1/N grid cells wholly inside that open set.  Iterate down from the full sets.
//!
//!   arc_sweep sweep KMIN KMAX BETA E0 STEP LOGN     widths i*STEP <= 3t'/2 at beta' = BETA - E0/2
//!   arc_sweep solve K S T L LOGN                    prints live residues of the greatest fixed point
//! Rationals are written p/q.

use std::cmp::Ordering;
use std::env;

#[derive(Clone, Copy, Debug)]
struct Q {
    n: i128,
    d: i128,
}

fn gcd(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

impl Q {
    fn new(n: i128, d: i128) -> Q {
        let g = gcd(n, d).max(1);
        let s = if d < 0 { -1 } else { 1 };
        Q { n: s * n / g, d: s * d / g }
    }
    fn to_f64(self) -> f64 {
        self.n as f64 / self.d as f64
    }
    fn int(n: i128) -> Q {
        Q { n, d: 1 }
    }
    fn parse(s: &str) -> Q {
        match s.split_once('/') {
            Some((a, b)) => Q::new(a.trim().parse().unwrap(), b.trim().parse().unwrap()),
            None => Q::int(s.trim().parse().unwrap()),
        }
    }
    fn add(self, o: Q) -> Q {
        Q::new(self.n * o.d + o.n * self.d, self.d * o.d)
    }
    fn sub(self, o: Q) -> Q {
        Q::new(self.n * o.d - o.n * self.d, self.d * o.d)
    }
    fn mul(self, o: Q) -> Q {
        Q::new(self.n * o.n, self.d * o.d)
    }
    fn div(self, o: Q) -> Q {
        Q::new(self.n * o.d, self.d * o.n)
    }
    fn floor(self) -> i128 {
        self.n.div_euclid(self.d)
    }
    fn ceil(self) -> i128 {
        -((-self.n).div_euclid(self.d))
    }
}

impl PartialEq for Q {
    fn eq(&self, o: &Q) -> bool {
        self.n * o.d == o.n * self.d
    }
}
impl PartialOrd for Q {
    fn partial_cmp(&self, o: &Q) -> Option<Ordering> {
        (self.n * o.d).partial_cmp(&(o.n * self.d))
    }
}

type Ivs = Vec<(Q, Q)>;

/// Closed intervals, merged; degenerate ones dropped (they carry no open move set).
fn norm(mut v: Ivs) -> Ivs {
    v.retain(|(a, b)| a < b);
    v.sort_by(|x, y| x.0.partial_cmp(&y.0).unwrap());
    let mut out: Ivs = Vec::new();
    for (a, b) in v {
        if let Some(last) = out.last_mut() {
            if a <= last.1 {
                if b > last.1 {
                    last.1 = b;
                }
                continue;
            }
        }
        out.push((a, b));
    }
    out
}

fn inter(a: &Ivs, b: &Ivs) -> Ivs {
    let mut out = Vec::new();
    for &(x0, x1) in a {
        for &(y0, y1) in b {
            let lo = if x0 > y0 { x0 } else { y0 };
            let hi = if x1 < y1 { x1 } else { y1 };
            if lo < hi {
                out.push((lo, hi));
            }
        }
    }
    norm(out)
}

struct Game {
    k: u32,
    s: Q,
    t: Q,
    l: Q,
    n_grid: i128,
}

fn nocarry() -> bool {
    env::var("ARC_NOCARRY").map(|v| v == "1").unwrap_or(false)
}

impl Game {
    /// Open set of starts with an open move interval into both lifts (residue r), as closed-interval
    /// closures: a in (g0 - l/3, g1) for each good-move component (g0, g1).
    fn step_open(&self, p: &Vec<Ivs>, r: usize) -> Ivs {
        let half = 1usize << (self.k - 1);
        let three_halves = Q::new(3, 2);
        let d = if r % 2 == 1 { Q::new(1, 2) } else { Q::int(0) };
        let w = Q::new(2, 3).mul(self.l);
        let l3 = self.l.div(Q::int(3));
        // arc lifts for u: [m + s, m + s + t - w]
        let mut arc: Ivs = Vec::new();
        if self.t > w {
            for m in -2..6 {
                let lo = Q::int(m).add(self.s);
                arc.push((lo, lo.add(self.t).sub(w)));
            }
        }
        let arc = norm(arc);
        let mut good: Ivs = Vec::new();
        for j in 0..6i128 {
            // ARC_NOCARRY=1: the pure delay game (the residue is the next k parities, shifted out one per
            // move; the constructor's floor j adds no carry).  A model, not the k-memory game.
            let b = if nocarry() { (r >> 1) % half } else { ((3 * r - r % 2) / 2 + j as usize) % half };
            let tgt = inter(&p[b], &p[b + half]);
            // c in [j + lo, j + hi]  <=>  u in [(j + lo - d)/(3/2), (j + hi - d)/(3/2)]
            let us: Ivs = tgt
                .iter()
                .map(|&(lo, hi)| {
                    (
                        Q::int(j).add(lo).sub(d).div(three_halves),
                        Q::int(j).add(hi).sub(d).div(three_halves),
                    )
                })
                .collect();
            for iv in inter(&norm(us), &arc) {
                good.push(iv);
            }
        }
        // starts: a in (g0 - l/3, g1) for each nondegenerate good piece, clipped to [0, 1]
        let starts: Ivs = good
            .iter()
            .filter(|(g0, g1)| g0 < g1)
            .map(|&(g0, g1)| {
                let lo = g0.sub(l3);
                (if lo > Q::int(0) { lo } else { Q::int(0) }, if g1 < Q::int(1) { g1 } else { Q::int(1) })
            })
            .collect();
        norm(starts)
    }

    /// Closed grid cells [i/N, (i+1)/N] for the half-open cells [i/N, (i+1)/N) inside each open start
    /// interval (lo, hi): cells start strictly after lo (except at the clip point 0) and may end at hi.
    fn round_in(&self, v: &Ivs) -> Ivs {
        let nq = Q::int(self.n_grid);
        let mut out = Vec::new();
        for &(lo, hi) in v {
            let x = lo.mul(nq);
            let y = hi.mul(nq);
            // the start set is open at both ends: cells start strictly after lo (unless lo == 0, the clip
            // point) and may END AT hi (an Ico cell [i/N, (i+1)/N) with (i+1)/N <= hi lies inside (lo, hi)).
            // 2026-10-10 fix: was ceil(hi N) - 1, which dropped that last cell (unsafe for emptiness).
            let i0 = if lo == Q::int(0) { 0 } else { x.floor() + 1 };
            let i1 = y.floor();
            if i0 < i1 {
                out.push((Q::new(i0, self.n_grid), Q::new(i1, self.n_grid)));
            }
        }
        norm(out)
    }

    fn solve(&self, max_iter: usize) -> (Vec<Ivs>, bool) {
        let (p, fx, _) = self.solve_n(max_iter);
        (p, fx)
    }

    /// As `solve`, also returning the number of descent steps taken (for an emptying descent, a proxy
    /// for the adversary's kill depth).
    fn solve_n(&self, max_iter: usize) -> (Vec<Ivs>, bool, usize) {
        let n = 1usize << self.k;
        let mut p: Vec<Ivs> = vec![vec![(Q::int(0), Q::int(1))]; n];
        for it in 0..max_iter {
            let mut next = Vec::with_capacity(n);
            for r in 0..n {
                let acc = self.round_in(&self.step_open(&p, r));
                next.push(inter(&p[r], &acc));
            }
            let same = next.iter().zip(p.iter()).all(|(a, b)| {
                a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.0 == y.0 && x.1 == y.1)
            });
            p = next;
            // ARC_TRACE=1: print every residue's survivor set after each descent step
            if env::var("ARC_TRACE").map(|v| v == "1").unwrap_or(false) {
                for (r, iv) in p.iter().enumerate() {
                    let v: Vec<String> = iv.iter().map(|(x, y)| format!("[{:.5},{:.5}]", x.to_f64(), y.to_f64())).collect();
                    println!("T {} {} {}", it + 1, r, v.join(" "));
                }
            }
            if same || p.iter().all(|x| x.is_empty()) {
                return (p, true, it + 1);
            }
        }
        (p, false, max_iter)
    }
}


/// k-memory component game (`ArcDelayGame.KComponentStrategy`): windows of positions mod 2^k, the
/// constructor keeps a component inside an arc lift, the adversary picks the top bit of the 3/2-image.
/// Memo per window: survives up to `tu` moves, dies by `ff` (survival is monotone in the depth).
struct Comp {
    s: Q,
    e: Q,
    mh: Q,
    memo: std::collections::HashMap<(i128, i128, i128, i128), (usize, usize)>,
}

impl Comp {
    fn surv(&mut self, x: Q, y: Q, d: usize) -> bool {
        if d == 0 {
            return true;
        }
        let key = (x.n, x.d, y.n, y.d);
        let (tu, ff) = *self.memo.get(&key).unwrap_or(&(0, usize::MAX));
        if d <= tu {
            return true;
        }
        if d >= ff {
            return false;
        }
        let mut ok = false;
        for j in (x.floor() - 1)..=y.floor() {
            let lo = Q::int(j).add(self.s);
            let hi = Q::int(j).add(self.e);
            let a = if x > lo { x } else { lo };
            let b = if y < hi { y } else { hi };
            if a < b {
                let h = Q::new(3, 2);
                let (na, nb) = (h.mul(a), h.mul(b));
                let sh = Q::int(na.div(self.mh).floor()).mul(self.mh);
                let (ca, cb) = (na.sub(sh), nb.sub(sh));
                if self.surv(ca, cb, d - 1) && self.surv(ca.add(self.mh), cb.add(self.mh), d - 1) {
                    ok = true;
                    break;
                }
            }
        }
        let ent = self.memo.entry(key).or_insert((0, usize::MAX));
        if ok {
            ent.0 = ent.0.max(d);
        } else {
            ent.1 = ent.1.min(d);
        }
        ok
    }

    /// children pairs of every constructor move from (x, y)
    fn moves(&self, x: Q, y: Q) -> Vec<((Q, Q), (Q, Q))> {
        let mut out = Vec::new();
        for j in (x.floor() - 1)..=y.floor() {
            let lo = Q::int(j).add(self.s);
            let hi = Q::int(j).add(self.e);
            let a = if x > lo { x } else { lo };
            let b = if y < hi { y } else { hi };
            if a < b {
                let h = Q::new(3, 2);
                let (na, nb) = (h.mul(a), h.mul(b));
                let sh = Q::int(na.div(self.mh).floor()).mul(self.mh);
                let (ca, cb) = (na.sub(sh), nb.sub(sh));
                out.push(((ca, cb), (ca.add(self.mh), cb.add(self.mh))));
            }
        }
        out
    }

    /// first depth at which (x, y) dies, or None within cap
    fn death(&mut self, x: Q, y: Q, cap: usize) -> Option<usize> {
        (1..=cap).find(|&d| !self.surv(x, y, d))
    }
}

fn main() {
    let a: Vec<String> = env::args().collect();
    match a.get(1).map(|s| s.as_str()) {
        Some("solve") => {
            let g = Game {
                k: a[2].parse().unwrap(),
                s: Q::parse(&a[3]),
                t: Q::parse(&a[4]),
                l: Q::parse(&a[5]),
                n_grid: 1i128 << a[6].parse::<u32>().unwrap(),
            };
            let (p, fx, it) = g.solve_n(5000);
            let live: Vec<usize> = (0..p.len()).filter(|&r| !p[r].is_empty()).collect();
            println!("converged {} live {:?} iters {}", fx, live, it);
            // ARC_DUMP=1: print each residue's interval list (exact rationals), for witness extraction
            if env::var("ARC_DUMP").map(|v| v == "1").unwrap_or(false) {
                for (r, iv) in p.iter().enumerate() {
                    let v: Vec<String> = iv.iter().map(|(x, y)| format!("[{}/{},{}/{}]", x.n, x.d, y.n, y.d)).collect();
                    println!("P {} {}", r, v.join(" "));
                }
            }
        }
        Some("sweep") => {
            let (kmin, kmax): (u32, u32) = (a[2].parse().unwrap(), a[3].parse().unwrap());
            let beta = Q::parse(&a[4]);
            let e0 = Q::parse(&a[5]);
            let step = Q::parse(&a[6]);
            let n_grid = 1i128 << a[7].parse::<u32>().unwrap();
            let bp = beta.sub(e0.div(Q::int(2)));
            let tp = Q::int(1).sub(Q::int(2).mul(bp));
            let mut top = Q::new(3, 2).mul(tp);
            // optional LMIN LMAX: restrict to widths in [LMIN, LMAX] (exploration, not the certified sweep)
            let lmin = a.get(8).map(|x| Q::parse(x));
            if let Some(x) = a.get(9).map(|x| Q::parse(x)) {
                if x < top { top = x; }
            }
            for k in kmin..=kmax {
                let mut bad: Vec<String> = Vec::new();
                let mut count = 0;
                let mut l = step;
                if let Some(m) = lmin {
                    while l < m { l = l.add(step); }
                }
                while l <= top {
                    let g = Game { k, s: bp, t: tp, l, n_grid };
                    let (p, fx) = g.solve(5000);
                    if !fx || p.iter().any(|x| !x.is_empty()) {
                        bad.push(format!("{}/{}", l.n, l.d));
                    }
                    count += 1;
                    l = l.add(step);
                }
                println!("k {} widths {} nonempty {:?}", k, count, bad);
                std::io::Write::flush(&mut std::io::stdout()).unwrap();
            }
        }
        Some("round") => {
            // round LOGN LO HI: the rounding of one open start interval, for regression tests
            let g = Game { k: 1, s: Q::int(0), t: Q::int(1), l: Q::int(1), n_grid: 1i128 << a[2].parse::<u32>().unwrap() };
            let out = g.round_in(&vec![(Q::parse(&a[3]), Q::parse(&a[4]))]);
            let v: Vec<String> = out.iter().map(|(x, y)| format!("({}/{},{}/{})", x.n, x.d, y.n, y.d)).collect();
            println!("{}", v.join(" "));
        }
        Some("component") => {
            // component K BETA MAXD: first depth at which every start residue of the k-memory
            // component game dies (exact rationals; i128 overflow panics, see Cargo.toml)
            let k: u32 = a[2].parse().unwrap();
            let beta = Q::parse(&a[3]);
            let maxd: usize = a[4].parse().unwrap();
            let mut c = Comp { s: beta, e: Q::int(1).sub(beta), mh: Q::int(1i128 << (k - 1)), memo: Default::default() };
            let mut dead = None;
            for dd in 1..=maxd {
                let any = (0..(1i128 << k)).any(|r| c.surv(Q::int(r).add(c.s), Q::int(r).add(c.e), dd));
                if !any {
                    dead = Some(dd);
                    break;
                }
            }
            println!("k {} beta {}/{} dead {:?} memo {}", k, beta.n, beta.d, dead, c.memo.len());
        }
        Some("effmem") => {
            // effmem K BETA: along the adversary's kill tree (all constructor moves, the child with the smaller
            // death depth), the effective memory of each state s: least m with D_m(s mod 2^m) = D_k(s).
            // Prints, per tree level (moves from a start), the histogram of effective memory.
            let k: u32 = a[2].parse().unwrap();
            let beta = Q::parse(&a[3]);
            let mk = |k: u32| Comp { s: beta, e: Q::int(1).sub(beta), mh: Q::int(1i128 << (k - 1)), memo: Default::default() };
            let mut g: Vec<Comp> = (1..=k).map(mk).collect();
            let starts: Vec<(Q, Q)> = (0..(1i128 << k)).map(|r| (Q::int(r).add(beta), Q::int(r).add(Q::int(1).sub(beta)))).collect();
            let key = |q: &(Q, Q)| (q.0.n, q.0.d, q.1.n, q.1.d);
            let mut seen: std::collections::HashSet<(i128, i128, i128, i128)> = starts.iter().map(key).collect();
            let mut fr = starts.clone();
            let mut level = 0;
            while !fr.is_empty() {
                let mut hist = vec![0usize; k as usize + 1];
                let mut nf = Vec::new();
                for &(x, y) in &fr {
                    let dk = g[k as usize - 1].death(x, y, 300);
                    let mut eff = k;
                    for m in 1..k {
                        let mm = Q::int(1i128 << m);
                        let sh = Q::int(x.div(mm).floor()).mul(mm);
                        if g[m as usize - 1].death(x.sub(sh), y.sub(sh), 300) == dk { eff = m; break; }
                    }
                    hist[eff as usize] += 1;
                    let c = &mut g[k as usize - 1];
                    for (c0, c1) in c.moves(x, y) {
                        let (d0, d1) = (c.death(c0.0, c0.1, 300), c.death(c1.0, c1.1, 300));
                        let ch = if d1 < d0 { c1 } else { c0 };
                        if seen.insert(key(&ch)) { nf.push(ch); }
                    }
                }
                println!("level {} states {} effmem(1..k) {:?}", level, fr.len(), &hist[1..]);
                fr = nf;
                level += 1;
            }
        }
        Some("projdiff") => {
            // projdiff K BETA: over every state reachable from the starts within the start death depth,
            // histogram of D_k(s) - D_{k-1}(s mod 2^(k-1)) (does one bit of memory cost a bounded delay?)
            let k: u32 = a[2].parse().unwrap();
            let beta = Q::parse(&a[3]);
            let mk = |k: u32| Comp { s: beta, e: Q::int(1).sub(beta), mh: Q::int(1i128 << (k - 1)), memo: Default::default() };
            let (mut c, mut p) = (mk(k), mk(k - 1));
            let starts: Vec<(Q, Q)> = (0..(1i128 << k)).map(|r| (Q::int(r).add(c.s), Q::int(r).add(c.e))).collect();
            let d0 = starts.iter().map(|&(x, y)| c.death(x, y, 200).unwrap()).max().unwrap();
            let key = |q: &(Q, Q)| (q.0.n, q.0.d, q.1.n, q.1.d);
            let mut seen: std::collections::HashSet<(i128, i128, i128, i128)> = starts.iter().map(key).collect();
            let kt = env::var("ARC_KILLTREE").map(|v| v == "1").unwrap_or(false);
            let mut all = starts.clone();
            let mut fr = starts.clone();
            for _ in 0..d0 {
                let mut nf = Vec::new();
                for &(x, y) in &fr {
                    for (c0, c1) in c.moves(x, y) {
                        // ARC_KILLTREE=1: only the adversary's optimal child (smaller death depth, ties to c0)
                        let kids = if kt {
                            let (d0, d1) = (c.death(c0.0, c0.1, 200), c.death(c1.0, c1.1, 200));
                            vec![if d1 < d0 { c1 } else { c0 }]
                        } else { vec![c0, c1] };
                        for ch in kids {
                            if seen.insert(key(&ch)) { nf.push(ch); all.push(ch); }
                        }
                    }
                }
                assert!(all.len() < 20_000_000, "reachable set over 20M states");
                fr = nf;
            }
            let m = Q::int(1i128 << (k - 1));
            let mut hist: std::collections::BTreeMap<i64, usize> = Default::default();
            let mut worst: Vec<String> = Vec::new();
            let mut wmax = i64::MIN;
            for &(x, y) in &all {
                let dk = c.death(x, y, 200).unwrap() as i64;
                let sh = Q::int(x.div(m).floor()).mul(m);
                let dp = p.death(x.sub(sh), y.sub(sh), 200).map(|v| v as i64).unwrap_or(9999);
                let df = dk - dp;
                *hist.entry(df).or_default() += 1;
                if df > wmax { wmax = df; worst.clear(); }
                if df == wmax && worst.len() < 6 {
                    worst.push(format!("[{}/{},{}/{}] Dk {} Dk-1 {}", x.n, x.d, y.n, y.d, dk, dp));
                }
            }
            println!("k {} beta {}/{} d0 {} reachable {} hist {:?}", k, beta.n, beta.d, d0, all.len(), hist);
            println!("worst {}: {}", wmax, worst.join(" ; "));
        }
        _ => {
            eprintln!("usage: arc_sweep sweep KMIN KMAX BETA E0 STEP LOGN | solve K S T L LOGN | round LOGN LO HI | component K BETA MAXD | projdiff K BETA");
            std::process::exit(2);
        }
    }
}
