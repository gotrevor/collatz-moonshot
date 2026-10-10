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
            let b = ((3 * r - r % 2) / 2 + j as usize) % half;
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

    /// Grid cells [i/N, (i+1)/N] wholly inside the OPEN interior of the union (strict at both ends,
    /// except at the clip points 0 and 1 where the start set is closed by definition).
    fn round_in(&self, v: &Ivs) -> Ivs {
        let nq = Q::int(self.n_grid);
        let mut out = Vec::new();
        for &(lo, hi) in v {
            let x = lo.mul(nq);
            let y = hi.mul(nq);
            // strict interior: first cell start > lo unless lo == 0; last cell end < hi unless hi == 1
            let i0 = if lo == Q::int(0) { 0 } else { x.floor() + 1 };
            let i1 = if hi == Q::int(1) { self.n_grid } else { y.ceil() - 1 };
            if i0 < i1 {
                out.push((Q::new(i0, self.n_grid), Q::new(i1, self.n_grid)));
            }
        }
        norm(out)
    }

    fn solve(&self, max_iter: usize) -> (Vec<Ivs>, bool) {
        let n = 1usize << self.k;
        let mut p: Vec<Ivs> = vec![vec![(Q::int(0), Q::int(1))]; n];
        for _ in 0..max_iter {
            let mut next = Vec::with_capacity(n);
            for r in 0..n {
                let acc = self.round_in(&self.step_open(&p, r));
                next.push(inter(&p[r], &acc));
            }
            let same = next.iter().zip(p.iter()).all(|(a, b)| {
                a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.0 == y.0 && x.1 == y.1)
            });
            p = next;
            if same || p.iter().all(|x| x.is_empty()) {
                return (p, true);
            }
        }
        (p, false)
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
            let (p, fx) = g.solve(5000);
            let live: Vec<usize> = (0..p.len()).filter(|&r| !p[r].is_empty()).collect();
            println!("converged {} live {:?}", fx, live);
        }
        Some("sweep") => {
            let (kmin, kmax): (u32, u32) = (a[2].parse().unwrap(), a[3].parse().unwrap());
            let beta = Q::parse(&a[4]);
            let e0 = Q::parse(&a[5]);
            let step = Q::parse(&a[6]);
            let n_grid = 1i128 << a[7].parse::<u32>().unwrap();
            let bp = beta.sub(e0.div(Q::int(2)));
            let tp = Q::int(1).sub(Q::int(2).mul(bp));
            let top = Q::new(3, 2).mul(tp);
            for k in kmin..=kmax {
                let mut bad: Vec<String> = Vec::new();
                let mut count = 0;
                let mut l = step;
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
            }
        }
        _ => {
            eprintln!("usage: arc_sweep sweep KMIN KMAX BETA E0 STEP LOGN | solve K S T L LOGN");
            std::process::exit(2);
        }
    }
}
