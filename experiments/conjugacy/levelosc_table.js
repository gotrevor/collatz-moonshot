// Probe for the node SliceOscDecay (BeyondWordsLinear.lean); node port of levelosc_table.py
// (the box has node but no numpy).  Exact over all 2^j starts:
//   levelOsc j a m / #levelSet j a = sum_{y<3^a} |mu(y) - 3^{m-a} mu(y mod 3^m)| / card,
// for a within +-2 of j/2, all 1 <= m <= a.  Usage: node levelosc_table.js j1 j2 ...
for (const jj of process.argv.slice(2)) {
  const j = Number(jj);
  const want = []; for (let a = (j >> 1) - 2; a <= (j >> 1) + 2; a++) want.push(a);
  const mass = {}; for (const a of want) mass[a] = new Float64Array(3 ** a);
  const amin = want[0], amax = want[want.length - 1];
  for (let r = 0; r < 2 ** j; r++) {
    let x = r, a = 0;
    for (let i = 0; i < j; i++) { if (x % 2 === 1) { x = (3 * x + 1) / 2; a++; } else x = x / 2; }
    if (a >= amin && a <= amax) mass[a][x] += 1;
  }
  for (const a of want) {
    const mu = mass[a], N = 3 ** a; let cnt = 0; for (let y = 0; y < N; y++) cnt += mu[y];
    const row = [];
    for (let m = 1; m <= a; m++) {
      const M = 3 ** m, cls = new Float64Array(M);
      for (let y = 0; y < N; y++) cls[y % M] += mu[y];
      const q = 3 ** (m - a); let tot = 0;
      for (let y = 0; y < N; y++) tot += Math.abs(mu[y] - q * cls[y % M]);
      row.push((tot / cnt).toFixed(3));
    }
    console.log(`j=${j} a=${a} n=${cnt} card/3^a=${(cnt / N).toFixed(2)} ` + row.join(' '));
  }
}
