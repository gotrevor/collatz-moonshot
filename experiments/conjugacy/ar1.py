#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# Null model for the sign persistence: b~_m = rho b~_{m-1} + eta, rho = (4/3)/sqrt2 from the mod-3 recursion.
import numpy as np
E=[2,2,6,6,14,18,34,34,30,14,38,42,114,178,282,362,354,570,790,1042,2482,4206,4254,8054,12150,13738,16890,28682,33986,56482,83458]
j=np.arange(1,32); b=np.array(E)/2**(j/2)
rho0=(4/3)/np.sqrt(2)
for lo in (10,14):
    x=b[lo-1:-1]; y=b[lo:]
    rho=(x*y).sum()/(x*x).sum(); eta=y-rho0*x
    print(f"fit from j>={lo}: rho_hat(through origin)={rho:.3f}  recursion rho0={rho0:.3f}; innovations eta=b_m-rho0*b_(m-1): mean={eta.mean():+.3f} sd={eta.std():.3f}")
# Expected zero-crossing rate of a stationary Gaussian AR(1): arccos(rho)/pi per step
print(f"AR(1) rho0: crossings per level = {np.arccos(rho0)/np.pi:.3f}; stationary sd = sd_eta/sqrt(1-rho0^2) = sd_eta*{1/np.sqrt(1-rho0**2):.2f}")
# Simulate: start at the observed b_9, run 22 steps with mean-zero innovations of the fitted sd; P(all positive)? and P(mean of run >= observed)?
rng=np.random.default_rng(1); eta_sd=(b[10:]-rho0*b[9:-1]).std(); N=200000
start=b[8]; obs=b[9:]; n=len(obs)
sims=np.empty((N,n)); x=np.full(N,start)
for t in range(n): x=rho0*x+eta_sd*rng.standard_normal(N); sims[:,t]=x
print(f"null (zero-mean innovations, sd={eta_sd:.3f}, start b_9={start:.2f}): P(all {n} values j=10..31 positive)={(sims>0).all(1).mean():.3f}; P(run mean >= observed {obs.mean():.2f})={(sims.mean(1)>=obs.mean()).mean():.4f}")
# Alternative null: innovations with the observed mean (a drift) -> what drift is needed?
print(f"observed innovation mean = {(b[10:]-rho0*b[9:-1]).mean():+.3f}  (a positive drift of this size = stationary mean {((b[10:]-rho0*b[9:-1]).mean())/(1-rho0):.2f})")
