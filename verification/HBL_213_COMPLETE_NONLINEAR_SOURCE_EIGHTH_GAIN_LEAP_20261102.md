# HBL 2.13 — one-orbit complete Hartree nonlinear source: shortest positive-order proof

**Status (2026-11-02 US/Pacific): analytical deduction, not strict Lean acceptance.** This is a replacement *analysis lemma candidate*, not a claim that the original finite-profile theorem or type-II blowup rate theorem has been proved. Formal revised manuscript stays **11/13** until the actual complete revised environment and its PDE-closure consumers are audited.

## Same-equation physical variables

For a genuine regular radial Hartree slice `z(t,·)` and the true critical length `0<ell<=1`, use

```
m(t) = radialPhysicalQuarticMoment(z(t)),
c(t,ell) = kappa_H * ell * m(t),
V(r) = monopolePerturbedRadialProfile(monopoleQuadraticRadius(c),c,r),
Z(r) = sqrt(ell) * z(t,ell*r),
C(u) = |u|^2 u,
P_V = I[|V|^4], P_Z = I[|Z|^4],
P_mix = I[|V+Z|^4-|V|^4-|Z|^4].
```

Here `I` is the ORIGINAL normalized three-dimensional inverse-square radial logarithmic Riesz convolution, not a local proxy, a cut-off polynomial or an independently defined kernel. Pointwise

```
S = P_mix*C(V+Z)
  + P_Z*(C(V+Z)-C(Z))
  + P_V*(C(V+Z)-C(V)).
```

This is the same genuine nonlinear interaction as in the four-term exact Hartree split (with `P_mix*C(V)` separated from its changed cubic); both real H+/H- sources are projections of the SAME complex source.

## Native physical source bounds

Let `d=1+r >=1`, `q=1+ell*r >=1`, so `q >= ell*d`. Under bounded radial high-regularity amplitude/Strauss and the true moment window, the existing strict Lean source estimates plus the scalar Riesz-row bridge in progress give nonnegative constants `D,E,F,G,H,J`, independent of `r,ell`, such that

```
|V| <= D/d,
|Z| <= E*sqrt(ell)/q,
|P_mix| <= F*sqrt(ell)/d,
|P_Z| <= G*ell,
|P_V| <= H/d^2 + J*ell.
```

The last line uses the exact core ground-state identity `I[W^4]=3 W^2`, `W^2=(1+r^2)^(-1)<=2/d^2` so `H=6`, and the derived physical moment Taylor error `O(ell)`. The third line relies critically on **the unaccepted scalar Riesz-decay bridge** (PR #16) and the separately strict accepted true positive-kernel comparison (PR #15). Do not silently treat either pending source as already fully accepted.

The original complex cubic satisfies exactly

```
|C(V+Z)| <= (|V|+|Z|)^3,
|C(V+Z)-C(Z)| <= |V|*(|V|+2|Z|)^2,
|C(V+Z)-C(V)| <= |Z|*(2|V|+|Z|)^2.
```

Thus

```
|S| <= F*sqrt(ell)/d*(D/d + E*sqrt(ell)/q)^3
     + G*ell*(D/d)*(D/d + 2*E*sqrt(ell)/q)^2
     + (H/d^2+J*ell)*(E*sqrt(ell)/q)*
              (2*D/d + E*sqrt(ell)/q)^2.
```

## Check every generated physical monomial — no artificial order labels

Fix the original admissible Fredholm exponent `sigma=7/4`, so `w_sigma=(1+r^2)^(7/8)<=d^(7/4)`. Put `p=5/8`. A monomial of the form `ell^a*d^b*q^(-n)` is controlled by `ell^epsilon*d^(-p)` if:

- `b+p<0`: take `epsilon=a`, since `d^b<=d^(-p)`, `q>=1`.
- `b+p>=0`: require `n>=b+p` and take `epsilon=a-b-p`. Indeed `ell^(b+p)*d^(b+p)<=q^(b+p)<=q^n`.

The table below lists **every** cubic product, including the limiting case `P_V^{error}*Z^3`, where `k` is the number of factors `Z` in the remaining cubic after any mandatory `V` or `Z` factor.

| Genuine source family | k | a | b | n | epsilon lower bound |
| --- | ---: | ---: | ---: | ---: | ---: |
| P_mix * C(V+Z) | 0 | 1/2 | -9/4 | 0 | 1/2 |
| P_mix * C(V+Z) | 1 | 1 | -5/4 | 1 | 1 |
| P_mix * C(V+Z) | 2 | 3/2 | -1/4 | 2 | 9/8 |
| P_mix * C(V+Z) | 3 | 2 | 3/4 | 3 | 5/8 |
| P_Z*(C(V+Z)-C(Z)) | 0 | 1 | -5/4 | 0 | 1 |
| P_Z*(C(V+Z)-C(Z)) | 1 | 3/2 | -1/4 | 1 | 9/8 |
| P_Z*(C(V+Z)-C(Z)) | 2 | 2 | 3/4 | 2 | 5/8 |
| 3W²*(C(V+Z)-C(V)) | 0 | 1/2 | -9/4 | 1 | 1/2 |
| 3W²*(C(V+Z)-C(V)) | 1 | 1 | -5/4 | 2 | 1 |
| 3W²*(C(V+Z)-C(V)) | 2 | 3/2 | -1/4 | 3 | 9/8 |
| (P_V-3W²)*(C(V+Z)-C(V)) | 0 | 3/2 | -1/4 | 1 | 9/8 |
| (P_V-3W²)*(C(V+Z)-C(V)) | 1 | 2 | 3/4 | 2 | 5/8 |
| **(P_V-3W²)*Z³** | **2** | **5/2** | **7/4** | **3** | **1/8** |

All `epsilon>=1/8` and all required `n>=b+p` hold. At `0<ell<=1` we therefore obtain

```
w_(7/4)(r)*|S(r)| <= C_source*ell^(1/8)*(1+r)^(-5/8)
C_source = F*(D+E)^3 + G*D*(D+2*E)^2
           +(H+J)*E*(2*D+E)^2 .
```

All constants are nonnegative and independent of `ell,r`. Since

```
integral_0^infty (1+r)^(-5/4) dr=4,
||w_(7/4)*S||_(L²(0,infty)) <= 2*C_source*ell^(1/8).
```

This is a **mathematically substantive positive length-order bound** for the SAME complete physical Hartree nonlinear interaction, and the limiting exponent `1/8` follows from the true core-moment error rather than an assigned generated term. It does not force or assume the temporal concentration law.

## Strict acceptance gate toward 12/13

1. Obtain strict Lean4.35.0-rc3/pinned Mathlib success for the scalar `I[W²](r)<=C/(1+r)` proof and exact physical mixed potential decay from PRs #16/#18.
2. Kernel-check the single-physical-source certificate (PR #19), the original-`sigma=7/4` weight inequality, all 13 finite monomial comparisons, integration of `(1+r)^(-5/4)`, and the actual complete `S` weighted-L² theorem. Do not count a proof based on assuming its own weighted bound.
3. Derive `C¹` time/parameter source control, the two actual normalized Fredholm charges, actual origin-normalized Kummer/remote gluing, all generated physical PDE residual gains and a **genuine** finite (N_*) profile. Existing `HBL/FiniteProfile.lean` is an abstract solver/GeneratedTerm constructor and does NOT itself supply these physical PDE producers.
4. Only the complete, meaningfully revised and manuscript-synchronized theorem 2.13 can change **11/13 to 12/13**. The final existence/Type-II dynamical rate theorem then remains the last environment; it must derive the rate from real PDE modulation, not insert it as a premise.

Source related PRs: #11, #14, #15, #16, #17, #18, #19, #20. Do not equate success of any isolated CI with the acceptance of entire revised 2.13.
