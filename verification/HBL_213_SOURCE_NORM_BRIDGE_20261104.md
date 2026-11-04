# HBL 2.13 — Quantitative source-norm bridge (2026-11-04)

Scope: exact reduction using the previously strictly accepted compatible construction, **not** an acceptance of manuscript 2.13.

Let `L = actualHartreeSlowInnerRadius ell` and
`F_{+,0}=actualHartreeTransmissionPlusSource ell c z`,
`F_{-,0}=actualHartreeTransmissionMinusSource ell c z`.
Use the actual speed sources
`G_omega=actualMomentLockedInnerPhaseSource L c` and
`G_b=actualMomentLockedInnerScaleSource L c`. Let
`F_+=F_{+,0}+delta_omega G_omega`, `F_-=F_{-,0}+delta_b G_b`.
All source norms below are the original weighted `L^{2,7/4}(dr)` norms.

Set

```
N0 = ||F_{+,0}|| + ||F_{-,0}||
S  = max(||G_b||, ||G_omega||)
Z  = actualMomentLockedIntervalObstruction K (L/a) B F0 J0.1 J0.2
alpha = 1024/(a*B^2)
```

with `F0=-actualHartreeLaplacianScaledKummerSource a ell c z`,
`J0=actualMomentLockedCanonicalInnerJet F_{+,0} F_{-,0} ... a (L/a)`.
On the accepted physical parameter region, the full compatibility inverse yields

```
|delta_b| + |delta_omega| <= alpha * ||Z||.
```

The triangle inequality gives the **unconditional bridge**

```
N_adjusted <= N0 + S*(|delta_b|+|delta_omega|)
           <= N0 + alpha*S*||Z||.                 (B1)
```

Thus the already certified shell estimate becomes

```
||E_shell||_(L^{2,7/4})
  <= C*(L/2)^(-3/4) * (N0 + alpha*S*||Z||). (B2)
```

Importantly, `Z` contains the **complete** outer forcing integral and the actual baseline Fredholm Cauchy jet. It is not just a two-column projection of `F0` and not a freely chosen scalar. Formula (B2) cannot be simplified to `C*(L/2)^(-3/4)*N0` unless a bound of the form

```
||Z|| <= C_Z * a*B^2*N0/S
```

(or a different sufficient scale-aware estimate) is **proved for the same physical source**, with a separately handled case `S=0`. Even if this estimate is obtained, it controls only the frozen matched shell, not the complete PDE residual. 

## Concrete next producer / consumer interface

**Producer:** prove a bound for `Z` from the existing actual Green source integral plus both actual Fredholm traces, with constants uniform in the *constructed* Kummer basis and parameter region, without assuming smallness of the obstruction.

**Consumer:** insert this bound into (B1), then insert (B1) into the existing `ActualMomentLockedPhysicalBackwardShellConclusion`. Check the resulting exponent against the required one-step residual gain. The full residual also includes the time derivative of the correction, moving basis/interface, Hartree nonlocal feedback, outer radiation condition at infinity and the nonlinear Taylor remainder. None can be deleted or hidden in `hstep`.

**Numerical caution:** the speed-source weighted norm `S` may grow with `L`; neither its boundedness nor the useful smallness of `alpha*S` follows from the determinant lower bound alone. The exact power budget has to use the already proved response-moment / source-norm estimates. The `B`-trace cancellation is at a finite point; it is not automatically the infinity radiation condition.

Latest strict proof anchor: commit `8eb8daada29a861d025dd5b38a177d7b2a72c957`, workflow `41844544308`. Historical accepted manuscript count **11/13**. This note adds no Lean-verified theorem and changes no denominator.
