# HBL 2.13 — complete physical moving-shell positive time order

Date: 2026-11-05. Revised manuscript acceptance remains **11/13 (84.62%)**. This is a strict physical PDE producer for the revised 2.13 closure, not yet the whole finite-profile environment.

## Strict acceptance

- Proof commit: `cfbe0a7958fff86d38494cb92e43ac69433fd3f7`.
- Workflow: [41971968925](https://github.com/penghongzhong/HBL/actions/runs/41971968925), job `127062068702`: **success**.
- Artifact: `13390007003`, `hbl-213-shell-time-audit`.
- Downloaded ZIP SHA256: `0099e133b6d9893b90674b2026c48caaf771e1272ed876e0ed3883f7028a93d3`.
- Lean 4.35.0-rc3, compiler `470d5ce1400764999581fd26d5d72b00d990b0f4`; pinned Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- Target strict replay: `--trust=0 -DwarningAsError=true`, empty strict log.
- Three public theorem declarations were checked with full types and transitive `#print axioms`. Each uses only `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`.
- Independent artifact readback checked the ZIP digest, proof commit, source SHA256 `87468aea4092aa6a99be6f5a076933dc2fb68a7cb33b6bd12cf5344f12bfba0b`, empty strict log and audit summary.

## Reuse rather than re-proving

The new file `ActualHartreeOneOrbitFullShellTimeGain.lean` is deliberately a thin consumer of
`actual_Hartree_one_orbit_full_shell_from_PDE_moment_and_Strauss`.
The latter already contains the true physical moment-selected moving radius and proves the complete same-PDE overlap residual estimate, including:

1. exact material cutoff transport from the actual moment-radius drift;
2. the real three-dimensional radial Laplacian cutoff commutator;
3. the full original nonlocal inverse-square Hartree cutoff commutator;
4. Strauss/L-infinity production of the actual quartic source envelope.

None of those pieces is reimplemented in this round.

## New derived time gain

Define
\[
\epsilon_{\rm sh}(\beta)=\frac{5\beta}{2}-1.
\]
Lean proves
\[
\beta>\frac12\quad\Longrightarrow\quad \epsilon_{\rm sh}(\beta)>0.
\]

The exact factor produced by the already verified full moving-shell PDE theorem is
\[
\ell(s)^2\sqrt{\ell(s)}.
\]
For \(s\ge1\), \(\ell(s)>0\), and the visible bootstrap trap
\[
\ell(s)\le s^{-\beta},
\]
the new kernel-checked scale theorem proves
\[
\boxed{\;
\ell(s)^2\sqrt{\ell(s)}
\le s^{-1-\epsilon_{\rm sh}(\beta)}
=s^{-5\beta/2}.
\;}
\]
No limiting blowup exponent is put into this statement.

Consequently the same actual complete moving-shell residual satisfies
\[
\boxed{\;
\|\operatorname{Res}(\chi_{R(s)}f)
-\chi_{R(s)}\operatorname{Res}(f)\|
\le C_{\rm sh}\,
s^{-1-(5\beta/2-1)}.
\;}
\]
The coefficient \(C_{\rm sh}\) is exactly the coefficient inherited from the physical theorem (moment-flux, Laplacian, Hartree-row, Strauss and amplitude constants); no abstract GeneratedTerm coefficient replaces it.

Since \(5\beta/2-1>0\), the resulting scalar time majorant is integrable on every \([s_0,\infty)\), \(s_0>0\), by the already verified `HBL.Kinematic.integral_Ioi_rpow_neg_one_sub`. No new integrability theorem is counted here because the existing producer suffices.

## Scope and next shortening

This closes the complete **moving-shell** spatial/time commutator as a genuine positive-time-order physical producer. It does not close the whole revised 2.13. The bootstrap trap must eventually be derived/preserved by the actual dynamics.

The next expensive historical obstruction is exact Kummer-to-remote C1 matching. The repository already contains:
- exact three-region common-PDE source identities;
- exact two-boundary Kummer transfer obstruction;
- moving remote Hartree source/center-error bounds;
- full nonlinear Hartree difference/remainder estimates.

Therefore the preferred revised proof route is to test a **smooth controlled Kummer-to-remote transition** on a buffer annulus, rather than require an unnecessary exact independent remote Cauchy match. Such a revision is acceptable only if its cutoff commutator and Hartree nonlinear feedback gain a strictly positive physical order and the resulting global profile remains in the target energy class.

No manuscript count changes in this record. Revised acceptance remains **11/13**.
