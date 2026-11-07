# HBL locked targets and shortened single-orbit proof chain — 2026-11-06

This record fixes the mathematical targets after explicit authorization to modify, bypass or delete any intermediate theorem environment and corresponding Lean verification. Only the two targets below are immutable.

## Target A — final theorem (unchanged)

The final target is exactly verification/typeii-minimal-main-replacement.tex:

- one genuine radial strong solution of the 3D focusing energy-critical inverse-square quartic Hartree equation;
- finite maximal forward time T;
- one concentrating ground-state bubble plus a radiation term converging in Hdot1;
- bounded critical norm and no strong Hdot1 extension through T;
- the modulation scale and phase are determined by the actual two-channel orthogonality conditions;
- mu_s is integrable, there is an emergent limit mu_infty > 9/16, and

  lambda(t)^(-1) = C_lambda (T-t)^(1/2+2 mu_infty) (1+o(1)).

The limiting exponent is an output of the actual Hartree dynamics and is never prescribed.

## Target B — replacement for revised manuscript §2.13

The old strongest formulation “for every large N, every admissible radiation and a full C1 parameter family” is no longer a required intermediate theorem.

The locked replacement is a single-orbit fixed-order physical parametrix theorem. It will use one fixed legitimate terminal radiation and only the retained two threshold coordinates needed by the final shooting/backward construction.

1. Exact physical source and compatibility. The same original Hartree source feeds the fixed Fredholm channels, the same complete compatibility matrix selects the unique real speed correction, and the selected Kummer/repair field is glued with the correct physical sign. No free monopole amplitude, abstract regional solver, or guessed remote trace is allowed.
2. Fixed residual order 9/4. The actual center/profile residual and the actual threshold forcing are continuous and obey a uniform O(s^(-9/4)) bound in the norms consumed by the backward problem.
3. Direct threshold Lipschitz order 9/4. For retained threshold coordinates theta, eta in R^2:

   ||R_cen(s,theta)-R_cen(s,eta)|| <= L s^(-9/4) ||theta-eta||.

   This replaces the old requirement to build a full Frechet derivative D_theta R and then estimate it.
4. Three-region energy control. Inner, Kummer/repair and remote pieces have strictly positive regional Hdot1 decay, sufficient for the already verified global complex-radial H1 gluing.
5. No arbitrary-order conclusion. No statement for all N, no D_zeta Theta_N = I_2+o(1) family theorem, no codimension-one C1 graph and no all-radiation uniformity are required here unless a later step of Target A explicitly consumes them.

### Why order 3 is sufficient

Fix p_* = 9/8 and N_* = nu_* = 9/4. Then

  1 < p_*,    p_* + 1 = 17/8 < 9/4,    2 < 9/4.

Hence the already verified weighted affine forcing machinery accepts an O(s^(-9/4)) fixed center residual and threshold source, while the direct threshold-Lipschitz Duhamel feedback needs only nu_* > 2. The locked exponents are strict-audited in HBL/LockedSingleOrbitExponents.lean. No arbitrary high-order profile is needed for the locked single-orbit final theorem.

## Main-chain replacement

The preferred backward map now consumes H(t,theta)-H(t,eta) with

  ||H(t,theta)-H(t,eta)|| <= C t^(-9/4) ||theta-eta||,

rather than a separately constructed linear coefficient E(t) = -D_theta R(t).

The files HBL/WeightedThresholdResidualFeedback.lean and HBL/WeightedJointBackwardResidualLipschitz.lean implement this replacement and are under strict CI. If accepted, the following old derivative route is not part of the locked main chain:

- HBL/ResidualTangentDerivative.lean;
- HBL/ResidualDecayFromFiniteAtoms.lean insofar as it is used only to obtain E=-D_theta R;
- the long Kummer/source parameter-derivative chain whose only downstream purpose was to manufacture that Frechet derivative.

Those files may remain as a proof pool, but future work should not spend time repairing them unless Target A needs them independently.

## What still has to be proved

The nontrivial remaining §2.13 task is now sharply reduced to:

  actual current residual of order rho  ->  actual next residual of order rho + kappa_phys

for the finite set of real Hartree mechanisms, iterated only until the residual crosses order 9/4. The already strict realized atoms, compatible speed selection, Kummer replacement tail, full moving-cutoff commutator and true-background nonlocal feedback are the proof pool for this step.

Once order 9/4 is reached, the arbitrary-N packet recursion is not used. The profile is passed directly to weighted affine forcing, direct threshold-Lipschitz feedback, the joint Banach fixed point, unstable shooting, global H1 gluing and dynamical rate selection.

Counting: this target reduction changes no current manuscript numerator by itself. Revised acceptance remains 11/13 until the locked fixed-order physical parametrix theorem is proved and strictly audited.
