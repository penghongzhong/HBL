# Actual inner reconstruction

For `3/2 < sigma < 2`, this directory reconstructs the actual normalized
H-plus/H-minus Hilbert Fredholm solutions in the original half-line variable.
Each new theorem has its own Lean file. `ReconstructionAudit.lean` exports every
complete theorem type and its transitive axioms.

Write `a(r) = (1+r^2)^(-1)`, and let `F0` denote the actual affine-corrected source.
The representative is

    q(r) = integral min(r,rho) * (a(rho) g(rho) + F0(rho)) d rho,

where `g = 9 x + weightedHartreeOperator x` in the plus channel and `g = 3 x`
in the phase channel. The operator equation proves `x = a q` almost everywhere.
The first moment is integrable because `sigma > 3/2` and `g` belongs to L2.
Consequently `q` is continuous, vanishes at zero, is bounded on the positive
half-line, belongs to every `L^{2,-tau}` with `tau > 1/2`, and has a finite
constant limit at infinity.

For continuous input sources, the same representative is twice differentiable
on the positive half-line and solves the actual nonlocal H-plus or local H-minus
equation with source `F0`. This continuity assumption is explicit: an arbitrary
weighted L2 source is not asserted to have a pointwise classical equation.

`ActualClassicalAffineSolution.lean` restores the concrete cutoff affine model.
For continuous `Fplus, Fminus` in `L^{2,sigma}`, it proves existence of `up, um`
with the actual kernel-complement Hilbert normalization and

    H_plus up = Fplus,       H_minus um = Fminus,
    up(0) = um(0) = 0,
    up(r) - actualPlusCharge(Fplus) r -> dp,
    um(r) - actualMinusCharge(Fminus) r -> dm.

Both full functions belong to every `L^{2,-tau}` with `tau > 3/2`, including the
required `tau = sigma`. Their first and second pointwise differentiability on
the positive half-line is part of the terminal theorem's conclusion. The affine
slopes use the existing physical charge formula, not newly introduced parameters.

Run `python verification/inner_reconstruction_validation.py` under the pinned
Lean 4.35.0-rc3 environment to build the terminal graph, strictly check each new
source with `--trust=0 -DwarningAsError=true`, and inspect all complete types and
axioms. The full untruncated output is retained as a reproducible gzip artifact,
with both compressed and uncompressed SHA256 values in the status JSON. The Mathlib revision is `a98628e16c11f5167f16124105ddce53efa9bfe5`.

This is a supporting reconstruction result. Uniform inverse norm bounds,
parameter jets, quantitative derivative/tail rates, Kummer/remote matching,
generated-order gains, and the exact nonlinear one-layer residual remain to be
assembled. Original manuscript acceptance stays 9/21; `prop:one-layer-stage3`
and the main PDE theorem remain open.
