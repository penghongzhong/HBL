# HBL 2.13 — radius-uniform physical Kummer propagation: STRICT ACCEPTED

The formerly analytical derivative-shear route is now Lean-verified, including its specialization to the SAME canonical Hartree inner correction and original nonlocal forcing. This record supersedes the pending status of the uniform dyadic transfer in `HBL_213_SHEARED_KUMMER_UNIFORM_TRANSFER_REDUCTION_20261104.md`.

## Immutable evidence, downloaded and inspected

- Generic shear and actual same-source transfer CI: https://github.com/penghongzhong/HBL/actions/runs/41752095633 . Strict build and axiom audit passed, 3535 Lake jobs.
- Generic audited commit: `3941479f5e2b0d2ce6c80ba79b31dabb1a631d1c`.
- Generic artifact ID 13287066042, 5330 bytes; independently computed SHA256 `59923332abfffef6a1f7066258f1173dd2ab204d6943a3ff63658d4af95070dc`.
- Integrated ACTUAL Hartree-source CI: https://github.com/penghongzhong/HBL/actions/runs/41752536092 — completed/success.
- Integrated audited commit: `e77601510dc7db7495fc11def58a1bebd3d47f96`.
- Complete integrated Lake build: **4105 jobs**, success.
- Lean 4.35.0-rc3, compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`; Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`.
- All THREE new mathematical source files passed `--trust=0 -DwarningAsError=true`; all three strict logs are empty.
- The complete readable public theorem statements and all three integrated transitive axiom lists were inspected. Only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, added axiom, admit, unsafe or native_decide.
- Integrated artifact ID 13286222066: `HBL_PHYSICAL_UNIFORM_KUMMER_STRICT_41752536092.zip`, **20418 bytes**.
- Independently computed SHA256: `da6fbea05d4a05e0d644d77416ab8cd55a9a2c71c2dcac5bd252a4037c8b1269`, equal to the GitHub digest.
- The archive includes all three new mathematical sources and the integrated audit source. Each archived source hash was recomputed and compared against the checked source-hashes.txt. Commit, compiler pin, Mathlib pin, build result and empty strict logs were also inspected.

## Derived uniform estimate, not an assumed basis bound

For the ACTUAL homogeneous physical Kummer equation

    h''+(2/r+i*r/2)h'+b*h=0,  b=frozenZeroCoeff(mu,theta),

set

    a=2*i*b,
    P(r)=exp(i*r²/4),
    v(r)=P(r)*(r*h'(r)-a*h(r)),
    X(r)=(h(r),v(r)).

The exact derivative identities and |P|=1 are separately proved. The large O(r) imaginary drift cancels before norms are taken. In the product maximum norm, Lean proves

    ||X'(r)|| <= (1+|a|)²/r * ||X(r)||.

The pinned, proved Mathlib Gronwall theorem gives, for 0<r0<=r1<=2*r0,

    H(r1) <= C_b*H(r0),
    H(r)=max(|h(r)|,r*|h'(r)|),
    C_b=(1+2|b|)²*exp((1+2|b|)²).

C_b is independent of r0, r1, the normalization of the fundamental pair and the particular source. Uniformity over external parameter families requires bounded b; no bound uniform over unbounded b is claimed. The explicit dyadic ratio hypothesis is retained.

The accepted SAME-source cancellation lemma supplies h as an exact combination of the original LocalKummerPair. Thus the second public result controls the original right transfer itself:

    max(|Delta value(r1)|,r1*|Delta slope(r1)|)
       <= C_b*max(|U-A|,r0*|DU-DA|),

where Delta compares T_K[F](U,DU) with T_K[F](A,DA), using exactly the same original F. No continuity hypothesis is needed merely to control this homogeneous difference; no unsupported classical C2 assertion about a measurable-forcing particular solution is made.

## Complete canonical Hartree-source specialization

For fixed radiation bounds B,A>=0, the integrated theorem chooses Cp,Cm>=0 BEFORE ell,c,z. It then retains precisely the existing physical assumptions: 0<ell<=1, |c|<=1, measurability of z, |z(u)|<=B for u>0, and u*|z(u)|<=A for u>=1.

It constructs the actual weighted two-channel source memberships and a normalized x satisfying BOTH original corrected Fredholm equations. Its physical representatives are the exact affine-restored Green reconstructions divided by r. Their derivatives are proved to be actual derivatives, not unconstrained jet variables.

With G=r*(1-cutoff(r/R))*F_ell,c, R=ell^(-1/16), and

    alpha=actualPlusCharge(Re G)+i*actualMinusCharge(Im G),

the two transfers are driven explicitly by `actualHartreePhysicalSliceInteraction ell c z`. The reference is (alpha,0), NOT the zero solution. For 2<r0<r1<=2*r0 on the actual Kummer annulus, the checked conclusion is

    max(|Delta value(r1)|,r1*|Delta slope(r1)|)
       <= C_b*(Cp+Cm)*ell^(1/16)/r0.

The forced affine charge and both canonical Fredholm equations are preserved in the exported type. No uniform trace, transfer, generated source order or blowup rate is inserted as a new hypothesis.

At r0=2*ell^(-1/16), 0<ell<1, direct scalar substitution gives

    |Delta value(r1)| <= C_b*(Cp+Cm)/2 * ell^(1/8),
    |Delta slope(r1)| <= C_b*(Cp+Cm)/4 * ell^(3/16).

The exported Lean theorem is the stronger all-r0 expression above; the displayed specialization is its elementary corollary, not separately counted as another verified environment.

## Files and public conclusions

- `HBL/TypeIIDynamicSelection/ActualKummerShearedGronwall.lean`: exact phase and derivative shear, 1/r system bound, actual_Kummer_homogeneous_dyadic_uniform_bound.
- `HBL/TypeIIDynamicSelection/ActualKummerUniformSameSourceTransfer.lean`: explicit C_b and actual_Kummer_same_source_scaled_transfer_uniform.
- `HBL/TypeIIDynamicSelection/ActualHartreeUniformKummerPropagation.lean`: actual_Hartree_canonical_inner_to_uniform_Kummer_transfer.
- Separate generic and integrated Audit.lean files print full types and transitive axioms.

## Remaining original manuscript obligations

The dyadic moving-annulus amplification obstacle is CLOSED for this canonical core/radiation source comparison. This does not identify the forced-charge reference transfer T_K[F](alpha,0) with the independently constructed remote/outgoing solution or the manuscript's original endpoint normalization. Those compatibility conditions still require proof. No unrestricted annulus-ratio estimate is claimed.

All generated common-PDE transport, parameter, cutoff and nonlinear higher-profile residuals must still be controlled before applying the existing finite recursion. The final Type-II concentration law must be derived from PDE dynamics. Physical-length smallness is not a prescribed time law.

**Retained numbered manuscript acceptance remains 11/13 (84.62%). Full environment 2.13 and the final Type-II theorem are not relabeled as proved by this auxiliary-chain closure.**
