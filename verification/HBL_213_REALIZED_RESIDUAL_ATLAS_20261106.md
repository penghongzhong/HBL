# HBL 2.13 — realized residual atlas and selected upper-jet source order

Date: 2026-11-06. Revised manuscript acceptance remains **11/13 (84.62%)**. This record collects strict main-chain producers; it does not count auxiliary theorem declarations as a manuscript environment.

## Newly strict results

### 1. Physical Kummer repair as a realized residual atom

- Commit: `1f7e56233a5f571ee6b023da02ee27e3719666e4`.
- Workflow: [42132216704](https://github.com/penghongzhong/HBL/actions/runs/42132216704): **success**.
- Artifact: `13464720450`, SHA-256 `1d22b7568aa3b378627b6e5f523e9264d21e9ed1c67f0ff98125437ad63fa82d`.

The actual scaled Kummer operator applied to the concrete physical interface-repair field is now a `WeightedResidualAtom ℂ`. If the true boundary jet has current order `s^(-rho)`, its residual has order
[
  ho+kappa_{m phys},
  qquad
  kappa_{m phys}=	exttt{actualHartreePhysicalKappa}(eta,ho_* )>0.
]
The order comes from the strict physical `a^{-2}` pullback/time-gain theorem; no `GainCause` tag supplies the estimate.

### 2. Six concrete residual producers under one physical gain floor

- Commit: `959d2ea22c9fe765d0bdbdae11d64e79760177da`.
- Workflow: [42132619110](https://github.com/penghongzhong/HBL/actions/runs/42132619110): **success**.
- Artifact: `13463449507`, SHA-256 `db11b6a2fa5daf58f6ed657ee6653ec282b0f7333b1c086ec2c0a645bbe31614`.

The joint module imports and strict-audits the realized:
1. moment-locked correction remainder;
2. complete moving-cutoff residual;
3. flat-radiation source;
4. threshold/parameter coordinate residual;
5. whole-radiation slow-center mismatch;
6. physical Kummer repair residual.

It proves one numerical floor (kappa_{m phys}>0) lies below the cutoff, parameter, flat and slow-center gains, while the correction and Kummer-repair remainders already occur at (ho+kappa_{m phys}).

This replaces the old *purely order-labelled* statement for these concrete producers. It still does **not** prove that every recursively generated PDE source is exhausted by the six classes.

### 3. The selected Kummer upper jet inherits the original source order

- Commit: `7df2bc21912ca1622b40839359273f8b2ceeca3c`.
- Workflow: [42133130029](https://github.com/penghongzhong/HBL/actions/runs/42133130029): **success**.
- Artifact: `13463753421`, SHA-256 `aaa4594a8096d6fc48c6e6e61549ce8b2e72aac66310de996005098ded696aff`.

For the SAME complete compatibility-selected speed and SAME matched Kummer field, the existing source-to-jet estimate is now propagated through time. If
[
 N_0+Qle C_{m src}s^{-ho},
]
then
[
oxed{
 |U_B|+B|D_B|
 le C_{m jet}C_{m src}s^{-ho}.
}
]
Here (N_0) is the original two-channel weighted source norm, (Q) is the complete outer-source envelope, and (U_B,D_B) are the actual selected upper Kummer value and normalized slope. No independent boundary-jet decay assumption is used.

## Correct orientation of the outer replacement tail

For replacing the Kummer solution beyond (B) by the concrete repair tail that vanishes by the outer edge, the repair's left jet must have the **same sign** ((U_B,D_B)). The opposite sign belongs to the distinct construction in which a repair is *added* to an existing Green solution to cancel a mismatch. The source-to-repair composition was corrected accordingly in commit `266fdefb511f59836af3227ae9a8af484a00c828`.

## What this closes and what remains

The chain
[
	ext{original source order}
 longrightarrow
	ext{unique compatible speed}
 longrightarrow
	ext{selected Kummer upper jet of the same order}
 longrightarrow
	ext{physical repair with an extra }kappa_{m phys}
]
is now strict through the first three arrows, and the generic repair-to-next-layer producer is strict.

The combined one-statement source-to-repair theorem is under a dedicated strict replay. It is not needed to justify the three accepted producers above.

More importantly, the repair theorem controls the **scaled linear Kummer operator** on the replacement annulus. The complete Hartree PDE still requires the nonlocal feedback caused by the far repair tail to be controlled. The existing `ExteriorSpatialGain.lean` supplies the correct reusable mechanism:
[
 |mathcal I_{m ext}(r)-C_{m ext}|
 lesssim (r/R)^2,|F_{m ext}|_{L^1}.
]
The next main-chain obligation is therefore to derive the actual exterior quartic-density (L^1) bound for the same repair tail and combine it with this geometric gain. After that, the true one-step correction must assemble this outer feedback with the already strict backward-shell, Taylor, speed-cross, cutoff, parameter, flat and slow-center residuals.

The structural `ActualHartreePhysicalFiniteProfile.lean` is still conditional on honest packets / a step relation. It is not yet an acceptance of revised 2.13. The final numerator remains **11/13**.
