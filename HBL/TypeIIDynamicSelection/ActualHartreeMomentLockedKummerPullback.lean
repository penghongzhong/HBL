import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedMatchedKummerClassical
import HBL.TypeIIDynamicSelection.ActualHartreeTwoChannelMatchedShell

/-!
The SAME matched origin Green solution is pulled back to the physical
radius y=a*r. Its exact classical equation remains valid to the LEFT of
its matching point L/a, so the overlap [L/2,L] can use the right endpoint
L as its zero-jet anchor. No matrix, source, homogeneous coefficient or
upper boundary condition is changed by this continuation.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Physical pullback of the explicitly matched Green formula; its original
integral endpoints and its two forced Cramer coefficients stay fixed. -/
def actualOriginMatchedKummerPullback
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a r0 r1 : ℝ) (F : ℝ → ℂ) (U DU : ℂ) (y : ℝ) : ℂ :=
  actualOriginMatchedKummerValue K r0 r1 F U DU (y / a)

/-- Genuine C2 pullback and the full scaled Kummer equation on the open
physical positive domain. In particular this holds below a*r0 without
changing the source to a localized or artificially repaired source. -/
theorem actual_Hartree_matched_Kummer_pullback_classical
    {mu theta scale r0 r1 : ℝ} (K : OriginKummerPair mu theta scale)
    (a : ℝ) (ha : 0 < a) (hr0 : 0 < r0) (horder : r0 ≤ r1) (hr1 : r1 < scale)
    (F : ℝ → ℂ) (hF : ∀ r ∈ Ioo 0 scale, ContinuousAt F r) (U DU : ℂ) :
    ∀ y ∈ Ioo 0 (a * scale),
      HasDerivAt (actualOriginMatchedKummerPullback K a r0 r1 F U DU)
        ((a : ℂ)⁻¹ * deriv (actualOriginMatchedKummerValue K r0 r1 F U DU) (y / a)) y ∧
      DifferentiableAt ℝ (deriv (actualOriginMatchedKummerPullback K a r0 r1 F U DU)) y ∧
      actualMatchedScaledKummerApply mu theta a
        (actualOriginMatchedKummerPullback K a r0 r1 F U DU) y =
          ((a ^ 2)⁻¹ : ℝ) • F (y / a) := by
  let w := actualOriginMatchedKummerValue K r0 r1 F U DU
  let v := actualOriginMatchedKummerPullback K a r0 r1 F U DU
  have hClass := actual_origin_matched_Kummer_classical_on_positive_interval
    K hr0 horder hr1 F hF U DU
  have hmem (y : ℝ) (hy : y ∈ Ioo 0 (a * scale)) : y / a ∈ Ioo 0 scale := by
    refine ⟨div_pos hy.1 ha, (div_lt_iff₀ ha).2 ?_⟩
    simpa only [mul_comm] using hy.2
  have hFirst (y : ℝ) (hy : y ∈ Ioo 0 (a * scale)) :
      HasDerivAt v ((a : ℂ)⁻¹ * deriv w (y / a)) y := by
    have hW : HasDerivAt w (deriv w (y / a)) (y / a) :=
      (hClass (y / a) (hmem y hy)).1.differentiableAt.hasDerivAt
    change HasDerivAt (fun t : ℝ => w (t / a)) _ y
    simpa only [Function.comp_def, one_div, Complex.real_smul, Complex.ofReal_inv] using
      hW.scomp y ((hasDerivAt_id y).div_const a)
  intro y hy
  have hnear : deriv v =ᶠ[𝓝 y] (fun t => (a : ℂ)⁻¹ * deriv w (t / a)) := by
    filter_upwards [Ioo_mem_nhds hy.1 hy.2] with t ht
    exact (hFirst t ht).deriv
  have hW2 : HasDerivAt (deriv w) (deriv (deriv w) (y / a)) (y / a) :=
    (hClass (y / a) (hmem y hy)).2.1.differentiableAt.hasDerivAt
  have hModel : HasDerivAt (fun t => (a : ℂ)⁻¹ * deriv w (t / a))
      ((a : ℂ)⁻¹ * ((a : ℂ)⁻¹ * deriv (deriv w) (y / a))) y := by
    simpa only [Function.comp_def, one_div, Complex.real_smul, Complex.ofReal_inv] using
      (hW2.scomp y ((hasDerivAt_id y).div_const a)).const_mul (a : ℂ)⁻¹
  have hSecond := hModel.congr_of_eventuallyEq hnear
  refine ⟨hFirst y hy, hSecond.differentiableAt, ?_⟩
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.1.ne'
  have hvValue : v y = w (y / a) := rfl
  calc
    actualMatchedScaledKummerApply mu theta a v y =
        ((a ^ 2)⁻¹ : ℝ) •
          (deriv (deriv w) (y / a) + frozenFirstCoeff (y / a) * deriv w (y / a) +
            frozenZeroCoeff mu theta * w (y / a)) := by
      unfold actualMatchedScaledKummerApply complexRadialLaplacian
      rw [hSecond.deriv, (hFirst y hy).deriv, hvValue]
      unfold frozenFirstCoeff
      simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow,
        Complex.ofReal_div]
      field_simp [haC, hyC]
      ring
    _ = ((a ^ 2)⁻¹ : ℝ) • F (y / a) := by
      rw [(hClass (y / a) (hmem y hy)).2.2]

/-- The physical pullback matches the ACTUAL fixed-Fredholm field and its
actual derivative at y=L. Consequently the mismatch has a genuine zero
Cauchy jet at the RIGHT endpoint of the backward shell [L/2,L]. This uses
only weighted membership for the inner C1 traces. -/
theorem actual_Hartree_moment_locked_pullback_actual_inner_jet
    {mu theta scale B : ℝ} (K : OriginKummerPair mu theta scale)
    (L a : ℝ) (hL : 0 < L) (ha : 0 < a) (hLB : L / a ≤ B) (hB : B < scale)
    (Fp Fm : ℝ → ℝ) (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm) (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo 0 scale, ContinuousAt F r) :
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
    let u := actualHartreeTwoChannelInner Fp Fm hp hm
    let v := actualOriginMatchedKummerPullback K a (L / a) B F J.1 J.2
    v L = u L ∧ HasDerivAt v (deriv u L) L ∧ deriv v L = deriv u L ∧
      (fun y => u y - v y) L = 0 ∧
      HasDerivAt (fun y => u y - v y) 0 L ∧
      deriv (fun y => u y - v y) L = 0 := by
  dsimp only
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (L / a)
  let u := actualHartreeTwoChannelInner Fp Fm hp hm
  let v := actualOriginMatchedKummerPullback K a (L / a) B F J.1 J.2
  let up := actualMomentLockedPhysicalPlus Fp hp
  let um := actualMomentLockedPhysicalMinus Fm hm
  have hPlus : DifferentiableAt ℝ up L :=
    ((normalizedPlusOutput_C1 Fp hp).1 L).div differentiableAt_id hL.ne'
  have hMinus : DifferentiableAt ℝ um L :=
    ((normalizedMinusOutput_C1 Fm hm).1 L).div differentiableAt_id hL.ne'
  have hInner : HasDerivAt u
      (((deriv up L : ℝ) : ℂ) + Complex.I * ((deriv um L : ℝ) : ℂ)) L :=
    hPlus.hasDerivAt.ofReal_comp.add (hMinus.hasDerivAt.ofReal_comp.const_mul Complex.I)
  have hScale : a * (L / a) = L := by field_simp [ha.ne']
  have hJ : J.1 = u L ∧ J.2 = (a : ℂ) * deriv u L := by
    constructor
    · dsimp only [J, actualMomentLockedCanonicalInnerJet, u, actualHartreeTwoChannelInner]
      rw [hScale]
    · rw [hInner.deriv]
      dsimp only [J, actualMomentLockedCanonicalInnerJet, up, um]
      rw [hScale]
  have hOuter := actual_origin_matched_Kummer_actual_endpoint_jets K
    (div_pos hL ha) hLB hB F hF J.1 J.2
  have hLdomain : L ∈ Ioo 0 (a * scale) := by
    refine ⟨hL, ?_⟩
    have h := (div_lt_iff₀ ha).1 (hLB.trans_lt hB)
    simpa only [mul_comm] using h
  have hPull := actual_Hartree_matched_Kummer_pullback_classical K a ha
    (div_pos hL ha) hLB hB F hF J.1 J.2 L hLdomain
  have hValue : v L = u L := hOuter.1.trans hJ.1
  have hV : HasDerivAt v (deriv u L) L := by
    have hCoeff : (a : ℂ)⁻¹ *
        deriv (actualOriginMatchedKummerValue K (L / a) B F J.1 J.2) (L / a) =
        deriv u L := by
      rw [hOuter.2.2.1, hJ.2, ← mul_assoc, inv_mul_cancel₀
        (Complex.ofReal_ne_zero.mpr ha.ne'), one_mul]
    have h := hPull.1
    rw [hCoeff] at h
    exact h
  have hZero : HasDerivAt (fun y => u y - v y) 0 L := by
    simpa only [sub_self] using hInner.differentiableAt.hasDerivAt.sub hV
  exact ⟨hValue, hV, hV.deriv, sub_eq_zero.mpr hValue.symm, hZero, hZero.deriv⟩

end HBL.TypeIIDynamicSelection
