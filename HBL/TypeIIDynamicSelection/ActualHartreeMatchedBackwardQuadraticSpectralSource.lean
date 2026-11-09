import HBL.TypeIIDynamicSelection.ActualHartreeBackwardMatchedValueGain
import HBL.TypeIIDynamicSelection.ActualHartreeBackwardZeroLeftSpectralVolterra
import HBL.TypeIIDynamicSelection.ActualHartreeMomentLockedKummerPullback
import Mathlib.Tactic

/-!
# Genuine matched Fredholm source to backward QUADRATIC spectral forcing

The original matched Green field u0, its TWO actual Fredholm channels,
and its forced matching Cauchy jet are the inputs. Its backward [R,2R]
value is produced from the original two-channel source, not postulated.

For q=delta*u0 and the actual zero-left Cramer solution u1=G[q;0,0]
anchored at normalized r0=(2R)/a, the exact reversed Volterra integrals
provide a direct bound on the normalized BACKWARD interval [r0/2,r0].
Both delta factors are exposed in the true current-operator residual.
No global nonlinear time gain or Type-II law is claimed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- Actual Cramer-matched physical field supplies the FIRST spectral
source, while the backward zero-Cauchy Green bound supplies the SECOND
one. Both are the SAME matched field and normalized origin basis. -/
theorem actual_Hartree_matched_backward_quadratic_spectral_source
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a R B C G : ℝ)
    (ha : 0 < a) (hR : 2 < R)
    (hOrder : 2 * R / a ≤ B) (hB : B < scale)
    (hG : 0 ≤ G)
    (hK : OriginBasisOn K (2 * R / a) B C)
    (hModes : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (hSmall : 16 * R ^ 2 *
      ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) ≤ 1)
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (hcp : Continuous Fp) (hcm : Continuous Fm)
    (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo (0 : ℝ) scale, ContinuousAt F r)
    (hSame : ∀ y ∈ Icc R (2 * R),
      actualMatchedScaledKummerApply mu theta a
        (actualOriginMatchedKummerPullback K a (2 * R / a) B
          F
          (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)).1
          (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)).2) y =
        -actualHartreeTwoChannelPhysicalSource Fp Fm y)
    (delta : ℂ)
    (hInt : ∀ x ∈ Icc ((2 * R / a) / 2) (2 * R / a),
      IntervalIntegrable
        (originGreenSourceA K
          (fun t => delta * actualOriginMatchedKummerValue K
            (2 * R / a) B F
            (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)).1
            (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)).2 t))
        volume x (2 * R / a))
    (hIntR : IntervalIntegrable
      (originGreenSourceA K
        (fun t => delta * actualOriginMatchedKummerValue K
          (2 * R / a) B F
          (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)).1
          (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)).2 t))
      volume (2 * R / a) B)
    (y : ℝ) (hy : y ∈ Icc R (2 * R)) :
    let r0 := 2 * R / a
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a r0
    let u0 := actualOriginMatchedKummerValue K r0 B F J.1 J.2
    let u1 := actualOriginMatchedKummerValue K r0 B
      (fun x => delta * u0 x) 0 0
    let D := actualInnerShellValueConstant *
      (innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm) +
        8 * R ^ 2 * actualHartreeTwoChannelShellBudget mu theta a R Fp Fm
    ‖(((a ^ 2)⁻¹ : ℝ) : ℂ) * (delta * u1 (y / a))‖ ≤
      ((a ^ 2)⁻¹ * ‖delta‖) * (2 * G ^ 2 * (r0 * ‖delta‖ * D)) := by
  dsimp only
  let L : ℝ := 2 * R
  let r0 : ℝ := L / a
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a r0
  let u0 := actualOriginMatchedKummerValue K r0 B F J.1 J.2
  let q : ℝ → ℂ := fun t => delta * u0 t
  let u1 := actualOriginMatchedKummerValue K r0 B q 0 0
  let v := actualOriginMatchedKummerPullback K a r0 B F J.1 J.2
  let D : ℝ := actualInnerShellValueConstant *
      (innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm) +
      8 * R ^ 2 * actualHartreeTwoChannelShellBudget mu theta a R Fp Fm
  let M : ℝ := r0 * ‖delta‖ * D
  have hL : 0 < L := by dsimp [L]; linarith
  have hr0 : 0 < r0 := div_pos hL ha
  have hRpos : 0 < R := by linarith
  let U : Set ℝ := Ioo 0 (a * scale)
  have hU : IsOpen U := isOpen_Ioo
  have hLscale : L < a * scale := by
    have h := (div_lt_iff₀ ha).1 (hOrder.trans_lt hB)
    simpa only [L, mul_comm] using h
  have hSub : Icc R (2 * R) ⊆ U := by
    intro t ht
    exact ⟨hRpos.trans_le ht.1, ht.2.trans_lt hLscale⟩
  have hClass :=
    actual_Hartree_matched_Kummer_pullback_classical K a ha
      hr0 hOrder hB F hF J.1 J.2
  have hv : ∀ x ∈ U, DifferentiableAt ℝ v x :=
    fun x hx => (hClass x hx).1.differentiableAt
  have hv2 : ∀ x ∈ Icc R (2 * R),
      DifferentiableAt ℝ (deriv v) x :=
    fun x hx => (hClass x (hSub hx)).2.1
  have hJet :=
    actual_Hartree_moment_locked_pullback_actual_inner_jet
      K L a hL ha hOrder hB Fp Fm hp hm F hF
  have hAnchor : L ∈ Icc R (2 * R) := ⟨by linarith, le_rfl⟩
  have hSame' : ∀ x ∈ Icc R (2 * R),
      actualMatchedScaledKummerApply mu theta a v x =
        -actualHartreeTwoChannelPhysicalSource Fp Fm x := by
    intro x hx
    simpa only [v, L, r0, J] using hSame x hx
  have hVal := actual_Hartree_backward_original_matched_Kummer_value_from_same_source
    mu theta a R L Fp Fm hp hm U v
      hcp hcm hU hSub ha hR hSmall hAnchor hv hv2
      hJet.1.symm hJet.2.2.1.symm hSame'
  have hStart : R ∈ Icc R (2 * R) := ⟨le_rfl, by linarith⟩
  have hD : 0 ≤ D := by
    have h := hVal R hStart
    change ‖v R‖ ≤ D at h
    exact (norm_nonneg _).trans h
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have haR : a * r0 = L := by
    dsimp [r0]
    field_simp [ha.ne']
  have hHalf : a * (r0 / 2) = R := by
    dsimp [L] at haR
    nlinarith [haR]
  have hForcing (x : ℝ) (hx : x ∈ Icc (r0 / 2) r0) :
      ‖q x‖ ≤ M / x := by
    have hxpos : 0 < x := (by positivity : 0 < r0 / 2).trans_le hx.1
    have hxPhys : a * x ∈ Icc R (2 * R) := by
      constructor
      · have h := mul_le_mul_of_nonneg_left hx.1 ha.le
        nlinarith [h, hHalf]
      · have h := mul_le_mul_of_nonneg_left hx.2 ha.le
        dsimp [L] at haR
        nlinarith [h, haR]
    have hScale : a * x / a = x := by field_simp [ha.ne']
    have hu : ‖u0 x‖ ≤ D := by
      have h := hVal (a * x) hxPhys
      change ‖u0 (a * x / a)‖ ≤ D at h
      simpa only [hScale] using h
    have hq : ‖q x‖ ≤ ‖delta‖ * D := by
      dsimp only [q]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hu (norm_nonneg delta)
    have hxBound : ‖delta‖ * D ≤ M / x := by
      apply (le_div_iff₀ hxpos).2
      have hCo : 0 ≤ ‖delta‖ * D := mul_nonneg (norm_nonneg _) hD
      have hMul := mul_le_mul_of_nonneg_left hx.2 hCo
      simpa only [M, mul_assoc, mul_comm, mul_left_comm] using hMul
    exact hq.trans hxBound
  have hx : y / a ∈ Icc (r0 / 2) r0 := by
    have hBound : R / a ≤ y / a :=
      div_le_div_of_nonneg_right hy.1 ha.le
    have hUpper : y / a ≤ 2 * R / a :=
      div_le_div_of_nonneg_right hy.2 ha.le
    have hEq : r0 / 2 = R / a := by dsimp [r0, L]; ring
    constructor
    · simpa only [hEq] using hBound
    · simpa only [r0, L] using hUpper
  have hVal1 :=
    actual_Hartree_zero_left_original_Green_backward_inverse_linear_bound
      K r0 B C G M hr0 hOrder hB.le hG hM hK hModes
      q hForcing (y / a) hx
      (by simpa only [r0, L, q, J, u0] using hInt (y / a) (by
        simpa only [r0, L] using hx))
      (by simpa only [r0, L, q, J, u0] using hIntR)
  have hInv : 0 ≤ (a ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg a)
  have hEq :
      ‖(((a ^ 2)⁻¹ : ℝ) : ℂ) * (delta * u1 (y / a))‖ =
        ((a ^ 2)⁻¹ * ‖delta‖) * ‖u1 (y / a)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hInv, norm_mul]
    ring
  change ‖(((a ^ 2)⁻¹ : ℝ) : ℂ) * (delta * u1 (y / a))‖ ≤
    ((a ^ 2)⁻¹ * ‖delta‖) * (2 * G ^ 2 * (r0 * ‖delta‖ * D))
  rw [hEq]
  have hCoef : 0 ≤ (a ^ 2)⁻¹ * ‖delta‖ :=
    mul_nonneg hInv (norm_nonneg delta)
  exact mul_le_mul_of_nonneg_left hVal1 hCoef

end HBL.TypeIIDynamicSelection
