import HBL.KummerOriginBasis.AnnulusBound
import HBL.KummerOriginBasis.UniformBound
import HBL.KummerOriginBasis.Normalization
import HBL.KummerOriginBasis.Uniqueness
import HBL.KummerOriginBasis.AsymptoticBound

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace HBL.Profile.Kummer

/-- The origin-normalized singular/regular physical basis exists on every input
positive annulus, with one C1 and inverse-Wronskian bound for an input compact
parameter set. No annulus shrinking or assumed fundamental pair is used. -/
theorem exists_compact_origin_kummer_basis
    (A : Set (ℝ × ℝ)) (hA : IsCompact A) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧ ∀ p ∈ A, ∃ K : OriginKummerPair p.1 p.2 (b + 1),
      OriginBasisOn K a b C ∧ OriginBasisNormalization K ∧
      (∀ J : OriginKummerPair p.1 p.2 (b + 1), ∀ r ∈ Icc 0 (b + 1),
        K.y r = J.y r ∧ K.dy r = J.dy r ∧ K.x r = J.x r ∧ K.dx r = J.dx r) ∧
      (∀ r ∈ Ioc 0 (b + 1),
        ‖originPhysicalValue K.y r - (r : ℂ)⁻¹‖ ≤ H * r ∧
        ‖originPhysicalValue K.x r - 1‖ ≤ H * r ^ 2) := by
  have hR : 0 < b + 1 := by linarith
  have hc : Continuous (fun p : ℝ × ℝ => originZeroCoeff p.1 p.2) := by
    unfold originZeroCoeff
    fun_prop
  obtain ⟨M₀, hM₀⟩ := hA.exists_bound_of_continuousOn hc.continuousOn
  let D := (b + 1) / 2 + max M₀ 0
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let G := Real.exp ((D + 1) * (b + 1))
  refine ⟨G * (1 / a + 1 / a ^ 2) + b ^ 2 + 1, (D + 1) * G,
    by dsimp [G]; positivity, by dsimp [G]; positivity, ?_⟩
  intro p hp
  obtain ⟨K⟩ := exists_origin_kummer_pair p.1 p.2 (b + 1) hR.le
  have hcoeff (r : ℝ) (hr : r ∈ Icc 0 (b + 1)) :
      ‖originFirstCoeff r‖ + ‖originZeroCoeff p.1 p.2‖ ≤ D := by
    have hfirst : ‖originFirstCoeff r‖ = r / 2 := by
      simp [originFirstCoeff, abs_of_nonneg hr.1]
    rw [hfirst]
    have hM := (hM₀ p hp).trans (le_max_left M₀ 0)
    dsimp [D]
    linarith [hr.2]
  refine ⟨K, origin_kummer_annulus_bound K a b G ha (by linarith)
    (Real.exp_pos _).le (origin_kummer_pair_bound K D hD hcoeff),
    origin_kummer_normalization K hR, origin_kummer_pair_unique K, ?_⟩
  intro r hr
  obtain ⟨hy, hx⟩ := origin_kummer_asymptotic_bound K D G hD (Real.exp_pos _).le
    hcoeff (origin_kummer_pair_bound K D hD hcoeff) r hr
  refine ⟨hy.trans ?_, hx⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le) hr.1.le
end HBL.Profile.Kummer
