import HBL.KummerOriginBasis.Definitions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace HBL.Profile.Kummer

/-- Uniform Grönwall bound for the actual origin-normalized solutions. -/
theorem origin_kummer_pair_bound {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) (D : ℝ) (hD : 0 ≤ D)
    (hcoeff : ∀ r ∈ Icc 0 R,
      ‖originFirstCoeff r‖ + ‖originZeroCoeff mu theta‖ ≤ D) :
    ∀ r ∈ Icc 0 R,
      ‖K.y r‖ ≤ Real.exp ((D + 1) * R) ∧ ‖K.dy r‖ ≤ Real.exp ((D + 1) * R) ∧
      ‖K.x r‖ ≤ Real.exp ((D + 1) * R) ∧ ‖K.dx r‖ ≤ Real.exp ((D + 1) * R) := by
  have hb (u v : ℝ → ℂ)
      (hu : ∀ r ∈ Icc 0 R, HasDerivWithinAt u (v r) (Icc 0 R) r)
      (hv : ∀ r ∈ Icc 0 R, HasDerivWithinAt v
        (-(originFirstCoeff r * v r + originZeroCoeff mu theta * u r)) (Icc 0 R) r)
      (hzero : ‖(u 0, v 0)‖ ≤ 1) (r : ℝ) (hr : r ∈ Icc 0 R) :
      ‖(u r, v r)‖ ≤ Real.exp ((D + 1) * R) := by
    have hder (t : ℝ) (ht : t ∈ Icc 0 R) := (hu t ht).prodMk (hv t ht)
    have hnorm (t : ℝ) (ht : t ∈ Icc 0 R) :
        ‖(v t, -(originFirstCoeff t * v t + originZeroCoeff mu theta * u t))‖ ≤
          (D + 1) * ‖(u t, v t)‖ := by
      have huN : ‖u t‖ ≤ ‖(u t, v t)‖ := le_max_left _ _
      have hvN : ‖v t‖ ≤ ‖(u t, v t)‖ := le_max_right _ _
      have hN := norm_nonneg (u t, v t)
      rw [Prod.norm_def, max_le_iff]
      constructor
      · nlinarith
      · calc
          ‖-(originFirstCoeff t * v t + originZeroCoeff mu theta * u t)‖
              ≤ ‖originFirstCoeff t‖ * ‖v t‖ + ‖originZeroCoeff mu theta‖ * ‖u t‖ := by
                simpa only [norm_neg, norm_mul] using norm_add_le
                  (originFirstCoeff t * v t) (originZeroCoeff mu theta * u t)
          _ ≤ (‖originFirstCoeff t‖ + ‖originZeroCoeff mu theta‖) * ‖(u t, v t)‖ := by
            calc
              _ ≤ ‖originFirstCoeff t‖ * ‖(u t, v t)‖ +
                  ‖originZeroCoeff mu theta‖ * ‖(u t, v t)‖ := by gcongr
              _ = _ := by ring
          _ ≤ D * ‖(u t, v t)‖ := mul_le_mul_of_nonneg_right (hcoeff t ht) hN
          _ ≤ (D + 1) * ‖(u t, v t)‖ := by nlinarith
    have hh := norm_le_gronwallBound_of_norm_deriv_right_le (K := D + 1) (ε := 0)
      (HasDerivWithinAt.continuousOn hder)
      (fun t ht => (hder t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)))
      hzero (fun t ht => by simpa using hnorm t ⟨ht.1, ht.2.le⟩) r hr
    simp only [gronwallBound_ε0, sub_zero, one_mul] at hh
    exact hh.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr.2 (by linarith)))
  intro r hr
  have hy := hb K.y K.dy K.y_deriv K.dy_deriv (by simp [K.y_zero, K.dy_zero]) r hr
  have hx := hb K.x K.dx K.x_deriv K.dx_deriv (by simp [K.x_zero, K.dx_zero]) r hr
  simpa only [Prod.norm_def, max_le_iff, and_assoc] using And.intro hy hx
end HBL.Profile.Kummer
