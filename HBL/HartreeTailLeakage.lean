import HBL.HartreeKernelShortRange
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Absolute integrability and quantitative leakage of actual Hartree outer tails. -/

noncomputable section
open Set MeasureTheory

namespace HBL.Modulation.AffineTail

/-- A measurable outer tail of at most linear growth has an absolutely
integrable actual Hartree density, with an explicit separated-region bound. -/
theorem hartree_tail_linear_bound
    {r R M : ℝ} (f : ℝ → ℝ) (hf : Measurable f) (_hM : 0 ≤ M)
    (hr : 0 < r) (hR : 0 < R) (hsep : 2 * r ≤ R)
    (hbound : ∀ ρ : ℝ, R ≤ ρ → |f ρ| ≤ M * ρ) :
    IntegrableOn (fun ρ => hartreeKernel r ρ * f ρ) (Ioi R) ∧
      |∫ ρ in Ioi R, hartreeKernel r ρ * f ρ| ≤
        16 * Real.pi * hartreeKappa * M * r * bubble r ^ 3 / R ^ 2 := by
  let C := 4 * |8 * Real.pi * hartreeKappa| * M * r * bubble r ^ 3
  have hpoint : ∀ ρ ∈ Ioi R, |hartreeKernel r ρ * f ρ| ≤ C * ρ ^ (-3 : ℝ) := by
    intro ρ hρ
    have hρpos : 0 < ρ := hR.trans hρ
    have hk := hartreeKernel_separated_ordered ρ r hρpos hr (hsep.trans hρ.le)
    rw [hartreeKernel_symm ρ r, ← bubble_pow_three_eq_bracket] at hk
    rw [abs_mul]
    calc
      |hartreeKernel r ρ| * |f ρ| ≤
          ((4 * |8 * Real.pi * hartreeKappa|) * ρ⁻¹ ^ 4 * r * bubble r ^ 3) *
            (M * ρ) := by
        exact mul_le_mul hk (hbound ρ hρ.le) (abs_nonneg _)
          (by unfold bubble; positivity)
      _ = C * ρ ^ (-3 : ℝ) := by
        have hp : ρ ^ (-3 : ℝ) = ρ⁻¹ ^ 3 := by
          rw [Real.rpow_neg hρpos.le, inv_pow]
          norm_num
        rw [hp]
        dsimp [C]
        field_simp
  have hmeas : Measurable (fun ρ => hartreeKernel r ρ * f ρ) :=
    (hartreeKernel_uncurry_measurable.comp
      (measurable_const.prodMk measurable_id)).mul hf
  have hpowint := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hR
  have hint : IntegrableOn (fun ρ => hartreeKernel r ρ * f ρ) (Ioi R) := by
    apply (hpowint.const_mul C).mono' hmeas.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    rw [Real.norm_eq_abs]
    exact hpoint ρ hρ
  refine ⟨hint, ?_⟩
  have hI : (∫ ρ : ℝ in Ioi R, ρ ^ (-3 : ℝ)) = (R ^ 2)⁻¹ / 2 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hR]
    norm_num
  calc
    |∫ ρ in Ioi R, hartreeKernel r ρ * f ρ| ≤
        ∫ ρ in Ioi R, |hartreeKernel r ρ * f ρ| := abs_integral_le_integral_abs
    _ ≤ ∫ ρ in Ioi R, C * ρ ^ (-3 : ℝ) := by
      apply integral_mono_ae hint.abs (hpowint.const_mul C)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
      exact hpoint ρ hρ
    _ = C * ((R ^ 2)⁻¹ / 2) := by rw [integral_const_mul, hI]
    _ = _ := by
      dsimp [C]
      rw [abs_of_nonneg (show 0 ≤ 8 * Real.pi * hartreeKappa by
        unfold hartreeKappa
        positivity)]
      ring

end HBL.Modulation.AffineTail
