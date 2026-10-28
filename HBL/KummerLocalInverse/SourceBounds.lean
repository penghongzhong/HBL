import HBL.KummerLocalInverse.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem localAnnulus_source_norm_le
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : LocalKummerBound K C)
    (F : ℝ → ℂ) {t : ℝ} (ht : t ∈ Icc (-eps) eps) (hF : ‖F t‖ ≤ M) :
    ‖localAnnulusSourceA K F t‖ ≤ C ^ 2 * M ∧ ‖localAnnulusSourceB K F t‖ ≤ C ^ 2 * M := by
  have hb := hK t ht
  have hbound (p : ℂ) (hp : ‖p‖ ≤ C) : ‖p * F t / localAnnulusWronskian K t‖ ≤ C ^ 2 * M := by
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    calc
      _ ≤ C * M * C := mul_le_mul (mul_le_mul hp hF (norm_nonneg _) hC)
        hb.2.2.2.2 (by positivity) (mul_nonneg hC hM)
      _ = _ := by ring
  exact ⟨hbound _ hb.2.2.1, hbound _ hb.1⟩
end HBL.Profile.Kummer
