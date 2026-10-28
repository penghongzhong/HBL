import HBL.KummerLocalInverse.PhysicalDefinitions
import HBL.KummerLocalInverse.C1Bound
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem physicalLocalKummer_norm_le
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps) (d C M : ℝ)
    (hde : d ≤ eps) (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : LocalKummerBound K C)
    (F : ℝ → ℂ) (hF : ∀ r ∈ Icc (z - d) (z + d), ‖F r‖ ≤ M)
    {r : ℝ} (hr : r ∈ Icc (z - d) (z + d)) :
    ‖physicalLocalKummerValue K d F r‖ + ‖physicalLocalKummerDeriv K d F r‖ ≤ (4 * d * C ^ 3) * M := by
  have hsub : Icc (-d) d ⊆ Icc (-eps) eps := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hFs (t : ℝ) (ht : t ∈ Icc (-d) d) : ‖F (z + t)‖ ≤ M :=
    hF (z + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have ht : r - z ∈ Icc (-d) d := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have h := localAnnulus_value_deriv_norm_le K (-d) d C M hC hM hK hsub _ hFs ht
  unfold physicalLocalKummerValue physicalLocalKummerDeriv
  calc
    _ ≤ _ := h
    _ = _ := by ring
end HBL.Profile.Kummer
