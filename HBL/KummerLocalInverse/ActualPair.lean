import HBL.KummerLocalInverse.Definitions
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

theorem exists_actual_bounded_localKummerPair (mu theta z : ℝ) (hz : 0 < z) :
    ∃ eps C : ℝ, 0 < eps ∧ 0 < C ∧
      ∃ K : LocalKummerPair mu theta z eps, LocalKummerBound K C := by
  obtain ⟨X, Y, eps, C, heps, hC, hX0, hY0, hp⟩ :=
    exists_uniformlyBounded_localPhysicalKummerPair mu theta z hz
  let K : LocalKummerPair mu theta z eps := {
    phi := fun t => (X t).2.1
    psi := fun t => (Y t).2.1
    dphi := fun t => (X t).2.2
    dpsi := fun t => (Y t).2.2
    radial_pos := fun t ht => (hp t ht).2.2.1
    phi_hasDeriv := fun t ht => (hp t ht).2.2.2.1
    dphi_hasDeriv := fun t ht => (hp t ht).2.2.2.2.1
    psi_hasDeriv := fun t ht => (hp t ht).2.2.2.2.2.1
    dpsi_hasDeriv := fun t ht => (hp t ht).2.2.2.2.2.2.1
    wronskian_ne := fun t ht => (hp t ht).2.2.2.2.2.2.2.1
    phi_zero := by rw [hX0]
    dphi_zero := by rw [hX0]
    psi_zero := by rw [hY0]
    dpsi_zero := by rw [hY0] }
  refine ⟨eps, C, heps, hC, K, ?_⟩
  intro t ht
  have hb := (hp t ht).2.2.2.2.2.2.2.2
  simp only [localKummerBoundVector, Prod.norm_def, max_le_iff] at hb
  exact ⟨hb.1.1.1, hb.1.1.2, hb.1.2.1, hb.1.2.2, hb.2⟩
end HBL.Profile.Kummer
