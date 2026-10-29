import HBL.KummerPrescribedAnnulus.ActualIVP
import HBL.KummerPrescribedAnnulus.Wronskian
import HBL.KummerLocalInverse.Definitions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace HBL.Profile.Kummer

/-- The normalized actual Kummer pair exists on every prescribed closed
positive annulus, with a finite bound there. The radius is an input. -/
theorem exists_prescribed_bounded_kummer_pair
    (mu theta z eps : ℝ) (heps : 0 < eps) (hz : eps < z) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : LocalKummerPair mu theta z eps, LocalKummerBound K C := by
  let a := (z - eps) / 2
  let b := z + eps + 1
  have ha : 0 < a := by dsimp [a]; linarith
  have hab : a ≤ b := by dsimp [a, b]; linarith
  obtain ⟨u, v, hu₀, hv₀, huv⟩ := exists_actual_kummer_prescribed_ivp
    mu theta a b ha hab 1 0
  obtain ⟨p, q, hp₀, hq₀, hpq⟩ := exists_actual_kummer_prescribed_ivp
    mu theta a b ha hab 0 1
  have hW := kummer_wronskian_ne_on_prescribed_interval mu theta a b ha u v p q
    (fun t ht => (huv t ht).1) (fun t ht => (huv t ht).2)
    (fun t ht => (hpq t ht).1) (fun t ht => (hpq t ht).2)
    (by simp [hu₀, hv₀, hp₀, hq₀])
  have hr (t : ℝ) (ht : t ∈ Icc (-eps) eps) : z + t ∈ Ioo a b := by
    dsimp [a, b]
    constructor <;> linarith [ht.1, ht.2]
  have hzmem : z ∈ Icc a b := by dsimp [a, b]; constructor <;> linarith
  let w := u z * q z - v z * p z
  have hw : w ≠ 0 := hW z hzmem
  have hd (t : ℝ) (ht : t ∈ Icc (-eps) eps) :
      HasDerivAt (fun s => u (z + s)) (v (z + t)) t ∧
      HasDerivAt (fun s => v (z + s))
        (-(frozenFirstCoeff (z + t) * v (z + t) + frozenZeroCoeff mu theta * u (z + t))) t ∧
      HasDerivAt (fun s => p (z + s)) (q (z + t)) t ∧
      HasDerivAt (fun s => q (z + s))
        (-(frozenFirstCoeff (z + t) * q (z + t) + frozenZeroCoeff mu theta * p (z + t))) t := by
    have hm := hr t ht
    have hn := Icc_mem_nhds hm.1 hm.2
    have hs : HasDerivAt (fun s : ℝ => z + s) 1 t := by
      simpa only [id_eq] using (hasDerivAt_id t).const_add z
    exact ⟨by simpa only [Function.comp_def, one_smul] using! ((huv _ (Ioo_subset_Icc_self hm)).1.hasDerivAt hn).scomp t hs,
      by simpa only [Function.comp_def, one_smul] using! ((huv _ (Ioo_subset_Icc_self hm)).2.hasDerivAt hn).scomp t hs,
      by simpa only [Function.comp_def, one_smul] using! ((hpq _ (Ioo_subset_Icc_self hm)).1.hasDerivAt hn).scomp t hs,
      by simpa only [Function.comp_def, one_smul] using! ((hpq _ (Ioo_subset_Icc_self hm)).2.hasDerivAt hn).scomp t hs⟩
  let K : LocalKummerPair mu theta z eps := {
    phi := fun t => (q z * u (z + t) - v z * p (z + t)) / w
    dphi := fun t => (q z * v (z + t) - v z * q (z + t)) / w
    psi := fun t => (u z * p (z + t) - p z * u (z + t)) / w
    dpsi := fun t => (u z * q (z + t) - p z * v (z + t)) / w
    radial_pos := fun t ht => by linarith [ht.1]
    phi_hasDeriv := fun t ht =>
      (((hd t ht).1.const_mul (q z)).sub ((hd t ht).2.2.1.const_mul (v z))).div_const w
    psi_hasDeriv := fun t ht =>
      (((hd t ht).2.2.1.const_mul (u z)).sub ((hd t ht).1.const_mul (p z))).div_const w
    dphi_hasDeriv := by
      intro t ht
      convert (((hd t ht).2.1.const_mul (q z)).sub
        ((hd t ht).2.2.2.const_mul (v z))).div_const w using 1
      ring
    dpsi_hasDeriv := by
      intro t ht
      convert (((hd t ht).2.2.2.const_mul (u z)).sub
        ((hd t ht).2.1.const_mul (p z))).div_const w using 1
      ring
    wronskian_ne := by
      intro t ht
      have heq :
          (q z * u (z + t) - v z * p (z + t)) / w *
            ((u z * q (z + t) - p z * v (z + t)) / w) -
          (q z * v (z + t) - v z * q (z + t)) / w *
            ((u z * p (z + t) - p z * u (z + t)) / w) =
          (u (z + t) * q (z + t) - v (z + t) * p (z + t)) / w := by
        field_simp
        dsimp [w]
        ring
      rw [heq]
      exact div_ne_zero (hW _ (Ioo_subset_Icc_self (hr t ht))) hw
    phi_zero := by
      simp only [add_zero]
      apply (div_eq_one_iff_eq hw).2
      dsimp [w]
      ring
    dphi_zero := by simp [mul_comm]
    psi_zero := by simp [mul_comm]
    dpsi_zero := by
      simp only [add_zero]
      apply (div_eq_one_iff_eq hw).2
      dsimp [w]
      ring }
  have hc : ContinuousOn
      (fun t => (((K.phi t, K.dphi t), (K.psi t, K.dpsi t)),
        (localAnnulusWronskian K t)⁻¹)) (Icc (-eps) eps) := by
    intro t ht
    have h₁ := (K.phi_hasDeriv t ht).continuousAt
    have h₂ := (K.dphi_hasDeriv t ht).continuousAt
    have h₃ := (K.psi_hasDeriv t ht).continuousAt
    have h₄ := (K.dpsi_hasDeriv t ht).continuousAt
    exact (((h₁.prodMk h₂).prodMk (h₃.prodMk h₄)).prodMk
      (((h₁.mul h₄).sub (h₂.mul h₃)).inv₀ (K.wronskian_ne t ht))).continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C₀ 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), K, ?_⟩
  intro t ht
  have h := (hC₀ t ht).trans (le_max_left C₀ 1)
  simpa only [Prod.norm_def, max_le_iff, and_assoc] using h
end HBL.Profile.Kummer
