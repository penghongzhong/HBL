import HBL.KummerBoundaryUnique.HomogeneousCoordinates
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem kummer_homogeneous_boundary_zero {mu theta z eps d : ℝ}
    (K : LocalKummerPair mu theta z eps) (hd : 0 < d) (hde : d < eps)
    (u v : ℝ → ℂ)
    (hD : ∀ t ∈ Icc (-d) d,
      HasDerivAt u (v t) t ∧
      HasDerivAt v (-(frozenFirstCoeff (z+t) * v t + frozenZeroCoeff mu theta * u t)) t)
    (hp : u d * K.dpsi d - v d * K.psi d = 0)
    (hm : K.phi (-d) * v (-d) - K.dphi (-d) * u (-d) = 0) :
    ∀ t ∈ Icc (-d) d, u t = 0 ∧ v t = 0 := by
  let A := fun s => (u s * K.dpsi s - v s * K.psi s) / localAnnulusWronskian K s
  let B := fun s => (K.phi s * v s - K.dphi s * u s) / localAnnulusWronskian K s
  have hsub : Icc (-d) d ⊆ Icc (-eps) eps := by intro t ht; constructor <;> linarith [ht.1,ht.2]
  have hcoords := fun t ht => kummer_homogeneous_coordinates_derivative K u v t (hsub ht) (hD t ht).1 (hD t ht).2
  have hmemP : d ∈ Icc (-d) d := ⟨by linarith, le_rfl⟩
  have hmemM : -d ∈ Icc (-d) d := ⟨le_rfl, by linarith⟩
  intro t ht
  have hA : A t = 0 := by
    have h := (convex_Icc (-d) d).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := A) (f' := fun _ => (0 : ℂ)) (C := 0)
      (fun s hs => (hcoords s hs).1.hasDerivWithinAt) (by intro s hs; simp) hmemP ht
    have he : A d = 0 := by dsimp [A]; rw [hp, zero_div]
    simpa only [he, sub_zero, zero_mul, norm_le_zero_iff] using h
  have hB : B t = 0 := by
    have h := (convex_Icc (-d) d).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := B) (f' := fun _ => (0 : ℂ)) (C := 0)
      (fun s hs => (hcoords s hs).2.hasDerivWithinAt) (by intro s hs; simp) hmemM ht
    have he : B (-d) = 0 := by dsimp [B]; rw [hm, zero_div]
    simpa only [he, sub_zero, zero_mul, norm_le_zero_iff] using h
  have hn := K.wronskian_ne t (hsub ht)
  have hAz : u t * K.dpsi t - v t * K.psi t = 0 := (div_eq_zero_iff.mp hA).resolve_right hn
  have hBz : K.phi t * v t - K.dphi t * u t = 0 := (div_eq_zero_iff.mp hB).resolve_right hn
  constructor
  · apply (mul_eq_zero.mp (show u t * (K.phi t * K.dpsi t - K.dphi t * K.psi t) = 0 by
      linear_combination K.phi t * hAz + K.psi t * hBz)).resolve_right hn
  · apply (mul_eq_zero.mp (show v t * (K.phi t * K.dpsi t - K.dphi t * K.psi t) = 0 by
      linear_combination K.dphi t * hAz + K.dpsi t * hBz)).resolve_right hn
end HBL.Profile.Kummer
