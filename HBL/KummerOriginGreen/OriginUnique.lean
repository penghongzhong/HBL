import HBL.KummerOriginGreen.GreenTerminal
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set

namespace HBL.Profile.Kummer

/-- The origin-normalized physical basis yields two constant homogeneous coordinates.
This is the actual physical Kummer equation, with no abstract inverse assumption. -/
theorem originGreen_homogeneous_coordinates_derivative {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) {a b C : ℝ}
    (hK : OriginBasisOn K a b C) (u v : ℝ → ℂ)
    (r : ℝ) (hr : r ∈ Icc a b)
    (hu : HasDerivAt u (v r) r)
    (hv : HasDerivAt v
      (-(frozenFirstCoeff r * v r + frozenZeroCoeff mu theta * u r)) r) :
    HasDerivAt
      (fun s => (u s * originPhysicalSlope K.x K.dx s -
        v s * originPhysicalValue K.x s) / originGreenWronskian K s)
      0 r ∧
    HasDerivAt
      (fun s => (originPhysicalValue K.y s * v s -
        originPhysicalSlope K.y K.dy s * u s) / originGreenWronskian K s)
      0 r := by
  rcases hK r hr with ⟨hphi, hdphi, hpsi, hdpsi, _, hne, _, _, _, _, _⟩
  have hW : HasDerivAt (originGreenWronskian K)
      (-frozenFirstCoeff r * originGreenWronskian K r) r := by
    convert ((hphi.mul hdpsi).sub (hdphi.mul hpsi)) using 1
    · rfl
    · unfold originGreenWronskian
      ring
  constructor
  · convert ((hu.mul hdpsi).sub (hv.mul hpsi)).div hW hne using 1
    simp only [Pi.sub_apply, Pi.mul_apply]
    unfold originGreenWronskian
    ring
  · convert ((hphi.mul hv).sub (hdphi.mul hu)).div hW hne using 1
    simp only [Pi.sub_apply, Pi.mul_apply]
    unfold originGreenWronskian
    ring

/-- Zero source and the two ACTUAL separated outgoing conditions force zero.
Unlike the old LocalKummerPair theorem, this uses the basis normalized at r=0. -/
theorem originGreen_homogeneous_boundary_zero {mu theta R : ℝ}
    (K : OriginKummerPair mu theta R) {a b C : ℝ}
    (hK : OriginBasisOn K a b C) (hab : a < b)
    (u v : ℝ → ℂ)
    (hD : ∀ r ∈ Icc a b,
      HasDerivAt u (v r) r ∧
      HasDerivAt v
        (-(frozenFirstCoeff r * v r + frozenZeroCoeff mu theta * u r)) r)
    (hp : u b * originPhysicalSlope K.x K.dx b -
      v b * originPhysicalValue K.x b = 0)
    (hm : originPhysicalValue K.y a * v a -
      originPhysicalSlope K.y K.dy a * u a = 0) :
    ∀ r ∈ Icc a b, u r = 0 ∧ v r = 0 := by
  let A := fun s => (u s * originPhysicalSlope K.x K.dx s -
      v s * originPhysicalValue K.x s) / originGreenWronskian K s
  let B := fun s => (originPhysicalValue K.y s * v s -
      originPhysicalSlope K.y K.dy s * u s) / originGreenWronskian K s
  have hcoords := fun r hr =>
    originGreen_homogeneous_coordinates_derivative K hK u v r hr
      (hD r hr).1 (hD r hr).2
  have hmemP : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hmemM : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  intro r hr
  have hA : A r = 0 := by
    have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := A) (f' := fun _ => (0 : ℂ)) (C := 0)
      (fun s hs => (hcoords s hs).1.hasDerivWithinAt) (by intro s hs; simp)
      hmemP hr
    have he : A b = 0 := by dsimp [A]; rw [hp, zero_div]
    simpa only [he, sub_zero, zero_mul, norm_le_zero_iff] using h
  have hB : B r = 0 := by
    have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := B) (f' := fun _ => (0 : ℂ)) (C := 0)
      (fun s hs => (hcoords s hs).2.hasDerivWithinAt) (by intro s hs; simp)
      hmemM hr
    have he : B a = 0 := by dsimp [B]; rw [hm, zero_div]
    simpa only [he, sub_zero, zero_mul, norm_le_zero_iff] using h
  have hn := originGreenWronskian_ne K hK hr
  have hAz :
      u r * originPhysicalSlope K.x K.dx r -
        v r * originPhysicalValue K.x r = 0 :=
    (div_eq_zero_iff.mp hA).resolve_right hn
  have hBz :
      originPhysicalValue K.y r * v r -
        originPhysicalSlope K.y K.dy r * u r = 0 :=
    (div_eq_zero_iff.mp hB).resolve_right hn
  constructor
  · apply (mul_eq_zero.mp (show
      u r * (originPhysicalValue K.y r * originPhysicalSlope K.x K.dx r -
        originPhysicalSlope K.y K.dy r * originPhysicalValue K.x r) = 0 by
      linear_combination (originPhysicalValue K.y r) * hAz +
        (originPhysicalValue K.x r) * hBz)).resolve_right hn
  · apply (mul_eq_zero.mp (show
      v r * (originPhysicalValue K.y r * originPhysicalSlope K.x K.dx r -
        originPhysicalSlope K.y K.dy r * originPhysicalValue K.x r) = 0 by
      linear_combination (originPhysicalSlope K.y K.dy r) * hAz +
        (originPhysicalSlope K.x K.dx r) * hBz)).resolve_right hn

end HBL.Profile.Kummer
