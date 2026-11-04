import HBL.TypeIIDynamicSelection.ActualKummerUniformSameSourceTransfer
import Mathlib.Tactic

/-!
The actual unit-slope impulse kernel, not a bound on a freely normalized
fundamental pair. It uses the original nonzero physical Wronskian at the
source point. The accepted shear theorem is reused at every source radius;
this is the input needed to control the NONHOMOGENEOUS Green contribution,
which does not appear in the earlier same-source difference estimate.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

def actualKummerImpulseValue
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (s t : ℝ) : ℂ :=
  actualKummerMatchPhi K s 0 1 * K.phi t +
    actualKummerMatchPsi K s 0 1 * K.psi t

def actualKummerImpulseSlope
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (s t : ℝ) : ℂ :=
  actualKummerMatchPhi K s 0 1 * K.dphi t +
    actualKummerMatchPsi K s 0 1 * K.dpsi t

/-- A genuine unit-slope impulse at z+s propagates with a constant
independent of the moving annulus and of the pair normalization. -/
theorem actual_Kummer_impulse_scaled_uniform
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (d s : ℝ) (hd : 0 < d) (hde : d < eps)
    (hRatio : z + d ≤ 2 * (z - d)) (hs : s ∈ Icc (-d) d) :
    max ‖actualKummerImpulseValue K s d‖
      ((z + d) * ‖actualKummerImpulseSlope K s d‖) ≤
      actualKummerUniformTransferConstant (frozenZeroCoeff mu theta) * (z + s) := by
  let ap := actualKummerMatchPhi K s 0 1
  let cp := actualKummerMatchPsi K s 0 1
  let h : ℝ → ℂ := fun r => ap * K.phi (r-z) + cp * K.psi (r-z)
  let dh : ℝ → ℂ := fun r => ap * K.dphi (r-z) + cp * K.dpsi (r-z)
  have hsK : s ∈ Icc (-eps) eps := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hr0 : 0 < z + s := K.radial_pos s hsK
  have h01 : z + s ≤ z + d := by linarith [hs.2]
  have hRat : z + d ≤ 2 * (z + s) := by linarith [hs.1]
  have ht (r : ℝ) (hr : r ∈ Icc (z+s) (z+d)) :
      r-z ∈ Icc (-eps) eps :=
    ⟨by linarith [hr.1, hs.1], by linarith [hr.2]⟩
  have hDer (r : ℝ) (hr : r ∈ Icc (z+s) (z+d)) :
      HasDerivAt h (dh r) r := by
    have hshift : HasDerivAt (fun x : ℝ => x-z) 1 r := (hasDerivAt_id r).sub_const z
    have hp : HasDerivAt (fun x => K.phi (x-z)) (K.dphi (r-z)) r := by
      simpa only [Function.comp_def, one_smul] using
        (K.phi_hasDeriv (r-z) (ht r hr)).scomp r hshift
    have hq : HasDerivAt (fun x => K.psi (x-z)) (K.dpsi (r-z)) r := by
      simpa only [Function.comp_def, one_smul] using
        (K.psi_hasDeriv (r-z) (ht r hr)).scomp r hshift
    exact (hp.const_mul ap).add (hq.const_mul cp)
  have hDer2 (r : ℝ) (hr : r ∈ Icc (z+s) (z+d)) :
      HasDerivAt dh
        (-((2 / (r : ℂ) + Complex.I * (r : ℂ) / 2) * dh r +
          frozenZeroCoeff mu theta * h r)) r := by
    have hshift : HasDerivAt (fun x : ℝ => x-z) 1 r := (hasDerivAt_id r).sub_const z
    have hp := (K.dphi_hasDeriv (r-z) (ht r hr)).scomp r hshift
    have hq := (K.dpsi_hasDeriv (r-z) (ht r hr)).scomp r hshift
    rw [show z + (r-z) = r by ring] at hp hq
    simp only [Function.comp_def, one_smul] at hp hq
    have H := (hp.const_mul ap).add (hq.const_mul cp)
    convert H using 1
    dsimp [h, dh, frozenFirstCoeff]
    ring
  have hLeft := actual_Kummer_Wronskian_two_Cauchy_jets_match K s hsK 0 1
  have hh0 : h (z+s) = 0 := by
    dsimp [h]
    rw [show z+s-z = s by ring]
    exact hLeft.1
  have hd0 : dh (z+s) = 1 := by
    dsimp [dh]
    rw [show z+s-z = s by ring]
    exact hLeft.2
  have hh1 : h (z+d) = actualKummerImpulseValue K s d := by
    dsimp [h, actualKummerImpulseValue, ap, cp]
    rw [show z+d-z = d by ring]
  have hd1 : dh (z+d) = actualKummerImpulseSlope K s d := by
    dsimp [dh, actualKummerImpulseSlope, ap, cp]
    rw [show z+d-z = d by ring]
  have hBound := actual_Kummer_homogeneous_dyadic_uniform_bound
    (frozenZeroCoeff mu theta) h dh (z+s) (z+d)
    hr0 h01 hRat hDer hDer2
  simpa only [actualKummerScaledJet, hh0, hd0, hh1, hd1,
    norm_zero, norm_one, mul_one, max_eq_right hr0.le] using hBound

end HBL.TypeIIDynamicSelection
