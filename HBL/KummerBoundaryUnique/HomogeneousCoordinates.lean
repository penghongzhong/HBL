import HBL.KummerBoundaryUnique.Definitions
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

theorem kummer_homogeneous_coordinates_derivative {mu theta z eps : ℝ}
    (K : LocalKummerPair mu theta z eps) (u v : ℝ → ℂ)
    (t : ℝ) (ht : t ∈ Icc (-eps) eps)
    (hu : HasDerivAt u (v t) t)
    (hv : HasDerivAt v (-(frozenFirstCoeff (z+t) * v t + frozenZeroCoeff mu theta * u t)) t) :
    HasDerivAt (fun s => (u s * K.dpsi s - v s * K.psi s) / localAnnulusWronskian K s) 0 t ∧
    HasDerivAt (fun s => (K.phi s * v s - K.dphi s * u s) / localAnnulusWronskian K s) 0 t := by
  have hW : HasDerivAt (localAnnulusWronskian K)
      (-frozenFirstCoeff (z+t) * localAnnulusWronskian K t) t := by
    convert ((K.phi_hasDeriv t ht).mul (K.dpsi_hasDeriv t ht)).sub
      ((K.dphi_hasDeriv t ht).mul (K.psi_hasDeriv t ht)) using 1
    · rfl
    · unfold localAnnulusWronskian
      ring
  have hne : localAnnulusWronskian K t ≠ 0 := K.wronskian_ne t ht
  constructor
  · convert ((hu.mul (K.dpsi_hasDeriv t ht)).sub (hv.mul (K.psi_hasDeriv t ht))).div hW hne using 1
    simp only [Pi.sub_apply, Pi.mul_apply]
    unfold localAnnulusWronskian
    ring
  · convert (((K.phi_hasDeriv t ht).mul hv).sub ((K.dphi_hasDeriv t ht).mul hu)).div hW hne using 1
    simp only [Pi.sub_apply, Pi.mul_apply]
    unfold localAnnulusWronskian
    ring
end HBL.Profile.Kummer
