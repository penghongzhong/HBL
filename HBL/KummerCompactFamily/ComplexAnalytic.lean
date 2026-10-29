import HBL.KummerParameterInverse.BlockUnit
import Mathlib.Analysis.Calculus.ContDiff.Operations
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff
namespace HBL.Profile.Kummer

theorem annulusParameterInverse_contDiffAt {z d : ℝ}
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) (δ : ℂ)
    (hsmall : ‖δ‖ * ‖T‖ ≤ (1 / 2 : ℝ)) :
    ContDiffAt ℂ ω (annulusParameterInverse T) δ := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  let hu := annulusParameterBlock_isUnit T δ hsmall
  have hi := contDiffAt_ringInverse ℂ (n := ω) (R := AnnulusSource z d →L[ℂ] AnnulusSource z d) hu.unit
  rw [hu.unit_spec] at hi
  have hb : ContDiff ℂ ω (annulusParameterBlock T) := by
    unfold annulusParameterBlock
    fun_prop
  have hr : ContDiffAt ℂ ω (annulusParameterResolvent T) δ := by
    unfold annulusParameterResolvent
    simpa only [Function.comp_def] using! hi.comp δ hb.contDiffAt
  unfold annulusParameterInverse
  exact (contDiffAt_const (c := T) (x := δ) (𝕜 := ℂ) (n := ω)).clm_comp hr
end HBL.Profile.Kummer
