import HBL.KummerCompactFamily.ComplexAnalytic
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff
namespace HBL.Profile.Kummer

theorem annulusPhysicalParameterInverse_contDiffAt {z d : ℝ}
    (T : AnnulusSource z d →L[ℂ] AnnulusJet z d) (p : ℝ × ℝ)
    (hsmall : ‖frozenZeroCoeff p.1 p.2 - frozenZeroCoeff 0 0‖ * ‖T‖ ≤ (1 / 2 : ℝ)) :
    ContDiffAt ℝ ω (fun q : ℝ × ℝ => annulusParameterInverse T
      (frozenZeroCoeff q.1 q.2 - frozenZeroCoeff 0 0)) p := by
  let : CompactSpace (PhysicalAnnulus z d) := inferInstance
  have hδ : ContDiff ℝ ω (fun q : ℝ × ℝ => frozenZeroCoeff q.1 q.2 - frozenZeroCoeff 0 0) := by
    have hcast : ContDiff ℝ ω (fun x : ℝ => (x : ℂ)) := by
      simpa only [Complex.ofRealCLM_apply] using! Complex.ofRealCLM.contDiff (n := ω)
    have h1 := hcast.comp (contDiff_fst : ContDiff ℝ ω (fun q : ℝ × ℝ => q.1))
    have h2 := hcast.comp (contDiff_snd : ContDiff ℝ ω (fun q : ℝ × ℝ => q.2))
    unfold frozenZeroCoeff
    exact (h2.add (contDiff_const.mul (contDiff_const.sub h1))).sub contDiff_const
  have hi := (annulusParameterInverse_contDiffAt T _ hsmall).restrict_scalars ℝ
  simpa only [Function.comp_def] using! hi.comp p hδ.contDiffAt
end HBL.Profile.Kummer
