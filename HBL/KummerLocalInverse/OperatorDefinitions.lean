import HBL.KummerLocalInverse.JetLinearity
import HBL.KummerLocalInverse.JetBound
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

variable {mu theta z eps : ℝ}

def localKummerJetLinear (K : LocalKummerPair mu theta z eps) (d : ℝ) (hd : 0 < d) (hde : d < eps) :
    C(PhysicalAnnulus z d, ℂ) →ₗ[ℂ] C(PhysicalAnnulus z d, ℂ × ℂ) where
  toFun := localKummerJet K d hd hde
  map_add' F G := by simpa only [one_smul] using localKummerJet_add_smul K d hd hde F G 1
  map_smul' c F := by
    have hzero := localKummerJet_add_smul K d hd hde 0 0 1
    simp only [one_smul, add_zero] at hzero
    have hz : localKummerJet K d hd hde 0 = 0 := by
      exact add_left_cancel (show localKummerJet K d hd hde 0 + localKummerJet K d hd hde 0 =
        localKummerJet K d hd hde 0 + 0 by simpa only [add_zero] using hzero.symm)
    simpa only [zero_add, hz, RingHom.id_apply] using localKummerJet_add_smul K d hd hde 0 F c

def localKummerJetOperator (K : LocalKummerPair mu theta z eps) (d C : ℝ)
    (hd : 0 < d) (hde : d < eps) (hC : 0 ≤ C) (hK : LocalKummerBound K C) :
    C(PhysicalAnnulus z d, ℂ) →L[ℂ] C(PhysicalAnnulus z d, ℂ × ℂ) :=
  (localKummerJetLinear K d hd hde).mkContinuous (4 * d * C ^ 3)
    (localKummerJet_norm_le K d C hd hde hC hK)
end HBL.Profile.Kummer
