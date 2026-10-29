import HBL.KummerPrescribedAnnulus.LinearIVP
import HBL.KummerFrozenAnnulus
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
set_option autoImplicit false
namespace HBL.Profile.Kummer

abbrev RealKummerJet := Fin 4 → ℝ

def realJetEntry (i j : Fin 4) : RealKummerJet →L[ℝ] RealKummerJet :=
  (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => ℝ) i).comp
    (ContinuousLinearMap.proj j)

def realKummerOperator (mu theta t : ℝ) : RealKummerJet →L[ℝ] RealKummerJet :=
  realJetEntry 0 2 + realJetEntry 1 3 -
    theta • (realJetEntry 2 0 + realJetEntry 3 1) +
    (1 / 4 - mu) • (realJetEntry 2 1 - realJetEntry 3 0) -
    (2 / t) • (realJetEntry 2 2 + realJetEntry 3 3) +
    (t / 2) • (realJetEntry 2 3 - realJetEntry 3 2)

def realJetValue : RealKummerJet →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj 0) +
    Complex.I • Complex.ofRealCLM.comp (ContinuousLinearMap.proj 1)

def realJetSlope : RealKummerJet →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj 2) +
    Complex.I • Complex.ofRealCLM.comp (ContinuousLinearMap.proj 3)

def encodeKummerJet (u v : ℂ) : RealKummerJet := ![u.re, u.im, v.re, v.im]
end HBL.Profile.Kummer
