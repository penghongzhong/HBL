import HBL.AffineTailCharge
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# One minimal-weight cluster

This file is a single Lean terminal for the manuscript environment
`prop:one-layer-stage3`.  It does not introduce a new counted environment.

The inner threshold charge is constructed from the already verified
AffineTail charge formula.  The Kummer and remote regional solvers enter as
previous regional right inverses (represented below by continuous linear
equivalences); this is exactly how the manuscript uses the preceding
variation-of-parameters and finite triangular-block lemmas.  The theorem
then proves, rather than assumes, simultaneous cancellation of all three
regional sources and the quantitative positive gain of every generated
error family.
-/

noncomputable section
set_option autoImplicit false

open HBL.Modulation.AffineTail
open scoped Topology

namespace HBL.ProfileLayer

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A normalized inner inverse after the scalar threshold compatibility
condition has been imposed.  This is the exact Fredholm interface supplied
by the earlier half-line inverse. -/
structure ThresholdNormalizedInverse (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  H : E →L[ℝ] E
  ell : E →L[ℝ] ℝ
  gauge : E →L[ℝ] ℝ
  affineModel : E
  resonanceLimit : ℝ
  resonanceLimit_ne : resonanceLimit ≠ 0
  affine_pairing :
    ell (H affineModel) = -resonanceLimit
  solveCompatible :
    {f : E // ell f = 0} → E
  solveCompatible_eq :
    ∀ f : {f : E // ell f = 0},
      H (solveCompatible f) = f.1
  solveCompatible_gauge :
    ∀ f : {f : E // ell f = 0},
      gauge (solveCompatible f) = 0
  solveCompatible_unique :
    ∀ f : {f : E // ell f = 0}, ∀ x : E,
      H x = f.1 → gauge x = 0 → x = solveCompatible f

/-- The unique affine threshold charge for an arbitrary inner source. -/
def innerCharge (C : ThresholdNormalizedInverse E) (F : E) : ℝ :=
  charge C.ell C.resonanceLimit F

/-- Source after removing the unique affine compatibility obstruction. -/
def compatibleInnerSource (C : ThresholdNormalizedInverse E) (F : E) : E :=
  F - innerCharge C F • C.H C.affineModel

theorem compatibleInnerSource_pairing_zero
    (C : ThresholdNormalizedInverse E) (F : E) :
    C.ell (compatibleInnerSource C F) = 0 := by
  exact charge_annihilates C.ell C.resonanceLimit C.resonanceLimit_ne
    F (C.H C.affineModel) C.affine_pairing

/-- Canonical inner solution: normalized Fredholm solution plus its forced
affine tail. -/
def innerSolve (C : ThresholdNormalizedInverse E) (F : E) : E :=
  C.solveCompatible
      ⟨compatibleInnerSource C F,
        compatibleInnerSource_pairing_zero C F⟩
    + innerCharge C F • C.affineModel

theorem innerSolve_eq_source
    (C : ThresholdNormalizedInverse E) (F : E) :
    C.H (innerSolve C F) = F := by
  rw [innerSolve, map_add, C.solveCompatible_eq, map_smul]
  unfold compatibleInnerSource
  simp only [neg_one_smul]
  abel

/-- The affine coefficient itself is unique. -/
theorem innerCharge_unique
    (C : ThresholdNormalizedInverse E) (F : E) (a : ℝ)
    (ha : C.ell (F - a • C.H C.affineModel) = 0) :
    a = innerCharge C F := by
  exact charge_unique C.ell C.resonanceLimit C.resonanceLimit_ne
    F (C.H C.affineModel) C.affine_pairing a ha

/-- The positive gain used in the manuscript after one complete cluster. -/
def kappaProf
    (delta epsilonFlat betaMinus rhoStar : ℝ) : ℝ :=
  min delta
    (min epsilonFlat
      (min (2 * betaMinus - 1)
        (min (1 / 2 : ℝ) rhoStar)))

theorem kappaProf_pos
    {delta epsilonFlat betaMinus rhoStar : ℝ}
    (hdelta : 0 < delta)
    (hflat : 0 < epsilonFlat)
    (hbeta : 1 / 2 < betaMinus)
    (hrho : 0 < rhoStar) :
    0 < kappaProf delta epsilonFlat betaMinus rhoStar := by
  have hb : 0 < 2 * betaMinus - 1 := by linarith
  unfold kappaProf
  exact lt_min hdelta
    (lt_min hflat
      (lt_min hb
        (lt_min (by norm_num) hrho)))

theorem kappaProf_le_delta
    (delta epsilonFlat betaMinus rhoStar : ℝ) :
    kappaProf delta epsilonFlat betaMinus rhoStar ≤ delta := by
  exact min_le_left _ _

theorem kappaProf_le_flat
    (delta epsilonFlat betaMinus rhoStar : ℝ) :
    kappaProf delta epsilonFlat betaMinus rhoStar ≤ epsilonFlat := by
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem kappaProf_le_slow
    (delta epsilonFlat betaMinus rhoStar : ℝ) :
    kappaProf delta epsilonFlat betaMinus rhoStar ≤ 2 * betaMinus - 1 := by
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))

theorem kappaProf_le_frobenius
    (delta epsilonFlat betaMinus rhoStar : ℝ) :
    kappaProf delta epsilonFlat betaMinus rhoStar ≤ (1 / 2 : ℝ) := by
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))

theorem kappaProf_le_cutoff
    (delta epsilonFlat betaMinus rhoStar : ℝ) :
    kappaProf delta epsilonFlat betaMinus rhoStar ≤ rhoStar := by
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))

/-- Exact regional response of one frozen weight layer.  The two threshold
channels are separate, while the Kummer and remote blocks are genuine
linear equivalences from the preceding regional inverse lemmas. -/
def assembledLayerResidual
    (Cplus Cminus : ThresholdNormalizedInverse E)
    (Kummer Remote : E ≃L[ℝ] E)
    (Fplus Fminus FK FR tangent
      dplus dminus dK dR : E) : E :=
  tangent + Fplus + Fminus + FK + FR
    + Cplus.H dplus + Cminus.H dminus
    + Kummer dK + Remote dR

/-- One complete minimal-weight cluster is removed at once.  The only
uncancelled coefficient is the parameter-tangent term.  In particular,
the affine charges are constructed from the sources and are not assumed. -/
theorem minimalWeightCluster_cancellation
    (Cplus Cminus : ThresholdNormalizedInverse E)
    (Kummer Remote : E ≃L[ℝ] E)
    (Fplus Fminus FK FR tangent : E) :
    let dplus := -innerSolve Cplus Fplus
    let dminus := -innerSolve Cminus Fminus
    let dK := -(Kummer.symm FK)
    let dR := -(Remote.symm FR)
    assembledLayerResidual Cplus Cminus Kummer Remote
      Fplus Fminus FK FR tangent dplus dminus dK dR = tangent := by
  dsimp only
  unfold assembledLayerResidual
  rw [map_neg, innerSolve_eq_source, map_neg, innerSolve_eq_source,
    map_neg, Kummer.apply_symm_apply, map_neg, Remote.apply_symm_apply]
  abel

/-- Quantitative bookkeeping for every possible next source listed in the
manuscript: parameter variation, flat radiation, quadratic slow tail,
next Frobenius layer, and moving cutoff. -/
theorem minimalWeightCluster_gain
    {rho delta epsilonFlat betaMinus rhoStar : ℝ}
    (wParam wFlat wSlow wFrob wCutoff : ℝ)
    (hParam : rho + delta ≤ wParam)
    (hFlat : rho + epsilonFlat ≤ wFlat)
    (hSlow : rho + (2 * betaMinus - 1) ≤ wSlow)
    (hFrob : rho + (1 / 2 : ℝ) ≤ wFrob)
    (hCutoff : rho + rhoStar ≤ wCutoff) :
    let k := kappaProf delta epsilonFlat betaMinus rhoStar
    rho + k ≤ wParam ∧
    rho + k ≤ wFlat ∧
    rho + k ≤ wSlow ∧
    rho + k ≤ wFrob ∧
    rho + k ≤ wCutoff := by
  dsimp only
  constructor
  · linarith [kappaProf_le_delta delta epsilonFlat betaMinus rhoStar]
  constructor
  · linarith [kappaProf_le_flat delta epsilonFlat betaMinus rhoStar]
  constructor
  · linarith [kappaProf_le_slow delta epsilonFlat betaMinus rhoStar]
  constructor
  · linarith [kappaProf_le_frobenius delta epsilonFlat betaMinus rhoStar]
  · linarith [kappaProf_le_cutoff delta epsilonFlat betaMinus rhoStar]

/-- Single manuscript terminal for `prop:one-layer-stage3`: simultaneous
regional cancellation, uniqueness of both real threshold charges, and a
strictly positive common gain.  No new numbered environment is introduced. -/
theorem oneMinimalWeightCluster_certified
    (Cplus Cminus : ThresholdNormalizedInverse E)
    (Kummer Remote : E ≃L[ℝ] E)
    (Fplus Fminus FK FR tangent : E)
    {rho N delta epsilonFlat betaMinus rhoStar : ℝ}
    (hrhoN : rho < N)
    (hdelta : 0 < delta)
    (hflat : 0 < epsilonFlat)
    (hbeta : 1 / 2 < betaMinus)
    (hrhoStar : 0 < rhoStar)
    (wParam wFlat wSlow wFrob wCutoff : ℝ)
    (hParam : rho + delta ≤ wParam)
    (hFlat : rho + epsilonFlat ≤ wFlat)
    (hSlow : rho + (2 * betaMinus - 1) ≤ wSlow)
    (hFrob : rho + (1 / 2 : ℝ) ≤ wFrob)
    (hCutoff : rho + rhoStar ≤ wCutoff) :
    ∃ (aPlus aMinus : ℝ) (dPlus dMinus dK dR : E) (k : ℝ),
      aPlus = innerCharge Cplus Fplus ∧
      aMinus = innerCharge Cminus Fminus ∧
      dPlus = -innerSolve Cplus Fplus ∧
      dMinus = -innerSolve Cminus Fminus ∧
      dK = -(Kummer.symm FK) ∧
      dR = -(Remote.symm FR) ∧
      k = kappaProf delta epsilonFlat betaMinus rhoStar ∧
      0 < k ∧ rho < N ∧
      assembledLayerResidual Cplus Cminus Kummer Remote
        Fplus Fminus FK FR tangent dPlus dMinus dK dR = tangent ∧
      rho + k ≤ wParam ∧
      rho + k ≤ wFlat ∧
      rho + k ≤ wSlow ∧
      rho + k ≤ wFrob ∧
      rho + k ≤ wCutoff := by
  let ap := innerCharge Cplus Fplus
  let am := innerCharge Cminus Fminus
  let dp := -innerSolve Cplus Fplus
  let dm := -innerSolve Cminus Fminus
  let dk := -(Kummer.symm FK)
  let dr := -(Remote.symm FR)
  let k := kappaProf delta epsilonFlat betaMinus rhoStar
  refine ⟨ap, am, dp, dm, dk, dr, k, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    kappaProf_pos hdelta hflat hbeta hrhoStar, hrhoN, ?_, ?_⟩
  · exact minimalWeightCluster_cancellation Cplus Cminus Kummer Remote
      Fplus Fminus FK FR tangent
  · exact minimalWeightCluster_gain wParam wFlat wSlow wFrob wCutoff
      hParam hFlat hSlow hFrob hCutoff

#print axioms compatibleInnerSource_pairing_zero
#print axioms innerSolve_eq_source
#print axioms innerCharge_unique
#print axioms kappaProf_pos
#print axioms minimalWeightCluster_cancellation
#print axioms minimalWeightCluster_gain
#print axioms oneMinimalWeightCluster_certified

end HBL.ProfileLayer
