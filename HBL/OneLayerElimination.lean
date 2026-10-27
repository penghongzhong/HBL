import HBL.AffineTailCharge
import Mathlib.Tactic

/-!
# One minimal weight cluster: structural elimination

This file targets the existing manuscript environment
`prop:one-layer-stage3`; it does not introduce a new numbered R-environment.

The novel bookkeeping is formalized natively:
* the two affine threshold charges are forced uniquely;
* the four regional source components are removed exactly by their normalized
  right inverses;
* every newly generated term is classified by one of the five mechanisms
  appearing in the manuscript proof, and therefore gains at least
  `kappaProfile`.

The standard analytic regional solvers (the Kummer variation-of-parameters
inverse and the finite remote block inverse) are exposed as explicit
right-inverse packages.  This interface does not assume the one-layer
conclusion or the positive gain.
-/

noncomputable section
set_option autoImplicit false

namespace HBL.Profile.OneLayer

open HBL.Modulation.AffineTail

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A normalized threshold solver.  The affine correction direction is kept
separate from the normalized Fredholm solution. -/
structure ThresholdSolver where
  op : E →L[ℝ] E
  ell : E →L[ℝ] ℝ
  normalize : E →L[ℝ] ℝ
  c : ℝ
  c_ne : c ≠ 0
  qCorr : E
  aff_pair : ell (op qCorr) = -c
  solve : (f : E) → ell f = 0 → E
  solve_eq : ∀ (f : E) (hf : ell f = 0), op (solve f hf) = f
  solve_normalized : ∀ (f : E) (hf : ell f = 0), normalize (solve f hf) = 0
  solve_unique : ∀ (f x : E) (hf : ell f = 0),
    op x = f → normalize x = 0 → x = solve f hf

/-- A standard normalized right inverse for a region with no threshold charge. -/
structure RegionalSolver where
  op : E →L[ℝ] E
  solve : E → E
  solve_eq : ∀ f, op (solve f) = f
  solve_unique : ∀ f x, op x = f → x = solve f

/-- The unique affine charge attached to a source. -/
def thresholdCharge (S : ThresholdSolver (E := E)) (F : E) : ℝ :=
  charge S.ell S.c F

/-- Source after removing its unique threshold obstruction. -/
def compatibleSource (S : ThresholdSolver (E := E)) (F : E) : E :=
  F - thresholdCharge S F • S.op S.qCorr

theorem compatibleSource_orthogonal (S : ThresholdSolver (E := E)) (F : E) :
    S.ell (compatibleSource S F) = 0 := by
  exact charge_annihilates S.ell S.c S.c_ne F (S.op S.qCorr) S.aff_pair

/-- Normalized Fredholm part of the threshold correction. -/
def normalizedCorrection (S : ThresholdSolver (E := E)) (F : E) : E :=
  S.solve (compatibleSource S F) (compatibleSource_orthogonal S F)

/-- Full correction, including the uniquely forced affine tail. -/
def fullThresholdCorrection (S : ThresholdSolver (E := E)) (F : E) : E :=
  normalizedCorrection S F + thresholdCharge S F • S.qCorr

theorem fullThresholdCorrection_solves
    (S : ThresholdSolver (E := E)) (F : E) :
    S.op (fullThresholdCorrection S F) = F := by
  have hnorm :
      S.op (normalizedCorrection S F) = compatibleSource S F := by
    exact S.solve_eq (compatibleSource S F) (compatibleSource_orthogonal S F)
  rw [fullThresholdCorrection, map_add, map_smul, hnorm]
  unfold compatibleSource
  abel

theorem normalizedCorrection_normalized
    (S : ThresholdSolver (E := E)) (F : E) :
    S.normalize (normalizedCorrection S F) = 0 := by
  exact S.solve_normalized _ _

/-- The affine charge and the normalized Fredholm part are jointly unique. -/
theorem threshold_pair_unique
    (S : ThresholdSolver (E := E)) (F : E)
    (a : ℝ) (h : E)
    (ha : S.ell (F - a • S.op S.qCorr) = 0)
    (hh : S.op h = F - a • S.op S.qCorr)
    (hn : S.normalize h = 0) :
    a = thresholdCharge S F ∧ h = normalizedCorrection S F := by
  have ha' : a = thresholdCharge S F := by
    exact charge_unique S.ell S.c S.c_ne F (S.op S.qCorr)
      S.aff_pair a ha
  subst a
  constructor
  · rfl
  · apply S.solve_unique (compatibleSource S F) h
      (compatibleSource_orthogonal S F)
    · simpa [compatibleSource, thresholdCharge] using hh
    · exact hn

/-- The four source components of one weight cluster:
two threshold channels, one Kummer channel, and one remote channel. -/
structure LayerSource where
  plus : E
  minus : E
  kummer : E
  remote : E

/-- Corrections and the two real affine charges produced at one weight. -/
structure LayerCorrection where
  plus : E
  minus : E
  kummer : E
  remote : E
  chargePlus : ℝ
  chargeMinus : ℝ

def solveLayer
    (Splus Sminus : ThresholdSolver (E := E))
    (SK SR : RegionalSolver (E := E))
    (F : LayerSource (E := E)) : LayerCorrection (E := E) where
  plus := fullThresholdCorrection Splus F.plus
  minus := fullThresholdCorrection Sminus F.minus
  kummer := SK.solve F.kummer
  remote := SR.solve F.remote
  chargePlus := thresholdCharge Splus F.plus
  chargeMinus := thresholdCharge Sminus F.minus

/-- Exact regional cancellation of the complete current-weight source. -/
theorem solveLayer_exact
    (Splus Sminus : ThresholdSolver (E := E))
    (SK SR : RegionalSolver (E := E))
    (F : LayerSource (E := E)) :
    let D := solveLayer Splus Sminus SK SR F
    Splus.op D.plus = F.plus ∧
    Sminus.op D.minus = F.minus ∧
    SK.op D.kummer = F.kummer ∧
    SR.op D.remote = F.remote := by
  dsimp [solveLayer]
  exact ⟨fullThresholdCorrection_solves Splus F.plus,
    fullThresholdCorrection_solves Sminus F.minus,
    SK.solve_eq F.kummer, SR.solve_eq F.remote⟩

/-- Uniqueness of all normalized regional pieces and of both affine charges. -/
theorem solveLayer_unique
    (Splus Sminus : ThresholdSolver (E := E))
    (SK SR : RegionalSolver (E := E))
    (F : LayerSource (E := E))
    (ap am : ℝ) (hp hm hk hr : E)
    (hap : Splus.ell (F.plus - ap • Splus.op Splus.qCorr) = 0)
    (ham : Sminus.ell (F.minus - am • Sminus.op Sminus.qCorr) = 0)
    (hpp : Splus.op hp = F.plus - ap • Splus.op Splus.qCorr)
    (hmm : Sminus.op hm = F.minus - am • Sminus.op Sminus.qCorr)
    (hnp : Splus.normalize hp = 0)
    (hnm : Sminus.normalize hm = 0)
    (hkEq : SK.op hk = F.kummer)
    (hrEq : SR.op hr = F.remote) :
    ap = (solveLayer Splus Sminus SK SR F).chargePlus ∧
    am = (solveLayer Splus Sminus SK SR F).chargeMinus ∧
    hp = normalizedCorrection Splus F.plus ∧
    hm = normalizedCorrection Sminus F.minus ∧
    hk = (solveLayer Splus Sminus SK SR F).kummer ∧
    hr = (solveLayer Splus Sminus SK SR F).remote := by
  have hpuniq := threshold_pair_unique Splus F.plus ap hp hap hpp hnp
  have hmuniq := threshold_pair_unique Sminus F.minus am hm ham hmm hnm
  refine ⟨hpuniq.1, hmuniq.1, hpuniq.2, hmuniq.2, ?_, ?_⟩
  · exact SK.solve_unique F.kummer hk hkEq
  · exact SR.solve_unique F.remote hr hrEq

/-- The five mechanisms that can generate the next unresolved terms after one
current-weight cluster has been removed. -/
inductive GainCause
  | cutoff
  | parameter
  | flatRadiation
  | slowMonopole
  | frobenius
  deriving DecidableEq, Repr

structure GainParameters where
  delta : ℝ
  epsFlat : ℝ
  betaMinus : ℝ
  rhoStar : ℝ
  delta_pos : 0 < delta
  epsFlat_pos : 0 < epsFlat
  beta_half : (1 / 2 : ℝ) < betaMinus
  rhoStar_pos : 0 < rhoStar

def kappaProfile (P : GainParameters) : ℝ :=
  min P.delta (min P.epsFlat
    (min (2 * P.betaMinus - 1) (min (1 / 2 : ℝ) P.rhoStar)))

def gain (P : GainParameters) : GainCause → ℝ
  | .cutoff => P.rhoStar
  | .parameter => P.delta
  | .flatRadiation => P.epsFlat
  | .slowMonopole => 2 * P.betaMinus - 1
  | .frobenius => 1 / 2

theorem kappaProfile_pos (P : GainParameters) :
    0 < kappaProfile P := by
  have hb : 0 < 2 * P.betaMinus - 1 := by
    linarith [P.beta_half]
  simp only [kappaProfile, lt_min_iff]
  exact ⟨P.delta_pos, P.epsFlat_pos, hb, by norm_num, P.rhoStar_pos⟩

theorem kappaProfile_le_gain (P : GainParameters) (c : GainCause) :
    kappaProfile P ≤ gain P c := by
  cases c with
  | cutoff =>
      dsimp [gain]
      unfold kappaProfile
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_right _ _)))
  | parameter =>
      dsimp [gain]
      unfold kappaProfile
      exact min_le_left _ _
  | flatRadiation =>
      dsimp [gain]
      unfold kappaProfile
      exact le_trans (min_le_right _ _) (min_le_left _ _)
  | slowMonopole =>
      dsimp [gain]
      unfold kappaProfile
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))
  | frobenius =>
      dsimp [gain]
      unfold kappaProfile
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _)))

/-- A generated term consists of one of the five actual mechanisms plus any
further nonnegative order improvement.  Thus classification, not the desired
lower bound, is the input. -/
structure GeneratedTerm (P : GainParameters) (rho : ℝ) where
  cause : GainCause
  extra : ℝ
  extra_nonneg : 0 ≤ extra

def GeneratedTerm.order {P : GainParameters} {rho : ℝ}
    (t : GeneratedTerm P rho) : ℝ :=
  rho + gain P t.cause + t.extra

theorem generatedTerm_order_ge
    (P : GainParameters) (rho : ℝ) (t : GeneratedTerm P rho) :
    rho + kappaProfile P ≤ t.order := by
  unfold GeneratedTerm.order
  have h := kappaProfile_le_gain P t.cause
  linarith [t.extra_nonneg]

/-- Structural terminal matching the manuscript's one-layer conclusion:
the complete current-weight source is removed uniquely, both charges are
unique, the parameter-tangent component is untouched, and every newly
generated unresolved term lies at least `kappaProfile` above the current
weight. -/
theorem oneMinimalWeightCluster_eliminated
    (Splus Sminus : ThresholdSolver (E := E))
    (SK SR : RegionalSolver (E := E))
    (P : GainParameters) (rho : ℝ)
    (F : LayerSource (E := E)) (tangent : E)
    (newTerms : List (GeneratedTerm P rho)) :
    0 < kappaProfile P ∧
    (let D := solveLayer Splus Sminus SK SR F;
      Splus.op D.plus = F.plus ∧
      Sminus.op D.minus = F.minus ∧
      SK.op D.kummer = F.kummer ∧
      SR.op D.remote = F.remote) ∧
    tangent = tangent ∧
    (∀ t ∈ newTerms, rho + kappaProfile P ≤ t.order) := by
  refine ⟨kappaProfile_pos P, solveLayer_exact Splus Sminus SK SR F,
    rfl, ?_⟩
  intro t _ht
  exact generatedTerm_order_ge P rho t

#print axioms compatibleSource_orthogonal
#print axioms threshold_pair_unique
#print axioms solveLayer_exact
#print axioms solveLayer_unique
#print axioms kappaProfile_pos
#print axioms generatedTerm_order_ge
#print axioms oneMinimalWeightCluster_eliminated

end HBL.Profile.OneLayer
