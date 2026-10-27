import HBL.HyperbolicSpectralBoundary
import HBL.StableInitialPropagation
import Mathlib.Tactic

/-!
# Hyperbolic spectral coordinate = terminal shooting coordinate

This unnumbered bridge turns the literature-level fixed-bubble hyperbolic
coordinate into the already verified terminal shooting formula.  No blow-up
orbit is assumed: the theorem says that *if* a strong trajectory satisfies
the actual generator equation and the projected moving perturbation has the
stated scalar form, then every bounded growth coordinate is necessarily the
terminal integral.
-/

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace HBL.MainBackward

def movingGrowthRate
    (S : FixedBubbleHyperbolicSpectralBoundary)
    (delta : ℝ → ℝ) (t : ℝ) : ℝ :=
  S.e0 + delta t

theorem movingGrowthRate_half_gap
    (S : FixedBubbleHyperbolicSpectralBoundary)
    (delta : ℝ → ℝ) {s0 t : ℝ}
    (hdelta : ∀ r, s0 ≤ r → |delta r| ≤ S.e0 / 2)
    (ht : s0 ≤ t) :
    S.e0 / 2 ≤ movingGrowthRate S delta t := by
  exact moving_hyperbolic_rate_lower S delta (hdelta t ht)

/-- The concrete moving growth rate and projected source satisfy the full
scalar terminal-shooting theorem. -/
theorem hyperbolicTerminalShooting_certified
    (S : FixedBubbleHyperbolicSpectralBoundary)
    (delta f : ℝ → ℝ)
    (s0 p F : ℝ)
    (hs0 : 0 < s0) (hp : 0 < p) (hF : 0 ≤ F)
    (hdeltaCont : Continuous delta) (hf : Continuous f)
    (hdelta : ∀ t, s0 ≤ t → |delta t| ≤ S.e0 / 2)
    (hsource : ∀ t, s0 ≤ t → |f t| ≤ F * t ^ (-p)) :
    let rate := movingGrowthRate S delta
    let c := HBL.Shooting.unstableShootingSolution rate f
    ContinuousOn c (Ici s0) ∧
    (∀ s, s0 < s →
      HasDerivAt c (rate s * c s + f s) s) ∧
    (∀ s, s0 ≤ s → |c s| ≤ (F / (S.e0 / 2)) * s ^ (-p)) ∧
    Tendsto c atTop (𝓝 0) ∧
    (∀ y : ℝ → ℝ, ContinuousOn y (Ici s0) →
      (∀ t, s0 < t → HasDerivAt y (rate t * y t + f t) t) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t, s0 ≤ t → |y t| ≤ C) →
      ∀ s, s0 ≤ s → y s = c s) := by
  dsimp only
  let rate := movingGrowthRate S delta
  have hrateCont : Continuous rate := by
    exact continuous_const.add hdeltaCont
  have he : 0 < S.e0 / 2 := moving_hyperbolic_half_gap_pos S
  have hrate : ∀ t, s0 ≤ t → S.e0 / 2 ≤ rate t := by
    intro t ht
    exact movingGrowthRate_half_gap S delta hdelta ht
  have h := HBL.Shooting.revisedUnstableShootingManuscriptEnvironment_closed
    hs0 hp he hF hrateCont hf hrate hsource
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- Every bounded strong Hartree growth coordinate is exactly the terminal
shooting solution, once the moving perturbation has been projected onto the
literature growth functional. -/
theorem growthCoordinate_eq_terminalShooting
    (S : FixedBubbleHyperbolicSpectralBoundary)
    (v H : ℝ → CenterPair)
    (delta f : ℝ → ℝ)
    (s0 p F : ℝ)
    (hs0 : 0 < s0) (hp : 0 < p) (hF : 0 ≤ F)
    (hvcont : ContinuousOn v (Ici s0))
    (hdeltaCont : Continuous delta) (hf : Continuous f)
    (hvdom : ∀ t, s0 ≤ t → v t ∈ S.domain)
    (hv : ∀ (t : ℝ) (ht : s0 < t) →
      HasDerivAt v (S.generator ⟨v t, hvdom t ht.le⟩ + H t) t)
    (hproj : ∀ t, s0 ≤ t →
      S.growthCoordinate (H t) =
        delta t * S.growthCoordinate (v t) + f t)
    (hdelta : ∀ t, s0 ≤ t → |delta t| ≤ S.e0 / 2)
    (hsource : ∀ t, s0 ≤ t → |f t| ≤ F * t ^ (-p))
    (hbounded : ∃ C : ℝ, 0 ≤ C ∧
      ∀ t, s0 ≤ t → |S.growthCoordinate (v t)| ≤ C) :
    ∀ s, s0 ≤ s →
      S.growthCoordinate (v s) =
        HBL.Shooting.unstableShootingSolution
          (movingGrowthRate S delta) f s := by
  have hrateCont : Continuous (movingGrowthRate S delta) :=
    continuous_const.add hdeltaCont
  have he : 0 < S.e0 / 2 := moving_hyperbolic_half_gap_pos S
  have hrate : ∀ t, s0 ≤ t →
      S.e0 / 2 ≤ movingGrowthRate S delta t :=
    fun t ht => movingGrowthRate_half_gap S delta hdelta ht
  have hycont : ContinuousOn (fun t => S.growthCoordinate (v t)) (Ici s0) := by
    simpa only [Function.comp_def] using
      S.growthCoordinate.continuous.comp_continuousOn hvcont
  have hyderiv : ∀ t, s0 < t →
      HasDerivAt (fun r => S.growthCoordinate (v r))
        (movingGrowthRate S delta t * S.growthCoordinate (v t) + f t) t := by
    intro t ht
    have hvt := hv t ht
    have hbase := moving_growthCoordinate_hasDerivAt
      S v H delta f t (hvdom t ht.le) hvt (hproj t ht.le)
    simpa [movingGrowthRate] using hbase
  exact HBL.Shooting.unstableShootingSolution_unique_bounded
    hs0 hp he hF hrateCont hf hrate hsource
    hycont hyderiv hbounded

#print axioms hyperbolicTerminalShooting_certified
#print axioms growthCoordinate_eq_terminalShooting

end HBL.MainBackward
