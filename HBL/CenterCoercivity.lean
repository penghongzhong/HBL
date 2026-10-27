import HBL.CompactTwoChannelCoercivity
import Mathlib.Tactic

/-!
# Perturbative centre coercivity

The exact two-channel Hartree energy gap has already been verified on the
physical scale/phase/bubble-orthogonal slice.  This file proves the only
additional algebra needed for a moving centre evolution: any symmetric form
perturbation smaller than one half of that gap preserves uniform coercivity.

No propagator or blow-up solution is assumed.
-/

noncomputable section
set_option autoImplicit false

open Filter
open scoped Topology RealInnerProductSpace

namespace HBL.MainBackward

open HBL.Modulation.Monopole
open HBL.L2Kernel

abbrev CenterPair := FullRadialEnergyL2 × FullRadialEnergyL2

def centerBaseForm (z : CenterPair) : ℝ :=
  inner ℝ (weightedVolterraAPlus z.1) z.1 +
    inner ℝ (weightedVolterraAMinus z.2) z.2

/-- The verified HBL two-channel gap survives a small moving-form
perturbation. -/
theorem center_coercive_under_small_form_perturbation
    (P : CenterPair →L[ℝ] CenterPair →L[ℝ] ℝ)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hsmall : 2 * eps ≤ compactTwoChannelGap)
    (q p : FullRadialEnergyL2)
    (hq : scaleCompactTest q = 0)
    (hp : phaseCompactTest p = 0)
    (hn : inner ℝ fullBubbleRadialEnergyL2 q = 0)
    (hP : |P (q,p) (q,p)| ≤ eps * (‖q‖ ^ 2 + ‖p‖ ^ 2)) :
    (compactTwoChannelGap / 2) * (‖q‖ ^ 2 + ‖p‖ ^ 2) ≤
      centerBaseForm (q,p) + P (q,p) (q,p) := by
  have hbase := actualCompactTwoChannelCoercivity_certified.2.2.2.1 q p hq hp hn
  have hPlow : -(eps * (‖q‖ ^ 2 + ‖p‖ ^ 2)) ≤ P (q,p) (q,p) :=
    (abs_le.mp hP).1
  have hS : 0 ≤ ‖q‖ ^ 2 + ‖p‖ ^ 2 := by positivity
  unfold centerBaseForm
  nlinarith only [hbase, hPlow, hsmall, hS]

/-- A form perturbation converging to zero is eventually smaller than half
the verified Hartree gap. -/
theorem eventually_center_form_small
    (eps : ℝ → ℝ)
    (heps : Tendsto eps atTop (𝓝 0)) :
    ∃ s0 : ℝ, ∀ s, s0 ≤ s →
      |eps s| ≤ compactTwoChannelGap / 2 := by
  have hgap : 0 < compactTwoChannelGap :=
    actualCompactTwoChannelCoercivity_certified.2.1
  have hm : Set.Icc (-(compactTwoChannelGap / 2))
      (compactTwoChannelGap / 2) ∈ 𝓝 (0 : ℝ) := by
    exact Set.Icc_mem_nhds (by linarith) (by linarith)
  have he := heps.eventually hm
  rw [eventually_atTop] at he
  rcases he with ⟨s0, hs0⟩
  refine ⟨s0, ?_⟩
  intro s hs
  have hmem := hs0 s hs
  rw [Set.mem_Icc] at hmem
  exact abs_le.mpr hmem

#print axioms center_coercive_under_small_form_perturbation
#print axioms eventually_center_form_small

end HBL.MainBackward
