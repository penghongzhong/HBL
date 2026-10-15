import HBL.RadialHardy3D
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Order.Compact

/-!
Finite-interval L2 input for the compact threshold tests in the first
manuscript lemma.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace HBL.Modulation

/-- A continuous real function belongs to every finite `L^p` space after
restriction to a bounded interval. -/
theorem continuous_memLp_restrict_Ioc
    (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) (hf : Continuous f)
    (p : ℝ≥0∞) :
    MemLp f p (volume.restrict (Ioc a b)) := by
  obtain ⟨x, hx, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab) hf.norm.continuousOn
  letI : Fact (volume (Ioc a b) < ∞) := ⟨measure_Ioc_lt_top⟩
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioc a b)) :=
    hf.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  refine MemLp.of_bound hmeas ‖f x‖ ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  exact hmax ⟨le_of_lt hy.1, hy.2⟩

end HBL.Modulation
