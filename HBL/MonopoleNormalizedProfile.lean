import HBL.MonopoleCompactNormalization
import HBL.MonopoleProfileEquation

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HBL.Modulation.Monopole

open HBL.L2Kernel
open HBL.Modulation.AffineTail

/-- The concrete compact-test-normalized weighted Fredholm solution. -/
def monopoleCompactNormalizedSolution : RealL2 halfLineMeasure :=
  monopoleFredholmNormalizedSolution compactMonopoleNormalization

theorem monopoleCompactNormalizedSolution_equation :
    (1 - weightedBirmanSchwingerOperator) monopoleCompactNormalizedSolution =
      monopoleFredholmRightHandSide :=
  monopoleFredholmNormalizedSolution_equation compactMonopoleNormalization

theorem monopoleCompactNormalizedSolution_normalization :
    compactMonopoleNormalization monopoleCompactNormalizedSolution = 0 :=
  monopoleFredholmNormalizedSolution_normalization compactMonopoleNormalization
    compactMonopoleNormalization_scale_ne_zero

/-- The manuscript's concrete compact test gives existence and uniqueness
among all actual weighted L2 vectors, with no free normalization premise. -/
theorem existsUnique_monopoleCompactNormalizedSolution :
    ∃! x : RealL2 halfLineMeasure,
      (1 - weightedBirmanSchwingerOperator) x = monopoleFredholmRightHandSide ∧
        compactMonopoleNormalization x = 0 :=
  existsUnique_monopoleFredholmNormalizedSolution compactMonopoleNormalization
    compactMonopoleNormalization_scale_ne_zero

end HBL.Modulation.Monopole
