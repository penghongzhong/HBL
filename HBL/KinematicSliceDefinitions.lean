import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Actual scalar functions in the manuscript's synchronized initial slice.
Here `A = 4 μ∞` and `h` is the real component of the parameter path.
The reciprocal tail is defined before any estimates; later declarations
prove its integrability from decay of the actual path.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Kinematic

/-- The integrated perturbation of the asymptotic affine clock. -/
def clockPerturbation (s₀ : ℝ) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  4 * ∫ σ in s₀..s, h σ

/-- The manuscript's actual `q_κ[h] = s p_κ[h]`. -/
def sliceClock (A s₀ κ : ℝ) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  A * s + κ + clockPerturbation s₀ h s

/-- The convergent reciprocal difference determining the synchronized slice. -/
def sliceIntegrand (A s₀ κ : ℝ) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  (sliceClock A s₀ κ h s)⁻¹ - (A * s)⁻¹

/-- The actual scalar tail equation used to select the initial-slice shift. -/
def sliceTail (A s₀ κ : ℝ) (h : ℝ → ℝ) : ℝ :=
  ∫ s in Ioi s₀, sliceIntegrand A s₀ κ h s

@[simp] theorem clockPerturbation_zero (s₀ s : ℝ) :
    clockPerturbation s₀ (fun _ => 0) s = 0 := by
  simp [clockPerturbation]

@[simp] theorem sliceClock_zero (A s₀ κ s : ℝ) :
    sliceClock A s₀ κ (fun _ => 0) s = A * s + κ := by
  simp [sliceClock]

@[simp] theorem sliceClock_initial (A s₀ κ : ℝ) (h : ℝ → ℝ) :
    sliceClock A s₀ κ h s₀ = A * s₀ + κ := by
  simp [sliceClock, clockPerturbation]

theorem sliceClock_sub_parameter (A s₀ κ η : ℝ) (h : ℝ → ℝ) (s : ℝ) :
    sliceClock A s₀ κ h s - sliceClock A s₀ η h s = κ - η := by
  simp only [sliceClock]
  ring

end HBL.Kinematic
