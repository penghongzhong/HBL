import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic
noncomputable section
set_option autoImplicit false
namespace HBL.ZeroCenterObstruction

abbrev Plane := ℝ × ℝ
abbrev State := Plane × (Plane × Plane)

def dot (x y : State) : ℝ :=
  x.1.1*y.1.1 + x.1.2*y.1.2 + x.2.1.1*y.2.1.1 +
  x.2.1.2*y.2.1.2 + x.2.2.1*y.2.2.1 + x.2.2.2*y.2.2.2

def symplecticLinear : State →ₗ[ℝ] State where
  toFun x := ((x.1.2,-x.1.1),(x.2.2,-x.2.1))
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' a x := by ext <;> simp

def hessianLinear : State →ₗ[ℝ] State where
  toFun x := ((-x.1.1,x.1.2),(0,x.2.2))
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' a x := by ext <;> simp

def J : State →L[ℝ] State := symplecticLinear.toContinuousLinearMap
def L : State →L[ℝ] State := hessianLinear.toContinuousLinearMap
def A : State →L[ℝ] State := J.comp L

def zeroMode (z : Plane) : State := (0,(z,0))
def centerMode (c : Plane) : State := (0,(0,c))
def plusMode : State := ((1,1),(0,0))
def minusMode : State := ((1,-1),(0,0))

def graphMode (ell : Plane →ₗ[ℝ] Plane) (c : Plane) : State := (0,(ell c,c))

/-- A commuting retraction onto the actual kernel, required by an invariant direct complement. -/
def HasInvariantZeroProjection : Prop :=
  ∃ P : State →L[ℝ] State,
    (∀ z, P (zeroMode z) = zeroMode z) ∧
    (∀ x, A (P x) = 0) ∧
    (∀ x, P (A x) = A (P x))
end HBL.ZeroCenterObstruction
