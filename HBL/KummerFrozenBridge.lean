import Mathlib.Tactic

/-!
# Exact frozen Kummer change of variables

For the manuscript frozen annular operator
  u'' + (2/z + i z/2)u' + theta u + i(1/4-mu)u,
set w=-i z^2/4 and u=z^{-1} y(w).  This file verifies the exact
algebraic reduction to the confluent-hypergeometric equation with
b=1/2 and a=-(mu+1/4+i theta).
-/

noncomputable section
set_option autoImplicit false

namespace HBL.Profile.Kummer

def kummerVariable (z : ℂ) : ℂ :=
  -(Complex.I * z ^ 2 / 4)

def kummerA (mu theta : ℝ) : ℂ :=
  -((mu : ℂ) + 1 / 4 + Complex.I * theta)

def kummerB : ℂ := 1 / 2

def confluentResidual
    (mu theta : ℝ) (z y y1 y2 : ℂ) : ℂ :=
  let w := kummerVariable z
  w * y2 + (kummerB - w) * y1 - kummerA mu theta * y

/-- The three jets of u=z^{-1} y(w), after the chain rule
w'=-i z/2 has been substituted. -/
def reconstructedValue (z y : ℂ) : ℂ :=
  y / z

def reconstructedFirstJet (z y y1 : ℂ) : ℂ :=
  -y / z ^ 2 - Complex.I * y1 / 2

def reconstructedSecondJet (z y y1 y2 : ℂ) : ℂ :=
  2 * y / z ^ 3 + Complex.I * y1 / (2 * z) - z * y2 / 4

def frozenRadialJetResidual
    (mu theta : ℝ) (z u u1 u2 : ℂ) : ℂ :=
  u2 + (2 / z + Complex.I * z / 2) * u1 +
    theta * u + Complex.I * (1 / 4 - mu) * u

theorem frozenRadialJetResidual_reduction
    (mu theta : ℝ) (z y y1 y2 : ℂ) (hz : z ≠ 0) :
    frozenRadialJetResidual mu theta z
      (reconstructedValue z y)
      (reconstructedFirstJet z y y1)
      (reconstructedSecondJet z y y1 y2) =
      (-Complex.I / z) * confluentResidual mu theta z y y1 y2 := by
  unfold frozenRadialJetResidual reconstructedValue reconstructedFirstJet
    reconstructedSecondJet confluentResidual kummerVariable kummerA kummerB
  push_cast
  field_simp [hz]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem frozenRadialJetResidual_zero_of_confluent
    (mu theta : ℝ) (z y y1 y2 : ℂ) (hz : z ≠ 0)
    (hK : confluentResidual mu theta z y y1 y2 = 0) :
    frozenRadialJetResidual mu theta z
      (reconstructedValue z y)
      (reconstructedFirstJet z y y1)
      (reconstructedSecondJet z y y1 y2) = 0 := by
  rw [frozenRadialJetResidual_reduction mu theta z y y1 y2 hz, hK, mul_zero]

theorem kummer_parameters_exact (mu theta : ℝ) :
    kummerB = (1 / 2 : ℂ) ∧
    -kummerA mu theta = (mu : ℂ) + 1 / 4 + Complex.I * theta := by
  constructor
  · rfl
  · unfold kummerA
    ring

#print axioms frozenRadialJetResidual_reduction
#print axioms frozenRadialJetResidual_zero_of_confluent
#print axioms kummer_parameters_exact

end HBL.Profile.Kummer
