import HBL.AffineTailCutoff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Local Green identity for the affine-tail threshold charge.

This module isolates the second-order one-dimensional integration by parts.
It applies directly to H_- and to the local differential part of H_+.
For the nonlocal real channel H_+, the remaining integral is the commutator
pairing <T psi,q> - <psi,T q>, which must be cancelled by the symmetry of
the Hartree kernel on the full half-line rather than silently discarded on
a finite interval.
-/

noncomputable section

open MeasureTheory

namespace HBL.Modulation.AffineTail

/-- Wronskian boundary expression appearing in the manuscript Green formula. -/
def greenBoundary
    (psi dpsi q dq : ℝ → ℝ) (r : ℝ) : ℝ :=
  -psi r * dq r + dpsi r * q r

/-- Pointwise derivative of the Wronskian boundary expression. -/
theorem greenBoundary_hasDerivAt
    (psi dpsi ddpsi q dq ddq : ℝ → ℝ) (r : ℝ)
    (hpsi : HasDerivAt psi (dpsi r) r)
    (hdpsi : HasDerivAt dpsi (ddpsi r) r)
    (hq : HasDerivAt q (dq r) r)
    (hdq : HasDerivAt dq (ddq r) r) :
    HasDerivAt
      (greenBoundary psi dpsi q dq)
      (psi r * (-ddq r) - (-ddpsi r) * q r) r := by
  have hfirst := (hpsi.mul hdq).neg
  have hsecond := hdpsi.mul hq
  have hsum := hfirst.add hsecond
  change HasDerivAt
    (fun x => -psi x * dq x + dpsi x * q x)
    (psi r * (-ddq r) - (-ddpsi r) * q r) r
  convert hsum using 1
  · funext x
    simp
  · ring

/-- One-dimensional Green identity for the second-derivative part. -/
theorem green_secondDerivative
    (a b : ℝ)
    (psi dpsi ddpsi q dq ddq : ℝ → ℝ)
    (hpsi : ∀ r, HasDerivAt psi (dpsi r) r)
    (hdpsi : ∀ r, HasDerivAt dpsi (ddpsi r) r)
    (hq : ∀ r, HasDerivAt q (dq r) r)
    (hdq : ∀ r, HasDerivAt dq (ddq r) r)
    (hint : IntervalIntegrable
      (fun r => psi r * (-ddq r) - (-ddpsi r) * q r)
      volume a b) :
    (∫ r in a..b,
      psi r * (-ddq r) - (-ddpsi r) * q r) =
      greenBoundary psi dpsi q dq b -
        greenBoundary psi dpsi q dq a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => greenBoundary_hasDerivAt
      psi dpsi ddpsi q dq ddq r
      (hpsi r) (hdpsi r) (hq r) (hdq r))
    hint

/-- A common multiplication potential cancels identically in Green's formula. -/
theorem localSchrodinger_commutator
    (V psi ddpsi q ddq : ℝ → ℝ) (r : ℝ) :
    psi r * ((-ddq r) - V r * q r) -
        (((-ddpsi r) - V r * psi r) * q r) =
      psi r * (-ddq r) - (-ddpsi r) * q r := by
  ring

/-- Green identity for a local half-line Schrödinger operator
H_V q = -q'' - V q. -/
theorem green_localSchrodinger
    (a b : ℝ)
    (V psi dpsi ddpsi q dq ddq : ℝ → ℝ)
    (hpsi : ∀ r, HasDerivAt psi (dpsi r) r)
    (hdpsi : ∀ r, HasDerivAt dpsi (ddpsi r) r)
    (hq : ∀ r, HasDerivAt q (dq r) r)
    (hdq : ∀ r, HasDerivAt dq (ddq r) r)
    (hint : IntervalIntegrable
      (fun r => psi r * ((-ddq r) - V r * q r) -
        (((-ddpsi r) - V r * psi r) * q r))
      volume a b) :
    (∫ r in a..b,
      psi r * ((-ddq r) - V r * q r) -
        (((-ddpsi r) - V r * psi r) * q r)) =
      greenBoundary psi dpsi q dq b -
        greenBoundary psi dpsi q dq a := by
  have heq :
      (fun r => psi r * ((-ddq r) - V r * q r) -
        (((-ddpsi r) - V r * psi r) * q r)) =
      (fun r => psi r * (-ddq r) - (-ddpsi r) * q r) := by
    funext r
    exact localSchrodinger_commutator V psi ddpsi q ddq r
  rw [heq] at hint ⊢
  exact green_secondDerivative a b psi dpsi ddpsi q dq ddq
    hpsi hdpsi hq hdq hint

end HBL.Modulation.AffineTail
