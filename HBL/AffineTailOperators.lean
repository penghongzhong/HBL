import HBL.AffineTailNonlocalSymmetry
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Concrete half-line operators entering the manuscript affine-tail lemma.

The normalization is the one fixed earlier in the manuscript:
  kappa_H = 3/pi^2,
  V(r) = 3/(1+r^2)^2,
and the radial real-channel nonlocal kernel is
  8*pi*kappa_H W(r)^3 W(rho)^3 log((r+rho)/|r-rho|).

The kernel value on the diagonal is irrelevant for Lebesgue integration;
Lean's totalized real operations give a harmless pointwise value there.
-/

noncomputable section

open Set MeasureTheory

namespace HBL.Modulation.AffineTail

/-- Manuscript Hartree normalization. -/
def hartreeKappa : ℝ := 3 / (Real.pi ^ 2)

/-- Local half-line potential after radial conjugation. -/
def potential (r : ℝ) : ℝ :=
  3 / (1 + r ^ 2) ^ 2

/-- Symmetric radial nonlocal kernel of the real channel. -/
def hartreeKernel (r rho : ℝ) : ℝ :=
  8 * Real.pi * hartreeKappa *
    bubble r ^ 3 * bubble rho ^ 3 *
      Real.log ((r + rho) / |r - rho|)

/-- The nonlocal kernel is exactly symmetric. -/
theorem hartreeKernel_symm (r rho : ℝ) :
    hartreeKernel r rho = hartreeKernel rho r := by
  unfold hartreeKernel
  rw [add_comm r rho, abs_sub_comm r rho]
  ring

/-- Integral nonlocal operator on the positive half-line. -/
def nonlocalApply (q : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ rho in Ioi (0 : ℝ), hartreeKernel r rho * q rho

/-- Imaginary-channel half-line operator. -/
def hMinusApply (q : ℝ → ℝ) (r : ℝ) : ℝ :=
  -deriv (deriv q) r - potential r * q r

/-- Real-channel half-line operator. -/
def hPlusApply (q : ℝ → ℝ) (r : ℝ) : ℝ :=
  -deriv (deriv q) r - 3 * potential r * q r - nonlocalApply q r

/-- The manuscript phase resonance. -/
def resonanceMinus : ℝ → ℝ :=
  radialResonanceMinus

/-- The manuscript scale resonance. -/
def resonancePlus : ℝ → ℝ :=
  radialResonancePlus

@[simp]
theorem resonanceMinus_def (r : ℝ) :
    resonanceMinus r = r * bubble r := by
  rfl

@[simp]
theorem resonancePlus_def (r : ℝ) :
    resonancePlus r = r * dilationGenerator bubble r := by
  rfl

end HBL.Modulation.AffineTail
