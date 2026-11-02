import HBL.Literature.AroraRoudenko2020Parameters
import HBL.RegularRadiationOriginalEnvironment
import Mathlib.Tactic

/-!
# Published Hartree local theory as an explicit reusable Lean input

Arora--Roudenko, *J. Hyperbolic Differential Equations* 17 (2020),
727--763, DOI 10.1142/S0219891620500228, establishes critical local
well-posedness for generalized Hartree. The numerical specialization
N=3, b=2, p=4, s_c=1 is proved in AroraRoudenko2020Parameters.

**Logical trust boundary:** a paper theorem is an explicit supplied
mathematical premise, NOT a Lean axiom. Lean cannot infer existence of
the particular high-regularity witness below from bibliographic metadata.

The preexisting CitedHighRegularityHartreeLocalTheory contains the
published critical LWP boundary PLUS separate analytic upgrades:
arbitrary high Sobolev persistence, finite time jets, C1 dependence in
H^L, radial 3D reduction, and other assumptions. Those upgrades are
not silently attributed to Arora--Roudenko Theorems 1.1 / 3.1.
They remain visible in the parameter LT and require their own proof
or precisely applicable independent authoritative theorems.

Downstream 2.12 can import this module rather than rebuild a local
Strichartz theory. Neither the real Kummer/remote matching nor the
PDE-selected Type II rate is part of the external premise.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace HBL.Literature.AroraRoudenko2020

open HBL.RegularRadiation

/-- The existing HIGH-REGULARITY literature interface, distinguished
from the BASIC energy-critical published local well-posedness. -/
abbrev ExtendedHighRegularityInput (κ : ℝ) :=
  CitedHighRegularityHartreeLocalTheory κ

/-- On a high-regularity continuation of the cited local theory,
the selected physical flow has the correct terminal datum,
continuity, strong H^(L-2) time derivative and genuine Hartree PDE. -/
theorem certified_cited_flow_is_physical_strong_solution
    (κ : ℝ) (LT : ExtendedHighRegularityInput κ)
    {L : ℕ} (hL : 4 ≤ L) (T : ℝ) (g : Sobolev L)
    (hg : ‖g‖ ≤ LT.epsilon L) :
    IsRegularHartreeSolutionOn κ L T (LT.tau L) g (LT.flow L T g) :=
  cited_flow_is_regular_solution κ LT hL T g hg

/-- Transfer of the genuine NONLOCAL physical Hartree equation
under exactly the same high-regularity interface and time window. -/
theorem certified_cited_flow_satisfies_actual_Hartree
    (κ : ℝ) (LT : ExtendedHighRegularityInput κ)
    {L : ℕ} (hL : 4 ≤ L) (T : ℝ) (g : Sobolev L)
    (hg : ‖g‖ ≤ LT.epsilon L) {t : ℝ}
    (ht : t ∈ Icc (T - LT.tau L) T) :
    HartreeEquationAt κ (LT.flow L T g t)
      (LT.jet L T g 1 t).toDistr :=
  (regularRadiation_strong_equation_certified κ
    LT.toGeneralizedHartreeRegularLocalTheory hL T g hg ht).2.1

/-- The Hartree quartic convolution for the same physical flow
is integrable at every observation point. -/
theorem certified_cited_flow_physical_Riesz_integrable
    (κ : ℝ) (LT : ExtendedHighRegularityInput κ)
    {L : ℕ} (hL : 4 ≤ L) (T : ℝ) (g : Sobolev L)
    (hg : ‖g‖ ≤ LT.epsilon L) {t : ℝ}
    (ht : t ∈ Icc (T - LT.tau L) T) :
    ∀ x : Space, Integrable (fun y : Space =>
      (kernel (x - y) : ℂ) *
        quarticDensity (physicalL2 (LT.flow L T g t)) y) :=
  (regularRadiation_strong_equation_certified κ
    LT.toGeneralizedHartreeRegularLocalTheory hL T g hg ht).2.2

/-- Unique strong solution in the SAME original Cauchy solution
class and with the SAME physical inverse-square Hartree equation. -/
theorem certified_cited_flow_unique
    (κ : ℝ) (LT : ExtendedHighRegularityInput κ)
    {L : ℕ} (hL : 4 ≤ L) (T : ℝ) (g : Sobolev L)
    (hg : ‖g‖ ≤ LT.epsilon L)
    (u : ℝ → Sobolev L)
    (hu : IsRegularHartreeSolutionOn κ L T (LT.tau L) g u)
    {t : ℝ} (ht : t ∈ Icc (T - LT.tau L) T) :
    u t = LT.flow L T g t :=
  LT.uniqueness L hL T g hg u hu t ht

/-- Genuine radiality preservation from the explicit high-regularity
interface; the 2020 critical result alone is not claimed to establish
the required all-jets pointwise radial identification. -/
theorem certified_cited_flow_radial
    (κ : ℝ) (LT : ExtendedHighRegularityInput κ)
    {L : ℕ} (hL : 4 ≤ L) (T : ℝ) (g : Sobolev L)
    (hg : ‖g‖ ≤ LT.epsilon L)
    (hRad : IsRadialSobolev g)
    {t : ℝ} (ht : t ∈ Icc (T - LT.tau L) T) :
    IsRadialSobolev (LT.flow L T g t) :=
  LT.radial_preserved L hL T g hg hRad t ht

end HBL.Literature.AroraRoudenko2020
