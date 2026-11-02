import HBL.TypeIIDynamicSelection.ActualHartreeMomentFluxFromContinuity
import HBL.TypeIIDynamicSelection.ActualPDEMomentCutoffStrictGain
import Mathlib.Tactic

/-!
# Original HBL 2.12: one ACTUAL selected orbit, uniform moving-cutoff gain

The two key analytic facts are both about the SAME physical Hartree
radiation z(t,r): (1) its positive quartic terminal moment and its
real PDE flux are continuous at T; (2) the radial Hartree PDE implies
the time derivative of that very physical moment.

The fixed manuscript cutoff chi_c(s,r) is the same at every time,
so its first derivative admits ONE global C_chi.  The exact material
transport formula cancels the potentially bad b*c term.  This gives a
single uniform r>=0, large-s positive order from the real PDE:

 |(partial_s+b*r*partial_r)chi_c|
     <= C_* s^{-1-(2*beta_minus-1)},  beta_minus>1/2.

The actual scale trap ell(s)<=C s^{-beta_minus} is visible; beta_minus
is NOT prescribed to equal the final Type-II blowup exponent. There
is no externally assumed bound |m_0'(t)|/m_0(t) because it is derived
from terminal moment positivity and actual PDE-flux continuity.
The Sobolev-to-pointwise radial Hartree flow and dominated
differentiation remain legitimate, explicit standard PDE analytic
inputs; they are not Lean axioms or a presumed gain.

This closes ONE genuine PDE-generated moving-cutoff gain class, NOT
all original prop:one-layer-stage3 classes (Kummer/remote/Frobenius,
parameter derivatives and global nonlinear localized residual).
-/

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The SAME fixed smooth cutoff constant works at all physical
renormalized times, a stronger quantifier than ∀s ∃C_chi. The
quartic moment derivative is the actual Hartree PDE value. -/
theorem actual_Hartree_one_orbit_uniform_moment_cutoff_transport
    (ell b : ℝ → ℝ) (z : ℝ → ℝ → ℂ) (time : ℝ → ℝ)
    (S : Set ℝ)
    (hEll : ∀ s ∈ S,
      HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : ∀ s ∈ S, 0 < ell s)
    (hClock : ∀ s ∈ S,
      HasDerivAt time ((ell s) ^ 2) s)
    (hPDEMoment : ∀ s ∈ S,
      HasDerivAt
        (fun t => actualPhysicalInverseSquareMoment (z t))
        (actualMomentLaplacianFlux (z (time s))) (time s))
    (hMomentPos : ∀ s ∈ S,
      0 < actualPhysicalInverseSquareMoment (z (time s))) :
    ∃ Cchi : ℝ, 0 < Cchi ∧
      ∀ s ∈ S, ∀ r : ℝ, 0 ≤ r →
        |deriv (fun t => actualMomentInnerCutoff ell z time t r) s +
          b s * r * deriv (actualMomentInnerCutoff ell z time s) r| ≤
        (2 * (ell s) ^ 2 *
          (|actualMomentLaplacianFlux (z (time s))| /
            radialPhysicalQuarticMoment (z (time s)))) * Cchi := by
  obtain ⟨Cchi,hCchi,hDerivBound⟩ :=
    exists_actual_fixed_cutoff_uniform_deriv_bound
  refine ⟨Cchi,hCchi,?_⟩
  intro s hs r hr
  let c : ℝ := actualPhysicalRadiationMonopole ell z time s
  by_cases htransition : c * r / 4 ≤ 2
  · exact actualMomentInnerCutoff_transport_length_gain
      ell b z time r Cchi (hEll s hs) (hEllPos s hs)
      (hClock s hs) (hPDEMoment s hs) (hMomentPos s hs)
      hr htransition (hDerivBound _)
  · have houter : 2 < c * r / 4 := lt_of_not_ge htransition
    have hcut : deriv cutoff (c * r / 4) = 0 :=
      actual_fixed_cutoff_deriv_zero_of_gt_two houter
    have hmrad : HasDerivAt
        (fun t => radialPhysicalQuarticMoment (z t))
          (actualMomentLaplacianFlux (z (time s))) (time s) := by
      simpa only [actual_physical_inverse_square_radial_reduction] using
        hPDEMoment s hs
    have htransport := actualMomentInnerCutoff_material_derivative
      ell b z time r (hEll s hs) (hEllPos s hs)
      (hClock s hs) hmrad
    change |deriv (fun t => actualMomentInnerCutoff ell z time t r) s +
      b s * r * deriv (actualMomentInnerCutoff ell z time s) r| ≤ _
    rw [htransport, hcut, mul_zero, abs_zero]
    positivity

/-- The manuscript's ACTUAL one-orbit moving overlap transport is
uniformly integrably small at ALL large renormalized times and ALL
nonnegative radii. Terminal flux boundedness is DERIVED from the
same real Hartree flow, not supplied as an independent hypothesis.
-/
theorem actual_Hartree_one_orbit_eventual_strict_moving_cutoff_gain
    (ell b : ℝ → ℝ) (z : ℝ → ℝ → ℂ)
    (time : ℝ → ℝ) (T s0 C beta : ℝ)
    (hs0 : 1 ≤ s0)
    (hC : 0 ≤ C)
    (hBeta : 1 / 2 < beta)
    (hEll : ∀ s, s0 ≤ s →
      HasDerivAt ell (-(b s * ell s)) s)
    (hEllPos : ∀ s, s0 ≤ s → 0 < ell s)
    (hClock : ∀ s, s0 ≤ s →
      HasDerivAt time ((ell s) ^ 2) s)
    (hPDEMoment : ∀ s, s0 ≤ s →
      HasDerivAt
        (fun t => actualPhysicalInverseSquareMoment (z t))
        (actualMomentLaplacianFlux (z (time s))) (time s))
    (hTrap : ∀ s, s0 ≤ s →
      ell s ≤ C * s ^ (-beta))
    (hm : ContinuousAt (fun t => radialPhysicalQuarticMoment (z t)) T)
    (hFlux : ContinuousAt (fun t => actualMomentLaplacianFlux (z t)) T)
    (hmT : 0 < radialPhysicalQuarticMoment (z T))
    (hPhysicalClock : Tendsto time atTop (𝓝 T)) :
    ∃ K : ℝ, 0 < K ∧
      0 < actualPDEMomentCutoffGain beta ∧
      ∀ᶠ s in atTop,
        ∀ r : ℝ, 0 ≤ r →
          |deriv (fun t => actualMomentInnerCutoff ell z time t r) s +
            b s * r * deriv (actualMomentInnerCutoff ell z time s) r| ≤
            K * s ^ (-1 - actualPDEMomentCutoffGain beta) := by
  let S : Set ℝ := {s : ℝ |
    s0 ≤ s ∧ 0 < actualPhysicalInverseSquareMoment (z (time s))}
  obtain ⟨Cchi,hCchi,hCut⟩ :=
    actual_Hartree_one_orbit_uniform_moment_cutoff_transport
      ell b z time S
      (by intro s hs; exact hEll s hs.1)
      (by intro s hs; exact hEllPos s hs.1)
      (by intro s hs; exact hClock s hs.1)
      (by intro s hs; exact hPDEMoment s hs.1)
      (by intro s hs; exact hs.2)
  obtain ⟨J,hJ,hNear⟩ :=
    actual_Hartree_terminal_flux_bounded_on_physical_clock
      z time T hm hFlux hmT hPhysicalClock
  let K : ℝ := 2 * Cchi * C ^ 2 * J
  have hK : 0 < K := by
    have hCpos : 0 < C := by
      have hs : s0 ≤ s0 := le_rfl
      have he := hEllPos s0 hs
      have htr := hTrap s0 hs
      by_contra h
      have hzero : C = 0 := le_antisymm (le_of_not_gt h) hC
      rw [hzero, zero_mul] at htr
      linarith
    dsimp [K]
    positivity
  refine ⟨K,hK,actual_PDE_moment_cutoff_gain_positive beta hBeta,?_⟩
  have hLarge : ∀ᶠ s : ℝ in atTop, s0 ≤ s :=
    eventually_ge_atTop s0
  filter_upwards [hLarge,hNear] with s hs hFluxS
  intro r hr
  have htime : 1 ≤ s := hs0.trans hs
  have hM : 0 < radialPhysicalQuarticMoment (z (time s)) :=
    hFluxS.1
  have h3DMoment : 0 <
      actualPhysicalInverseSquareMoment (z (time s)) := by
    simpa only [actual_physical_inverse_square_radial_reduction] using hM
  have hR :
      |actualMomentLaplacianFlux (z (time s))| /
        radialPhysicalQuarticMoment (z (time s)) ≤ J :=
    (div_le_iff₀ hM).2 hFluxS.2
  have hEll2 :
      (ell s) ^ 2 ≤ C ^ 2 * s ^ (-1 - actualPDEMomentCutoffGain beta) :=
    actual_PDE_trapped_length_squared_positive_gain
      s (ell s) C beta htime (hEllPos s hs).le hC (hTrap s hs)
  have hcoef : 0 ≤ 2 * J * Cchi := by positivity
  calc
    |deriv (fun t => actualMomentInnerCutoff ell z time t r) s +
      b s * r * deriv (actualMomentInnerCutoff ell z time s) r| ≤
        (2 * (ell s) ^ 2 *
          (|actualMomentLaplacianFlux (z (time s))| /
            radialPhysicalQuarticMoment (z (time s)))) * Cchi :=
      hCut s ⟨hs,h3DMoment⟩ r hr
    _ ≤ (2 * (ell s) ^ 2 * J) * Cchi := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hR (by positivity)) hCchi.le
    _ = (ell s) ^ 2 * (2 * J * Cchi) := by ring
    _ ≤ (C ^ 2 * s ^ (-1 - actualPDEMomentCutoffGain beta)) *
          (2 * J * Cchi) :=
      mul_le_mul_of_nonneg_right hEll2 hcoef
    _ = K * s ^ (-1 - actualPDEMomentCutoffGain beta) := by
      dsimp [K]
      ring

end HBL.TypeIIDynamicSelection
