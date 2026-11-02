import HBL.GlobalH1Matching
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Full radial-energy three-region gluing from genuine physical components

This is a conditional analytical bridge towards the manuscript's retained
`prop:global-H1-profile-v3`. It works on the actual completed physical
radial-gradient L² coordinate, not an arbitrary synthetic regional solver.

The hypotheses are explicit three-region energy estimates, together with
the actual profile-minus-bubble/radiation/algebraic decomposition. From
their strictly positive local exponents this theorem derives one common
positive global exponent and convergence in the real physical radial
homogeneous-energy coordinate. The exact Euclidean 3D physical-gradient
identity follows from the already proved Hilbert-space equivalence.

IMPORTANT: The finite Hartree PDE profile, its three genuine regional
bounds, complex phase component and terminal algebraic Kummer
extraction remain prerequisites from the unresolved original 2.13/2.14.
This bridge does NOT itself close the original 2.14 or increase 9/13.
-/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology

namespace HBL.Profile.GlobalH1
open HBL.Modulation HBL.Modulation.Monopole

theorem actual_physical_three_region_H1_gluing_and_limit
    (V W Zg Zalg Qin QK Qrem err : ℝ → FullRadialEnergyL2)
    (s₀ mIn mK mRem M CIn CK CRem CErr : ℝ)
    (hs₀ : 1 ≤ s₀)
    (hmIn : 0 < mIn) (hmK : 0 < mK) (hmRem : 0 < mRem)
    (hM : 0 < M)
    (hCIn : 0 ≤ CIn) (hCK : 0 ≤ CK) (hCRem : 0 ≤ CRem)
    (hSplit : ∀ s : ℝ, s₀ ≤ s →
      V s - W s - Zg s - Zalg s = Qin s + QK s + Qrem s)
    (hIn : ∀ s : ℝ, s₀ ≤ s → ‖Qin s‖ ≤ CIn * s ^ (-mIn))
    (hK : ∀ s : ℝ, s₀ ≤ s → ‖QK s‖ ≤ CK * s ^ (-mK))
    (hRem : ∀ s : ℝ, s₀ ≤ s → ‖Qrem s‖ ≤ CRem * s ^ (-mRem))
    (hErr : ∀ s : ℝ, s₀ ≤ s → ‖err s‖ ≤ CErr * s ^ (-M)) :
    ∃ nuE : ℝ, 0 < nuE ∧
      (∀ s : ℝ, s₀ ≤ s →
        ‖V s - W s - Zg s - Zalg s‖ ≤
          (CIn + CK + CRem) * s ^ (-nuE) ∧
        ‖V s - W s - Zg s - Zalg s + err s‖ ≤
          (CIn + CK + CRem) * s ^ (-nuE) + CErr * s ^ (-M) ∧
        ‖physicalGradientRealization
          (physicalEnergyEquiv.symm (V s - W s - Zg s - Zalg s))‖ ^ 2 =
          (4 * Real.pi) * ‖V s - W s - Zg s - Zalg s‖ ^ 2) ∧
      Tendsto (fun s : ℝ => V s - W s - Zg s - Zalg s + err s)
        atTop (𝓝 (0 : FullRadialEnergyL2)) := by
  let nuE : ℝ := min mIn (min mK mRem)
  have hnu : 0 < nuE := by
    dsimp [nuE]
    exact lt_min hmIn (lt_min hmK hmRem)
  have hnuIn : nuE ≤ mIn := by
    dsimp [nuE]
    exact min_le_left _ _
  have hnuK : nuE ≤ mK := by
    dsimp [nuE]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hnuRem : nuE ≤ mRem := by
    dsimp [nuE]
    exact (min_le_right _ _).trans (min_le_right _ _)
  let q : ℝ → FullRadialEnergyL2 :=
    fun s => V s - W s - Zg s - Zalg s
  have hBounds (s : ℝ) (hs : s₀ ≤ s) :
      ‖q s‖ ≤ (CIn + CK + CRem) * s ^ (-nuE) ∧
      ‖q s + err s‖ ≤
        (CIn + CK + CRem) * s ^ (-nuE) + CErr * s ^ (-M) ∧
      ‖physicalGradientRealization (physicalEnergyEquiv.symm (q s))‖ ^ 2 =
        (4 * Real.pi) * ‖q s‖ ^ 2 := by
    let D : ThreeRegionEnergyData FullRadialEnergyL2 :=
      { profile := q s
        inner := Qin s
        kummer := QK s
        remote := Qrem s
        split := hSplit s hs }
    have hS : 1 ≤ s := hs₀.trans hs
    have hGlobal :=
      three_region_energy_bound D s nuE mIn mK mRem CIn CK CRem
        hS hnuIn hnuK hnuRem hCIn hCK hCRem
        (hIn s hs) (hK s hs) (hRem s hs)
    have hWithErr :=
      three_region_with_error_bound D (err s) s nuE
        mIn mK mRem M CIn CK CRem CErr hS
        hnuIn hnuK hnuRem hCIn hCK hCRem
        (hIn s hs) (hK s hs) (hRem s hs) (hErr s hs)
    exact ⟨hGlobal, hWithErr,
      physical_gradient_energy_of_radial_coordinate (q s)⟩
  refine ⟨nuE, hnu, ?_, ?_⟩
  · intro s hs
    simpa only [q] using hBounds s hs
  · have hNuLimit :
        Tendsto (fun s : ℝ => (CIn + CK + CRem) * s ^ (-nuE))
          atTop (𝓝 0) := by
      have h :=
        (tendsto_const_nhds : Tendsto
          (fun _ : ℝ => CIn + CK + CRem) atTop
          (𝓝 (CIn + CK + CRem))).mul
          (tendsto_rpow_neg_atTop hnu)
      simpa only [mul_zero] using h
    have hErrLimit :
        Tendsto (fun s : ℝ => CErr * s ^ (-M)) atTop (𝓝 0) := by
      have h :=
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => CErr)
          atTop (𝓝 CErr)).mul (tendsto_rpow_neg_atTop hM)
      simpa only [mul_zero] using h
    have hUpper :
        Tendsto
          (fun s : ℝ =>
            (CIn + CK + CRem) * s ^ (-nuE) + CErr * s ^ (-M))
          atTop (𝓝 0) := by
      simpa only [zero_add] using hNuLimit.add hErrLimit
    have hEventually :
        ∀ᶠ s : ℝ in atTop,
          ‖q s + err s‖ ≤
            (CIn + CK + CRem) * s ^ (-nuE) + CErr * s ^ (-M) := by
      filter_upwards [eventually_ge_atTop s₀] with s hs
      exact (hBounds s hs).2.1
    have hLimit : Tendsto (fun s : ℝ => q s + err s)
        atTop (𝓝 (0 : FullRadialEnergyL2)) :=
      squeeze_zero_norm' hEventually hUpper
    simpa only [q] using hLimit

end HBL.Profile.GlobalH1
