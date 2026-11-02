import HBL.GlobalH1Matching
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
A genuine two-channel physical radial-energy gluing statement for the
reduced Type-II main chain. The two components are the real and imaginary
physical radial-gradient L² coordinates. The conclusion gives the
physical 3D gradient identity and full global energy convergence.

Explicit assumptions: the actual finite Hartree profile has already
been decomposed by its regional Kummer/inner/remote construction, and
each part obeys its specific positive regional energy estimate.
These nontrivial physical inputs must come from the STILL-OPEN 2.13.
The terminal algebraic Kummer branch is an explicit supplied component.
Nothing here proves it exists or proves the original full 2.14.
This is a mathematically meaningful candidate for a revised,
conditional H1-gluing theorem, NOT original-number acceptance.
-/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology

namespace HBL.Profile.GlobalH1

open HBL.Modulation HBL.Modulation.Monopole

/-- Actual complex-radial physical energy is a pair of the independently
verified 3D real radial-gradient energy coordinates. -/
abbrev PhysicalComplexRadialEnergyPair :=
  FullRadialEnergyL2 × FullRadialEnergyL2

theorem physical_complex_three_region_H1_gluing_and_convergence
    (V W Zg Zalg Qin QK Qrem err :
      ℝ → PhysicalComplexRadialEnergyPair)
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
        let q := V s - W s - Zg s - Zalg s
        ‖q‖ ≤ (CIn + CK + CRem) * s ^ (-nuE) ∧
        ‖q + err s‖ ≤
          (CIn + CK + CRem) * s ^ (-nuE) + CErr * s ^ (-M) ∧
        ‖physicalGradientRealization (physicalEnergyEquiv.symm q.1)‖ ^ 2 +
          ‖physicalGradientRealization (physicalEnergyEquiv.symm q.2)‖ ^ 2 =
          (4 * Real.pi) * (‖q.1‖ ^ 2 + ‖q.2‖ ^ 2)) ∧
      Tendsto
        (fun s : ℝ => V s - W s - Zg s - Zalg s + err s)
        atTop (𝓝 (0 : PhysicalComplexRadialEnergyPair)) := by
  let nuE : ℝ := min mIn (min mK mRem)
  have hnu : 0 < nuE := by
    dsimp [nuE]
    exact lt_min hmIn (lt_min hmK hmRem)
  have hnIn : nuE ≤ mIn := by
    dsimp [nuE]
    exact min_le_left _ _
  have hnK : nuE ≤ mK := by
    dsimp [nuE]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hnRem : nuE ≤ mRem := by
    dsimp [nuE]
    exact (min_le_right _ _).trans (min_le_right _ _)
  let q : ℝ → PhysicalComplexRadialEnergyPair :=
    fun s => V s - W s - Zg s - Zalg s
  have hBounds (s : ℝ) (hs : s₀ ≤ s) :
      ‖q s‖ ≤ (CIn + CK + CRem) * s ^ (-nuE) ∧
      ‖q s + err s‖ ≤
        (CIn + CK + CRem) * s ^ (-nuE) + CErr * s ^ (-M) ∧
      ‖physicalGradientRealization
        (physicalEnergyEquiv.symm (q s).1)‖ ^ 2 +
      ‖physicalGradientRealization
        (physicalEnergyEquiv.symm (q s).2)‖ ^ 2 =
        (4 * Real.pi) *
          (‖(q s).1‖ ^ 2 + ‖(q s).2‖ ^ 2) := by
    let D : ThreeRegionEnergyData PhysicalComplexRadialEnergyPair :=
      { profile := q s
        inner := Qin s
        kummer := QK s
        remote := Qrem s
        split := hSplit s hs }
    have hS : 1 ≤ s := hs₀.trans hs
    have hWhole :=
      three_region_energy_bound D s nuE mIn mK mRem CIn CK CRem
        hS hnIn hnK hnRem hCIn hCK hCRem
        (hIn s hs) (hK s hs) (hRem s hs)
    have hError :=
      three_region_with_error_bound D (err s) s nuE
        mIn mK mRem M CIn CK CRem CErr
        hS hnIn hnK hnRem hCIn hCK hCRem
        (hIn s hs) (hK s hs) (hRem s hs) (hErr s hs)
    have hPhysicalReal :=
      physical_gradient_energy_of_radial_coordinate (q s).1
    have hPhysicalImag :=
      physical_gradient_energy_of_radial_coordinate (q s).2
    refine ⟨hWhole,hError,?_⟩
    rw [hPhysicalReal,hPhysicalImag]
    ring
  refine ⟨nuE,hnu,?_,?_⟩
  · intro s hs
    simpa only [q] using hBounds s hs
  · have hNuLimit :
        Tendsto (fun s : ℝ => (CIn + CK + CRem) * s ^ (-nuE))
          atTop (𝓝 0) := by
      have h :=
        (tendsto_const_nhds : Tendsto
          (fun _ : ℝ => CIn + CK + CRem)
          atTop (𝓝 (CIn + CK + CRem))).mul
          (tendsto_rpow_neg_atTop hnu)
      simpa only [mul_zero] using h
    have hErrLimit :
        Tendsto (fun s : ℝ => CErr * s ^ (-M))
          atTop (𝓝 0) := by
      have h :=
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => CErr)
          atTop (𝓝 CErr)).mul
          (tendsto_rpow_neg_atTop hM)
      simpa only [mul_zero] using h
    have hUpper : Tendsto
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
    have hFinal :
        Tendsto (fun s : ℝ => q s + err s)
          atTop (𝓝 (0 : PhysicalComplexRadialEnergyPair)) :=
      squeeze_zero_norm' hEventually hUpper
    simpa only [q] using hFinal

end HBL.Profile.GlobalH1
