import HBL.KummerOriginGreen.UniformBound

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

/-- Exact origin-gauge Green bridge on a *prescribed* positive annulus:
the two actual normalized basis functions solve the frozen physical ODE,
the integral construction solves its forced equation with separated endpoint
conditions, and one constant controls the C1 norm over every member of the
given compact parameter set. This is a Kummer-region result, not the
manuscript's full nonlinear one-layer Hartree elimination. -/
theorem exists_compact_originGreen_outgoing_and_uniform
    (A : Set (ℝ × ℝ)) (hA : IsCompact A)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧
      ∀ p ∈ A, ∃ K : OriginKummerPair p.1 p.2 (b + 1),
        OriginBasisOn K a b C ∧ OriginBasisNormalization K ∧
        (∀ (F : ℝ → ℂ), Continuous F →
          (∀ r ∈ Ioo a b,
            HasDerivAt (originGreenValue K a b F) (originGreenSlope K a b F r) r ∧
            HasDerivAt (originGreenSlope K a b F) (originGreenSecond K a b F r) r ∧
            originGreenSecond K a b F r +
                frozenFirstCoeff r * originGreenSlope K a b F r +
                frozenZeroCoeff p.1 p.2 * originGreenValue K a b F r = F r) ∧
          (originGreenValue K a b F b * originPhysicalSlope K.x K.dx b -
             originGreenSlope K a b F b * originPhysicalValue K.x b = 0) ∧
          (originPhysicalValue K.y a * originGreenSlope K a b F a -
             originPhysicalSlope K.y K.dy a * originGreenValue K a b F a = 0) ∧
          (∀ M : ℝ, 0 ≤ M → (∀ r ∈ Icc a b, ‖F r‖ ≤ M) →
             ∀ r ∈ Icc a b,
               ‖originGreenValue K a b F r‖ + ‖originGreenSlope K a b F r‖ ≤
                 (2 * C ^ 3 * (b - a)) * M)) := by
  obtain ⟨C, H, hC, hH, hpairs⟩ :=
    exists_compact_origin_kummer_basis A hA a b ha hab
  refine ⟨C, H, hC, hH, ?_⟩
  intro p hp
  obtain ⟨K, hK, hN, _, _⟩ := hpairs p hp
  refine ⟨K, hK, hN, ?_⟩
  intro F hF
  obtain ⟨hODE, hplus, hminus⟩ := originGreen_classical_outgoing K hK hab F hF
  refine ⟨hODE, hplus, hminus, ?_⟩
  intro M hM hbound r hr
  exact originGreen_value_slope_norm_le K a b C M hC.le hM hK F hbound hr

end HBL.Profile.Kummer
