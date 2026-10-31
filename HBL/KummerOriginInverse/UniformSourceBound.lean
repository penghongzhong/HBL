import HBL.KummerOriginInverse.C1Bound

noncomputable section
set_option autoImplicit false
open Set
namespace HBL.Profile.Kummer

/-- The manuscript's two-endpoint origin basis yields one source-to-C1
constant for every parameter in the prescribed compact set. No new inverse
or outgoing boundary condition is postulated. -/
theorem exists_compact_origin_kummer_source_bound
    (A : Set (ℝ × ℝ)) (hA : IsCompact A)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧
      ∀ p ∈ A, ∃ K : OriginKummerPair p.1 p.2 (b + 1),
        OriginBasisOn K a b C ∧ OriginBasisNormalization K ∧
        ∀ (F : ℝ → ℂ) (M : ℝ),
          0 ≤ M → (∀ r ∈ Icc a b, ‖F r‖ ≤ M) →
          ∀ r ∈ Icc a b,
            ‖originAnnulusValue K a b F r‖ +
              ‖originAnnulusSlope K a b F r‖ ≤
                (2 * C ^ 3 * (b - a)) * M := by
  obtain ⟨C, H, hC, hH, hpair⟩ :=
    exists_compact_origin_kummer_basis A hA a b ha hab
  refine ⟨C, H, hC, hH, ?_⟩
  intro p hp
  obtain ⟨K, hK, hnorm, _, _⟩ := hpair p hp
  refine ⟨K, hK, hnorm, ?_⟩
  intro F M hM hF r hr
  exact originAnnulus_value_slope_norm_le K a b C M hC.le hM hK F hF hr

#print axioms exists_compact_origin_kummer_source_bound
end HBL.Profile.Kummer
