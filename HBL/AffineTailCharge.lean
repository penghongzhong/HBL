import HBL.FirstModulationLemma

/-!
Algebraic core of the manuscript's affine-tail threshold-charge lemma.

Once the Green/self-adjointness calculation supplies
  ell(H(chi_aff r)) = -c,   c != 0,
the charge is forced uniquely:
  alpha = -ell(F0)/c.
This module proves the existence, exact formula, and uniqueness in an
arbitrary real normed vector space.  The analytic Green identity for the
two concrete half-line Hartree operators is deliberately separated into
the next modules.
-/

noncomputable section

namespace HBL.AffineTail

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine threshold charge determined by a nonzero resonance limit. -/
def charge (ell : E →L[ℝ] ℝ) (c : ℝ) (F₀ : E) : ℝ :=
  -(ell F₀) / c

/-- The proposed affine charge annihilates the resonance pairing as soon
as the affine model has pairing -c. -/
theorem charge_annihilates
    (ell : E →L[ℝ] ℝ) (c : ℝ) (hc : c ≠ 0)
    (F₀ qAff : E) (hq : ell qAff = -c) :
    ell (F₀ - charge ell c F₀ • qAff) = 0 := by
  rw [map_sub, map_smul, hq]
  change ell F₀ - charge ell c F₀ * (-c) = 0
  unfold charge
  field_simp [hc] <;> ring

/-- Any scalar that annihilates the threshold pairing equals the proposed
affine charge. -/
theorem charge_unique
    (ell : E →L[ℝ] ℝ) (c : ℝ) (hc : c ≠ 0)
    (F₀ qAff : E) (hq : ell qAff = -c)
    (alpha : ℝ)
    (hzero : ell (F₀ - alpha • qAff) = 0) :
    alpha = charge ell c F₀ := by
  have hzero' := hzero
  rw [map_sub, map_smul, hq] at hzero'
  change ell F₀ - alpha * (-c) = 0 at hzero'
  have hlin : ell F₀ + alpha * c = 0 := by
    linarith
  unfold charge
  apply (eq_div_iff hc).2
  linarith

/-- Exact existence-and-uniqueness statement corresponding to the scalar
part of the manuscript lemma. -/
theorem existsUnique_charge
    (ell : E →L[ℝ] ℝ) (c : ℝ) (hc : c ≠ 0)
    (F₀ qAff : E) (hq : ell qAff = -c) :
    ∃! alpha : ℝ, ell (F₀ - alpha • qAff) = 0 := by
  refine ⟨charge ell c F₀, charge_annihilates ell c hc F₀ qAff hq, ?_⟩
  intro alpha hzero
  exact charge_unique ell c hc F₀ qAff hq alpha hzero

/-- The unique zero is exactly the formula displayed in the manuscript. -/
theorem zero_iff_eq_charge
    (ell : E →L[ℝ] ℝ) (c : ℝ) (hc : c ≠ 0)
    (F₀ qAff : E) (hq : ell qAff = -c)
    (alpha : ℝ) :
    ell (F₀ - alpha • qAff) = 0 ↔
      alpha = -(ell F₀) / c := by
  constructor
  · intro h
    exact charge_unique ell c hc F₀ qAff hq alpha h
  · intro h
    rw [h]
    exact charge_annihilates ell c hc F₀ qAff hq

end HBL.AffineTail
