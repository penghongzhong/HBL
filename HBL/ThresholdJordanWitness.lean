import HBL.AffineTailMinusZeroMode
import HBL.ThresholdTestExistence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Diagnostic audit of the asserted bounded exact zero/centre splitting.

This file proves the actual differential identity Hminus G = r Lambda W
for an explicit generalized radial profile, and the elementary topological
obstruction to a bounded zero projection when a nonzero kernel vector lies
in the closure of the range. The compact-cutoff convergence in homogeneous
Sobolev norm is proved separately in the mathematical note, NOT in Lean here.
No manuscript environment is accepted by these two diagnostic statements.
-/

noncomputable section
open Filter
open scoped Topology

namespace HBL.Modulation.ThresholdAudit

open HBL.Modulation.AffineTail

private def w1 (r : ℝ) : ℝ := -r / (1 + r ^ 2) * bubble r
private def w2 (r : ℝ) : ℝ := (2 * r ^ 2 - 1) / (1 + r ^ 2) ^ 2 * bubble r

private theorem w_hasDerivAt (r : ℝ) : HasDerivAt bubble (w1 r) r := by
  have hq : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * r) r := by
    have h := (hasDerivAt_const r (1 : ℝ)).add ((hasDerivAt_id r).pow 2)
    convert h using 1
    · funext x
      simp
    · norm_num
  have hqpos : 0 < (1 + r ^ 2 : ℝ) := by positivity
  have hsne : Real.sqrt (1 + r ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hqpos)
  have hs2 := Real.sq_sqrt hqpos.le
  have hs : HasDerivAt (fun x : ℝ => Real.sqrt (1 + x ^ 2))
      (r / Real.sqrt (1 + r ^ 2)) r := by
    convert hq.sqrt (ne_of_gt hqpos) using 1
    field_simp [hsne]
  have h := hs.inv hsne
  apply h.congr_deriv
  unfold w1 bubble
  rw [hs2]
  field_simp [hsne, ne_of_gt hqpos]

private theorem w1_hasDerivAt (r : ℝ) : HasDerivAt w1 (w2 r) r := by
  have hq : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * r) r := by
    have h := (hasDerivAt_const r (1 : ℝ)).add ((hasDerivAt_id r).pow 2)
    convert h using 1
    · funext x
      simp
    · norm_num
  have hqne : (1 + r ^ 2 : ℝ) ≠ 0 := by positivity
  have h := (((hasDerivAt_id r).neg).div hq hqne).mul (w_hasDerivAt r)
  apply h.congr_deriv
  unfold w1 w2
  simp only [Pi.neg_apply, Pi.div_apply, id_eq]
  field_simp [hqne]
  ring

/-- A globally smooth odd numerator, without an artificial singularity at r=0. -/
def jordanNumerator (r : ℝ) : ℝ :=
  r ^ 3 / 4 - (r ^ 2 - 1) * Real.arctan r + r * Real.log (1 + r ^ 2) - r

private def j1 (r : ℝ) : ℝ :=
  3 * r ^ 2 / 4 - 2 * r * Real.arctan r + Real.log (1 + r ^ 2)

private def j2 (r : ℝ) : ℝ := 3 * r / 2 - 2 * Real.arctan r

private theorem j_hasDerivAt (r : ℝ) : HasDerivAt jordanNumerator (j1 r) r := by
  have hq : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * r) r := by
    have h := (hasDerivAt_const r (1 : ℝ)).add ((hasDerivAt_id r).pow 2)
    convert h using 1
    · funext x
      simp
    · norm_num
  have hqne : (1 + r ^ 2 : ℝ) ≠ 0 := by positivity
  have h := ((((hasDerivAt_id r).pow 3).div_const 4).sub
    ((((hasDerivAt_id r).pow 2).sub_const 1).mul (Real.hasDerivAt_arctan r))).add
    ((hasDerivAt_id r).mul (hq.log hqne))
  have h' := h.sub (hasDerivAt_id r)
  apply h'.congr_deriv
  unfold j1
  simp only [Pi.pow_apply, id_eq]
  field_simp [hqne]
  ring

private theorem j1_hasDerivAt (r : ℝ) : HasDerivAt j1 (j2 r) r := by
  have hq : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * r) r := by
    have h := (hasDerivAt_const r (1 : ℝ)).add ((hasDerivAt_id r).pow 2)
    convert h using 1
    · funext x
      simp
    · norm_num
  have hqne : (1 + r ^ 2 : ℝ) ≠ 0 := by positivity
  have h := (((((hasDerivAt_id r).pow 2).const_mul 3).div_const 4).sub
    (((hasDerivAt_id r).const_mul 2).mul (Real.hasDerivAt_arctan r))).add (hq.log hqne)
  apply h.congr_deriv
  unfold j2
  simp only [id_eq]
  field_simp [hqne]
  ring

/-- Half-line generalized mode G=r g for the actual physical phase channel. -/
def jordanHalfLine (r : ℝ) : ℝ := bubble r * jordanNumerator r

private def g1 (r : ℝ) : ℝ := w1 r * jordanNumerator r + bubble r * j1 r
private def g2 (r : ℝ) : ℝ :=
  w2 r * jordanNumerator r + 2 * w1 r * j1 r + bubble r * j2 r

private theorem g_hasDerivAt (r : ℝ) : HasDerivAt jordanHalfLine (g1 r) r :=
  (w_hasDerivAt r).mul (j_hasDerivAt r)

private theorem g1_hasDerivAt (r : ℝ) : HasDerivAt g1 (g2 r) r := by
  have h := ((w1_hasDerivAt r).mul (j_hasDerivAt r)).add
    ((w_hasDerivAt r).mul (j1_hasDerivAt r))
  apply h.congr_deriv
  unfold g2
  ring

/-- Exact generalized threshold equation, on the existing Hminus and
existing scale resonance. There is no spectral or inverse hypothesis. -/
theorem jordanHalfLine_exact (r : ℝ) :
    hMinusApply jordanHalfLine r = resonancePlus r := by
  have hfirst : deriv jordanHalfLine = g1 := funext fun x => (g_hasDerivAt x).deriv
  have hsecond : deriv (deriv jordanHalfLine) r = g2 r := by
    rw [hfirst]
    exact (g1_hasDerivAt r).deriv
  have hw : deriv bubble r = w1 r := (w_hasDerivAt r).deriv
  unfold hMinusApply
  rw [hsecond]
  unfold g2 w1 w2 jordanHalfLine jordanNumerator j1 j2 potential
  unfold resonancePlus radialResonancePlus dilationGenerator
  rw [hw]
  unfold w1
  have hqne : (1 + r ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp [hqne]
  ring

/-- A bounded map cannot annihilate a convergent range sequence and
fix its nonzero limit. This is the topological step in the obstruction;
the concrete homogeneous-Sobolev cutoff convergence is a separate proof. -/
theorem no_bounded_zero_projection_of_range_limit
    {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : D → E) (z : ℕ → D) (e : E) (he : e ≠ 0)
    (hlim : Tendsto (fun n => A (z n)) atTop (𝓝 e)) :
    ¬ ∃ P : E →L[ℝ] E, (∀ x, P (A x) = 0) ∧ P e = e := by
  rintro ⟨P, hzero, hfix⟩
  have hp : Tendsto (fun n => P (A (z n))) atTop (𝓝 (P e)) :=
    P.continuous.continuousAt.tendsto.comp hlim
  have hp0 : Tendsto (fun n => P (A (z n))) atTop (𝓝 (0 : E)) := by
    simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : E)) atTop (𝓝 0))
  exact he (hfix.symm.trans (tendsto_nhds_unique hp hp0))

end HBL.Modulation.ThresholdAudit
