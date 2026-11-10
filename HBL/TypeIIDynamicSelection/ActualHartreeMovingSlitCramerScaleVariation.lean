import HBL.TypeIIDynamicSelection.ActualHartreeTrueMovingGreenOneRadiusGain
import Mathlib.Tactic

/-!
# Moving-slit geometry from the true Hartree scale variation

The previously certified real-Cramer source-time budget is valid only for
1/a(τ) ≤ r ≤ B. The actual singular Green time MVT runs at every
intermediate τ and every radius between L(ell(s))/a(s) and
L(ell(t))/a(t), L(e) = e^(-1/16).

This theorem does NOT assume that inclusion. Instead it proves it from
the true physical scale's variation V along the time segment, and the
explicit slow-cutoff slack at the two endpoint scales. In particular it
pinpoints the exact missing modulation budget:
V * L(ell(endpoint)) ≤ a(endpoint) * (L(ell(endpoint)) - 1).
There is no prescribed Type-II rate, source envelope, or PDE residual
gain in this geometric statement.
-/

noncomputable section
set_option autoImplicit false
open Set
namespace HBL.TypeIIDynamicSelection

/-- A finite variation bound for the genuine time-varying scale converts
the two slow-inner endpoint margins into an original physical Cramer shell
on the ENTIRE moving slit and at EVERY intermediate time. -/
theorem actual_Hartree_original_Cramer_shell_covers_moving_slow_slit
    (a ell : ℝ → ℝ) (s t B V : ℝ)
    (has : 0 < a s) (hat : 0 < a t)
    (hes : 0 < ell s) (het : 0 < ell t)
    (haSegment : ∀ τ ∈ Icc (min s t) (max s t), 0 < a τ)
    (hVariationS : ∀ τ ∈ Icc (min s t) (max s t),
      |a τ - a s| ≤ V)
    (hVariationT : ∀ τ ∈ Icc (min s t) (max s t),
      |a τ - a t| ≤ V)
    (hMarginS : V * actualHartreeSlowInnerRadius (ell s) ≤
      a s * (actualHartreeSlowInnerRadius (ell s) - 1))
    (hMarginT : V * actualHartreeSlowInnerRadius (ell t) ≤
      a t * (actualHartreeSlowInnerRadius (ell t) - 1))
    (hUpper : ∀ x ∈ uIoc
      (actualHartreeSlowInnerRadius (ell t) / a t)
      (actualHartreeSlowInnerRadius (ell s) / a s), x ≤ B) :
    ∀ τ ∈ Icc (min s t) (max s t),
      ∀ x ∈ uIoc
        (actualHartreeSlowInnerRadius (ell t) / a t)
        (actualHartreeSlowInnerRadius (ell s) / a s),
          x ∈ Icc (1 / a τ) B := by
  let Ls := actualHartreeSlowInnerRadius (ell s)
  let Lt := actualHartreeSlowInnerRadius (ell t)
  have hLs : 0 < Ls := Real.rpow_pos_of_pos hes _
  have hLt : 0 < Lt := Real.rpow_pos_of_pos het _
  intro τ hτ x hx
  have haτ := haSegment τ hτ
  have hlowS : a s - V ≤ a τ := by
    have h := (abs_le.mp (hVariationS τ hτ)).1
    linarith
  have hlowT : a t - V ≤ a τ := by
    have h := (abs_le.mp (hVariationT τ hτ)).1
    linarith
  have hscaleS : a s ≤ Ls * a τ := by
    have hn : 0 ≤ (a τ - (a s - V)) * Ls :=
      mul_nonneg (by linarith) hLs.le
    change V * Ls ≤ a s * (Ls - 1) at hMarginS
    nlinarith [hn, hMarginS]
  have hscaleT : a t ≤ Lt * a τ := by
    have hn : 0 ≤ (a τ - (a t - V)) * Lt :=
      mul_nonneg (by linarith) hLt.le
    change V * Lt ≤ a t * (Lt - 1) at hMarginT
    nlinarith [hn, hMarginT]
  have hsourceS : (1 : ℝ) / a τ ≤ Ls / a s :=
    (div_le_div_iff₀ haτ has).2 (by nlinarith [hscaleS])
  have hsourceT : (1 : ℝ) / a τ ≤ Lt / a t :=
    (div_le_div_iff₀ haτ hat).2 (by nlinarith [hscaleT])
  have hmin : min (Ls / a s) (Lt / a t) ≤ x := by
    change x ∈ Ioc (min (Lt / a t) (Ls / a s))
      (max (Lt / a t) (Ls / a s)) at hx
    simpa only [min_comm] using hx.1.le
  refine ⟨(le_min hsourceS hsourceT).trans hmin, ?_⟩
  exact hUpper x hx


/-- Local moving-slit domain inclusion along a genuinely continuous scale and
slow radius. Unlike the quantitative full-interval variation lemma above,
this requires NO assumed variation budget for a(s): continuity and the
strict physical gap ell(s) < 1 produce a common neighborhood for both
the intermediate time and the moving radius endpoint. It can therefore
supply the domain condition in a LOCAL time derivative/MVT argument,
but supplies no estimate for the size of the physical source derivative. -/
theorem actual_Hartree_original_Cramer_shell_local_from_continuous_orbit
    (a ell : ℝ → ℝ) (s B : ℝ)
    (ha : 0 < a s) (he : 0 < ell s) (heSmall : ell s < 1)
    (hCa : ContinuousAt a s) (hCe : ContinuousAt ell s)
    (hB : actualHartreeSlowInnerRadius (ell s) / a s < B) :
    ∃ U : Set ℝ, U ∈ nhds s ∧
      ∀ t ∈ U, ∀ τ ∈ U,
        ∀ x ∈ uIoc
          (actualHartreeSlowInnerRadius (ell t) / a t)
          (actualHartreeSlowInnerRadius (ell s) / a s),
          x ∈ Icc (1 / a τ) B := by
  let L : ℝ → ℝ := fun u => (1 : ℝ) / a u
  let R : ℝ → ℝ := fun u => actualHartreeSlowInnerRadius (ell u) / a u
  have hSlow : 1 < actualHartreeSlowInnerRadius (ell s) := by
    unfold actualHartreeSlowInnerRadius
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg
      he heSmall (by norm_num : (-(1 / 16 : ℝ)) < 0)
  have hLc : ContinuousAt L s := by
    dsimp [L]
    exact continuousAt_const.div hCa (ne_of_gt ha)
  have hSlowC :
      ContinuousAt (fun u => actualHartreeSlowInnerRadius (ell u)) s := by
    simpa only [actualHartreeSlowInnerRadius, Function.comp_def] using
      (hCe.rpow_const (Or.inl (ne_of_gt he)) :
        ContinuousAt (fun u => (ell u) ^ (-(1 / 16 : ℝ))) s)
  have hRc : ContinuousAt R s := by
    dsimp [R]
    exact hSlowC.div hCa (ne_of_gt ha)
  have hLR : L s < R s := by
    change (1 : ℝ) / a s < actualHartreeSlowInnerRadius (ell s) / a s
    exact div_lt_div_of_pos_right hSlow ha
  have hRB : R s < B := hB
  let m : ℝ := (L s + R s) / 2
  have hLm : L s < m := by
    dsimp [m]
    linarith
  have hmR : m < R s := by
    dsimp [m]
    linarith
  have hE1 : {u : ℝ | L u < m} ∈ nhds s :=
    hLc.eventually (Iio_mem_nhds hLm)
  have hE2 : {u : ℝ | m < R u} ∈ nhds s :=
    hRc.eventually (Ioi_mem_nhds hmR)
  have hE3 : {u : ℝ | R u < B} ∈ nhds s :=
    hRc.eventually (Iio_mem_nhds hRB)
  let U : Set ℝ := {u | L u < m ∧ m < R u ∧ R u < B}
  have hU : U ∈ nhds s := by
    exact Filter.inter_mem hE1 (Filter.inter_mem hE2 hE3)
  refine ⟨U, hU, ?_⟩
  intro t ht τ hτ x hx
  change L t < m ∧ m < R t ∧ R t < B at ht
  change L τ < m ∧ m < R τ ∧ R τ < B at hτ
  change x ∈ Ioc (min (R t) (R s)) (max (R t) (R s)) at hx
  have hmx : m ≤ x :=
    (le_min (le_of_lt ht.2.1) (le_of_lt hmR)).trans hx.1.le
  have hxB : x ≤ B :=
    hx.2.trans (max_le (le_of_lt ht.2.2) (le_of_lt hRB))
  exact ⟨(le_of_lt hτ.1).trans hmx, hxB⟩


/-- Every intermediate time on a short physical orbit segment lies in
the SAME original Cramer shell as the moving two-endpoint Green slit.
This removes the quantitative scale-variation input from local MVT
applications; a bound for the original nonlinear source time
derivative remains a separate PDE obligation. -/
theorem actual_Hartree_original_Cramer_shell_local_segment_from_continuous_orbit
    (a ell : ℝ → ℝ) (s B : ℝ)
    (ha : 0 < a s) (he : 0 < ell s) (heSmall : ell s < 1)
    (hCa : ContinuousAt a s) (hCe : ContinuousAt ell s)
    (hB : actualHartreeSlowInnerRadius (ell s) / a s < B) :
    ∃ l u : ℝ, l < s ∧ s < u ∧
      ∀ t ∈ Ioo l u, ∀ τ ∈ Icc (min s t) (max s t),
        ∀ x ∈ uIoc
          (actualHartreeSlowInnerRadius (ell t) / a t)
          (actualHartreeSlowInnerRadius (ell s) / a s),
          x ∈ Icc (1 / a τ) B := by
  obtain ⟨U, hU, hCover⟩ :=
    actual_Hartree_original_Cramer_shell_local_from_continuous_orbit
      a ell s B ha he heSmall hCa hCe hB
  obtain ⟨l, u, hs, hSub⟩ :=
    (mem_nhds_iff_exists_Ioo_subset.mp hU)
  refine ⟨l, u, hs.1, hs.2, ?_⟩
  intro t ht τ hτ x hx
  have hτI : τ ∈ Ioo l u := by
    have hlo : l < min s t := lt_min hs.1 ht.1
    have hhi : max s t < u := max_lt hs.2 ht.2
    exact ⟨hlo.trans_le hτ.1, hτ.2.trans_lt hhi⟩
  exact hCover t (hSub ht) τ (hSub hτI) x hx

end HBL.TypeIIDynamicSelection
