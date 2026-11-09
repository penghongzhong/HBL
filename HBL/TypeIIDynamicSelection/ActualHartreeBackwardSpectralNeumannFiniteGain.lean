import HBL.TypeIIDynamicSelection.ActualHartreeBackwardZeroLeftSpectralVolterra
import HBL.TypeIIDynamicSelection.ActualHartreeMatchedBackwardQuadraticSpectralSource
import Mathlib.Tactic

/-!
# Finite backward spectral Neumann corrections from the actual origin Green map

This is a genuine finite recursion of the original normalized Cramer Green
operator, not a recurrence of invented scalar envelopes.  The zeroth term
is the matched physical-source Green field and each subsequent correction
uses the preceding field as its actual spectral source, with zero anchor
Cauchy data.

The only size input is the initial matched field on the backward physical
shell.  Integrability of each explicitly constructed Green forcing is
stated separately; it is NOT an assumption of decay or positive time order.
The exact backward Wronskian/Volterra estimate is invoked at every step.

The conclusion is a quantitative spatial estimate for every finite n.
It neither proves the original four-domain nonlinear time residual nor
the finite physical profile theorem of manuscript section 2.13.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner HBL.L2Kernel
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

/-- The actual n-th backward spectral correction with the ORIGINAL
zero-jet origin Kummer Green map.  No abstract right inverse is introduced. -/
noncomputable def actualHartreeBackwardSpectralNeumannIterate
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b : ℝ) (F : ℝ → ℂ) (U DU delta : ℂ) :
    ℕ → ℝ → ℂ
  | 0 => actualOriginMatchedKummerValue K a b F U DU
  | n + 1 =>
      actualOriginMatchedKummerValue K a b
        (fun x => delta *
          actualHartreeBackwardSpectralNeumannIterate K a b F U DU delta n x)
        0 0

/-- All finite actual Green iterates have a geometrically improved
backward-shell bound.  Their sources are literally delta times the
previous original Cramer-Green response.  There is no independently
assigned size envelope for any correction of positive index. -/
theorem actual_Hartree_backward_spectral_Neumann_all_finite_value_gain
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a b C G H : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ scale)
    (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hK : OriginBasisOn K a b C)
    (hModes : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (F : ℝ → ℂ) (U DU delta : ℂ)
    (hInitial : ∀ r ∈ Icc (a / 2) a,
      ‖actualHartreeBackwardSpectralNeumannIterate
          K a b F U DU delta 0 r‖ ≤ H)
    (hInt : ∀ (n : ℕ) (r : ℝ), r ∈ Icc (a / 2) a →
      IntervalIntegrable
        (originGreenSourceA K
          (fun x => delta *
            actualHartreeBackwardSpectralNeumannIterate
              K a b F U DU delta n x))
        volume r a)
    (hIntR : ∀ (n : ℕ),
      IntervalIntegrable
        (originGreenSourceA K
          (fun x => delta *
            actualHartreeBackwardSpectralNeumannIterate
              K a b F U DU delta n x))
        volume a b) :
    ∀ (n : ℕ) (r : ℝ), r ∈ Icc (a / 2) a →
      ‖actualHartreeBackwardSpectralNeumannIterate
          K a b F U DU delta n r‖ ≤
        (2 * G ^ 2 * a * ‖delta‖) ^ n * H := by
  let c : ℝ := 2 * G ^ 2 * a * ‖delta‖
  have hc : 0 ≤ c := by dsimp [c]; positivity
  intro n
  induction n with
  | zero =>
      intro r hr
      simpa only [pow_zero, one_mul] using hInitial r hr
  | succ n ih =>
      intro r hr
      let Hn : ℝ := c ^ n * H
      have hHn : 0 ≤ Hn := by
        dsimp [Hn]
        exact mul_nonneg (pow_nonneg hc _) hH
      have hM : 0 ≤ a * ‖delta‖ * Hn := by positivity
      have hForce (x : ℝ) (hx : x ∈ Icc (a / 2) a) :
          ‖delta * actualHartreeBackwardSpectralNeumannIterate
              K a b F U DU delta n x‖ ≤ (a * ‖delta‖ * Hn) / x := by
        have hxpos : 0 < x := (half_pos ha).trans_le hx.1
        have hPrev :
            ‖actualHartreeBackwardSpectralNeumannIterate
                K a b F U DU delta n x‖ ≤ Hn := ih x hx
        have hConst : 0 ≤ ‖delta‖ * Hn :=
          mul_nonneg (norm_nonneg delta) hHn
        have hMul := mul_le_mul_of_nonneg_left hx.2 hConst
        apply (le_div_iff₀ hxpos).2
        calc
          ‖delta * actualHartreeBackwardSpectralNeumannIterate
              K a b F U DU delta n x‖ * x =
              (‖delta‖ *
                ‖actualHartreeBackwardSpectralNeumannIterate
                  K a b F U DU delta n x‖) * x := by rw [norm_mul]
          _ ≤ (‖delta‖ * Hn) * x :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hPrev (norm_nonneg delta))
              hxpos.le
          _ ≤ (‖delta‖ * Hn) * a := hMul
          _ = a * ‖delta‖ * Hn := by ring
      have hOne :=
        actual_Hartree_zero_left_original_Green_backward_inverse_linear_bound
          K a b C G (a * ‖delta‖ * Hn) ha hab hb hG hM hK
          hModes
          (fun x => delta *
            actualHartreeBackwardSpectralNeumannIterate
              K a b F U DU delta n x)
          hForce r hr (hInt n r hr) (hIntR n)
      calc
        ‖actualHartreeBackwardSpectralNeumannIterate
            K a b F U DU delta (n + 1) r‖ ≤
              2 * G ^ 2 * (a * ‖delta‖ * Hn) := hOne
        _ = c ^ (n + 1) * H := by
          dsimp [c, Hn]
          rw [pow_succ]
          ring



/-- The all-finite backward spectral estimate with its INITIAL bound
produced by the SAME physical two-channel Hartree source and the
canonical actual Cramer matching jet. No independent initial
field-envelope hypothesis remains. All generated forcings are
the literal recursively defined original Green sources.

The interval-integrability assumptions record only analytical
regularity of these actual sources; they supply no decay exponents. -/
theorem actual_Hartree_same_source_backward_spectral_Neumann_finite_gain
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (a R B C G : ℝ)
    (ha : 0 < a) (hR : 2 < R)
    (hOrder : 2 * R / a ≤ B) (hB : B < scale)
    (hG : 0 ≤ G)
    (hK : OriginBasisOn K (2 * R / a) B C)
    (hModes : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.x x‖ ≤ G)
    (hSmall : 16 * R ^ 2 *
      ((1 + ‖frozenZeroCoeff mu theta‖) / a ^ 2) ≤ 1)
    (Fp Fm : ℝ → ℝ)
    (hp : InWeightedL2 (7 / 4 : ℝ) Fp)
    (hm : InWeightedL2 (7 / 4 : ℝ) Fm)
    (hcp : Continuous Fp) (hcm : Continuous Fm)
    (F : ℝ → ℂ)
    (hF : ∀ r ∈ Ioo (0 : ℝ) scale, ContinuousAt F r)
    (hSame : ∀ y ∈ Icc R (2 * R),
      actualMatchedScaledKummerApply mu theta a
        (actualOriginMatchedKummerPullback K a (2 * R / a) B
          F
          (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)).1
          (actualMomentLockedCanonicalInnerJet Fp Fm hp hm a (2 * R / a)).2) y =
        -actualHartreeTwoChannelPhysicalSource Fp Fm y)
    (delta : ℂ)
    (hInt : ∀ (n : ℕ) (x : ℝ),
      x ∈ Icc ((2 * R / a) / 2) (2 * R / a) →
      IntervalIntegrable
        (originGreenSourceA K
          (fun t => delta *
            actualHartreeBackwardSpectralNeumannIterate
              K (2 * R / a) B F
                (actualMomentLockedCanonicalInnerJet
                    Fp Fm hp hm a (2 * R / a)).1
                (actualMomentLockedCanonicalInnerJet
                    Fp Fm hp hm a (2 * R / a)).2 delta n t))
        volume x (2 * R / a))
    (hIntR : ∀ (n : ℕ),
      IntervalIntegrable
        (originGreenSourceA K
          (fun t => delta *
            actualHartreeBackwardSpectralNeumannIterate
              K (2 * R / a) B F
                (actualMomentLockedCanonicalInnerJet
                    Fp Fm hp hm a (2 * R / a)).1
                (actualMomentLockedCanonicalInnerJet
                    Fp Fm hp hm a (2 * R / a)).2 delta n t))
        volume (2 * R / a) B) :
    let r0 := 2 * R / a
    let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a r0
    let D := actualInnerShellValueConstant *
        (innerWeightedNorm (7 / 4 : ℝ) Fp +
          innerWeightedNorm (7 / 4 : ℝ) Fm) +
        8 * R ^ 2 * actualHartreeTwoChannelShellBudget mu theta a R Fp Fm
    ∀ (n : ℕ) (x : ℝ), x ∈ Icc (r0 / 2) r0 →
      ‖actualHartreeBackwardSpectralNeumannIterate
        K r0 B F J.1 J.2 delta n x‖ ≤
        (2 * G ^ 2 * r0 * ‖delta‖) ^ n * D := by
  dsimp only
  let L : ℝ := 2 * R
  let r0 : ℝ := L / a
  let J := actualMomentLockedCanonicalInnerJet Fp Fm hp hm a r0
  let D : ℝ := actualInnerShellValueConstant *
      (innerWeightedNorm (7 / 4 : ℝ) Fp +
        innerWeightedNorm (7 / 4 : ℝ) Fm) +
      8 * R ^ 2 * actualHartreeTwoChannelShellBudget mu theta a R Fp Fm
  let v := actualOriginMatchedKummerPullback K a r0 B F J.1 J.2
  have hL : 0 < L := by dsimp [L]; linarith
  have hr0 : 0 < r0 := div_pos hL ha
  have hRpos : 0 < R := by linarith
  let U : Set ℝ := Ioo 0 (a * scale)
  have hU : IsOpen U := isOpen_Ioo
  have hLscale : L < a * scale := by
    have h := (div_lt_iff₀ ha).1 (hOrder.trans_lt hB)
    simpa only [L, mul_comm] using h
  have hSub : Icc R (2 * R) ⊆ U := by
    intro t ht
    exact ⟨hRpos.trans_le ht.1, ht.2.trans_lt hLscale⟩
  have hClass :=
    actual_Hartree_matched_Kummer_pullback_classical K a ha
      hr0 hOrder hB F hF J.1 J.2
  have hv : ∀ x ∈ U, DifferentiableAt ℝ v x :=
    fun x hx => (hClass x hx).1.differentiableAt
  have hv2 : ∀ x ∈ Icc R (2 * R),
      DifferentiableAt ℝ (deriv v) x :=
    fun x hx => (hClass x (hSub hx)).2.1
  have hJet :=
    actual_Hartree_moment_locked_pullback_actual_inner_jet
      K L a hL ha hOrder hB Fp Fm hp hm F hF
  have hAnchor : L ∈ Icc R (2 * R) := ⟨by linarith, le_rfl⟩
  have hSame' : ∀ x ∈ Icc R (2 * R),
      actualMatchedScaledKummerApply mu theta a v x =
        -actualHartreeTwoChannelPhysicalSource Fp Fm x := by
    intro x hx
    simpa only [v, L, r0, J] using hSame x hx
  have hVal := actual_Hartree_backward_original_matched_Kummer_value_from_same_source
    mu theta a R L Fp Fm hp hm U v
      hcp hcm hU hSub ha hR hSmall hAnchor hv hv2
      hJet.1.symm hJet.2.2.1.symm hSame'
  have hStart : R ∈ Icc R (2 * R) := ⟨le_rfl, by linarith⟩
  have hD : 0 ≤ D := by
    have h := hVal R hStart
    change ‖v R‖ ≤ D at h
    exact (norm_nonneg _).trans h
  have haR : a * r0 = L := by
    dsimp [r0]
    field_simp [ha.ne']
  have hHalf : a * (r0 / 2) = R := by
    dsimp [L] at haR
    nlinarith [haR]
  have hInitial (x : ℝ) (hx : x ∈ Icc (r0 / 2) r0) :
      ‖actualHartreeBackwardSpectralNeumannIterate
          K r0 B F J.1 J.2 delta 0 x‖ ≤ D := by
    have hxPhys : a * x ∈ Icc R (2 * R) := by
      constructor
      · have h := mul_le_mul_of_nonneg_left hx.1 ha.le
        nlinarith [h, hHalf]
      · have h := mul_le_mul_of_nonneg_left hx.2 ha.le
        dsimp [L] at haR
        nlinarith [h, haR]
    have hScale : a * x / a = x := by field_simp [ha.ne']
    have h := hVal (a * x) hxPhys
    change ‖actualOriginMatchedKummerValue
      K r0 B F J.1 J.2 (a * x / a)‖ ≤ D at h
    simpa only [actualHartreeBackwardSpectralNeumannIterate, hScale] using h
  exact actual_Hartree_backward_spectral_Neumann_all_finite_value_gain
    K r0 B C G D hr0 hOrder hB.le hG hD hK hModes
    F J.1 J.2 delta hInitial hInt hIntR

end HBL.TypeIIDynamicSelection
