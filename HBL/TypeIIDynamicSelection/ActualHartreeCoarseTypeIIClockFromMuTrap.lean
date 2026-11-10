import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# HBL: coarse dynamically selected Type-II clock, no prescribed rate

This is the replacement scalar TERMINAL for the first stage of the
revised main proof. It derives linear clock growth and a vanishing
Type-I normalized scale from the actual two-channel modulation
identity q_s = 4*mu and an invariant positive trap for mu.

No limit of mu, no derivative decay estimate, no preassigned blowup
exponent and no Hartree orbit existence is assumed. The still OPEN
PDE obligation is to construct one true radial Hartree orbit for
which the original modulation equation and invariant trap hold.

The theorem only closes the scalar kinematics. It does NOT verify
the original full Section 2.13 or Type-II existence main theorem.
-/

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection

/-- Once an actual Hartree trajectory supplies q_s = 4 mu and a
positive, bounded invariant physical mu-trapping interval, the
renormalized clock grows linearly and the Type-I normalized
concentration parameter q^(-1/2) vanishes. Neither a mu-limit
nor an asymptotic rate is required. -/
theorem actual_Hartree_coarse_TypeII_clock_from_dynamical_mu_trap
    (q mu : ℝ → ℝ) (s0 m M : ℝ)
    (hq0 : 0 < q s0) (hm : 0 < m)
    (hq : ∀ s ∈ Ici s0, HasDerivAt q (4 * mu s) s)
    (htrap : ∀ s ∈ Ici s0, m ≤ mu s ∧ mu s ≤ M) :
    (∀ s : ℝ, s0 ≤ s →
      q s0 + 4 * m * (s-s0) ≤ q s ∧
      q s ≤ q s0 + 4 * M * (s-s0) ∧
      0 < q s) ∧
    Tendsto q atTop atTop ∧
    Tendsto (fun s : ℝ => (q s) ^ (-(1 / 2 : ℝ)))
      atTop (𝓝 0) := by
  have hCont : ContinuousOn q (Ici s0) := by
    intro x hx
    exact (hq x hx).continuousAt.continuousWithinAt
  have hDiff : DifferentiableOn ℝ q (interior (Ici s0)) := by
    intro x hx
    exact (hq x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hDeriv (x : ℝ) (hx : x ∈ interior (Ici s0)) :
      deriv q x = 4 * mu x :=
    (hq x (interior_subset hx)).deriv
  have hLowerDerivative :
      ∀ x ∈ interior (Ici s0), 4 * m ≤ deriv q x := by
    intro x hx
    rw [hDeriv x hx]
    exact mul_le_mul_of_nonneg_left (htrap x (interior_subset hx)).1 (by norm_num)
  have hUpperDerivative :
      ∀ x ∈ interior (Ici s0), deriv q x ≤ 4 * M := by
    intro x hx
    rw [hDeriv x hx]
    exact mul_le_mul_of_nonneg_left (htrap x (interior_subset hx)).2 (by norm_num)
  have hLinear (s : ℝ) (hs : s0 ≤ s) :
      q s0 + 4 * m * (s-s0) ≤ q s ∧
      q s ≤ q s0 + 4 * M * (s-s0) := by
    have hs0I : s0 ∈ Ici s0 := by simp
    have hsI : s ∈ Ici s0 := hs
    have hLower : (4 * m) * (s - s0) ≤ q s - q s0 :=
      Convex.mul_sub_le_image_sub_of_le_deriv
        (convex_Ici s0) hCont hDiff hLowerDerivative
        s0 hs0I s hsI hs
    have hUpper : q s - q s0 ≤ (4 * M) * (s - s0) :=
      Convex.image_sub_le_mul_sub_of_deriv_le
        (convex_Ici s0) hCont hDiff hUpperDerivative
        s0 hs0I s hsI hs
    constructor <;> linarith
  have hPos (s : ℝ) (hs : s0 ≤ s) : 0 < q s := by
    have hb := (hLinear s hs).1
    have hp : 0 ≤ 4 * m * (s-s0) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hs)
    linarith
  have hBounds (s : ℝ) (hs : s0 ≤ s) :
      q s0 + 4 * m * (s-s0) ≤ q s ∧
      q s ≤ q s0 + 4 * M * (s-s0) ∧ 0 < q s :=
    ⟨(hLinear s hs).1, (hLinear s hs).2, hPos s hs⟩
  have hGrowth : Tendsto q atTop atTop := by
    apply tendsto_atTop.2
    intro B
    let S : ℝ := max s0 (s0 + (B - q s0)/(4*m) + 1)
    filter_upwards [eventually_ge_atTop S] with s hs
    have hs0 : s0 ≤ s := (le_max_left _ _).trans hs
    have hgap : (B - q s0)/(4*m) + 1 ≤ s-s0 := by
      have hS : s0 + (B - q s0)/(4*m) + 1 ≤ S :=
        le_max_right _ _
      linarith
    have hc : 0 < 4 * m := by positivity
    have hMult :
        (4*m) * ((B - q s0)/(4*m) + 1) ≤ (4*m) * (s-s0) :=
      mul_le_mul_of_nonneg_left hgap hc.le
    have hCancel : (4*m) * ((B - q s0)/(4*m)) = B - q s0 := by
      field_simp [hc.ne']
    have hBound := (hLinear s hs0).1
    nlinarith [hMult, hCancel]
  have hTypeII :
      Tendsto (fun s : ℝ => (q s) ^ (-(1 / 2 : ℝ)))
        atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_rpow_neg_atTop
        (by norm_num : (0 : ℝ) < (1 / 2 : ℝ))).comp hGrowth
  exact ⟨hBounds, hGrowth, hTypeII⟩



/-- The physical remaining-time clock is NOT an independent prescribed
terminal law. Given the SAME two-channel modulation equations
q_s = 4*mu and ell_s = -((1+4*mu)/(2*q))*ell, its exact physical
derivative is -ell². The true PDE must still furnish these scalar
identities; the theorem does not assume a terminal exponent. -/
theorem actual_Hartree_dynamic_remaining_time_from_two_channel_equations
    (q ell mu : ℝ → ℝ) (s : ℝ)
    (hqpos : 0 < q s)
    (hq : HasDerivAt q (4 * mu s) s)
    (hell : HasDerivAt ell
      (-((1 + 4 * mu s) / (2 * q s)) * ell s) s) :
    HasDerivAt (fun t => q t * (ell t) ^ 2)
      (-(ell s) ^ 2) s := by
  have hSquare := hell.mul hell
  have h := hq.mul hSquare
  convert h using 1
  · funext t
    simp only [Pi.mul_apply]
    ring
  · simp only [Pi.mul_apply] 
    field_simp [hqpos.ne']
    ring

/-- Adding the ORIGINAL physical-time equation t_s = ell² cancels
the remaining-time derivative exactly. This gives the conserved
terminal clock from the physical modulation equations, rather than
postulating an independent terminal time or blowup law. -/
theorem actual_Hartree_dynamic_terminal_clock_local_conservation
    (q ell mu time : ℝ → ℝ) (s : ℝ)
    (hqpos : 0 < q s)
    (hq : HasDerivAt q (4 * mu s) s)
    (hell : HasDerivAt ell
      (-((1 + 4 * mu s) / (2 * q s)) * ell s) s)
    (htime : HasDerivAt time ((ell s) ^ 2) s) :
    HasDerivAt (fun t => time t + q t * (ell t) ^ 2) 0 s := by
  have h := htime.add
    (actual_Hartree_dynamic_remaining_time_from_two_channel_equations
      q ell mu s hqpos hq hell)
  convert h using 1
  ring



/-- The same dynamical trap also forces a STRICTLY better than
self-similar physical scale envelope. This logarithmic form avoids
prescribing the terminal exponent or a separate ell(s) bootstrap:
G(s) = log ell(s) + log q(s)/2 + log Q(s)/(8*M)
is nonincreasing, where Q(s)=q(s0)+4*M*(s-s0).

The explicit physical exponent 1/2 + 1/(8*M) is a direct
corollary by exponentiation and the already verified q bounds.
The actual Hartree PDE must still construct the trapped orbit. -/
theorem actual_Hartree_dynamic_mu_trap_log_scale_gain
    (q ell mu : ℝ → ℝ) (s0 m M : ℝ)
    (hq0 : 0 < q s0) (hm : 0 < m)
    (hq : ∀ s ∈ Ici s0, HasDerivAt q (4 * mu s) s)
    (hell : ∀ s ∈ Ici s0,
      HasDerivAt ell
        (-((1 + 4 * mu s) / (2 * q s)) * ell s) s)
    (hellPos : ∀ s ∈ Ici s0, 0 < ell s)
    (htrap : ∀ s ∈ Ici s0, m ≤ mu s ∧ mu s ≤ M) :
    ∀ s : ℝ, s0 ≤ s →
      Real.log (ell s) + Real.log (q s) / 2 +
        Real.log (q s0 + 4 * M * (s - s0)) / (8 * M) ≤
      Real.log (ell s0) + Real.log (q s0) / 2 +
        Real.log (q s0) / (8 * M) := by
  obtain ⟨hBounds, _hGrowth, _hTypeII⟩ :=
    actual_Hartree_coarse_TypeII_clock_from_dynamical_mu_trap
      q mu s0 m M hq0 hm hq htrap
  have hs0mem : s0 ∈ Ici s0 := by simp
  have hM : 0 < M :=
    lt_of_lt_of_le hm ((htrap s0 hs0mem).1.trans (htrap s0 hs0mem).2)
  let Q : ℝ → ℝ := fun s => q s0 + 4 * M * (s - s0)
  let G : ℝ → ℝ := fun s =>
    Real.log (ell s) + Real.log (q s) / 2 +
      Real.log (Q s) / (8 * M)
  have hQpos (s : ℝ) (hs : s ∈ Ici s0) : 0 < Q s :=
    (hBounds s hs).2.2.trans_le (hBounds s hs).2.1
  have hQderiv (s : ℝ) : HasDerivAt Q (4 * M) s := by
    have hbase := ((hasDerivAt_id s).sub_const s0).const_mul (4 * M)
    have htotal := (hasDerivAt_const s (q s0)).add hbase
    convert htotal using 1
    · funext x
      dsimp [Q]
    · ring
  have hGderiv (s : ℝ) (hs : s ∈ Ici s0) :
      HasDerivAt G
        (-1 / (2 * q s) + 1 / (2 * Q s)) s := by
    have heLog := (hell s hs).log (hellPos s hs).ne'
    have hqLog := (hq s hs).log (hBounds s hs).2.2.ne'
    have hQLog := (hQderiv s).log (hQpos s hs).ne'
    have htotal := (heLog.add (hqLog.div_const 2)).add
      (hQLog.div_const (8 * M))
    convert htotal using 1
    · funext x
      dsimp [G]
      simp only [Pi.add_apply, Pi.div_apply]
    · dsimp only [Q]
      field_simp [hq0.ne', (hBounds s hs).2.2.ne',
        (hQpos s hs).ne', hM.ne']
      ring
  have hGcont : ContinuousOn G (Ici s0) := by
    intro s hs
    exact (hGderiv s hs).continuousAt.continuousWithinAt
  have hGdiff : DifferentiableOn ℝ G (interior (Ici s0)) := by
    intro s hs
    exact (hGderiv s (interior_subset hs)).differentiableAt.differentiableWithinAt
  have hGdecrease : ∀ s ∈ interior (Ici s0), deriv G s ≤ 0 := by
    intro s hs
    have hsI : s ∈ Ici s0 := interior_subset hs
    have hposQ : 0 < Q s := hQpos s hsI
    have hposq : 0 < q s := (hBounds s hsI).2.2
    have hcomp : q s ≤ Q s := (hBounds s hsI).2.1
    have hInv : (1 : ℝ) / (2 * Q s) ≤ 1 / (2 * q s) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * Q s)
        (by positivity : 0 < 2 * q s)).2
      nlinarith
    rw [(hGderiv s hsI).deriv]
    calc
      -1 / (2 * q s) + 1 / (2 * Q s) =
          1 / (2 * Q s) - 1 / (2 * q s) := by ring
      _ ≤ 0 := sub_nonpos.mpr hInv
  intro s hs
  have hsI : s ∈ Ici s0 := hs
  have hNonincrease :=
    Convex.image_sub_le_mul_sub_of_deriv_le
      (convex_Ici s0) hGcont hGdiff hGdecrease
      s0 hs0mem s hsI hs
  have hQ0 : Q s0 = q s0 := by dsimp [Q]; ring
  dsimp [G] at hNonincrease
  rw [hQ0] at hNonincrease
  change
    Real.log (ell s) + Real.log (q s) / 2 +
      Real.log (Q s) / (8 * M) ≤
    Real.log (ell s0) + Real.log (q s0) / 2 +
      Real.log (q s0) / (8 * M)
  linarith

end HBL.TypeIIDynamicSelection
