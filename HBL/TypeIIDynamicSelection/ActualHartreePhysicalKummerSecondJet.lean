import HBL.TypeIIDynamicSelection.ActualHartreePhysicalInnerKummerBridge
import HBL.TypeIIDynamicSelection.ActualHartreeKummerCanonicalLocalizedSource
import Mathlib.Tactic

/-!
# HBL revised 2.13: actual physical H+/H- C2 jets in Kummer coordinates

The SAME continuous complex Hartree source and genuine weighted L2
Fredholm datum construct real classical H+ and H- corrections.
Their C2 physical radial representatives are converted by the TRUE
spatial Jacobian k=sqrt(q), including the mandatory second
derivative factor k^2. The exact frozen Kummer operator on this
profile is then an explicit physical-PDE defect, not a postulated
zero. This supplies the differential bridge needed to test (rather
than assume) two-boundary trace compatibility.

This does not establish conjugacy of the full physical Hartree
operator with frozen Kummer, nonlinear remote source decay, full
global matching, or the dynamical Type-II blowup rate.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer HBL.Profile.ActualInner
open HBL.Modulation.Monopole HBL.Modulation.AffineTail HBL.L2Kernel

/-- The genuine second spatial derivative in Kummer coordinates. -/
def actualHartreeInnerKummerSecond
    (up um : ℝ → ℝ) (k r : ℝ) : ℂ :=
  ((k ^ 2 * deriv (deriv up) (k * r) : ℝ) : ℂ) +
    Complex.I * ((k ^ 2 * deriv (deriv um) (k * r) : ℝ) : ℂ)

/-- The full second derivative follows from the two physical real C2
profiles, with k^2 rather than an assumed independent Kummer jet. -/
theorem actual_Hartree_two_channel_Kummer_C2_chain_rule
    (up um : ℝ → ℝ) (k r : ℝ) (hr : 0 < r)
    (hup : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ up (k * x))
    (hum : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ um (k * x))
    (hup2 : DifferentiableAt ℝ (deriv up) (k * r))
    (hum2 : DifferentiableAt ℝ (deriv um) (k * r)) :
    HasDerivAt (deriv (actualHartreeInnerKummerProfile up um k))
      (actualHartreeInnerKummerSecond up um k r) r := by
  have hk : HasDerivAt (fun x : ℝ => k * x) k r :=
    hasDerivAt_const_mul k
  have hp : HasDerivAt
      (fun x : ℝ => ((k * deriv up (k * x) : ℝ) : ℂ))
      (((k ^ 2 * deriv (deriv up) (k * r) : ℝ) : ℂ)) r := by
    have h := ((hup2.hasDerivAt.scomp r hk).const_mul k).ofReal_comp
    convert h using 1
    · funext x
      rfl
    · exact_mod_cast (show k ^ 2 * deriv (deriv up) (k * r) =
          k * (k * deriv (deriv up) (k * r)) by ring)
  have hm : HasDerivAt
      (fun x : ℝ => ((k * deriv um (k * x) : ℝ) : ℂ))
      (((k ^ 2 * deriv (deriv um) (k * r) : ℝ) : ℂ)) r := by
    have h := ((hum2.hasDerivAt.scomp r hk).const_mul k).ofReal_comp
    convert h using 1
    · funext x
      rfl
    · exact_mod_cast (show k ^ 2 * deriv (deriv um) (k * r) =
          k * (k * deriv (deriv um) (k * r)) by ring)
  have hSlope : HasDerivAt
      (actualHartreeInnerKummerSlope up um k)
      (actualHartreeInnerKummerSecond up um k r) r := by
    change HasDerivAt
      (fun x : ℝ => ((k * deriv up (k * x) : ℝ) : ℂ) +
        Complex.I * ((k * deriv um (k * x) : ℝ) : ℂ))
      (((k ^ 2 * deriv (deriv up) (k * r) : ℝ) : ℂ) +
        Complex.I * ((k ^ 2 * deriv (deriv um) (k * r) : ℝ) : ℂ)) r
    exact hp.add (hm.const_mul Complex.I)
  have hFirst :
      deriv (actualHartreeInnerKummerProfile up um k) =ᶠ[𝓝 r]
        actualHartreeInnerKummerSlope up um k := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact (actual_Hartree_two_channel_inner_Kummer_chain_rule
      up um k x (hup x hx) (hum x hx)).deriv
  exact hSlope.congr_of_eventuallyEq hFirst

/-- Genuine original frozen Kummer differential operator on the
actual two-channel physical correction. No Kummer equation or
matching constraint is inserted as a hypothesis. -/
theorem actual_Hartree_two_channel_Kummer_operator_exact
    (mu theta : ℝ) (up um : ℝ → ℝ) (k r : ℝ) (hr : 0 < r)
    (hup : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ up (k * x))
    (hum : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ um (k * x))
    (hup2 : DifferentiableAt ℝ (deriv up) (k * r))
    (hum2 : DifferentiableAt ℝ (deriv um) (k * r)) :
    actualHartreeFrozenKummerRadialApply mu theta
      (actualHartreeInnerKummerProfile up um k) r =
      actualHartreeInnerKummerSecond up um k r +
        frozenFirstCoeff r * actualHartreeInnerKummerSlope up um k r +
        frozenZeroCoeff mu theta * actualHartreeInnerKummerProfile up um k r := by
  have hFirst := actual_Hartree_two_channel_inner_Kummer_chain_rule
    up um k r (hup r hr) (hum r hr)
  have hSecond := actual_Hartree_two_channel_Kummer_C2_chain_rule
    up um k r hr hup hum hup2 hum2
  unfold actualHartreeFrozenKummerRadialApply
  rw [hSecond.deriv, hFirst.deriv]

/-- The remaining *physical* Kummer-source conjugacy defect, which
must be bounded or canceled from the true Hartree equations. -/
def actualHartreeInnerKummerSourceDefect
    (mu theta : ℝ) (up um : ℝ → ℝ) (k r : ℝ)
    (F : ℝ → ℂ) : ℂ :=
  actualHartreeInnerKummerSecond up um k r +
    frozenFirstCoeff r * actualHartreeInnerKummerSlope up um k r +
    frozenZeroCoeff mu theta * actualHartreeInnerKummerProfile up um k r -
    F r

theorem actual_Hartree_two_channel_physical_Kummer_defect_exact
    (mu theta : ℝ) (up um : ℝ → ℝ) (k r : ℝ) (hr : 0 < r)
    (F : ℝ → ℂ)
    (hup : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ up (k * x))
    (hum : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ um (k * x))
    (hup2 : DifferentiableAt ℝ (deriv up) (k * r))
    (hum2 : DifferentiableAt ℝ (deriv um) (k * r)) :
    actualHartreeFrozenKummerRadialApply mu theta
      (actualHartreeInnerKummerProfile up um k) r - F r =
        actualHartreeInnerKummerSourceDefect mu theta up um k r F := by
  rw [actual_Hartree_two_channel_Kummer_operator_exact
    mu theta up um k r hr hup hum hup2 hum2]
  rfl

/-- The same REAL physical Hartree residual produces C2 inner Kummer
jets for both H+ and H- simultaneously, with the physical coordinate
factor sqrt(q)^2. The continuity and weighted source assumptions
remain explicit analytical interfaces: neither is manufactured. -/
theorem actual_Hartree_PDE_generates_two_channel_Kummer_C2_jets
    (sigma : ℝ) (hLower : 3 / 2 < sigma) (hUpper : sigma < 2)
    (V : ℝ → ℝ → ℝ) (Z : ℝ → ℝ → ℂ)
    (b omega s q : ℝ) (hq : 0 < q)
    (hCont : Continuous (actualOneLayerCommonPDEResidual V Z b omega s))
    (hWeighted : MemLp
      (fun r : ℝ => affineJapaneseWeight sigma r *
        ‖actualOneLayerCommonPDEResidual V Z b omega s r‖)
      2 halfLineMeasure) :
    let k := Real.sqrt q
    ∃ up um : ℝ → ℝ,
      InnerAffineProperties up
        (actualPlusCharge (actualOneLayerPlusPDE V Z b omega s)) ∧
      InnerAffineProperties um
        (actualMinusCharge (actualOneLayerMinusPDE V Z b omega s)) ∧
      ∀ r : ℝ, 0 < r →
        HasDerivAt (deriv (actualHartreeInnerKummerProfile up um k))
          (actualHartreeInnerKummerSecond up um k r) r := by
  dsimp only
  let k : ℝ := Real.sqrt q
  have hk : 0 < k := Real.sqrt_pos.mpr hq
  obtain ⟨up, um, hUp, hUm, hClassical⟩ :=
    actual_Hartree_one_PDE_source_has_classical_Hplus_Hminus_jets
      sigma hLower hUpper V Z b omega s hCont hWeighted
  refine ⟨up, um, hUp, hUm, ?_⟩
  intro r hr
  have hup (x : ℝ) (hx : 0 < x) :
      DifferentiableAt ℝ up (k * x) :=
    (hClassical (k * x) (mul_pos hk hx)).1
  have hum (x : ℝ) (hx : 0 < x) :
      DifferentiableAt ℝ um (k * x) :=
    (hClassical (k * x) (mul_pos hk hx)).2.2.1
  obtain ⟨_, hUp2, _, hUm2, _, _⟩ :=
    hClassical (k * r) (mul_pos hk hr)
  exact actual_Hartree_two_channel_Kummer_C2_chain_rule
    up um k r hr hup hum hUp2 hUm2

end HBL.TypeIIDynamicSelection
