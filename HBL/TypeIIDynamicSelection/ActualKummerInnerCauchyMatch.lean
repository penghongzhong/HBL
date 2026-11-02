import HBL.KummerLocalInverse.PhysicalClassical
import HBL.KummerLocalInverse.PhysicalDerivatives
import HBL.KummerLocalInverse.PhysicalEquation
import HBL.KummerPrescribedAnnulus.ActualPair
import Mathlib.Tactic

/-!
# Actual inhomogeneous Kummer Cauchy matching, original HBL 2.12

For the previously constructed genuine normalized physical Kummer
fundamental pair (phi,psi) and its *actual* nonhomogeneous Green solution,
use the NONZERO physical Wronskian to select unique homogeneous
coefficients such that the Kummer solution's value and first derivative
match ANY prescribed pair of complex inner boundary traces at z-d.

The correction uses only actual homogeneous solutions of the original
frozen Kummer ODE, so it preserves the COMPLETE classical equation
u'' + first(r)u' + zero(mu,theta)u = F(r) on [z-d,z+d].

The boundary-jet matching is DERIVED by Wronskian inversion, not
inserted as a solver assumption. The remaining challenge is to match
the second (remote) boundary simultaneously and prove quantitative
source/jet bounds for the actual same-PDE orbit. No Type II rate
and no abstract RegionalSolver interface are present.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer

/-- Unique first homogeneous coefficient for a prescribed *difference*
(p,q) between a desired Cauchy jet and the normalized Kummer Green jet. -/
def actualKummerMatchPhi
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (t : ℝ) (p q : ℂ) : ℂ :=
  (p * K.dpsi t - q * K.psi t) / localAnnulusWronskian K t

/-- Unique second homogeneous coefficient for the same actual Wronskian. -/
def actualKummerMatchPsi
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (t : ℝ) (p q : ℂ) : ℂ :=
  (K.phi t * q - K.dphi t * p) / localAnnulusWronskian K t

/-- Exact two-by-two inversion of the original physical Kummer Wronskian.
Both Cauchy coordinates are matched; no boundary equation is postulated. -/
theorem actual_Kummer_Wronskian_two_Cauchy_jets_match
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (t : ℝ) (ht : t ∈ Icc (-eps) eps) (p q : ℂ) :
    actualKummerMatchPhi K t p q * K.phi t +
      actualKummerMatchPsi K t p q * K.psi t = p ∧
    actualKummerMatchPhi K t p q * K.dphi t +
      actualKummerMatchPsi K t p q * K.dpsi t = q := by
  have hW : localAnnulusWronskian K t ≠ 0 := K.wronskian_ne t ht
  unfold actualKummerMatchPhi actualKummerMatchPsi
  constructor
  · field_simp [hW]
    unfold localAnnulusWronskian
    ring
  · field_simp [hW]
    unfold localAnnulusWronskian
    ring

/-- The actual nonhomogeneous classical Kummer Green solution plus
two genuine Kummer fundamental solutions. -/
def actualKummerCauchyValue
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (F : ℝ → ℂ) (a c : ℂ) (r : ℝ) : ℂ :=
  physicalLocalKummerValue K d F r +
    a * K.phi (r - z) + c * K.psi (r - z)

/-- Its exact first derivative, on the entire prescribed annulus. -/
def actualKummerCauchyDeriv
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (F : ℝ → ℂ) (a c : ℂ) (r : ℝ) : ℂ :=
  physicalLocalKummerDeriv K d F r +
    a * K.dphi (r - z) + c * K.dpsi (r - z)

/-- Its second derivative with every original frozen coefficient. -/
def actualKummerCauchySecond
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (F : ℝ → ℂ) (a c : ℂ) (r : ℝ) : ℂ :=
  physicalLocalKummerSecond K d F r +
    a * (-(frozenFirstCoeff r * K.dphi (r - z) +
      frozenZeroCoeff mu theta * K.phi (r - z))) +
    c * (-(frozenFirstCoeff r * K.dpsi (r - z) +
      frozenZeroCoeff mu theta * K.psi (r - z)))

/-- The corrected physical Kummer source obeys the original FULL
classical inhomogeneous second-order ODE, with first and second
derivatives justified rather than introduced as algebraic variables. -/
theorem actual_Kummer_Cauchy_corrected_classical_equation
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (F : ℝ → ℂ) (hF : Continuous F)
    (a c : ℂ) (r : ℝ) (hr : r ∈ Icc (z - d) (z + d)) :
    HasDerivAt (actualKummerCauchyValue K d F a c)
      (actualKummerCauchyDeriv K d F a c r) r ∧
    HasDerivAt (deriv (actualKummerCauchyValue K d F a c))
      (actualKummerCauchySecond K d F a c r) r ∧
    deriv (deriv (actualKummerCauchyValue K d F a c)) r +
      frozenFirstCoeff r *
        deriv (actualKummerCauchyValue K d F a c) r +
      frozenZeroCoeff mu theta *
        actualKummerCauchyValue K d F a c r = F r := by
  have ha : -d ∈ Icc (-eps) eps := ⟨by linarith, by linarith⟩
  have hb : d ∈ Icc (-eps) eps := ⟨by linarith, by linarith⟩
  have hFshift : Continuous (fun t => F (z + t)) :=
    hF.comp (continuous_const.add continuous_id)
  have hOpen : r ∈ Ioo (z - eps) (z + eps) := by
    constructor <;> linarith [hr.1, hr.2]
  have hFirstOpen (x : ℝ) (hx : x ∈ Ioo (z - eps) (z + eps)) :
      HasDerivAt (actualKummerCauchyValue K d F a c)
        (actualKummerCauchyDeriv K d F a c x) x := by
    have ht : x - z ∈ Ioo (-eps) eps := by
      constructor <;> linarith [hx.1, hx.2]
    have hshift :
        HasDerivAt (fun y : ℝ => y - z) 1 x :=
      (hasDerivAt_id x).sub_const z
    have hBase :=
      (localAnnulusValue_hasDerivAt K (-d) d ha hb
        (fun t => F (z + t)) hFshift ht).scomp x hshift
    have hPhi := (K.phi_hasDeriv (x - z) (Ioo_subset_Icc_self ht)).scomp x hshift
    have hPsi := (K.psi_hasDeriv (x - z) (Ioo_subset_Icc_self ht)).scomp x hshift
    have hB : HasDerivAt (physicalLocalKummerValue K d F)
        (physicalLocalKummerDeriv K d F x) x := by
      unfold physicalLocalKummerValue physicalLocalKummerDeriv
      simpa only [one_smul, Function.comp_def] using hBase
    have hP : HasDerivAt (fun y => K.phi (y - z)) (K.dphi (x - z)) x := by
      simpa only [one_smul, Function.comp_def] using hPhi
    have hQ : HasDerivAt (fun y => K.psi (y - z)) (K.dpsi (x - z)) x := by
      simpa only [one_smul, Function.comp_def] using hPsi
    have h := (hB.add (hP.const_mul a)).add (hQ.const_mul c)
    have hfun :
        ((physicalLocalKummerValue K d F +
          fun y => a * K.phi (y-z)) +
          fun y => c * K.psi (y-z)) =
          actualKummerCauchyValue K d F a c := by
      funext y
      rfl
    rw [hfun] at h
    exact h
  have hFirst := hFirstOpen r hOpen
  have hBase := physicalLocalKummer_hasDerivAt K d hd hde F hF hr
  have ht : r - z ∈ Icc (-eps) eps := by
    constructor <;> linarith [hr.1, hr.2]
  have hshift : HasDerivAt (fun y : ℝ => y - z) 1 r :=
    (hasDerivAt_id r).sub_const z
  have hPhi2 := (K.dphi_hasDeriv (r - z) ht).scomp r hshift
  have hPsi2 := (K.dpsi_hasDeriv (r - z) ht).scomp r hshift
  have hP2 : HasDerivAt (fun y => K.dphi (y - z))
      (-(frozenFirstCoeff r * K.dphi (r - z) +
        frozenZeroCoeff mu theta * K.phi (r - z))) r := by
    rw [show z + (r-z) = r by ring] at hPhi2
    simpa only [one_smul, Function.comp_def] using hPhi2
  have hQ2 : HasDerivAt (fun y => K.dpsi (y - z))
      (-(frozenFirstCoeff r * K.dpsi (r - z) +
        frozenZeroCoeff mu theta * K.psi (r - z))) r := by
    rw [show z + (r-z) = r by ring] at hPsi2
    simpa only [one_smul, Function.comp_def] using hPsi2
  have hv : HasDerivAt (actualKummerCauchyDeriv K d F a c)
      (actualKummerCauchySecond K d F a c r) r := by
    have h := (hBase.2.add (hP2.const_mul a)).add (hQ2.const_mul c)
    have hfun :
        ((physicalLocalKummerDeriv K d F +
          fun y => a * K.dphi (y-z)) +
          fun y => c * K.dpsi (y-z)) =
          actualKummerCauchyDeriv K d F a c := by
      funext y
      rfl
    rw [hfun] at h
    exact h
  have heq : (deriv (actualKummerCauchyValue K d F a c)) =ᶠ[𝓝 r]
      actualKummerCauchyDeriv K d F a c := by
    filter_upwards [Ioo_mem_nhds hOpen.1 hOpen.2] with x hx
    exact (hFirstOpen x hx).deriv
  have hSecond :
      HasDerivAt (deriv (actualKummerCauchyValue K d F a c))
        (actualKummerCauchySecond K d F a c r) r :=
    hv.congr_of_eventuallyEq heq
  refine ⟨hFirst, hSecond, ?_⟩
  rw [hSecond.deriv, hFirst.deriv]
  have hSource := physicalLocalKummer_equation K d F r
  unfold actualKummerCauchyValue actualKummerCauchyDeriv
    actualKummerCauchySecond
  linear_combination hSource

/-- True Cauchy matching on the INNER interface of the original
positive physical Kummer annulus, while keeping the full classical
inhomogeneous source equation unchanged. Both complex boundary jets
are prescribed (e.g. by the genuine classical H+/H- inner solution). -/
theorem actual_Kummer_inner_interface_Cauchy_match
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (d : ℝ) (hd : 0 < d) (hde : d < eps)
    (F : ℝ → ℂ) (hF : Continuous F)
    (U DU : ℂ) :
    ∃ a c : ℂ,
      actualKummerCauchyValue K d F a c (z - d) = U ∧
      actualKummerCauchyDeriv K d F a c (z - d) = DU ∧
      (∀ r ∈ Icc (z - d) (z + d),
        HasDerivAt (actualKummerCauchyValue K d F a c)
          (actualKummerCauchyDeriv K d F a c r) r ∧
        HasDerivAt (deriv (actualKummerCauchyValue K d F a c))
          (actualKummerCauchySecond K d F a c r) r ∧
        deriv (deriv (actualKummerCauchyValue K d F a c)) r +
          frozenFirstCoeff r *
            deriv (actualKummerCauchyValue K d F a c) r +
          frozenZeroCoeff mu theta *
            actualKummerCauchyValue K d F a c r = F r) := by
  let p : ℂ := U - physicalLocalKummerValue K d F (z - d)
  let q : ℂ := DU - physicalLocalKummerDeriv K d F (z - d)
  let a : ℂ := actualKummerMatchPhi K (-d) p q
  let c : ℂ := actualKummerMatchPsi K (-d) p q
  have ht : -d ∈ Icc (-eps) eps := ⟨by linarith, by linarith⟩
  obtain ⟨hp,hq⟩ := actual_Kummer_Wronskian_two_Cauchy_jets_match K (-d) ht p q
  refine ⟨a,c,?_,?_,?_⟩
  · unfold actualKummerCauchyValue
    have hx : z - d - z = -d := by ring
    rw [hx]
    calc
      physicalLocalKummerValue K d F (z - d) +
          a * K.phi (-d) + c * K.psi (-d) =
          physicalLocalKummerValue K d F (z - d) + p := by
            linear_combination hp
      _ = U := by dsimp [p]; ring
  · unfold actualKummerCauchyDeriv
    have hx : z - d - z = -d := by ring
    rw [hx]
    calc
      physicalLocalKummerDeriv K d F (z - d) +
          a * K.dphi (-d) + c * K.dpsi (-d) =
          physicalLocalKummerDeriv K d F (z - d) + q := by
            linear_combination hq
      _ = DU := by dsimp [q]; ring
  · intro r hr
    exact actual_Kummer_Cauchy_corrected_classical_equation K d hd hde F hF a c r hr

end HBL.TypeIIDynamicSelection
