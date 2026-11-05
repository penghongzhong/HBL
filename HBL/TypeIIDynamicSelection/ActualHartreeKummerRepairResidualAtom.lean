import HBL.FiniteProfileResidualLedger
import HBL.TypeIIDynamicSelection.ActualKummerPhysicalRepairTimeGain
import Mathlib.Tactic

/-!
# The physical Kummer interface repair as a realized residual atom

The value is the actual scaled Kummer operator applied to the concrete
physical pullback of the interface repair at one fixed normalized shell
point x in [R,2R]. The repair itself has the exact a^(-2) source factor.
If the actual boundary jet is of the current profile order s^(-rho),
the already verified physical Kummer time gain places the repair source
at order rho + actualHartreePhysicalKappa.

No GainCause label or assigned source order is used.
The physical pullback and its time-gain producer are strict replayed dependencies.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Profile.ResidualLedger

def actualHartreeKummerRepairResidualValue
    (mu theta R x : ℝ)
    (a : ℝ → ℝ) (p q : ℝ → ℂ) (s : ℝ) : ℂ :=
  actualMatchedScaledKummerApply mu theta (a s)
    (actualKummerPhysicalInterfaceRepair (a s) R (p s) (q s))
    (a s * x)

/-- The genuine physical Kummer repair source is one full physical
profile layer above its boundary jet. The spatial point is tied to the
same moving physical annulus by y=a(s)x. -/
theorem actual_Hartree_Kummer_repair_realized_atom :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
    ∀ (mu theta R x beta rhoStar rho CJ : ℝ)
      (a ell : ℝ → ℝ) (p q : ℝ → ℂ),
      0 < R → x ∈ Icc R (2 * R) → 0 ≤ CJ →
      1 / 2 < beta → 0 < rhoStar →
      rhoStar < (5 * beta - 2) / 4 →
      (∀ s : ℝ, 1 ≤ s → 0 < a s) →
      (∀ s : ℝ, 1 ≤ s → 0 < ell s) →
      (∀ s : ℝ, 1 ≤ s → ell s ≤ 1) →
      (∀ s : ℝ, 1 ≤ s →
        actualHartreeSlowInnerRadius (ell s) ^ 3 ≤ a s) →
      (∀ s : ℝ, 1 ≤ s → ell s ≤ s ^ (-beta)) →
      (∀ s : ℝ, 1 ≤ s →
        ‖p s‖ + R * ‖q s‖ ≤ CJ * s ^ (-rho)) →
      let kappa := actualHartreePhysicalKappa beta rhoStar
      let Krep :=
        (9*C2+12*C1+2)/R^2 + 3*C1+1+
          ‖frozenZeroCoeff mu theta‖
      ∃ atom : WeightedResidualAtom ℂ,
        atom.value =
          actualHartreeKummerRepairResidualValue mu theta R x a p q ∧
        atom.order = rho + kappa ∧
        atom.constant = Krep * CJ := by
  obtain ⟨C1,C2,hC1,hC2,hRepair⟩ :=
    actual_Hartree_Kummer_physical_interface_repair_next_layer
  refine ⟨C1,C2,hC1,hC2,?_⟩
  intro mu theta R x beta rhoStar rho CJ a ell p q
    hR hx hCJ hbeta hrhoStar hflat
    ha hell hellOne ha3 htrap hJet
  dsimp only
  let kappa : ℝ := actualHartreePhysicalKappa beta rhoStar
  let Krep : ℝ :=
    (9*C2+12*C1+2)/R^2 + 3*C1+1+
      ‖frozenZeroCoeff mu theta‖
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    exact actual_Hartree_physical_kappa_positive
      beta rhoStar hbeta hrhoStar hflat
  have hKrep : 0 ≤ Krep := by
    dsimp [Krep]
    positivity
  have hConst : 0 ≤ Krep * CJ := mul_nonneg hKrep hCJ
  let atom : WeightedResidualAtom ℂ :=
    { value := actualHartreeKummerRepairResidualValue mu theta R x a p q
      order := rho + kappa
      constant := Krep * CJ
      constant_nonneg := hConst
      bound := by
        intro s hs
        have has : 0 < a s := ha s hs
        have hys : a s * x ∈ Icc (a s * R) (2 * a s * R) := by
          constructor
          · exact mul_le_mul_of_nonneg_left hx.1 has.le
          · calc
              a s * x ≤ a s * (2 * R) :=
                mul_le_mul_of_nonneg_left hx.2 has.le
              _ = 2 * a s * R := by ring
        have hRaw :=
          hRepair mu theta (a s) R (a s * x) s (ell s)
            beta rhoStar has hR hys hs (hell s hs)
            (hellOne s hs) (ha3 s hs) (htrap s hs)
            hbeta hrhoStar hflat (p s) (q s)
        have hD : ‖p s‖ + R * ‖q s‖ ≤ CJ * s ^ (-rho) :=
          hJet s hs
        have hsp : 0 < s := lt_of_lt_of_le zero_lt_one hs
        have hkpow : 0 ≤ s ^ (-kappa) :=
          Real.rpow_nonneg hsp.le _
        have hKD :
            Krep * (‖p s‖ + R * ‖q s‖) ≤
              Krep * (CJ * s ^ (-rho)) :=
          mul_le_mul_of_nonneg_left hD hKrep
        have hProd :
            s ^ (-rho) * s ^ (-kappa) =
              s ^ (-(rho + kappa)) := by
          rw [← Real.rpow_add hsp]
          congr 1
          ring
        calc
          ‖actualHartreeKummerRepairResidualValue
              mu theta R x a p q s‖ ≤
            (Krep * (‖p s‖ + R * ‖q s‖)) *
              s ^ (-kappa) := by
                simpa only [actualHartreeKummerRepairResidualValue,
                  Krep, kappa] using hRaw
          _ ≤ (Krep * (CJ * s ^ (-rho))) *
              s ^ (-kappa) :=
            mul_le_mul_of_nonneg_right hKD hkpow
          _ = (Krep * CJ) *
              (s ^ (-rho) * s ^ (-kappa)) := by ring
          _ = (Krep * CJ) *
              s ^ (-(rho + kappa)) := by rw [hProd] }
  exact ⟨atom, rfl, rfl, rfl⟩

theorem actual_Hartree_Kummer_repair_realized_gain_positive
    (beta rhoStar : ℝ)
    (hbeta : 1 / 2 < beta)
    (hrhoStar : 0 < rhoStar)
    (hflat : rhoStar < (5 * beta - 2) / 4) :
    0 < actualHartreePhysicalKappa beta rhoStar := by
  exact actual_Hartree_physical_kappa_positive
    beta rhoStar hbeta hrhoStar hflat

end HBL.TypeIIDynamicSelection
