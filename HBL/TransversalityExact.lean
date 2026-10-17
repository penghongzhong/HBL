import HBL.AffineTailLogIntegralReduction
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
Manuscript lemma thm:transversality (main-parameter transversality).

The first Laurent coefficient is not merely postulated below.  Substitution of
  z^(-1) + c*z
in the frozen Kummer operator gives the exact indicial residual
  2*c + theta - i*(mu+1/4).
Its unique zero is
  c1(mu,theta) = -theta/2 + i*(mu+1/4)/2.
The manuscript then defines the normalized jet coordinates
  Theta0 = (2 Im c1 - 1/4, -2 Re c1).
The two conclusions of the numbered lemma, namely Theta0=id and its
complete real Frechet Jacobian being I_2, are verified below.

This lemma is algebraically independent of the affine-charge lemma.
-/

noncomputable section

open scoped Topology

namespace HBL.Modulation.Transversality

/-- The coefficient `c₁` displayed in the manuscript's first Kummer jet. -/
def firstKummerCoefficient (mu theta : ℝ) : ℂ :=
  ⟨-theta / 2, (mu + 1 / 4) / 2⟩

/-- The singular two-term Laurent jet used to read off the first Kummer
coefficient. -/
def singularKummerJet (c z : ℂ) : ℂ :=
  z⁻¹ + c * z

/-- Its first formal derivative.  A separate theorem below verifies that this
is the genuine derivative away from the pole. -/
def singularKummerJetDeriv (c z : ℂ) : ℂ :=
  -(z ^ 2)⁻¹ + c

/-- Its second formal derivative. -/
def singularKummerJetSecondDeriv (z : ℂ) : ℂ :=
  2 * (z ^ 3)⁻¹

/-- Coefficient of `z⁻¹` obtained after inserting the singular jet into the
frozen Kummer operator. -/
def kummerIndicialResidual (mu theta : ℝ) (c : ℂ) : ℂ :=
  2 * c + theta - Complex.I * (mu + 1 / 4)

/-- Exact frozen Kummer operator evaluated on the two-term singular jet. -/
def frozenKummerJetApply (mu theta : ℝ) (c z : ℂ) : ℂ :=
  singularKummerJetSecondDeriv z +
    (2 / z) * singularKummerJetDeriv c z +
    (Complex.I / 2) * z * singularKummerJetDeriv c z +
    theta * singularKummerJet c z +
    Complex.I * (1 / 4 - mu) * singularKummerJet c z

/-- The formal first derivative is the genuine complex derivative away from
the Laurent pole. -/
theorem singularKummerJet_hasDerivAt (c z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (singularKummerJet c) (singularKummerJetDeriv c z) z := by
  have h := (hasDerivAt_inv hz).add ((hasDerivAt_id z).const_mul c)
  convert h using 1
  · funext w
    simp [singularKummerJet]
  · simp [singularKummerJetDeriv]

/-- The displayed second formal derivative is also the genuine derivative of
the first derivative away from zero. -/
theorem singularKummerJetDeriv_hasDerivAt (c z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (singularKummerJetDeriv c)
      (singularKummerJetSecondDeriv z) z := by
  unfold singularKummerJetDeriv singularKummerJetSecondDeriv
  have hpow : HasDerivAt (fun w : ℂ => w ^ 2) (2 * z) z := by
    have h := (hasDerivAt_id z).pow 2
    convert h using 1
    · funext w
      simp [id_eq]
    · norm_num
  have hinv := hpow.inv (pow_ne_zero 2 hz)
  convert hinv.neg.add_const c using 1
  all_goals field_simp [hz]

/-- Exact Laurent decomposition of the frozen Kummer operator: the coefficient
of `z⁻¹` is precisely `kummerIndicialResidual`. -/
theorem frozenKummerJetApply_decomposition
    (mu theta : ℝ) (c z : ℂ) (hz : z ≠ 0) :
    frozenKummerJetApply mu theta c z =
      kummerIndicialResidual mu theta c * z⁻¹ +
        ((Complex.I / 2) * c + theta * c +
          Complex.I * (1 / 4 - mu) * c) * z := by
  unfold frozenKummerJetApply singularKummerJetSecondDeriv
    singularKummerJetDeriv singularKummerJet kummerIndicialResidual
  field_simp [hz]
  ring

/-- The manuscript coefficient cancels the singular Kummer residual. -/
theorem firstKummerCoefficient_indicial
    (mu theta : ℝ) :
    kummerIndicialResidual mu theta
      (firstKummerCoefficient mu theta) = 0 := by
  unfold kummerIndicialResidual firstKummerCoefficient
  apply Complex.ext <;> norm_num <;> ring

/-- The indicial equation determines the first Laurent coefficient uniquely. -/
theorem firstKummerCoefficient_unique
    (mu theta : ℝ) (c : ℂ)
    (hc : kummerIndicialResidual mu theta c = 0) :
    c = firstKummerCoefficient mu theta := by
  have hroot := firstKummerCoefficient_indicial mu theta
  have hdiff : (2 : ℂ) *
      (c - firstKummerCoefficient mu theta) = 0 := by
    unfold kummerIndicialResidual at hc hroot
    linear_combination hc - hroot
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left htwo)

/-- The real two-component jet normalization of the first coefficient. -/
def mainJet (p : ℝ × ℝ) : ℝ × ℝ :=
  (2 * (firstKummerCoefficient p.1 p.2).im - 1 / 4,
    -2 * (firstKummerCoefficient p.1 p.2).re)

/-- Exact first coordinate of the normalized Kummer jet. -/
theorem mainJet_first (p : ℝ × ℝ) : (mainJet p).1 = p.1 := by
  dsimp [mainJet, firstKummerCoefficient]
  ring

/-- Exact second coordinate of the normalized Kummer jet. -/
theorem mainJet_second (p : ℝ × ℝ) : (mainJet p).2 = p.2 := by
  dsimp [mainJet, firstKummerCoefficient]
  ring

/-- The first assertion of the manuscript's numbered transversality lemma. -/
theorem mainJet_eq (p : ℝ × ℝ) : mainJet p = p := by
  apply Prod.ext
  · exact mainJet_first p
  · exact mainJet_second p

theorem mainJet_eq_id : mainJet = (id : ℝ × ℝ → ℝ × ℝ) := by
  funext p
  exact mainJet_eq p

/-- The full real Frechet Jacobian is the two-dimensional identity map. -/
theorem mainJet_fderiv (p : ℝ × ℝ) :
    fderiv ℝ mainJet p = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  rw [mainJet_eq_id]
  exact fderiv_id

/-- The normalized first jet recovers the two parameters uniquely. -/
theorem mainJet_unique (y : ℝ × ℝ) :
    ∃! p : ℝ × ℝ, mainJet p = y := by
  refine ⟨y, mainJet_eq y, ?_⟩
  intro p hp
  rw [mainJet_eq p] at hp
  exact hp

/-- The complete manuscript environment: the Laurent coefficient is the unique
root forced by the frozen Kummer equation, the normalized jet is the identity,
its full real Frechet derivative is `I₂`, and the parameters are uniquely
recoverable from the jet. -/
theorem manuscript_transversality_environment_closed :
    (∀ c z : ℂ, z ≠ 0 →
      HasDerivAt (singularKummerJet c) (singularKummerJetDeriv c z) z) ∧
    (∀ c z : ℂ, z ≠ 0 →
      HasDerivAt (singularKummerJetDeriv c)
        (singularKummerJetSecondDeriv z) z) ∧
    (∀ mu theta : ℝ, ∀ c z : ℂ, z ≠ 0 →
      frozenKummerJetApply mu theta c z =
        kummerIndicialResidual mu theta c * z⁻¹ +
          ((Complex.I / 2) * c + theta * c +
            Complex.I * (1 / 4 - mu) * c) * z) ∧
    (∀ mu theta : ℝ,
      kummerIndicialResidual mu theta
        (firstKummerCoefficient mu theta) = 0) ∧
    (∀ mu theta : ℝ, ∀ c : ℂ,
      kummerIndicialResidual mu theta c = 0 →
        c = firstKummerCoefficient mu theta) ∧
    (∀ p : ℝ × ℝ, mainJet p = p) ∧
    (∀ p : ℝ × ℝ,
      fderiv ℝ mainJet p = ContinuousLinearMap.id ℝ (ℝ × ℝ)) ∧
    (∀ y : ℝ × ℝ, ∃! p : ℝ × ℝ, mainJet p = y) := by
  exact ⟨singularKummerJet_hasDerivAt,
    singularKummerJetDeriv_hasDerivAt, frozenKummerJetApply_decomposition,
    firstKummerCoefficient_indicial, firstKummerCoefficient_unique,
    mainJet_eq, mainJet_fderiv, mainJet_unique⟩

end HBL.Modulation.Transversality
