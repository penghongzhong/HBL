import HBL.KummerPrescribedAnnulus.CenteredGrowth
import HBL.KummerLocalInverse.Definitions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace HBL.Profile.Kummer

/-- Uniform a priori bound for any actual center-normalized Kummer pair. -/
theorem prescribed_kummer_pair_exp_bound
    {mu theta z eps : ℝ} (K : LocalKummerPair mu theta z eps)
    (D : ℝ) (hD : 0 ≤ D)
    (hcoeff : ∀ t ∈ Icc (-eps) eps,
      ‖frozenFirstCoeff (z + t)‖ + ‖frozenZeroCoeff mu theta‖ ≤ D) :
    LocalKummerBound K (Real.exp ((D + 1) * eps)) := by
  have hb (u v : ℝ → ℂ)
      (hu : ∀ t ∈ Icc (-eps) eps, HasDerivAt u (v t) t)
      (hv : ∀ t ∈ Icc (-eps) eps, HasDerivAt v
        (-(frozenFirstCoeff (z + t) * v t + frozenZeroCoeff mu theta * u t)) t)
      (hzero : ‖(u 0, v 0)‖ ≤ 1) :
      ∀ t ∈ Icc (-eps) eps, ‖(u t, v t)‖ ≤ Real.exp ((D + 1) * eps) := by
    apply centered_ode_norm_le_exp eps (D + 1) (by linarith)
      (fun t => (u t, v t))
      (fun t => (v t, -(frozenFirstCoeff (z + t) * v t + frozenZeroCoeff mu theta * u t)))
      (fun t ht => (hu t ht).prodMk (hv t ht)) _ hzero
    intro t ht
    have huN : ‖u t‖ ≤ ‖(u t, v t)‖ := le_max_left _ _
    have hvN : ‖v t‖ ≤ ‖(u t, v t)‖ := le_max_right _ _
    have hN := norm_nonneg (u t, v t)
    rw [Prod.norm_def, max_le_iff]
    constructor
    · nlinarith
    · calc
        ‖-(frozenFirstCoeff (z + t) * v t + frozenZeroCoeff mu theta * u t)‖
          ≤ ‖frozenFirstCoeff (z + t)‖ * ‖v t‖ + ‖frozenZeroCoeff mu theta‖ * ‖u t‖ := by
            simpa only [norm_neg, norm_mul] using norm_add_le
              (frozenFirstCoeff (z + t) * v t) (frozenZeroCoeff mu theta * u t)
        _ ≤ (‖frozenFirstCoeff (z + t)‖ + ‖frozenZeroCoeff mu theta‖) * ‖(u t, v t)‖ := by
          calc
            _ ≤ ‖frozenFirstCoeff (z + t)‖ * ‖(u t, v t)‖ +
                ‖frozenZeroCoeff mu theta‖ * ‖(u t, v t)‖ := by gcongr
            _ = _ := by ring
        _ ≤ D * ‖(u t, v t)‖ := mul_le_mul_of_nonneg_right (hcoeff t ht) hN
        _ ≤ (D + 1) * ‖(u t, v t)‖ := by nlinarith
  have hphi := hb K.phi K.dphi K.phi_hasDeriv K.dphi_hasDeriv
    (by simp [K.phi_zero, K.dphi_zero])
  have hpsi := hb K.psi K.dpsi K.psi_hasDeriv K.dpsi_hasDeriv
    (by simp [K.psi_zero, K.dpsi_zero])
  have hW (t : ℝ) (ht : t ∈ Icc (-eps) eps) :
      HasDerivAt (localAnnulusWronskian K)
        (-frozenFirstCoeff (z + t) * localAnnulusWronskian K t) t := by
    convert ((K.phi_hasDeriv t ht).mul (K.dpsi_hasDeriv t ht)).sub
      ((K.dphi_hasDeriv t ht).mul (K.psi_hasDeriv t ht)) using 1
    · rfl
    · dsimp [localAnnulusWronskian]
      ring
  have hinv (t : ℝ) (ht : t ∈ Icc (-eps) eps) :
      HasDerivAt (fun s => (localAnnulusWronskian K s)⁻¹)
        (frozenFirstCoeff (z + t) * (localAnnulusWronskian K t)⁻¹) t := by
    have hi := ((hasFDerivAt_inv (K.wronskian_ne t ht)).restrictScalars ℝ).comp_hasDerivAt t (hW t ht)
    convert hi using 1
    · rfl
    · dsimp [localAnnulusWronskian]
      field_simp [K.wronskian_ne t ht]
  have hWinv := centered_ode_norm_le_exp eps (D + 1) (by linarith)
    (fun t => (localAnnulusWronskian K t)⁻¹)
    (fun t => frozenFirstCoeff (z + t) * (localAnnulusWronskian K t)⁻¹) hinv
    (fun t ht => by
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hc := hcoeff t ht
      have hn := norm_nonneg (frozenZeroCoeff mu theta)
      linarith)
    (by simp [localAnnulusWronskian, K.phi_zero, K.dphi_zero, K.psi_zero, K.dpsi_zero])
  intro t ht
  have hp := hphi t ht
  have hs := hpsi t ht
  simp only [Prod.norm_def, max_le_iff] at hp hs
  exact ⟨hp.1, hp.2, hs.1, hs.2, hWinv t ht⟩
end HBL.Profile.Kummer
