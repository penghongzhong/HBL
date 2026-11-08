import HBL.TypeIIDynamicSelection.ActualHartreeCramerSpeedDerivativeBound
import HBL.TypeIIDynamicSelection.ActualHartreeSpeedRegularGreen
import Mathlib.Tactic

/-!
# Actual real Cramer speed derivatives in the ORIGINAL regular Kummer Green field

The *same* two genuine scale/phase source directions entering the original
Hartree Kummer compatibility matrix have already been shown to obey
  ||B_K[S_b]||,||B_K[S_omega]|| <= Cs*G*a*B,
with B_K the ORIGINAL normalized regular Green integral on [L/a,B].

The true differentiable real Cramer selector has
  |p_b'|+|p_omega'| <= 1024/(a*B^2)
    *||Z'+p_b*b'+p_omega*w'||.
Multiplying these two independently strict physical estimates cancels a
exactly. This proves the nontrivial selected-speed time component of the
regular Green field has no positive or negative moving-scale loss:
  ||p_b' B_K[S_b]+p_omega' B_K[S_omega]||
    <= (1024*Cs*G/B)*||Z'+p_b*b'+p_omega*w'||.

This proof does not import a full field-derivative bound, assume an
independent speed derivative, replace the physical Green integrals by
arbitrary packets, or preselect the Type-II rate. The moving original
source, source-shape and moving-boundary derivative terms remain separate.
-/

noncomputable section
set_option autoImplicit false
open Set
namespace HBL.TypeIIDynamicSelection
open HBL.Profile.Kummer
open HBL.Modulation HBL.Modulation.Monopole HBL.Modulation.AffineTail

theorem actual_Hartree_selected_speed_derivative_original_regular_Green_no_scale
    {mu theta scale : ℝ} (K : OriginKummerPair mu theta scale)
    (G L c a B s : ℝ)
    (hG : 0 ≤ G) (hL : 1 ≤ L) (ha : 0 < a)
    (hB : 0 < B) (hBOne : B ≤ 1) (hBR : B < scale)
    (hSmall : a * |c| ≤ 1) (hOrder : L / a ≤ B)
    (hbound : ∀ x ∈ Icc 0 scale,
      ‖K.y x‖ ≤ G ∧ ‖K.dy x‖ ≤ G ∧
        ‖K.x x‖ ≤ G ∧ ‖K.dx x‖ ≤ G)
    (b w Z : ℝ → ℂ) (bdot wdot Zdot : ℂ)
    (hb : HasDerivAt b bdot s)
    (hw : HasDerivAt w wdot s)
    (hZ : HasDerivAt Z Zdot s)
    (hbNorm : ‖b s‖ ≤ a * B ^ 2)
    (hwNorm : ‖w s‖ ≤ a * B ^ 2)
    (hdet : a ^ 2 * B ^ 4 / 256 ≤
      actualRealCramerDet (b s) (w s)) :
    ∃ Cs : ℝ, 0 < Cs ∧
      ∃ pbDot pwDot : ℝ,
        let pb : ℝ → ℝ := fun t =>
          (actualRealCramerCorrection (b t) (w t) (Z t)).1
        let pw : ℝ → ℝ := fun t =>
          (actualRealCramerCorrection (b t) (w t) (Z t)).2
        HasDerivAt pb pbDot s ∧ HasDerivAt pw pwDot s ∧
        ‖(pbDot : ℂ) *
            originGreenCoeffB K (L / a)
              (actualMomentLockedScaledScaleSource a c) B +
          (pwDot : ℂ) *
            originGreenCoeffB K (L / a)
              (actualMomentLockedScaledPhaseSource a c) B‖ ≤
          (1024 * Cs * G / B) *
            ‖Zdot + (pb s : ℂ) * bdot + (pw s : ℂ) * wdot‖ := by
  obtain ⟨Cs, hCs, hGreen⟩ :=
    actual_Hartree_speed_regular_Green_coefficients
  have hCoeff :=
    hGreen K G L c a B hG hL ha hBOne hBR
      hSmall hOrder hbound
  obtain ⟨pbDot, pwDot, hpb, hpw, hSpeed⟩ :=
    actual_real_Cramer_selected_speed_derivative_bound
      a B s ha hB b w Z bdot wdot Zdot
      hb hw hZ hbNorm hwNorm hdet
  let pb : ℝ → ℝ := fun t =>
    (actualRealCramerCorrection (b t) (w t) (Z t)).1
  let pw : ℝ → ℝ := fun t =>
    (actualRealCramerCorrection (b t) (w t) (Z t)).2
  let Gb : ℂ := originGreenCoeffB K (L / a)
    (actualMomentLockedScaledScaleSource a c) B
  let Gw : ℂ := originGreenCoeffB K (L / a)
    (actualMomentLockedScaledPhaseSource a c) B
  let E : ℝ := Cs * G * a * B
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hbGreen : ‖Gb‖ ≤ E := by
    simpa only [Gb, E] using hCoeff.1
  have hwGreen : ‖Gw‖ ≤ E := by
    simpa only [Gw, E] using hCoeff.2
  have hBound :
      ‖(pbDot : ℂ) * Gb + (pwDot : ℂ) * Gw‖ ≤
        (|pbDot| + |pwDot|) * E := by
    calc
      _ ≤ ‖(pbDot : ℂ) * Gb‖ + ‖(pwDot : ℂ) * Gw‖ :=
        norm_add_le _ _
      _ = |pbDot| * ‖Gb‖ + |pwDot| * ‖Gw‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |pbDot| * E + |pwDot| * E := by
        have h1 := mul_le_mul_of_nonneg_left hbGreen (abs_nonneg pbDot)
        have h2 := mul_le_mul_of_nonneg_left hwGreen (abs_nonneg pwDot)
        linarith only [h1, h2]
      _ = (|pbDot| + |pwDot|) * E := by ring
  have hFinal :
      (|pbDot| + |pwDot|) * E ≤
        (1024 * Cs * G / B) *
          ‖Zdot + (pb s : ℂ) * bdot + (pw s : ℂ) * wdot‖ := by
    calc
      _ ≤ (1024 / (a * B ^ 2) *
          ‖Zdot + (pb s : ℂ) * bdot + (pw s : ℂ) * wdot‖) * E :=
        mul_le_mul_of_nonneg_right
          (by simpa only [pb, pw] using hSpeed) hE
      _ = _ := by
        dsimp [E]
        field_simp [ha.ne', hB.ne'] <;> ring
  refine ⟨Cs, hCs, pbDot, pwDot, ?_, ?_, ?_⟩
  · simpa only [pb] using hpb
  · simpa only [pw] using hpw
  · simpa only [Gb, Gw, pb, pw] using hBound.trans hFinal

end HBL.TypeIIDynamicSelection
