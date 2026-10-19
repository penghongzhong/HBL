import HBL.UnstableShootingKernel
import HBL.UnstableShootingMoments

/-!
Absolute convergence and polynomial bounds for the actual scalar backward
solution. The exponential kernel is constructed from the continuous growth
rate. The two-rate estimate retains the time-interval factor in the kernel
difference and integrates its first moment.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace HBL.Shooting

def unstableShootingSolution (a f : ℝ → ℝ) (s : ℝ) : ℝ :=
  -(∫ t in Ioi s, unstableShootingKernel a s t * f t)

theorem unstableShootingIntegrand_bound
    {a f : ℝ → ℝ} {s₀ p e F s t : ℝ}
    (hs₀ : 0 < s₀) (hp : 0 < p) (hF : 0 ≤ F)
    (ha : Continuous a)
    (hrate : ∀ t, s₀ ≤ t → e ≤ a t)
    (hsource : ∀ t, s₀ ≤ t → |f t| ≤ F * t ^ (-p))
    (hs : s₀ ≤ s) (hst : s ≤ t) :
    |unstableShootingKernel a s t * f t| ≤
      (F * s ^ (-p)) * Real.exp (-e * (t - s)) := by
  have hspos : 0 < s := hs₀.trans_le hs
  have hpow : t ^ (-p) ≤ s ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hspos hst (by linarith)
  have hf : |f t| ≤ F * s ^ (-p) :=
    (hsource t (hs.trans hst)).trans (mul_le_mul_of_nonneg_left hpow hF)
  have hk := unstableShootingKernel_le_exp hst ha.continuousOn
    (fun x hx => hrate x (hs.trans hx.1))
  rw [abs_mul, abs_of_pos (unstableShootingKernel_pos a s t)]
  calc
    unstableShootingKernel a s t * |f t| ≤
        Real.exp (-e * (t - s)) * (F * s ^ (-p)) :=
      mul_le_mul hk hf (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

theorem unstableShootingSolution_integrable
    {a f : ℝ → ℝ} {s₀ p e F s : ℝ}
    (hs₀ : 0 < s₀) (hp : 0 < p) (he : 0 < e) (hF : 0 ≤ F)
    (ha : Continuous a) (hf : Continuous f)
    (hrate : ∀ t, s₀ ≤ t → e ≤ a t)
    (hsource : ∀ t, s₀ ≤ t → |f t| ≤ F * t ^ (-p))
    (hs : s₀ ≤ s) :
    IntegrableOn (fun t => unstableShootingKernel a s t * f t) (Ioi s) := by
  have hm : AEStronglyMeasurable (fun t => unstableShootingKernel a s t * f t)
      (volume.restrict (Ioi s)) :=
    ((unstableShootingKernel_continuous_right ha s).mul hf).aestronglyMeasurable
  apply ((shootingExp_integrable he s).const_mul (F * s ^ (-p))).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact unstableShootingIntegrand_bound hs₀ hp hF ha hrate hsource hs ht.le

theorem unstableShootingSolution_bound
    {a f : ℝ → ℝ} {s₀ p e F s : ℝ}
    (hs₀ : 0 < s₀) (hp : 0 < p) (he : 0 < e) (hF : 0 ≤ F)
    (ha : Continuous a) (hf : Continuous f)
    (hrate : ∀ t, s₀ ≤ t → e ≤ a t)
    (hsource : ∀ t, s₀ ≤ t → |f t| ≤ F * t ^ (-p))
    (hs : s₀ ≤ s) :
    |unstableShootingSolution a f s| ≤ (F / e) * s ^ (-p) := by
  have hi := unstableShootingSolution_integrable hs₀ hp he hF ha hf hrate hsource hs
  rw [unstableShootingSolution, abs_neg]
  calc
    |∫ t in Ioi s, unstableShootingKernel a s t * f t| ≤
        ∫ t in Ioi s, |unstableShootingKernel a s t * f t| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioi s, (F * s ^ (-p)) * Real.exp (-e * (t - s)) := by
      apply integral_mono_ae hi.abs
        ((shootingExp_integrable he s).const_mul (F * s ^ (-p)))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact unstableShootingIntegrand_bound hs₀ hp hF ha hrate hsource hs ht.le
    _ = (F / e) * s ^ (-p) := by
      rw [integral_const_mul, shootingExp_integral he s]
      ring

theorem unstableShootingSolution_tendsto_zero
    {a f : ℝ → ℝ} {s₀ p e F : ℝ}
    (hs₀ : 0 < s₀) (hp : 0 < p) (he : 0 < e) (hF : 0 ≤ F)
    (ha : Continuous a) (hf : Continuous f)
    (hrate : ∀ t, s₀ ≤ t → e ≤ a t)
    (hsource : ∀ t, s₀ ≤ t → |f t| ≤ F * t ^ (-p)) :
    Tendsto (unstableShootingSolution a f) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (by
    simpa using (tendsto_rpow_neg_atTop hp).const_mul (F / e))
  filter_upwards [eventually_ge_atTop s₀] with s hs
  exact unstableShootingSolution_bound hs₀ hp he hF ha hf hrate hsource hs

theorem unstableShootingIntegrand_difference_bound
    {a b f g : ℝ → ℝ} {s₀ p e D E G s t : ℝ}
    (hs₀ : 0 < s₀) (hp : 0 < p)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hG : 0 ≤ G)
    (ha : Continuous a) (hb : Continuous b)
    (hratea : ∀ t, s₀ ≤ t → e ≤ a t)
    (hrateb : ∀ t, s₀ ≤ t → e ≤ b t)
    (hratediff : ∀ t, s₀ ≤ t → |a t - b t| ≤ D)
    (hsourceg : ∀ t, s₀ ≤ t → |g t| ≤ G * t ^ (-p))
    (hsourcediff : ∀ t, s₀ ≤ t → |f t - g t| ≤ E * t ^ (-p))
    (hs : s₀ ≤ s) (hst : s ≤ t) :
    |unstableShootingKernel a s t * f t - unstableShootingKernel b s t * g t| ≤
      (E * s ^ (-p)) * Real.exp (-e * (t - s)) +
        (G * s ^ (-p) * D) * ((t - s) * Real.exp (-e * (t - s))) := by
  have hfirst := unstableShootingIntegrand_bound (f := fun t => f t - g t)
    hs₀ hp hE ha hratea hsourcediff hs hst
  have hpow := Real.rpow_le_rpow_of_nonpos (hs₀.trans_le hs) hst
    (show -p ≤ 0 by linarith)
  have hg : |g t| ≤ G * s ^ (-p) :=
    (hsourceg t (hs.trans hst)).trans (mul_le_mul_of_nonneg_left hpow hG)
  have hk := unstableShootingKernel_difference_bound hst ha.continuousOn hb.continuousOn
    (fun x hx => hratea x (hs.trans hx.1))
    (fun x hx => hrateb x (hs.trans hx.1))
    (fun x hx => hratediff x (hs.trans hx.1))
  have hsecond : |(unstableShootingKernel a s t - unstableShootingKernel b s t) * g t| ≤
      (G * s ^ (-p) * D) * ((t - s) * Real.exp (-e * (t - s))) := by
    rw [abs_mul]
    calc
      |unstableShootingKernel a s t - unstableShootingKernel b s t| * |g t| ≤
          (D * (t - s) * Real.exp (-e * (t - s))) * (G * s ^ (-p)) :=
        mul_le_mul hk hg (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hid : unstableShootingKernel a s t * f t - unstableShootingKernel b s t * g t =
      unstableShootingKernel a s t * (f t - g t) +
        (unstableShootingKernel a s t - unstableShootingKernel b s t) * g t := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

theorem unstableShootingSolution_difference_bound
    {a b f g : ℝ → ℝ} {s₀ p e D E F G s : ℝ}
    (hs₀ : 0 < s₀) (hp : 0 < p) (he : 0 < e)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (ha : Continuous a) (hb : Continuous b) (hf : Continuous f) (hg : Continuous g)
    (hratea : ∀ t, s₀ ≤ t → e ≤ a t)
    (hrateb : ∀ t, s₀ ≤ t → e ≤ b t)
    (hratediff : ∀ t, s₀ ≤ t → |a t - b t| ≤ D)
    (hsourcef : ∀ t, s₀ ≤ t → |f t| ≤ F * t ^ (-p))
    (hsourceg : ∀ t, s₀ ≤ t → |g t| ≤ G * t ^ (-p))
    (hsourcediff : ∀ t, s₀ ≤ t → |f t - g t| ≤ E * t ^ (-p))
    (hs : s₀ ≤ s) :
    |unstableShootingSolution a f s - unstableShootingSolution b g s| ≤
      (E / e + G * D / e ^ 2) * s ^ (-p) := by
  have hi := unstableShootingSolution_integrable hs₀ hp he hF ha hf hratea hsourcef hs
  have hj := unstableShootingSolution_integrable hs₀ hp he hG hb hg hrateb hsourceg hs
  have hm₀ := (shootingExp_integrable he s).const_mul (E * s ^ (-p))
  have hm₁ := (shootingFirstMoment_integrable he s).const_mul (G * s ^ (-p) * D)
  have hid : unstableShootingSolution a f s - unstableShootingSolution b g s =
      -(∫ t in Ioi s,
        unstableShootingKernel a s t * f t - unstableShootingKernel b s t * g t) := by
    rw [integral_sub hi hj]
    unfold unstableShootingSolution
    ring
  rw [hid, abs_neg]
  calc
    |∫ t in Ioi s,
        unstableShootingKernel a s t * f t - unstableShootingKernel b s t * g t| ≤
      ∫ t in Ioi s,
        |unstableShootingKernel a s t * f t - unstableShootingKernel b s t * g t| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioi s,
        (E * s ^ (-p)) * Real.exp (-e * (t - s)) +
        (G * s ^ (-p) * D) * ((t - s) * Real.exp (-e * (t - s))) := by
      apply integral_mono_ae (hi.sub hj).abs (hm₀.add hm₁)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact unstableShootingIntegrand_difference_bound hs₀ hp hD hE hG ha hb
        hratea hrateb hratediff hsourceg hsourcediff hs ht.le
    _ = (E / e + G * D / e ^ 2) * s ^ (-p) := by
      rw [integral_add hm₀ hm₁, integral_const_mul, integral_const_mul,
        shootingExp_integral he s, shootingFirstMoment_integral he s]
      ring

/-- A decaying difference of the primitive growth rates gives the additional
polynomial margin, after integration of the true first kernel moment. -/
theorem unstableShootingSolution_difference_bound_of_rate_decay
    {a b f g : ℝ → ℝ} {s₀ p ρ e D E F G s : ℝ}
    (hs₀ : 0 < s₀) (hp : 0 < p) (hρ : 0 ≤ ρ) (he : 0 < e)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (ha : Continuous a) (hb : Continuous b) (hf : Continuous f) (hg : Continuous g)
    (hratea : ∀ t, s₀ ≤ t → e ≤ a t)
    (hrateb : ∀ t, s₀ ≤ t → e ≤ b t)
    (hratediff : ∀ t, s₀ ≤ t → |a t - b t| ≤ D * t ^ (-ρ))
    (hsourcef : ∀ t, s₀ ≤ t → |f t| ≤ F * t ^ (-p))
    (hsourceg : ∀ t, s₀ ≤ t → |g t| ≤ G * t ^ (-p))
    (hsourcediff : ∀ t, s₀ ≤ t → |f t - g t| ≤ E * t ^ (-p))
    (hs : s₀ ≤ s) :
    |unstableShootingSolution a f s - unstableShootingSolution b g s| ≤
      (E / e) * s ^ (-p) + (G * D / e ^ 2) * s ^ (-p - ρ) := by
  have hspos := hs₀.trans_le hs
  have hd : ∀ t, s ≤ t → |a t - b t| ≤ D * s ^ (-ρ) := by
    intro t ht
    exact (hratediff t (hs.trans ht)).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hspos ht (neg_nonpos.mpr hρ)) hD)
  have h := unstableShootingSolution_difference_bound hspos hp he
    (mul_nonneg hD (Real.rpow_nonneg hspos.le _)) hE hF hG ha hb hf hg
    (fun t ht => hratea t (hs.trans ht))
    (fun t ht => hrateb t (hs.trans ht)) hd
    (fun t ht => hsourcef t (hs.trans ht))
    (fun t ht => hsourceg t (hs.trans ht))
    (fun t ht => hsourcediff t (hs.trans ht)) le_rfl
  convert h using 1
  have hpow : s ^ (-p - ρ) = s ^ (-p) * s ^ (-ρ) := by
    rw [show -p - ρ = -p + -ρ by ring, Real.rpow_add hspos]
  rw [hpow]
  ring

end HBL.Shooting
