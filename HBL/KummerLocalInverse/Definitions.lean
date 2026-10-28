import HBL.KummerPhysicalPairUniformBound
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace HBL.Profile.Kummer

/-- Actual physical coefficients are required only on the local closed positive interval. -/
structure LocalKummerPair (mu theta z eps : ℝ) where
  phi : ℝ → ℂ
  psi : ℝ → ℂ
  dphi : ℝ → ℂ
  dpsi : ℝ → ℂ
  radial_pos : ∀ t ∈ Icc (-eps) eps, 0 < z + t
  phi_hasDeriv : ∀ t ∈ Icc (-eps) eps, HasDerivAt phi (dphi t) t
  psi_hasDeriv : ∀ t ∈ Icc (-eps) eps, HasDerivAt psi (dpsi t) t
  dphi_hasDeriv : ∀ t ∈ Icc (-eps) eps,
    HasDerivAt dphi (-(frozenFirstCoeff (z + t) * dphi t + frozenZeroCoeff mu theta * phi t)) t
  dpsi_hasDeriv : ∀ t ∈ Icc (-eps) eps,
    HasDerivAt dpsi (-(frozenFirstCoeff (z + t) * dpsi t + frozenZeroCoeff mu theta * psi t)) t
  wronskian_ne : ∀ t ∈ Icc (-eps) eps, phi t * dpsi t - dphi t * psi t ≠ 0
  phi_zero : phi 0 = 1
  dphi_zero : dphi 0 = 0
  psi_zero : psi 0 = 0
  dpsi_zero : dpsi 0 = 1

variable {mu theta z eps : ℝ}

def localAnnulusWronskian (K : LocalKummerPair mu theta z eps) (t : ℝ) : ℂ :=
  K.phi t * K.dpsi t - K.dphi t * K.psi t

def LocalKummerBound (K : LocalKummerPair mu theta z eps) (C : ℝ) : Prop :=
  ∀ t ∈ Icc (-eps) eps,
    ‖K.phi t‖ ≤ C ∧ ‖K.dphi t‖ ≤ C ∧ ‖K.psi t‖ ≤ C ∧ ‖K.dpsi t‖ ≤ C ∧
    ‖(localAnnulusWronskian K t)⁻¹‖ ≤ C

def localAnnulusSourceA (K : LocalKummerPair mu theta z eps) (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  K.psi t * F t / localAnnulusWronskian K t

def localAnnulusSourceB (K : LocalKummerPair mu theta z eps) (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  K.phi t * F t / localAnnulusWronskian K t

def localAnnulusCoeffA (K : LocalKummerPair mu theta z eps) (b : ℝ) (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s in t..b, localAnnulusSourceA K F s

def localAnnulusCoeffB (K : LocalKummerPair mu theta z eps) (a : ℝ) (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s in a..t, localAnnulusSourceB K F s

def localAnnulusValue (K : LocalKummerPair mu theta z eps) (a b : ℝ) (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  K.phi t * localAnnulusCoeffA K b F t + K.psi t * localAnnulusCoeffB K a F t

def localAnnulusDeriv (K : LocalKummerPair mu theta z eps) (a b : ℝ) (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  K.dphi t * localAnnulusCoeffA K b F t + K.dpsi t * localAnnulusCoeffB K a F t

def localAnnulusSecond (K : LocalKummerPair mu theta z eps) (a b : ℝ) (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  -(frozenFirstCoeff (z + t) * K.dphi t + frozenZeroCoeff mu theta * K.phi t) * localAnnulusCoeffA K b F t +
  -(frozenFirstCoeff (z + t) * K.dpsi t + frozenZeroCoeff mu theta * K.psi t) * localAnnulusCoeffB K a F t + F t
end HBL.Profile.Kummer
