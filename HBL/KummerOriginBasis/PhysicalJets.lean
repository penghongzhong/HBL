import HBL.KummerOriginBasis.Definitions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace HBL.Profile.Kummer

/-- Dividing a regularized solution by r gives the actual frozen radial equation. -/
theorem origin_kummer_physical_jets (mu theta r : ℝ) (hr : r ≠ 0)
    (y v : ℝ → ℂ) (hy : HasDerivAt y (v r) r)
    (hv : HasDerivAt v (-(originFirstCoeff r * v r + originZeroCoeff mu theta * y r)) r) :
    HasDerivAt (originPhysicalValue y) (originPhysicalSlope y v r) r ∧
    HasDerivAt (originPhysicalSlope y v)
      (-(frozenFirstCoeff r * originPhysicalSlope y v r +
        frozenZeroCoeff mu theta * originPhysicalValue y r)) r := by
  have hc : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 r := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
      Complex.ofRealCLM.hasDerivAt (x := r)
  have hn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  constructor
  · convert hy.div hc hn using 1
    · rfl
    · dsimp [originPhysicalSlope]
      field_simp
  · convert (hv.div hc hn).sub (hy.div (hc.pow 2) (pow_ne_zero 2 hn)) using 1
    · rfl
    · dsimp [originPhysicalSlope, originPhysicalValue, originFirstCoeff,
        originZeroCoeff, frozenFirstCoeff, frozenZeroCoeff]
      field_simp
      ring
end HBL.Profile.Kummer
