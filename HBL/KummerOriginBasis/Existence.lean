import HBL.KummerOriginBasis.RegularIVP

noncomputable section
set_option autoImplicit false
namespace HBL.Profile.Kummer

/-- The origin-normalized pair is constructed from actual finite-interval IVPs. -/
theorem exists_origin_kummer_pair (mu theta R : ℝ) (hR : 0 ≤ R) :
    Nonempty (OriginKummerPair mu theta R) := by
  obtain ⟨y, dy, hy, hdy, hY⟩ := exists_origin_kummer_prescribed_ivp mu theta 0 R hR 1 0
  obtain ⟨x, dx, hx, hdx, hX⟩ := exists_origin_kummer_prescribed_ivp mu theta 0 R hR 0 1
  exact ⟨{
    y := y, dy := dy, x := x, dx := dx
    y_zero := hy, dy_zero := hdy, x_zero := hx, dx_zero := hdx
    y_deriv := fun r hr => (hY r hr).1
    dy_deriv := fun r hr => (hY r hr).2
    x_deriv := fun r hr => (hX r hr).1
    dx_deriv := fun r hr => (hX r hr).2 }⟩
end HBL.Profile.Kummer
