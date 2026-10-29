import HBL.KummerPrescribedAnnulus.CompactInverse
set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#print HBL.Profile.Kummer.LocalKummerBound
#print HBL.Profile.Kummer.IsLocalKummerRightInverse
#print HBL.Profile.Kummer.IsKummerBoundarySolution
#print HBL.Profile.Kummer.frozenFirstCoeff
#print HBL.Profile.Kummer.frozenZeroCoeff
#check HBL.Profile.Kummer.LocalKummerPair.mk

#check @HBL.Profile.Kummer.centered_ode_norm_le_exp
#print axioms HBL.Profile.Kummer.centered_ode_norm_le_exp
#check @HBL.Profile.Kummer.prescribed_kummer_pair_exp_bound
#print axioms HBL.Profile.Kummer.prescribed_kummer_pair_exp_bound
#check @HBL.Profile.Kummer.exists_compact_prescribed_kummer_pair
#print axioms HBL.Profile.Kummer.exists_compact_prescribed_kummer_pair
#check @HBL.Profile.Kummer.exists_compact_prescribed_kummer_inverse
#print axioms HBL.Profile.Kummer.exists_compact_prescribed_kummer_inverse
