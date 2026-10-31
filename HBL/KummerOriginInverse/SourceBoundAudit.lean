import HBL.KummerOriginInverse.UniformSourceBound

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Profile.Kummer.originAnnulus_source_norm_le
#check @HBL.Profile.Kummer.originAnnulus_coefficients_norm_le
#check @HBL.Profile.Kummer.originAnnulus_value_slope_norm_le
#check @HBL.Profile.Kummer.exists_compact_origin_kummer_source_bound

set_option pp.all false in
#print axioms HBL.Profile.Kummer.originAnnulus_source_norm_le
set_option pp.all false in
#print axioms HBL.Profile.Kummer.originAnnulus_coefficients_norm_le
set_option pp.all false in
#print axioms HBL.Profile.Kummer.originAnnulus_value_slope_norm_le
set_option pp.all false in
#print axioms HBL.Profile.Kummer.exists_compact_origin_kummer_source_bound
