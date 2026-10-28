import HBL.KummerPhysicalAnnulusLocalized

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Profile.Kummer.regularizedFirstCoeff_eq_physical
#check @HBL.Profile.Kummer.regularizedFirstCoeff_continuous
#check @HBL.Profile.Kummer.actualKummerAnnulus_localized_certified

set_option pp.all false in
#print axioms HBL.Profile.Kummer.actualKummerAnnulus_localized_certified
