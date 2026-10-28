import HBL.KummerFrozenAnnulus

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Profile.Kummer.actualKummerAnnulus_certified
#check @HBL.Profile.Kummer.annulusSolution_actual_frozenResidual

set_option pp.all false in
#print axioms HBL.Profile.Kummer.actualKummerAnnulus_certified
set_option pp.all false in
#print axioms HBL.Profile.Kummer.annulusSolution_actual_frozenResidual
