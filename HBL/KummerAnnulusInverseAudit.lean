import HBL.KummerAnnulusInverse

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Profile.Kummer.annulusVariationOfParameters_certified
#check @HBL.Profile.Kummer.annulusSolution_equation

set_option pp.all false in
#print axioms HBL.Profile.Kummer.annulusVariationOfParameters_certified
set_option pp.all false in
#print axioms HBL.Profile.Kummer.annulusSolution_equation
