import HBL.KummerWronskianNormalized

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Profile.Kummer.abelInvariant_eq
#check @HBL.Profile.Kummer.wronskian_ne_of_normalized

set_option pp.all false in
#print axioms HBL.Profile.Kummer.abelInvariant_eq
set_option pp.all false in
#print axioms HBL.Profile.Kummer.wronskian_ne_of_normalized
