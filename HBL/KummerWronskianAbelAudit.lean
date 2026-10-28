import HBL.KummerWronskianAbel

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Profile.Kummer.wronskian_hasDerivAt
#check @HBL.Profile.Kummer.wronskian_deriv
#check @HBL.Profile.Kummer.wronskian_differentiable

set_option pp.all false in
#print axioms HBL.Profile.Kummer.wronskian_hasDerivAt
