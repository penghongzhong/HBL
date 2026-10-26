import HBL.RegularRadiationKernel
set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000
#print HBL.RegularRadiation.kernel
#print HBL.RegularRadiation.potential
#check @HBL.RegularRadiation.potential_bound
#check @HBL.RegularRadiation.potential_sub_bound
#check @HBL.RegularRadiation.quartic_difference
#check @HBL.RegularRadiation.regularRadiationKernel_checks
set_option pp.all false in
#print axioms HBL.RegularRadiation.potential_bound
set_option pp.all false in
#print axioms HBL.RegularRadiation.potential_sub_bound
set_option pp.all false in
#print axioms HBL.RegularRadiation.quartic_difference
set_option pp.all false in
#print axioms HBL.RegularRadiation.regularRadiationKernel_checks
