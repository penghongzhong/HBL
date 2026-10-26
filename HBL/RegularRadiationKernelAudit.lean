import HBL.RegularRadiationKernel
set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000
#print HBL.RegularRadiation.kernel
#print HBL.RegularRadiation.potential
#print HBL.RegularRadiation.quarticDensity
#print HBL.RegularRadiation.hartreeNonlinearity
#check @HBL.RegularRadiation.potential_bound
#check @HBL.RegularRadiation.potential_sub_bound
#check @HBL.RegularRadiation.quartic_difference
#check @HBL.RegularRadiation.quartic_potential_bound
#check @HBL.RegularRadiation.hartree_L2_bound
#check @HBL.RegularRadiation.regularRadiationKernel_checks
set_option pp.all false in
#print axioms HBL.RegularRadiation.potential_bound
set_option pp.all false in
#print axioms HBL.RegularRadiation.potential_sub_bound
set_option pp.all false in
#print axioms HBL.RegularRadiation.quartic_difference
set_option pp.all false in
#print axioms HBL.RegularRadiation.quartic_potential_bound
set_option pp.all false in
#print axioms HBL.RegularRadiation.hartree_L2_bound
set_option pp.all false in
#print axioms HBL.RegularRadiation.regularRadiationKernel_checks
