import HBL.HartreeFullRemainderBounds

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.RegularRadiation.PhysicalExpansion.linearPotentialConstant
#check @HBL.RegularRadiation.PhysicalExpansion.quadraticPotentialConstant
#check @HBL.RegularRadiation.PhysicalExpansion.fullRemainderHConstant
#check @HBL.RegularRadiation.PhysicalExpansion.densityLinear_potential_small
#check @HBL.RegularRadiation.PhysicalExpansion.fullRemainder_pointwise_bound
#check @HBL.RegularRadiation.PhysicalExpansion.fullRemainder_L2_bound
#check @HBL.RegularRadiation.PhysicalExpansion.fullRemainder_Linfty_bound

set_option pp.all false in
#print axioms HBL.RegularRadiation.PhysicalExpansion.linearPotentialConstant
set_option pp.all false in
#print axioms HBL.RegularRadiation.PhysicalExpansion.quadraticPotentialConstant
set_option pp.all false in
#print axioms HBL.RegularRadiation.PhysicalExpansion.fullRemainderHConstant
set_option pp.all false in
#print axioms HBL.RegularRadiation.PhysicalExpansion.densityLinear_potential_small
set_option pp.all false in
#print axioms HBL.RegularRadiation.PhysicalExpansion.fullRemainder_pointwise_bound
set_option pp.all false in
#print axioms HBL.RegularRadiation.PhysicalExpansion.fullRemainder_L2_bound
set_option pp.all false in
#print axioms HBL.RegularRadiation.PhysicalExpansion.fullRemainder_Linfty_bound
