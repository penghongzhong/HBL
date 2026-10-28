import HBL.ActualInnerTwoChannel

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Profile.ActualInner.existsUnique_actual_twoChannel_compatible_solve
#check @HBL.Profile.ActualInner.existsUnique_actual_twoChannel_affine_charges

set_option pp.all false in
#print axioms HBL.Profile.ActualInner.existsUnique_actual_twoChannel_compatible_solve
set_option pp.all false in
#print axioms HBL.Profile.ActualInner.existsUnique_actual_twoChannel_affine_charges
