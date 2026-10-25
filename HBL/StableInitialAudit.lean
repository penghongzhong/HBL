import HBL.StableInitialPropagation

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Shooting.stableInitialPropagation_certified
set_option pp.all false in
#print axioms HBL.Shooting.stableInitialPropagation_certified
