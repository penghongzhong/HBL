import HBL.RemotePerturbationInverse

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Profile.Remote.perturbationBlock_isInvertible
#check @HBL.Profile.Remote.perturbedInverse_right
#check @HBL.Profile.Remote.perturbedInverse_left
#check @HBL.Profile.Remote.perturbedBlock_bijective
#check @HBL.Profile.Remote.perturbedBlock_unique_solution

set_option pp.all false in
#print axioms HBL.Profile.Remote.perturbationBlock_isInvertible
set_option pp.all false in
#print axioms HBL.Profile.Remote.perturbedInverse_right
set_option pp.all false in
#print axioms HBL.Profile.Remote.perturbedInverse_left
set_option pp.all false in
#print axioms HBL.Profile.Remote.perturbedBlock_bijective
set_option pp.all false in
#print axioms HBL.Profile.Remote.perturbedBlock_unique_solution
