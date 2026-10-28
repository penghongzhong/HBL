import HBL.KummerLocalODE

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Profile.Kummer.frozenFirstCoeff_contDiffAt
#check @HBL.Profile.Kummer.frozenKummerAugmentedField_contDiffAt
#check @HBL.Profile.Kummer.exists_local_frozenKummer_augmented_solution

set_option pp.all false in
#print axioms HBL.Profile.Kummer.exists_local_frozenKummer_augmented_solution
