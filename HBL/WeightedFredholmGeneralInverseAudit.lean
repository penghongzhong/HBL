import HBL.WeightedFredholmGeneralInverse
set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000
#check @HBL.Modulation.Monopole.weightedFredholmGeneralInverse_certified
#check @HBL.Modulation.Monopole.weightedFredholmSolve_eq_green
set_option pp.all false in
#print axioms HBL.Modulation.Monopole.weightedFredholmGeneralInverse_certified
set_option pp.all false in
#print axioms HBL.Modulation.Monopole.weightedFredholmSolve_eq_green
