import HBL.WeightedPhaseFredholmInverse

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Modulation.Monopole.existsUnique_phaseFredholmSolution
#check @HBL.Modulation.Monopole.phaseFredholmSolution_green_equation

set_option pp.all false in
#print axioms HBL.Modulation.Monopole.existsUnique_phaseFredholmSolution
set_option pp.all false in
#print axioms HBL.Modulation.Monopole.phaseFredholmSolution_green_equation
