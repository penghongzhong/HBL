import HBL.WeightedSourceFredholmSolution

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Modulation.Monopole.existsUnique_weightedSourceFredholmSolution
#check @HBL.Modulation.Monopole.weightedSourceFredholmSolution_green_equation

set_option pp.all false in
#print axioms HBL.Modulation.Monopole.existsUnique_weightedSourceFredholmSolution
set_option pp.all false in
#print axioms HBL.Modulation.Monopole.weightedSourceFredholmSolution_green_equation
