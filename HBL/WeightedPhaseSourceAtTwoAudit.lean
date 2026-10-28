import HBL.WeightedPhaseSourceAtTwo

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Modulation.Monopole.phaseSourceData_charge_zero_iff
#check @HBL.Modulation.Monopole.existsUnique_physicalPhaseWeightedSourceSolve

set_option pp.all false in
#print axioms HBL.Modulation.Monopole.existsUnique_physicalPhaseWeightedSourceSolve
