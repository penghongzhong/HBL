import HBL.WeightedPhaseSourceFredholmBridge
set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Modulation.Monopole.weightedPhaseSourceGreen_cokernel_pairing
#check @HBL.Modulation.Monopole.weightedPhaseSourceGreen_cokernel_zero_of_charge_zero
#check @HBL.Modulation.Monopole.existsUnique_phaseWeightedSourceFredholmSolve

set_option pp.all false in
#print axioms HBL.Modulation.Monopole.weightedPhaseSourceGreen_cokernel_pairing
set_option pp.all false in
#print axioms HBL.Modulation.Monopole.existsUnique_phaseWeightedSourceFredholmSolve
