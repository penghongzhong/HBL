import HBL.WeightedSourceFredholmBridge

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Modulation.Monopole.weightedSourceGreen_cokernel_pairing
#check @HBL.Modulation.Monopole.weightedSourceGreen_mem_adjointKernel_orthogonal

set_option pp.all false in
#print axioms HBL.Modulation.Monopole.weightedSourceGreen_cokernel_pairing
set_option pp.all false in
#print axioms HBL.Modulation.Monopole.weightedSourceGreen_mem_adjointKernel_orthogonal
