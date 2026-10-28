import HBL.WeightedSourceGreen

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Modulation.Monopole.weightedSourceGreenKernel_sq_integrable
#check @HBL.Modulation.Monopole.weightedSourceGreenOperator_kernel_certificate

set_option pp.all false in
#print axioms HBL.Modulation.Monopole.weightedSourceGreenKernel_sq_integrable
set_option pp.all false in
#print axioms HBL.Modulation.Monopole.weightedSourceGreenOperator_kernel_certificate
