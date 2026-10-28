import HBL.WeightedPhaseFredholmCore

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Modulation.Monopole.weightedPhaseFredholm_kernel_eq_sine_span
#check @HBL.Modulation.Monopole.weightedPhaseFredholm_adjointKernel_eq_sine_span

set_option pp.all false in
#print axioms HBL.Modulation.Monopole.weightedPhaseFredholm_kernel_eq_sine_span
set_option pp.all false in
#print axioms HBL.Modulation.Monopole.weightedPhaseFredholm_adjointKernel_eq_sine_span
