import HBL.PhysicalNonlocalForm

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#print HBL.Modulation.Monopole.physicalHartreeKernel
#print HBL.Modulation.Monopole.physicalCubicWeight
#print HBL.Modulation.Monopole.physicalNonlocalForm
#print HBL.Modulation.Monopole.physicalNonlocalBound
#check @HBL.Modulation.Monopole.physicalNonlocalForm_certified

set_option pp.all false in
#print axioms HBL.Modulation.Monopole.physicalNonlocalForm_certified
