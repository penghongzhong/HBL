import HBL.PhysicalPhaseHessian

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#print HBL.Modulation.Monopole.physicalPhaseHessian
#check @HBL.Modulation.Monopole.physicalPhaseHessian_certified

set_option pp.all false in
#print axioms HBL.Modulation.Monopole.physicalPhaseHessian_certified
