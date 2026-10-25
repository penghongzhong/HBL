import HBL.RetainedThresholdBackward

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Modulation.TriangularRepair.phaseThresholdCoupling_certified
#check @HBL.Modulation.TriangularRepair.realThresholdCoupling_certified
#check @HBL.Modulation.TriangularRepair.retainedThresholdBackward_certified

set_option pp.all false in
#print axioms HBL.Modulation.TriangularRepair.phaseThresholdCoupling_certified
set_option pp.all false in
#print axioms HBL.Modulation.TriangularRepair.realThresholdCoupling_certified
set_option pp.all false in
#print axioms HBL.Modulation.TriangularRepair.retainedThresholdBackward_certified
