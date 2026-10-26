import HBL.PhysicalWeakRadial

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#print HBL.Modulation.Monopole.IsPhysicalWeakRadialCoordinate
#check @HBL.Modulation.Monopole.physicalWeakRadial_certified

set_option pp.all false in
#print axioms HBL.Modulation.Monopole.physicalWeakRadial_certified
