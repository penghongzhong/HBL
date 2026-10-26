import HBL.CompactPhaseNormalization

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Modulation.Monopole.actualCompactPhaseSlice_certified
#check @HBL.Modulation.Monopole.actualCompactPhaseInverse_certified

set_option pp.all false in
#print axioms HBL.Modulation.Monopole.actualCompactPhaseSlice_certified
set_option pp.all false in
#print axioms HBL.Modulation.Monopole.actualCompactPhaseInverse_certified
