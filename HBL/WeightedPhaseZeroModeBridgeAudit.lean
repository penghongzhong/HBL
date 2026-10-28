import HBL.WeightedPhaseZeroModeBridge

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Modulation.Monopole.firstSineMode_eq_twice_weightedPhaseResonance
#check @HBL.Modulation.Monopole.weightedPhaseResonanceL2_ae
#check @HBL.Modulation.Monopole.phaseFredholmSource_orthogonal_iff

set_option pp.all false in
#print axioms HBL.Modulation.Monopole.firstSineMode_eq_twice_weightedPhaseResonance
set_option pp.all false in
#print axioms HBL.Modulation.Monopole.phaseFredholmSource_orthogonal_iff
