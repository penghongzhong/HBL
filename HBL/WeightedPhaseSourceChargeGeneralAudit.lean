import HBL.WeightedPhaseSourceChargeGeneral
set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Modulation.Monopole.weightedPhaseSourceResonance_memLp_two
#check @HBL.Modulation.Monopole.weightedPhaseSourceResonance_inner_data_eq_pairing
#check @HBL.Modulation.Monopole.weightedPhaseSourceResonance_inner_data_zero_iff

set_option pp.all false in
#print axioms HBL.Modulation.Monopole.weightedPhaseSourceResonance_inner_data_eq_pairing
set_option pp.all false in
#print axioms HBL.Modulation.Monopole.weightedPhaseSourceResonance_inner_data_zero_iff
