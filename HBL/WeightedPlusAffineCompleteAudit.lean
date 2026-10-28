import HBL.WeightedPlusAffineComplete

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Modulation.AffineTail.hPlusAffineSource_inWeightedL2
#check @HBL.Modulation.AffineTail.hPlusAffineCorrectedSource_inWeightedL2
#check @HBL.Modulation.AffineTail.hPlusAffineCorrectedSource_charge_zero

set_option pp.all false in
#print axioms HBL.Modulation.AffineTail.hPlusAffineSource_inWeightedL2
set_option pp.all false in
#print axioms HBL.Modulation.AffineTail.hPlusAffineCorrectedSource_charge_zero
