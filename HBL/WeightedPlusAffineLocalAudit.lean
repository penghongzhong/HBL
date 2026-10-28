import HBL.WeightedPlusAffineLocal

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Modulation.AffineTail.affineModelSecondDerivative_inWeightedL2
#check @HBL.Modulation.AffineTail.hPlusLocalAffineSource_inWeightedL2

set_option pp.all false in
#print axioms HBL.Modulation.AffineTail.hPlusLocalAffineSource_inWeightedL2
