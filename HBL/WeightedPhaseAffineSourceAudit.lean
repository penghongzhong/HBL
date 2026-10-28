import HBL.WeightedPhaseAffineSource

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Modulation.AffineTail.phaseAffineSource_weighted_sq_far
#check @HBL.Modulation.AffineTail.phaseAffineSource_inWeightedL2
#check @HBL.Modulation.AffineTail.phaseAffine_correctedSource_inWeightedL2

set_option pp.all false in
#print axioms HBL.Modulation.AffineTail.phaseAffine_correctedSource_inWeightedL2
