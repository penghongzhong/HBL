import HBL.WeightedPlusAffineNonlocal

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Modulation.Monopole.affineConjugatedModel_memLp_two
#check @HBL.Modulation.Monopole.nonlocalAffine_inWeightedL2

set_option pp.all false in
#print axioms HBL.Modulation.Monopole.affineConjugatedModel_memLp_two
set_option pp.all false in
#print axioms HBL.Modulation.Monopole.nonlocalAffine_inWeightedL2
