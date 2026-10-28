import HBL.KummerPairFromNormalized

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Profile.Kummer.candidateWronskian_ne_of_normalized
#check @HBL.Profile.Kummer.CandidatePair.toFundamentalPair

set_option pp.all false in
#print axioms HBL.Profile.Kummer.candidateWronskian_ne_of_normalized
set_option pp.all false in
#print axioms HBL.Profile.Kummer.CandidatePair.toFundamentalPair
