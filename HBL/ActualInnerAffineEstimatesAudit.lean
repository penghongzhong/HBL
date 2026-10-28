import HBL.ActualInnerAffineEstimates

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Profile.ActualInner.actualPlusCharge_eq_twice_pairing
#check @HBL.Profile.ActualInner.actualMinusCharge_eq_neg_pairing
#check @HBL.Profile.ActualInner.actualPlusCharge_difference_le
#check @HBL.Profile.ActualInner.actualMinusCharge_difference_le
#check @HBL.Profile.ActualInner.weightedSourceDataL2_sub_const_mul
#check @HBL.Profile.ActualInner.correctedPlusDataL2_eq
#check @HBL.Profile.ActualInner.correctedMinusDataL2_eq
#check @HBL.Profile.ActualInner.correctedPlusDataL2_difference_le
#check @HBL.Profile.ActualInner.correctedMinusDataL2_difference_le

set_option pp.all false in
#print axioms HBL.Profile.ActualInner.actualPlusCharge_eq_twice_pairing
set_option pp.all false in
#print axioms HBL.Profile.ActualInner.actualMinusCharge_eq_neg_pairing
set_option pp.all false in
#print axioms HBL.Profile.ActualInner.actualPlusCharge_difference_le
set_option pp.all false in
#print axioms HBL.Profile.ActualInner.actualMinusCharge_difference_le
set_option pp.all false in
#print axioms HBL.Profile.ActualInner.weightedSourceDataL2_sub_const_mul
set_option pp.all false in
#print axioms HBL.Profile.ActualInner.correctedPlusDataL2_eq
set_option pp.all false in
#print axioms HBL.Profile.ActualInner.correctedMinusDataL2_eq
set_option pp.all false in
#print axioms HBL.Profile.ActualInner.correctedPlusDataL2_difference_le
set_option pp.all false in
#print axioms HBL.Profile.ActualInner.correctedMinusDataL2_difference_le
