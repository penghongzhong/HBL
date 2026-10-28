import HBL.KummerFrozenBridge

set_option pp.all true
set_option pp.maxSteps 10000000

#check @HBL.Profile.Kummer.frozenRadialJetResidual_reduction
#check @HBL.Profile.Kummer.frozenRadialJetResidual_zero_of_confluent

set_option pp.all false in
#print axioms HBL.Profile.Kummer.frozenRadialJetResidual_reduction
set_option pp.all false in
#print axioms HBL.Profile.Kummer.frozenRadialJetResidual_zero_of_confluent
