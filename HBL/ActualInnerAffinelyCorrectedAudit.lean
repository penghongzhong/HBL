import HBL.ActualInnerAffinelyCorrected

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Profile.ActualInner.existsUnique_actualInner_affinelyCorrected
#check @HBL.Profile.ActualInner.actualAffine_corrected_sources_compatible

set_option pp.all false in
#print axioms HBL.Profile.ActualInner.existsUnique_actualInner_affinelyCorrected
#print axioms HBL.Profile.ActualInner.actualAffine_corrected_sources_compatible
