import HBL.WeightedStrongDynamics
import HBL.WeightedTailIdentities
import HBL.HartreePhysicalLinearization

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#print HBL.RegularRadiation.hartreeNonlinearity
#check @HBL.MainBackward.constrainedCenterEmbedding
#check @HBL.MainBackward.centerDuhamelTail
#check @HBL.MainBackward.strongCenterDuhamel_certified
#check @HBL.MainBackward.neg_Ioi_integral_hasDerivAt
#check @HBL.MainBackward.weightedThresholdTail_hasDerivAt
#check @HBL.MainBackward.weightedThresholdForcingTail_hasDerivAt
#check @HBL.MainBackward.weightedCenterFeedbackTail_strong
#check @HBL.MainBackward.weightedCenterNonlinearTail_strong
#check @HBL.MainBackward.weightedCenterForcingTail_strong
#check @HBL.MainBackward.unweight_weightedThresholdMap
#check @HBL.MainBackward.unweight_weightedThresholdForcingPath
#check @HBL.MainBackward.unweight_weightedCenterFeedbackMap
#check @HBL.MainBackward.unweight_weightedCenterNonlinearMap
#check @HBL.MainBackward.unweight_weightedCenterForcingPath
#check @HBL.RegularRadiation.PhysicalExpansion.norm_sq_real_add
#check @HBL.RegularRadiation.PhysicalExpansion.cubic_split
#check @HBL.RegularRadiation.PhysicalExpansion.cubic_base
#check @HBL.RegularRadiation.PhysicalExpansion.quartic_density_split
#check @HBL.RegularRadiation.PhysicalExpansion.potential_split
#check @HBL.RegularRadiation.PhysicalExpansion.physical_hartree_expansion

set_option pp.all false in
#print axioms HBL.MainBackward.constrainedCenterEmbedding
set_option pp.all false in
#print axioms HBL.MainBackward.centerDuhamelTail
set_option pp.all false in
#print axioms HBL.MainBackward.strongCenterDuhamel_certified
set_option pp.all false in
#print axioms HBL.MainBackward.neg_Ioi_integral_hasDerivAt
set_option pp.all false in
#print axioms HBL.MainBackward.weightedThresholdTail_hasDerivAt
set_option pp.all false in
#print axioms HBL.MainBackward.weightedThresholdForcingTail_hasDerivAt
set_option pp.all false in
#print axioms HBL.MainBackward.weightedCenterFeedbackTail_strong
set_option pp.all false in
#print axioms HBL.MainBackward.weightedCenterNonlinearTail_strong
set_option pp.all false in
#print axioms HBL.MainBackward.weightedCenterForcingTail_strong
set_option pp.all false in
#print axioms HBL.MainBackward.unweight_weightedThresholdMap
set_option pp.all false in
#print axioms HBL.MainBackward.unweight_weightedThresholdForcingPath
set_option pp.all false in
#print axioms HBL.MainBackward.unweight_weightedCenterFeedbackMap
set_option pp.all false in
#print axioms HBL.MainBackward.unweight_weightedCenterNonlinearMap
set_option pp.all false in
#print axioms HBL.MainBackward.unweight_weightedCenterForcingPath
set_option pp.all false in
#print axioms HBL.RegularRadiation.PhysicalExpansion.norm_sq_real_add
set_option pp.all false in
#print axioms HBL.RegularRadiation.PhysicalExpansion.cubic_split
set_option pp.all false in
#print axioms HBL.RegularRadiation.PhysicalExpansion.cubic_base
set_option pp.all false in
#print axioms HBL.RegularRadiation.PhysicalExpansion.quartic_density_split
set_option pp.all false in
#print axioms HBL.RegularRadiation.PhysicalExpansion.potential_split
set_option pp.all false in
#print axioms HBL.RegularRadiation.PhysicalExpansion.physical_hartree_expansion
