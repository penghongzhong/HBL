import HBL.OneLayerElimination
import HBL.AffineTailLemmaClosed
import HBL.FredholmOrthogonalInverse

set_option pp.universes false
set_option pp.all false

#check @HBL.Profile.OneLayer.fullThresholdCorrection_solves
#check @HBL.Profile.OneLayer.threshold_pair_unique
#check @HBL.Profile.OneLayer.solveLayer_exact
#check @HBL.Profile.OneLayer.solveLayer_unique
#check @HBL.Profile.OneLayer.kappaProfile_pos
#check @HBL.Profile.OneLayer.generatedTerm_order_ge
#check @HBL.Profile.OneLayer.oneMinimalWeightCluster_eliminated
#check @HBL.Modulation.AffineTail.secondManuscriptAffineTailEnvironment_closed
#check @HBL.Fredholm.existsUnique_one_sub_apply_eq

#print axioms HBL.Profile.OneLayer.fullThresholdCorrection_solves
#print axioms HBL.Profile.OneLayer.threshold_pair_unique
#print axioms HBL.Profile.OneLayer.solveLayer_exact
#print axioms HBL.Profile.OneLayer.solveLayer_unique
#print axioms HBL.Profile.OneLayer.kappaProfile_pos
#print axioms HBL.Profile.OneLayer.generatedTerm_order_ge
#print axioms HBL.Profile.OneLayer.oneMinimalWeightCluster_eliminated
#print axioms HBL.Modulation.AffineTail.secondManuscriptAffineTailEnvironment_closed
#print axioms HBL.Fredholm.existsUnique_one_sub_apply_eq
