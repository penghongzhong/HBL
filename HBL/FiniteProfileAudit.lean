import HBL.FiniteProfile
import HBL.OneLayerElimination
import HBL.TransversalityExact
import HBL.KinematicTailEstimates

set_option pp.universes false
set_option pp.all false

#check @HBL.Profile.FiniteProfile.iterated_gain_lower_bound
#check @HBL.Profile.FiniteProfile.finite_gain_termination
#check @HBL.Profile.FiniteProfile.slow_degree_four_integrable_exponent
#check @HBL.Profile.FiniteProfile.power_tail_exact
#check @HBL.Profile.FiniteProfile.finiteProfile_recursion_certified
#check @HBL.Profile.OneLayer.oneMinimalWeightCluster_eliminated
#check @HBL.Modulation.Transversality.manuscript_transversality_environment_closed
#check @HBL.Kinematic.integral_Ioi_rpow_neg_one_sub

#print axioms HBL.Profile.FiniteProfile.iterated_gain_lower_bound
#print axioms HBL.Profile.FiniteProfile.finite_gain_termination
#print axioms HBL.Profile.FiniteProfile.slow_degree_four_integrable_exponent
#print axioms HBL.Profile.FiniteProfile.power_tail_exact
#print axioms HBL.Profile.FiniteProfile.finiteProfile_recursion_certified
#print axioms HBL.Profile.OneLayer.oneMinimalWeightCluster_eliminated
#print axioms HBL.Modulation.Transversality.manuscript_transversality_environment_closed
#print axioms HBL.Kinematic.integral_Ioi_rpow_neg_one_sub
