import HBL.GlobalH1Matching
import HBL.FiniteProfile
import HBL.PhysicalVectorGradient
import HBL.MonopoleGlobalEnergy

set_option pp.universes false
set_option pp.all false

#check @HBL.Profile.GlobalH1.choose_three_region_scales
#check @HBL.Profile.GlobalH1.three_region_energy_bound
#check @HBL.Profile.GlobalH1.three_region_with_error_bound
#check @HBL.Profile.GlobalH1.physical_gradient_energy_of_radial_coordinate
#check @HBL.Profile.GlobalH1.globalH1Matching_certified
#check @HBL.Profile.FiniteProfile.finiteProfile_recursion_certified
#check @HBL.Modulation.Monopole.physicalVectorGradient_certified
#check @HBL.Modulation.Monopole.monopoleMovingCutoffGlobalEnergy_closed

#print axioms HBL.Profile.GlobalH1.choose_three_region_scales
#print axioms HBL.Profile.GlobalH1.three_region_energy_bound
#print axioms HBL.Profile.GlobalH1.three_region_with_error_bound
#print axioms HBL.Profile.GlobalH1.physical_gradient_energy_of_radial_coordinate
#print axioms HBL.Profile.GlobalH1.globalH1Matching_certified
#print axioms HBL.Profile.FiniteProfile.finiteProfile_recursion_certified
#print axioms HBL.Modulation.Monopole.physicalVectorGradient_certified
#print axioms HBL.Modulation.Monopole.monopoleMovingCutoffGlobalEnergy_closed
