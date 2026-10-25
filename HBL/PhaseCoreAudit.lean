import HBL.PhysicalRadial3PhaseCore

set_option pp.all true

#check @HBL.Modulation.Monopole.radialU_deriv_memLp_of_upperSupport
#check @HBL.Modulation.Monopole.radialU_global_energy_of_upperSupport
#check @HBL.Modulation.Monopole.physicalRadial3_gradient_coordinate_of_upperSupport
#check @HBL.Modulation.Monopole.physicalRadial3_phase_core_eq_volterra
#check @HBL.Modulation.Monopole.physicalRadial3_phase_core_nonnegative
#check @HBL.Modulation.Monopole.physicalRadial3_phase_core_coercive

set_option pp.all false

#print axioms HBL.Modulation.Monopole.radialU_deriv_memLp_of_upperSupport
#print axioms HBL.Modulation.Monopole.radialU_global_energy_of_upperSupport
#print axioms HBL.Modulation.Monopole.physicalRadial3_gradient_coordinate_of_upperSupport
#print axioms HBL.Modulation.Monopole.physicalRadial3_phase_core_eq_volterra
#print axioms HBL.Modulation.Monopole.physicalRadial3_phase_core_nonnegative
#print axioms HBL.Modulation.Monopole.physicalRadial3_phase_core_coercive
