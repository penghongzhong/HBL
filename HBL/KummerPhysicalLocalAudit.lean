import HBL.KummerPhysicalLocal

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Profile.Kummer.frozenKummer_trajectory_time_coordinate
#check @HBL.Profile.Kummer.frozenKummer_local_physical_equation

set_option pp.all false in
#print axioms HBL.Profile.Kummer.frozenKummer_trajectory_time_coordinate
set_option pp.all false in
#print axioms HBL.Profile.Kummer.frozenKummer_local_physical_equation
