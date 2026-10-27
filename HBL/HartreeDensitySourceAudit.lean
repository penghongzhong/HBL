import HBL.HartreeDensitySourceBounds

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.RegularRadiation.PhysicalExpansion.densityQuadraticConstant
#check @HBL.RegularRadiation.PhysicalExpansion.densityLinear_source_integrable
#check @HBL.RegularRadiation.PhysicalExpansion.densityRemainder_source_bound
#check @HBL.RegularRadiation.PhysicalExpansion.densityRemainder_small_ball_bound
#check @HBL.RegularRadiation.PhysicalExpansion.physical_hartree_expansion_from_function_bounds

set_option pp.all false in
#print axioms HBL.RegularRadiation.PhysicalExpansion.densityQuadraticConstant
set_option pp.all false in
#print axioms HBL.RegularRadiation.PhysicalExpansion.densityLinear_source_integrable
set_option pp.all false in
#print axioms HBL.RegularRadiation.PhysicalExpansion.densityRemainder_source_bound
set_option pp.all false in
#print axioms HBL.RegularRadiation.PhysicalExpansion.densityRemainder_small_ball_bound
set_option pp.all false in
#print axioms HBL.RegularRadiation.PhysicalExpansion.physical_hartree_expansion_from_function_bounds
