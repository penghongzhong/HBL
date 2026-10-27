import HBL.RegularRadiationFlow

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.RegularRadiation.sobolevWeaken
#check @HBL.RegularRadiation.sobolevWeaken_toDistr
#check @HBL.RegularRadiation.physicalL2
#check @HBL.RegularRadiation.physicalL2_toDistr
#check @HBL.RegularRadiation.physicalQuarticPotential_bound
#check @HBL.RegularRadiation.IsRadialSobolev
#check @HBL.RegularRadiation.sobolevDropTwo
#check @HBL.RegularRadiation.sobolevLaplacian
#check @HBL.RegularRadiation.sobolevLaplacian_toDistr
#check @HBL.RegularRadiation.HartreeEquationAt
#check @HBL.RegularRadiation.GeneralizedHartreeRegularLocalTheory
#check @HBL.RegularRadiation.GeneralizedHartreeRegularLocalTheory.equation
#check @HBL.RegularRadiation.GeneralizedHartreeRegularLocalTheory.jet_step
#check @HBL.RegularRadiation.GeneralizedHartreeRegularLocalTheory.jet_bound
#check @HBL.RegularRadiation.GeneralizedHartreeRegularLocalTheory.data_c1
#check @HBL.RegularRadiation.regularRadiationFlow_certified
#check @HBL.RegularRadiation.regularRadiation_strong_equation_certified
#check @HBL.RegularRadiation.regularRadiation_actualKernel_check

set_option pp.all false in
#print axioms HBL.RegularRadiation.sobolevWeaken
set_option pp.all false in
#print axioms HBL.RegularRadiation.sobolevWeaken_toDistr
set_option pp.all false in
#print axioms HBL.RegularRadiation.physicalL2
set_option pp.all false in
#print axioms HBL.RegularRadiation.physicalL2_toDistr
set_option pp.all false in
#print axioms HBL.RegularRadiation.physicalQuarticPotential_bound
set_option pp.all false in
#print axioms HBL.RegularRadiation.IsRadialSobolev
set_option pp.all false in
#print axioms HBL.RegularRadiation.sobolevDropTwo
set_option pp.all false in
#print axioms HBL.RegularRadiation.sobolevLaplacian
set_option pp.all false in
#print axioms HBL.RegularRadiation.sobolevLaplacian_toDistr
set_option pp.all false in
#print axioms HBL.RegularRadiation.HartreeEquationAt
set_option pp.all false in
#print axioms HBL.RegularRadiation.GeneralizedHartreeRegularLocalTheory
set_option pp.all false in
#print axioms HBL.RegularRadiation.GeneralizedHartreeRegularLocalTheory.equation
set_option pp.all false in
#print axioms HBL.RegularRadiation.GeneralizedHartreeRegularLocalTheory.jet_step
set_option pp.all false in
#print axioms HBL.RegularRadiation.GeneralizedHartreeRegularLocalTheory.jet_bound
set_option pp.all false in
#print axioms HBL.RegularRadiation.GeneralizedHartreeRegularLocalTheory.data_c1
set_option pp.all false in
#print axioms HBL.RegularRadiation.regularRadiationFlow_certified
set_option pp.all false in
#print axioms HBL.RegularRadiation.regularRadiation_strong_equation_certified
set_option pp.all false in
#print axioms HBL.RegularRadiation.regularRadiation_actualKernel_check
