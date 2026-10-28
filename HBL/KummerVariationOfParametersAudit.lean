import HBL.KummerVariationOfParameters

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Profile.Kummer.FundamentalPair
#check @HBL.Profile.Kummer.variationOfParameters_certified

set_option pp.all false in
#print axioms HBL.Profile.Kummer.wronskian_continuous
set_option pp.all false in
#print axioms HBL.Profile.Kummer.coeffA_hasDerivAt
set_option pp.all false in
#print axioms HBL.Profile.Kummer.solution_hasDerivAt
set_option pp.all false in
#print axioms HBL.Profile.Kummer.solutionDeriv_hasDerivAt
set_option pp.all false in
#print axioms HBL.Profile.Kummer.solution_equation
set_option pp.all false in
#print axioms HBL.Profile.Kummer.variationOfParameters_certified
