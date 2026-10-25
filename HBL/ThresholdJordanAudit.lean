import HBL.ThresholdJordanWitness

set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs false
set_option pp.maxSteps 1000000

#check @HBL.Modulation.ThresholdAudit.jordanHalfLine_exact
set_option pp.universes false in
#print axioms HBL.Modulation.ThresholdAudit.jordanHalfLine_exact
#check @HBL.Modulation.ThresholdAudit.no_bounded_zero_projection_of_range_limit
set_option pp.universes false in
#print axioms HBL.Modulation.ThresholdAudit.no_bounded_zero_projection_of_range_limit
