import HBL.PhaseEnergyInverse

set_option pp.all true
set_option pp.universes true
set_option pp.maxDepth 1024
set_option pp.maxSteps 1000000

#check @HBL.Modulation.Monopole.phaseEnergyInverse_certified

set_option pp.all false
set_option pp.universes false

#print axioms HBL.Modulation.Monopole.phaseEnergyInverse_certified
