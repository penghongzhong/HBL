import HBL.TypeIIDynamicSelection.MonopoleRateTrapping

set_option autoImplicit false
set_option pp.all true

#check @HBL.TypeIIDynamicSelection.firstMonopoleDrivenMu_tendsto
#check @HBL.TypeIIDynamicSelection.firstMonopoleDrivenMu_tail
#check @HBL.TypeIIDynamicSelection.firstMonopoleDrivenMu_trapped

set_option pp.all false in
#print axioms HBL.TypeIIDynamicSelection.firstMonopoleDrivenMu_tendsto
set_option pp.all false in
#print axioms HBL.TypeIIDynamicSelection.firstMonopoleDrivenMu_tail
set_option pp.all false in
#print axioms HBL.TypeIIDynamicSelection.firstMonopoleDrivenMu_trapped
