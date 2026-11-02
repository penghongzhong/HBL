import HBL.Literature.AroraRoudenko2020Interface
set_option autoImplicit false

#check @HBL.Literature.AroraRoudenko2020.ExtendedHighRegularityInput
#check @HBL.Literature.AroraRoudenko2020.certified_cited_flow_is_physical_strong_solution
#print axioms HBL.Literature.AroraRoudenko2020.certified_cited_flow_is_physical_strong_solution
#check @HBL.Literature.AroraRoudenko2020.certified_cited_flow_satisfies_actual_Hartree
#print axioms HBL.Literature.AroraRoudenko2020.certified_cited_flow_satisfies_actual_Hartree
#check @HBL.Literature.AroraRoudenko2020.certified_cited_flow_physical_Riesz_integrable
#print axioms HBL.Literature.AroraRoudenko2020.certified_cited_flow_physical_Riesz_integrable
#check @HBL.Literature.AroraRoudenko2020.certified_cited_flow_unique
#print axioms HBL.Literature.AroraRoudenko2020.certified_cited_flow_unique
#check @HBL.Literature.AroraRoudenko2020.certified_cited_flow_radial
#print axioms HBL.Literature.AroraRoudenko2020.certified_cited_flow_radial

/-! This audit proves only conditional consequences of the LWP/high-regularity
literature interface. It does not assert Lean constructed an LT witness,
and it does not count original HBL manuscript 2.12 as proved. -/
