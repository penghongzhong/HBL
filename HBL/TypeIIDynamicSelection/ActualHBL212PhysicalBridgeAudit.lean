import HBL.TypeIIDynamicSelection.ActualOneLayerCertifiedKummerSource
import HBL.TypeIIDynamicSelection.ActualOneLayerInnerRemoteSource
import HBL.TypeIIDynamicSelection.ActualOneLayerSingleComplexWeightedSource
import HBL.TypeIIDynamicSelection.ActualPhasedFlatTimeTail
import HBL.TypeIIDynamicSelection.ActualFlatGainIntegrability

/-!
# Integration audit for the retained original Hartree profile 2.12

Every imported file comes verbatim from its separately trust-zero accepted
Lean 4.35.0-rc3 branch. This audit checks transitive declarations together,
with one concrete nonterminal PDE source shared by inner H+, H-, the actual
normalized Kummer inverse, and the moving exterior decomposition.

The derived flat-radiation time tail is included. This integration does
NOT provide the still missing offterminal PDE source weighted norm,
Kummer-to-remote boundary matching, or the full generated positive
minimum-order classification. Hence original 2.12 remains OPEN.
-/

set_option autoImplicit false

#check @HBL.TypeIIDynamicSelection.actual_one_layer_Kummer_inverse_source_coherent
#print axioms HBL.TypeIIDynamicSelection.actual_one_layer_Kummer_inverse_source_coherent

#check @HBL.TypeIIDynamicSelection.actual_Hartree_common_PDE_has_constructed_Kummer_certificate
#print axioms HBL.TypeIIDynamicSelection.actual_Hartree_common_PDE_has_constructed_Kummer_certificate

#check @HBL.TypeIIDynamicSelection.actual_one_layer_common_Hartree_PDE_inner_remote_exact
#print axioms HBL.TypeIIDynamicSelection.actual_one_layer_common_Hartree_PDE_inner_remote_exact

#check @HBL.TypeIIDynamicSelection.actual_one_layer_common_Hartree_PDE_inner_remote_both_channels
#print axioms HBL.TypeIIDynamicSelection.actual_one_layer_common_Hartree_PDE_inner_remote_both_channels

#check @HBL.TypeIIDynamicSelection.actual_Hartree_common_PDE_one_weighted_norm_unique_inner
#print axioms HBL.TypeIIDynamicSelection.actual_Hartree_common_PDE_one_weighted_norm_unique_inner

#check @HBL.TypeIIDynamicSelection.actual_Hartree_phased_flat_physical_time_integrable
#print axioms HBL.TypeIIDynamicSelection.actual_Hartree_phased_flat_physical_time_integrable

#check @HBL.TypeIIDynamicSelection.actual_Hartree_flat_power_integrable_with_tail
#print axioms HBL.TypeIIDynamicSelection.actual_Hartree_flat_power_integrable_with_tail
