import HBL.FirstModulationLemma
import HBL.AffineTailLemmaClosed
import HBL.MonopoleFirstCorrectionCertified
import HBL.MonopoleThresholdProjection
import HBL.KinematicSynchronizedSliceCertified
import HBL.UnstableShootingTerminal
import HBL.TransversalityExact
import HBL.HartreeKernelShortRange
import HBL.TriangularThresholdCoupling
import HBL.RealThresholdCoupling
import HBL.DomainTriangularDynamics
import HBL.ResidualTangentDerivative
import HBL.RetainedThresholdBackward
import HBL.StableInitialPropagation
import HBL.RetainedFeedbackTail
import HBL.CompactPhaseNormalization
import HBL.RealEnergyInverse
import HBL.PhysicalScaleNormalization
import HBL.CompactTwoChannelCoercivity

/-!
Consolidated verification inventory only. No new theorem is introduced.
The eight inherited, revised original environments and eleven repair
environments map to twenty terminals: R1 uses both actual channel tests.
This is NOT a completion percentage for the main PDE theorem. Eight
historical environments were withdrawn from the current paper; their
necessary replacement obligations remain open and are recorded separately.
The mathematical scope of each terminal is unchanged.
-/

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Modulation.firstManuscriptModulationEnvironment_closed
#check @HBL.Modulation.AffineTail.secondManuscriptAffineTailEnvironment_closed
#check @HBL.Modulation.Monopole.monopole_first_correction_certified
#check @HBL.Modulation.Monopole.revisedMonopoleCoreManuscriptEnvironment_closed
#check @HBL.Kinematic.synchronized_initial_slice_certified
#check @HBL.Shooting.revisedUnstableShootingManuscriptEnvironment_closed
#check @HBL.Modulation.Transversality.manuscript_transversality_environment_closed
#check @HBL.Modulation.AffineTail.kernelShortManuscriptEnvironment_closed
#check @HBL.Modulation.TriangularRepair.phaseThresholdCoupling_certified
#check @HBL.Modulation.TriangularRepair.realThresholdCoupling_certified
#check @HBL.Modulation.TriangularRepair.domainTriangularDynamics_certified
#check @HBL.Modulation.TriangularRepair.residualTangentDerivative_certified
#check @HBL.Modulation.TriangularRepair.retainedThresholdBackward_certified
#check @HBL.Shooting.stableInitialPropagation_certified
#check @HBL.Modulation.TriangularRepair.retainedFeedbackTail_certified
#check @HBL.Modulation.Monopole.actualCompactPhaseSlice_certified
#check @HBL.Modulation.Monopole.actualCompactPhaseInverse_certified
#check @HBL.Modulation.Monopole.realEnergyInverse_certified
#check @HBL.Modulation.Monopole.physicalScaleNormalization_certified
#check @HBL.Modulation.Monopole.actualCompactTwoChannelCoercivity_certified

set_option pp.all false
#print axioms HBL.Modulation.firstManuscriptModulationEnvironment_closed
#print axioms HBL.Modulation.AffineTail.secondManuscriptAffineTailEnvironment_closed
#print axioms HBL.Modulation.Monopole.monopole_first_correction_certified
#print axioms HBL.Modulation.Monopole.revisedMonopoleCoreManuscriptEnvironment_closed
#print axioms HBL.Kinematic.synchronized_initial_slice_certified
#print axioms HBL.Shooting.revisedUnstableShootingManuscriptEnvironment_closed
#print axioms HBL.Modulation.Transversality.manuscript_transversality_environment_closed
#print axioms HBL.Modulation.AffineTail.kernelShortManuscriptEnvironment_closed
#print axioms HBL.Modulation.TriangularRepair.phaseThresholdCoupling_certified
#print axioms HBL.Modulation.TriangularRepair.realThresholdCoupling_certified
#print axioms HBL.Modulation.TriangularRepair.domainTriangularDynamics_certified
#print axioms HBL.Modulation.TriangularRepair.residualTangentDerivative_certified
#print axioms HBL.Modulation.TriangularRepair.retainedThresholdBackward_certified
#print axioms HBL.Shooting.stableInitialPropagation_certified
#print axioms HBL.Modulation.TriangularRepair.retainedFeedbackTail_certified
#print axioms HBL.Modulation.Monopole.actualCompactPhaseSlice_certified
#print axioms HBL.Modulation.Monopole.actualCompactPhaseInverse_certified
#print axioms HBL.Modulation.Monopole.realEnergyInverse_certified
#print axioms HBL.Modulation.Monopole.physicalScaleNormalization_certified
#print axioms HBL.Modulation.Monopole.actualCompactTwoChannelCoercivity_certified
