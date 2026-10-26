import HBL.DomainTriangularDynamics
import HBL.ResidualTangentDerivative

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Modulation.TriangularRepair.domainTriangularDynamics_certified
#check @HBL.Modulation.TriangularRepair.residualTangentDerivative_certified

set_option pp.all false in
#print axioms HBL.Modulation.TriangularRepair.domainTriangularDynamics_certified
set_option pp.all false in
#print axioms HBL.Modulation.TriangularRepair.residualTangentDerivative_certified
