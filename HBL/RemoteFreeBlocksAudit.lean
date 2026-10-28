import HBL.RemoteFreeBlocks

set_option pp.all true
set_option pp.maxSteps 10000000
set_option maxRecDepth 1000000

#check @HBL.Profile.Remote.genericRemoteInverse_right
#check @HBL.Profile.Remote.existsUnique_logSolve

set_option pp.all false in
#print axioms HBL.Profile.Remote.genericRemoteInverse_right
set_option pp.all false in
#print axioms HBL.Profile.Remote.existsUnique_logSolve
