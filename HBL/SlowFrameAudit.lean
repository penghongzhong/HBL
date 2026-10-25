import HBL.SlowFrameConnection

set_option pp.all true

#check @HBL.SlowFrame.frame_norm_and_inverse_le
#check @HBL.SlowFrame.frame_inverse_difference_le
#check @HBL.SlowFrame.connectionValue_norm_le
#check @HBL.SlowFrame.connectionValue_difference_le
#check @HBL.SlowFrame.movingConnection_positive_margin

set_option pp.all false

#print axioms HBL.SlowFrame.frame_norm_and_inverse_le
#print axioms HBL.SlowFrame.frame_inverse_difference_le
#print axioms HBL.SlowFrame.connectionValue_norm_le
#print axioms HBL.SlowFrame.connectionValue_difference_le
#print axioms HBL.SlowFrame.movingConnection_positive_margin
