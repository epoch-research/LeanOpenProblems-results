import Submission.Tree
import Submission.Data91

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_91_valid : check_list 910000 920000 chunk_data_91 = true := by decide
