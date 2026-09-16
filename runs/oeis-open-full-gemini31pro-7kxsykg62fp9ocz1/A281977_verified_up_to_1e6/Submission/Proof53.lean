import Submission.Tree
import Submission.Data53

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_53_valid : check_list 530000 540000 chunk_data_53 = true := by decide
