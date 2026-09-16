import Submission.Tree
import Submission.Data46

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_46_valid : check_list 460000 470000 chunk_data_46 = true := by decide
