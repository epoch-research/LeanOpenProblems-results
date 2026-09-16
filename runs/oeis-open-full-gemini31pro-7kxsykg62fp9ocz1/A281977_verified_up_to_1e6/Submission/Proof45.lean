import Submission.Tree
import Submission.Data45

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_45_valid : check_list 450000 460000 chunk_data_45 = true := by decide
