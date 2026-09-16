import Submission.Tree
import Submission.Data72

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_72_valid : check_list 720000 730000 chunk_data_72 = true := by decide
