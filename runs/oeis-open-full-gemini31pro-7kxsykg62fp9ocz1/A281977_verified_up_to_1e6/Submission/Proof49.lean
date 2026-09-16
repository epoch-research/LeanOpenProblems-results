import Submission.Tree
import Submission.Data49

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_49_valid : check_list 490000 500000 chunk_data_49 = true := by decide
