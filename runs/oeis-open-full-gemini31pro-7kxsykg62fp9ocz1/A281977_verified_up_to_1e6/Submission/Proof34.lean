import Submission.Tree
import Submission.Data34

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_34_valid : check_list 340000 350000 chunk_data_34 = true := by decide
