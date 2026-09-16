import Submission.Tree
import Submission.Data41

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_41_valid : check_list 410000 420000 chunk_data_41 = true := by decide
