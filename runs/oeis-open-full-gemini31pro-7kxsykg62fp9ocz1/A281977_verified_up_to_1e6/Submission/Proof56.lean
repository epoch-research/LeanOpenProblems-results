import Submission.Tree
import Submission.Data56

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_56_valid : check_list 560000 570000 chunk_data_56 = true := by decide
