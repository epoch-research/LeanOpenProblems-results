import Submission.Tree
import Submission.Data27

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_27_valid : check_list 270000 280000 chunk_data_27 = true := by decide
