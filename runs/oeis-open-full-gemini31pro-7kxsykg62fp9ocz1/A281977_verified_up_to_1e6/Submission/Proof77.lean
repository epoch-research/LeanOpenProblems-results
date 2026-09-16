import Submission.Tree
import Submission.Data77

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_77_valid : check_list 770000 780000 chunk_data_77 = true := by decide
