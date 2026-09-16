import Submission.Tree
import Submission.Data19

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_19_valid : check_list 190000 200000 chunk_data_19 = true := by decide
