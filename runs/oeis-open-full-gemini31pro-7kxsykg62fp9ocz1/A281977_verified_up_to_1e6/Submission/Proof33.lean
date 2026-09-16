import Submission.Tree
import Submission.Data33

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_33_valid : check_list 330000 340000 chunk_data_33 = true := by decide
