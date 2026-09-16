import Submission.Tree
import Submission.Data98

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_98_valid : check_list 980000 990000 chunk_data_98 = true := by decide
