import Submission.Tree
import Submission.Data93

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_93_valid : check_list 930000 940000 chunk_data_93 = true := by decide
