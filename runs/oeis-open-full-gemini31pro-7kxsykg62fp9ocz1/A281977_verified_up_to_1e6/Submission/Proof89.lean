import Submission.Tree
import Submission.Data89

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_89_valid : check_list 890000 900000 chunk_data_89 = true := by decide
