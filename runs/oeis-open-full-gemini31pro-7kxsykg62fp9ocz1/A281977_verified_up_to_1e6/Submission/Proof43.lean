import Submission.Tree
import Submission.Data43

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_43_valid : check_list 430000 440000 chunk_data_43 = true := by decide
