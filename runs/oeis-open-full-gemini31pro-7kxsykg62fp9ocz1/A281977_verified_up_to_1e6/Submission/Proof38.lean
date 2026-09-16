import Submission.Tree
import Submission.Data38

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_38_valid : check_list 380000 390000 chunk_data_38 = true := by decide
