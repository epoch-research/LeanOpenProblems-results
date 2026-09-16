import Submission.Tree
import Submission.Data60

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_60_valid : check_list 600000 610000 chunk_data_60 = true := by decide
