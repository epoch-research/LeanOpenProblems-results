import Submission.Tree
import Submission.Data82

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_82_valid : check_list 820000 830000 chunk_data_82 = true := by decide
