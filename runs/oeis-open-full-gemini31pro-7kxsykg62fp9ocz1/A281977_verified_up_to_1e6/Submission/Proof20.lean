import Submission.Tree
import Submission.Data20

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_20_valid : check_list 200000 210000 chunk_data_20 = true := by decide
