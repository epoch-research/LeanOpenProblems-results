import Submission.Tree
import Submission.Data76

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_76_valid : check_list 760000 770000 chunk_data_76 = true := by decide
