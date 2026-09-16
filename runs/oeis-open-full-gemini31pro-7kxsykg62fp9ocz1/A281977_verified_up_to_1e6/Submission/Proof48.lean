import Submission.Tree
import Submission.Data48

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_48_valid : check_list 480000 490000 chunk_data_48 = true := by decide
