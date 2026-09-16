import Submission.Tree
import Submission.Data97

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_97_valid : check_list 970000 980000 chunk_data_97 = true := by decide
