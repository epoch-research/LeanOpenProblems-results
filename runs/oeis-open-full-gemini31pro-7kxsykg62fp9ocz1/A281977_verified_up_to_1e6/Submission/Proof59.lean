import Submission.Tree
import Submission.Data59

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_59_valid : check_list 590000 600000 chunk_data_59 = true := by decide
