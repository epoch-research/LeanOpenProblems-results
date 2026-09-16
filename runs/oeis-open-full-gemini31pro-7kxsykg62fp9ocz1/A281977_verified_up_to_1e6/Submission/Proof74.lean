import Submission.Tree
import Submission.Data74

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_74_valid : check_list 740000 750000 chunk_data_74 = true := by decide
