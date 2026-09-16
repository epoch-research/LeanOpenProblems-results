import Submission.Tree
import Submission.Data63

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_63_valid : check_list 630000 640000 chunk_data_63 = true := by decide
