import Submission.Tree
import Submission.Data78

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_78_valid : check_list 780000 790000 chunk_data_78 = true := by decide
