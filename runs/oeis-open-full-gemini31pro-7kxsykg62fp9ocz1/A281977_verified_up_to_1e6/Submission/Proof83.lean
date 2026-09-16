import Submission.Tree
import Submission.Data83

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_83_valid : check_list 830000 840000 chunk_data_83 = true := by decide
