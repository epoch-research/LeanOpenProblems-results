import Submission.Tree
import Submission.Data73

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_73_valid : check_list 730000 740000 chunk_data_73 = true := by decide
