import Submission.Tree
import Submission.Data68

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_68_valid : check_list 680000 690000 chunk_data_68 = true := by decide
