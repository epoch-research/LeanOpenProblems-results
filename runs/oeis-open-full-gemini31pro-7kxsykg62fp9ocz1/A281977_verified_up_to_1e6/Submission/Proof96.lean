import Submission.Tree
import Submission.Data96

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_96_valid : check_list 960000 970000 chunk_data_96 = true := by decide
