import Submission.Tree
import Submission.Data55

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_55_valid : check_list 550000 560000 chunk_data_55 = true := by decide
