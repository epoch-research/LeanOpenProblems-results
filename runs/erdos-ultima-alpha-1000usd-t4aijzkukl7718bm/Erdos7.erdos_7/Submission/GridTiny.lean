import Submission.GridCertificateCore
open Erdos7GridCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 100000000
example : ceilDiv (12345678901234567890123456789) (987654321)=12499999887343749991 := by decide +kernel
example : grid[246]!=1560772 := by decide +kernel
example : (cells[2]!)[246]!=⟨238,79004,47076,63040⟩ := by decide +kernel
