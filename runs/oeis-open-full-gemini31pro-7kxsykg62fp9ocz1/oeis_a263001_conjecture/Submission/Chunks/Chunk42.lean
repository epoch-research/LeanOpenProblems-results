import Submission.PrimeProof

set_option maxHeartbeats 200000000
set_option maxRecDepth 200000000

lemma chunk_42 : my_pi_chunk 410001 10000 = 776 := by decide
