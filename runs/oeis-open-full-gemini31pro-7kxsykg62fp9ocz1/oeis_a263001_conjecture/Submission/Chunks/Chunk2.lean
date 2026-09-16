import Submission.PrimeProof

set_option maxHeartbeats 200000000
set_option maxRecDepth 200000000

lemma chunk_2 : my_pi_chunk 10001 10000 = 1033 := by decide
