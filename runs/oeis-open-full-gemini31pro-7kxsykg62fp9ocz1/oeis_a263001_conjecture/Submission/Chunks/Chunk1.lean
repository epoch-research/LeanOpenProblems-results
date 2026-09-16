import Submission.PrimeProof

set_option maxHeartbeats 200000000
set_option maxRecDepth 200000000

lemma chunk_1 : my_pi_chunk 1 10000 = 1229 := by decide
