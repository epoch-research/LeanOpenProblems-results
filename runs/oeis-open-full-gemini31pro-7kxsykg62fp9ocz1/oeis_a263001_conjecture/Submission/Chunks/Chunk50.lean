import Submission.PrimeProof

set_option maxHeartbeats 200000000
set_option maxRecDepth 200000000

lemma chunk_50 : my_pi_chunk 490001 10000 = 772 := by decide
