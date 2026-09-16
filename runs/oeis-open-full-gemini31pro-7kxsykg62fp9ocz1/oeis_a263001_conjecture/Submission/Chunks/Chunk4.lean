import Submission.PrimeProof

set_option maxHeartbeats 200000000
set_option maxRecDepth 200000000

lemma chunk_4 : my_pi_chunk 30001 10000 = 958 := by decide
