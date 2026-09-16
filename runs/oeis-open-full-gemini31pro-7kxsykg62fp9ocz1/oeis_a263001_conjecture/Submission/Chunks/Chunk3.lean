import Submission.PrimeProof

set_option maxHeartbeats 200000000
set_option maxRecDepth 200000000

lemma chunk_3 : my_pi_chunk 20001 10000 = 983 := by decide
