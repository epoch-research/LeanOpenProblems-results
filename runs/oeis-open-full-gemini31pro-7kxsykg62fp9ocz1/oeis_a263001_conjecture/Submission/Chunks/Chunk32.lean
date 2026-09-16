import Submission.PrimeProof

set_option maxHeartbeats 200000000
set_option maxRecDepth 200000000

lemma chunk_32 : my_pi_chunk 310001 10000 = 808 := by decide
