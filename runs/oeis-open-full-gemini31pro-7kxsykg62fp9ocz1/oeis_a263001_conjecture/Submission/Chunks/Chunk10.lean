import Submission.PrimeProof

set_option maxHeartbeats 200000000
set_option maxRecDepth 200000000

lemma chunk_10 : my_pi_chunk 90001 10000 = 879 := by decide
