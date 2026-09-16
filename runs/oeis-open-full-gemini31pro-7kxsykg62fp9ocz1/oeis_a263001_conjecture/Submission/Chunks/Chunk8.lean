import Submission.PrimeProof

set_option maxHeartbeats 200000000
set_option maxRecDepth 200000000

lemma chunk_8 : my_pi_chunk 70001 10000 = 902 := by decide
