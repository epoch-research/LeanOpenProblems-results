import Submission.PrimeProof

set_option maxHeartbeats 200000000
set_option maxRecDepth 200000000

lemma chunk_31 : my_pi_chunk 300001 10000 = 803 := by decide
