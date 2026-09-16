import Submission.PrimeProof

set_option maxHeartbeats 200000000
set_option maxRecDepth 200000000

lemma chunk_5 : my_pi_chunk 40001 10000 = 930 := by decide
