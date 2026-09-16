import Submission.PrimeProof

set_option maxHeartbeats 200000000
set_option maxRecDepth 200000000

lemma chunk_60 : my_pi_chunk 590001 10000 = 747 := by decide
