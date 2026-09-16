import Submission.PrimeProof

set_option maxHeartbeats 200000000
set_option maxRecDepth 200000000

lemma chunk_40 : my_pi_chunk 390001 10000 = 793 := by decide
