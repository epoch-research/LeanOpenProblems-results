import Submission.PrimeProof

set_option maxHeartbeats 200000000
set_option maxRecDepth 200000000

lemma chunk_25 : my_pi_chunk 240001 10000 = 823 := by decide
