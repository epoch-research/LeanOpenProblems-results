import Submission.PrimeProof

set_option maxHeartbeats 200000000
set_option maxRecDepth 200000000

lemma chunk_20 : my_pi_chunk 190001 10000 = 814 := by decide
