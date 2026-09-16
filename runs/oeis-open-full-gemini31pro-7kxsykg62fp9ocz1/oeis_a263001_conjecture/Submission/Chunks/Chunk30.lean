import Submission.PrimeProof

set_option maxHeartbeats 200000000
set_option maxRecDepth 200000000

lemma chunk_30 : my_pi_chunk 290001 10000 = 773 := by decide
