import Submission.PrimeProof

set_option maxHeartbeats 200000000
set_option maxRecDepth 200000000

lemma chunk_15 : my_pi_chunk 140001 10000 = 838 := by decide
