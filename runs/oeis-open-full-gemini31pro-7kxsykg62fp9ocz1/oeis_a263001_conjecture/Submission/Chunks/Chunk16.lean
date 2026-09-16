import Submission.PrimeProof

set_option maxHeartbeats 200000000
set_option maxRecDepth 200000000

lemma chunk_16 : my_pi_chunk 150001 10000 = 835 := by decide
