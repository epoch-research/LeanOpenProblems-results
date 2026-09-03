import Submission.SemilinearBothDataBase

/-! Completion of the explicit kernel-checked doubly elliptic semilinear certificate.
This auxiliary counterexample is not a disproof of Erdős 714. -/

open Matrix SimpleGraph Erdos714BothModel
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
namespace Erdos714BothData
variable {K : Type*} [Field K] [CharP K 2]
variable (z : K) (hz : z^9+z^4+1 = 0)
include hz

lemma sqr_492 : (gf512% z 492)^2 = (gf512% z 15) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_15 : (gf512% z 15)^2 = (gf512% z 85) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_85 : (gf512% z 85)^2 = (gf512% z 409) := by
  apply cert_eq z hz (Q := (gf512% z 8))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_409 : (gf512% z 409)^2 = (gf512% z 436) := by
  apply cert_eq z hz (Q := (gf512% z 165))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_436 : (gf512% z 436)^2 = (gf512% z 455) := by
  apply cert_eq z hz (Q := (gf512% z 167))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_492 : (gf512% z 492)^32 = (gf512% z 455) := by
  rw [pow32_squares]
  rw [sqr_492 z hz, sqr_15 z hz, sqr_85 z hz, sqr_409 z hz, sqr_436 z hz]

lemma sigma_64 : sigmaM (mat512% z 492 230 478 0) = (mat512% z 455 345 272 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_492 z hz
  · exact power32_230 z hz
  · exact power32_478 z hz
  · exact power32_0 z hz

lemma product_72 : (mat512% z 492 230 478 0) * (mat512% z 455 345 272 0) = (mat512% z 36 473 382 37) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 492)*(gf512% z 455) + (gf512% z 230)*(gf512% z 272) = (gf512% z 36)
    apply cert_eq z hz (Q := (gf512% z 192))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 492)*(gf512% z 345) + (gf512% z 230)*(gf512% z 0) = (gf512% z 473)
    apply cert_eq z hz (Q := (gf512% z 197))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 478)*(gf512% z 455) + (gf512% z 0)*(gf512% z 272) = (gf512% z 382)
    apply cert_eq z hz (Q := (gf512% z 164))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 478)*(gf512% z 345) + (gf512% z 0)*(gf512% z 0) = (gf512% z 37)
    apply cert_eq z hz (Q := (gf512% z 219))
    ring_nf <;> reduce_mod_char! <;> ring

lemma mtrace_16 : (mat512% z 36 473 382 37).trace = (gf512% z 1) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 36)+(gf512% z 37) = (gf512% z 1)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_455 : (gf512% z 455)^2 = (gf512% z 104) := by
  apply cert_eq z hz (Q := (gf512% z 173))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_104 : (gf512% z 104)^2 = (gf512% z 234) := by
  apply cert_eq z hz (Q := (gf512% z 10))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_234 : (gf512% z 234)^2 = (gf512% z 223) := by
  apply cert_eq z hz (Q := (gf512% z 43))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_223 : (gf512% z 223)^2 = (gf512% z 492) := by
  apply cert_eq z hz (Q := (gf512% z 41))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_455 : (gf512% z 455)^32 = (gf512% z 15) := by
  rw [pow32_squares]
  rw [sqr_455 z hz, sqr_104 z hz, sqr_234 z hz, sqr_223 z hz, sqr_492 z hz]

lemma sigma_65 : sigmaM (mat512% z 455 345 272 0) = (mat512% z 15 143 297 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_455 z hz
  · exact power32_345 z hz
  · exact power32_272 z hz
  · exact power32_0 z hz

lemma power32_15 : (gf512% z 15)^32 = (gf512% z 104) := by
  rw [pow32_squares]
  rw [sqr_15 z hz, sqr_85 z hz, sqr_409 z hz, sqr_436 z hz, sqr_455 z hz]

lemma power32_297 : (gf512% z 297)^32 = (gf512% z 452) := by
  rw [pow32_squares]
  rw [sqr_297 z hz, sqr_167 z hz, sqr_6 z hz, sqr_20 z hz, sqr_272 z hz]

lemma sigma_66 : sigmaM (mat512% z 15 143 297 0) = (mat512% z 104 269 452 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_15 z hz
  · exact power32_143 z hz
  · exact power32_297 z hz
  · exact power32_0 z hz

lemma power32_104 : (gf512% z 104)^32 = (gf512% z 85) := by
  rw [pow32_squares]
  rw [sqr_104 z hz, sqr_234 z hz, sqr_223 z hz, sqr_492 z hz, sqr_15 z hz]

lemma power32_269 : (gf512% z 269)^32 = (gf512% z 100) := by
  rw [pow32_squares]
  rw [sqr_269 z hz, sqr_149 z hz, sqr_288 z hz, sqr_230 z hz, sqr_143 z hz]

lemma sigma_67 : sigmaM (mat512% z 104 269 452 0) = (mat512% z 85 100 167 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_104 z hz
  · exact power32_269 z hz
  · exact power32_452 z hz
  · exact power32_0 z hz

lemma power32_85 : (gf512% z 85)^32 = (gf512% z 234) := by
  rw [pow32_squares]
  rw [sqr_85 z hz, sqr_409 z hz, sqr_436 z hz, sqr_455 z hz, sqr_104 z hz]

lemma sigma_68 : sigmaM (mat512% z 85 100 167 0) = (mat512% z 234 149 109 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_85 z hz
  · exact power32_100 z hz
  · exact power32_167 z hz
  · exact power32_0 z hz

lemma power32_234 : (gf512% z 234)^32 = (gf512% z 409) := by
  rw [pow32_squares]
  rw [sqr_234 z hz, sqr_223 z hz, sqr_492 z hz, sqr_15 z hz, sqr_85 z hz]

lemma sigma_69 : sigmaM (mat512% z 234 149 109 0) = (mat512% z 409 186 6 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_234 z hz
  · exact power32_149 z hz
  · exact power32_109 z hz
  · exact power32_0 z hz

lemma power32_409 : (gf512% z 409)^32 = (gf512% z 223) := by
  rw [pow32_squares]
  rw [sqr_409 z hz, sqr_436 z hz, sqr_455 z hz, sqr_104 z hz, sqr_234 z hz]

lemma sigma_70 : sigmaM (mat512% z 409 186 6 0) = (mat512% z 223 288 251 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_409 z hz
  · exact power32_186 z hz
  · exact power32_6 z hz
  · exact power32_0 z hz

lemma power32_223 : (gf512% z 223)^32 = (gf512% z 436) := by
  rw [pow32_squares]
  rw [sqr_223 z hz, sqr_492 z hz, sqr_15 z hz, sqr_85 z hz, sqr_409 z hz]

lemma sigma_71 : sigmaM (mat512% z 223 288 251 0) = (mat512% z 436 343 20 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_223 z hz
  · exact power32_288 z hz
  · exact power32_251 z hz
  · exact power32_0 z hz

lemma product_73 : (mat512% z 492 230 478 0) * (mat512% z 0 323 360 249) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 492)*(gf512% z 0) + (gf512% z 230)*(gf512% z 360) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 97))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 492)*(gf512% z 323) + (gf512% z 230)*(gf512% z 249) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 226))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 478)*(gf512% z 0) + (gf512% z 0)*(gf512% z 360) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 478)*(gf512% z 323) + (gf512% z 0)*(gf512% z 249) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 211))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_74 : (mat512% z 455 345 272 0) * (mat512% z 249 332 106 165) = (mat512% z 0 323 360 249) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 455)*(gf512% z 249) + (gf512% z 345)*(gf512% z 106) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 101))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 455)*(gf512% z 332) + (gf512% z 345)*(gf512% z 165) = (gf512% z 323)
    apply cert_eq z hz (Q := (gf512% z 154))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 272)*(gf512% z 249) + (gf512% z 0)*(gf512% z 106) = (gf512% z 360)
    apply cert_eq z hz (Q := (gf512% z 120))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 272)*(gf512% z 332) + (gf512% z 0)*(gf512% z 165) = (gf512% z 249)
    apply cert_eq z hz (Q := (gf512% z 169))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_75 : (mat512% z 15 143 297 0) * (mat512% z 374 443 182 339) = (mat512% z 249 332 106 165) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 15)*(gf512% z 374) + (gf512% z 143)*(gf512% z 182) = (gf512% z 249)
    apply cert_eq z hz (Q := (gf512% z 41))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 15)*(gf512% z 443) + (gf512% z 143)*(gf512% z 339) = (gf512% z 332)
    apply cert_eq z hz (Q := (gf512% z 84))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 297)*(gf512% z 374) + (gf512% z 0)*(gf512% z 182) = (gf512% z 106)
    apply cert_eq z hz (Q := (gf512% z 172))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 297)*(gf512% z 443) + (gf512% z 0)*(gf512% z 339) = (gf512% z 165)
    apply cert_eq z hz (Q := (gf512% z 198))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_76 : (mat512% z 104 269 452 0) * (mat512% z 507 294 23 217) = (mat512% z 374 443 182 339) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 104)*(gf512% z 507) + (gf512% z 269)*(gf512% z 23) = (gf512% z 374)
    apply cert_eq z hz (Q := (gf512% z 45))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 104)*(gf512% z 294) + (gf512% z 269)*(gf512% z 217) = (gf512% z 443)
    apply cert_eq z hz (Q := (gf512% z 94))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 452)*(gf512% z 507) + (gf512% z 0)*(gf512% z 23) = (gf512% z 182)
    apply cert_eq z hz (Q := (gf512% z 186))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 452)*(gf512% z 294) + (gf512% z 0)*(gf512% z 217) = (gf512% z 339)
    apply cert_eq z hz (Q := (gf512% z 251))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_77 : (mat512% z 85 100 167 0) * (mat512% z 152 14 115 431) = (mat512% z 507 294 23 217) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 85)*(gf512% z 152) + (gf512% z 100)*(gf512% z 115) = (gf512% z 507)
    apply cert_eq z hz (Q := (gf512% z 31))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 85)*(gf512% z 14) + (gf512% z 100)*(gf512% z 431) = (gf512% z 294)
    apply cert_eq z hz (Q := (gf512% z 44))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 167)*(gf512% z 152) + (gf512% z 0)*(gf512% z 115) = (gf512% z 23)
    apply cert_eq z hz (Q := (gf512% z 47))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 167)*(gf512% z 14) + (gf512% z 0)*(gf512% z 431) = (gf512% z 217)
    apply cert_eq z hz (Q := (gf512% z 3))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_78 : (mat512% z 234 149 109 0) * (mat512% z 231 316 259 462) = (mat512% z 152 14 115 431) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 234)*(gf512% z 231) + (gf512% z 149)*(gf512% z 259) = (gf512% z 152)
    apply cert_eq z hz (Q := (gf512% z 97))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 234)*(gf512% z 316) + (gf512% z 149)*(gf512% z 462) = (gf512% z 14)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 109)*(gf512% z 231) + (gf512% z 0)*(gf512% z 259) = (gf512% z 115)
    apply cert_eq z hz (Q := (gf512% z 16))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 109)*(gf512% z 316) + (gf512% z 0)*(gf512% z 462) = (gf512% z 431)
    apply cert_eq z hz (Q := (gf512% z 51))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_79 : (mat512% z 409 186 6 0) * (mat512% z 135 93 372 134) = (mat512% z 231 316 259 462) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 409)*(gf512% z 135) + (gf512% z 186)*(gf512% z 372) = (gf512% z 231)
    apply cert_eq z hz (Q := (gf512% z 32))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 409)*(gf512% z 93) + (gf512% z 186)*(gf512% z 134) = (gf512% z 316)
    apply cert_eq z hz (Q := (gf512% z 21))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 6)*(gf512% z 135) + (gf512% z 0)*(gf512% z 372) = (gf512% z 259)
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 6)*(gf512% z 93) + (gf512% z 0)*(gf512% z 134) = (gf512% z 462)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_80 : (mat512% z 223 288 251 0) * (mat512% z 436 343 20 0) = (mat512% z 135 93 372 134) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 223)*(gf512% z 436) + (gf512% z 288)*(gf512% z 20) = (gf512% z 135)
    apply cert_eq z hz (Q := (gf512% z 91))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 223)*(gf512% z 343) + (gf512% z 288)*(gf512% z 0) = (gf512% z 93)
    apply cert_eq z hz (Q := (gf512% z 112))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 251)*(gf512% z 436) + (gf512% z 0)*(gf512% z 20) = (gf512% z 372)
    apply cert_eq z hz (Q := (gf512% z 72))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 251)*(gf512% z 343) + (gf512% z 0)*(gf512% z 0) = (gf512% z 134)
    apply cert_eq z hz (Q := (gf512% z 103))
    ring_nf <;> reduce_mod_char! <;> ring

lemma norm_8 : semilinearNorm 9 (mat512% z 492 230 478 0) = 1 := by
  have h8 : semilinearNorm 1 (mat512% z 436 343 20 0) = (mat512% z 436 343 20 0) := by simp [semilinearNorm]
  have h7 : semilinearNorm 2 (mat512% z 223 288 251 0) = (mat512% z 135 93 372 134) := by
    change (mat512% z 223 288 251 0) * semilinearNorm 1 (sigmaM (mat512% z 223 288 251 0)) = _
    rw [sigma_71 z hz, h8]
    exact product_80 z hz
  have h6 : semilinearNorm 3 (mat512% z 409 186 6 0) = (mat512% z 231 316 259 462) := by
    change (mat512% z 409 186 6 0) * semilinearNorm 2 (sigmaM (mat512% z 409 186 6 0)) = _
    rw [sigma_70 z hz, h7]
    exact product_79 z hz
  have h5 : semilinearNorm 4 (mat512% z 234 149 109 0) = (mat512% z 152 14 115 431) := by
    change (mat512% z 234 149 109 0) * semilinearNorm 3 (sigmaM (mat512% z 234 149 109 0)) = _
    rw [sigma_69 z hz, h6]
    exact product_78 z hz
  have h4 : semilinearNorm 5 (mat512% z 85 100 167 0) = (mat512% z 507 294 23 217) := by
    change (mat512% z 85 100 167 0) * semilinearNorm 4 (sigmaM (mat512% z 85 100 167 0)) = _
    rw [sigma_68 z hz, h5]
    exact product_77 z hz
  have h3 : semilinearNorm 6 (mat512% z 104 269 452 0) = (mat512% z 374 443 182 339) := by
    change (mat512% z 104 269 452 0) * semilinearNorm 5 (sigmaM (mat512% z 104 269 452 0)) = _
    rw [sigma_67 z hz, h4]
    exact product_76 z hz
  have h2 : semilinearNorm 7 (mat512% z 15 143 297 0) = (mat512% z 249 332 106 165) := by
    change (mat512% z 15 143 297 0) * semilinearNorm 6 (sigmaM (mat512% z 15 143 297 0)) = _
    rw [sigma_66 z hz, h3]
    exact product_75 z hz
  have h1 : semilinearNorm 8 (mat512% z 455 345 272 0) = (mat512% z 0 323 360 249) := by
    change (mat512% z 455 345 272 0) * semilinearNorm 7 (sigmaM (mat512% z 455 345 272 0)) = _
    rw [sigma_65 z hz, h2]
    exact product_74 z hz
  have h0 : semilinearNorm 9 (mat512% z 492 230 478 0) = (mat512% z 1 0 0 1) := by
    change (mat512% z 492 230 478 0) * semilinearNorm 8 (sigmaM (mat512% z 492 230 478 0)) = _
    rw [sigma_64 z hz, h1]
    exact product_73 z hz
  simpa only [code_identity] using h0

lemma mtrace_17 : (mat512% z 492 230 478 0).trace = (gf512% z 492) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 492)+(gf512% z 0) = (gf512% z 492)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma mdet_16 : (mat512% z 492 230 478 0).det = (gf512% z 197) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 492)*(gf512% z 0) - (gf512% z 230)*(gf512% z 478) = (gf512% z 197)
  apply cert_eq z hz (Q := (gf512% z 81))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_493 : (gf512% z 493)^2 = (gf512% z 14) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_180 : (gf512% z 180)^2 = (gf512% z 259) := by
  apply cert_eq z hz (Q := (gf512% z 35))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_300 : (gf512% z 300)^2 = (gf512% z 182) := by
  apply cert_eq z hz (Q := (gf512% z 134))
  ring_nf <;> reduce_mod_char! <;> ring

lemma atr_8 : trace2 9 (gf512% z 186) = 1 := by
  have h0 : trace2 0 (gf512% z 186) = (gf512% z 0) := by simp [trace2]
  have h1 : trace2 1 (gf512% z 186) = (gf512% z 186) := by
    change (trace2 0 (gf512% z 186))^2 + (gf512% z 186) = _
    rw [h0, sqr_0 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h2 : trace2 2 (gf512% z 186) = (gf512% z 493) := by
    change (trace2 1 (gf512% z 186))^2 + (gf512% z 186) = _
    rw [h1, sqr_186 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h3 : trace2 3 (gf512% z 186) = (gf512% z 180) := by
    change (trace2 2 (gf512% z 186))^2 + (gf512% z 186) = _
    rw [h2, sqr_493 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h4 : trace2 4 (gf512% z 186) = (gf512% z 441) := by
    change (trace2 3 (gf512% z 186))^2 + (gf512% z 186) = _
    rw [h3, sqr_180 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h5 : trace2 5 (gf512% z 186) = (gf512% z 300) := by
    change (trace2 4 (gf512% z 186))^2 + (gf512% z 186) = _
    rw [h4, sqr_441 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h6 : trace2 6 (gf512% z 186) = (gf512% z 12) := by
    change (trace2 5 (gf512% z 186))^2 + (gf512% z 186) = _
    rw [h5, sqr_300 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h7 : trace2 7 (gf512% z 186) = (gf512% z 234) := by
    change (trace2 6 (gf512% z 186))^2 + (gf512% z 186) = _
    rw [h6, sqr_12 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h8 : trace2 8 (gf512% z 186) = (gf512% z 101) := by
    change (trace2 7 (gf512% z 186))^2 + (gf512% z 186) = _
    rw [h7, sqr_234 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h9 : trace2 9 (gf512% z 186) = (gf512% z 1) := by
    change (trace2 8 (gf512% z 186))^2 + (gf512% z 186) = _
    rw [h8, sqr_101 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  simpa using h9

lemma elliptic_16 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 492 230 478 0) := by
  have ht : (gf512% z 492)*(gf512% z 382) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 217))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 197)*(gf512% z 382)^2 = (gf512% z 186) := by
    apply cert_eq z hz (Q := (gf512% z 26206))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_17 z hz, mdet_16 z hz]
  apply no_quadratic_root hK (gf512% z 492) (gf512% z 197) (gf512% z 382) ht
  rw [hd]
  exact atr_8 z hz

lemma mdet_17 : (mat512% z 36 473 382 37).det = (gf512% z 335) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 36)*(gf512% z 37) - (gf512% z 473)*(gf512% z 382) = (gf512% z 335)
  apply cert_eq z hz (Q := (gf512% z 197))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_335 : (gf512% z 335)^2 = (gf512% z 25) := by
  apply cert_eq z hz (Q := (gf512% z 140))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_23 : (gf512% z 23)^2 = (gf512% z 277) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_90 : (gf512% z 90)^2 = (gf512% z 460) := by
  apply cert_eq z hz (Q := (gf512% z 8))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_131 : (gf512% z 131)^2 = (gf512% z 52) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_379 : (gf512% z 379)^2 = (gf512% z 299) := by
  apply cert_eq z hz (Q := (gf512% z 142))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_501 : (gf512% z 501)^2 = (gf512% z 334) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma atr_9 : trace2 9 (gf512% z 335) = 1 := by
  have h0 : trace2 0 (gf512% z 335) = (gf512% z 0) := by simp [trace2]
  have h1 : trace2 1 (gf512% z 335) = (gf512% z 335) := by
    change (trace2 0 (gf512% z 335))^2 + (gf512% z 335) = _
    rw [h0, sqr_0 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h2 : trace2 2 (gf512% z 335) = (gf512% z 342) := by
    change (trace2 1 (gf512% z 335))^2 + (gf512% z 335) = _
    rw [h1, sqr_335 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h3 : trace2 3 (gf512% z 335) = (gf512% z 23) := by
    change (trace2 2 (gf512% z 335))^2 + (gf512% z 335) = _
    rw [h2, sqr_342 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h4 : trace2 4 (gf512% z 335) = (gf512% z 90) := by
    change (trace2 3 (gf512% z 335))^2 + (gf512% z 335) = _
    rw [h3, sqr_23 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h5 : trace2 5 (gf512% z 335) = (gf512% z 131) := by
    change (trace2 4 (gf512% z 335))^2 + (gf512% z 335) = _
    rw [h4, sqr_90 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h6 : trace2 6 (gf512% z 335) = (gf512% z 379) := by
    change (trace2 5 (gf512% z 335))^2 + (gf512% z 335) = _
    rw [h5, sqr_131 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h7 : trace2 7 (gf512% z 335) = (gf512% z 100) := by
    change (trace2 6 (gf512% z 335))^2 + (gf512% z 335) = _
    rw [h6, sqr_379 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h8 : trace2 8 (gf512% z 335) = (gf512% z 501) := by
    change (trace2 7 (gf512% z 335))^2 + (gf512% z 335) = _
    rw [h7, sqr_100 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h9 : trace2 9 (gf512% z 335) = (gf512% z 1) := by
    change (trace2 8 (gf512% z 335))^2 + (gf512% z 335) = _
    rw [h8, sqr_501 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  simpa using h9

lemma elliptic_17 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 36 473 382 37) := by
  have ht : (gf512% z 1)*(gf512% z 1) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 335)*(gf512% z 1)^2 = (gf512% z 335) := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_16 z hz, mdet_17 z hz]
  apply no_quadratic_root hK (gf512% z 1) (gf512% z 335) (gf512% z 1) ht
  rw [hd]
  exact atr_9 z hz

lemma good_8 (hK : ∀ x : K, x^512 = x) : Good (mat512% z 492 230 478 0) := by
  unfold Good
  rw [sigma_64 z hz, product_72 z hz]
  refine ⟨?_, elliptic_16 z hz hK, norm_8 z hz, elliptic_17 z hz hK⟩
  simpa using mtrace_16 z hz

#check good_8

lemma sigma_72 : sigmaM (mat512% z 492 312 478 0) = (mat512% z 455 73 272 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_492 z hz
  · exact power32_312 z hz
  · exact power32_478 z hz
  · exact power32_0 z hz

lemma product_81 : (mat512% z 492 312 478 0) * (mat512% z 455 73 272 0) = (mat512% z 322 7 382 323) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 492)*(gf512% z 455) + (gf512% z 312)*(gf512% z 272) = (gf512% z 322)
    apply cert_eq z hz (Q := (gf512% z 38))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 492)*(gf512% z 73) + (gf512% z 312)*(gf512% z 0) = (gf512% z 7)
    apply cert_eq z hz (Q := (gf512% z 59))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 478)*(gf512% z 455) + (gf512% z 0)*(gf512% z 272) = (gf512% z 382)
    apply cert_eq z hz (Q := (gf512% z 164))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 478)*(gf512% z 73) + (gf512% z 0)*(gf512% z 0) = (gf512% z 323)
    apply cert_eq z hz (Q := (gf512% z 61))
    ring_nf <;> reduce_mod_char! <;> ring

lemma mtrace_18 : (mat512% z 322 7 382 323).trace = (gf512% z 1) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 322)+(gf512% z 323) = (gf512% z 1)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sigma_73 : sigmaM (mat512% z 455 73 272 0) = (mat512% z 15 422 297 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_455 z hz
  · exact power32_73 z hz
  · exact power32_272 z hz
  · exact power32_0 z hz

lemma sigma_74 : sigmaM (mat512% z 15 422 297 0) = (mat512% z 104 201 452 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_15 z hz
  · exact power32_422 z hz
  · exact power32_297 z hz
  · exact power32_0 z hz

lemma sigma_75 : sigmaM (mat512% z 104 201 452 0) = (mat512% z 85 195 167 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_104 z hz
  · exact power32_201 z hz
  · exact power32_452 z hz
  · exact power32_0 z hz

lemma power32_195 : (gf512% z 195)^32 = (gf512% z 248) := by
  rw [pow32_squares]
  rw [sqr_195 z hz, sqr_188 z hz, sqr_323 z hz, sqr_73 z hz, sqr_201 z hz]

lemma sigma_76 : sigmaM (mat512% z 85 195 167 0) = (mat512% z 234 248 109 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_85 z hz
  · exact power32_195 z hz
  · exact power32_167 z hz
  · exact power32_0 z hz

lemma sigma_77 : sigmaM (mat512% z 234 248 109 0) = (mat512% z 409 188 6 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_234 z hz
  · exact power32_248 z hz
  · exact power32_109 z hz
  · exact power32_0 z hz

lemma sigma_78 : sigmaM (mat512% z 409 188 6 0) = (mat512% z 223 475 251 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_409 z hz
  · exact power32_188 z hz
  · exact power32_6 z hz
  · exact power32_0 z hz

lemma sigma_79 : sigmaM (mat512% z 223 475 251 0) = (mat512% z 436 323 20 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_223 z hz
  · exact power32_475 z hz
  · exact power32_251 z hz
  · exact power32_0 z hz

lemma product_82 : (mat512% z 492 312 478 0) * (mat512% z 0 323 272 1) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 492)*(gf512% z 0) + (gf512% z 312)*(gf512% z 272) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 145))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 492)*(gf512% z 323) + (gf512% z 312)*(gf512% z 1) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 204))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 478)*(gf512% z 0) + (gf512% z 0)*(gf512% z 272) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 478)*(gf512% z 323) + (gf512% z 0)*(gf512% z 1) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 211))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_83 : (mat512% z 455 73 272 0) * (mat512% z 1 312 272 479) = (mat512% z 0 323 272 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 455)*(gf512% z 1) + (gf512% z 73)*(gf512% z 272) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 39))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 455)*(gf512% z 312) + (gf512% z 73)*(gf512% z 479) = (gf512% z 323)
    apply cert_eq z hz (Q := (gf512% z 204))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 272)*(gf512% z 1) + (gf512% z 0)*(gf512% z 272) = (gf512% z 272)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 272)*(gf512% z 312) + (gf512% z 0)*(gf512% z 479) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 145))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_84 : (mat512% z 15 422 297 0) * (mat512% z 455 266 212 207) = (mat512% z 1 312 272 479) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 15)*(gf512% z 455) + (gf512% z 422)*(gf512% z 212) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 84))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 15)*(gf512% z 266) + (gf512% z 422)*(gf512% z 207) = (gf512% z 312)
    apply cert_eq z hz (Q := (gf512% z 92))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 297)*(gf512% z 455) + (gf512% z 0)*(gf512% z 212) = (gf512% z 272)
    apply cert_eq z hz (Q := (gf512% z 255))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 297)*(gf512% z 266) + (gf512% z 0)*(gf512% z 207) = (gf512% z 479)
    apply cert_eq z hz (Q := (gf512% z 149))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_85 : (mat512% z 104 201 452 0) * (mat512% z 313 41 77 218) = (mat512% z 455 266 212 207) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 104)*(gf512% z 313) + (gf512% z 201)*(gf512% z 77) = (gf512% z 455)
    apply cert_eq z hz (Q := (gf512% z 42))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 104)*(gf512% z 41) + (gf512% z 201)*(gf512% z 218) = (gf512% z 266)
    apply cert_eq z hz (Q := (gf512% z 40))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 452)*(gf512% z 313) + (gf512% z 0)*(gf512% z 77) = (gf512% z 212)
    apply cert_eq z hz (Q := (gf512% z 240))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 452)*(gf512% z 41) + (gf512% z 0)*(gf512% z 218) = (gf512% z 207)
    apply cert_eq z hz (Q := (gf512% z 27))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_86 : (mat512% z 85 195 167 0) * (mat512% z 78 341 59 8) = (mat512% z 313 41 77 218) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 85)*(gf512% z 78) + (gf512% z 195)*(gf512% z 59) = (gf512% z 313)
    apply cert_eq z hz (Q := (gf512% z 2))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 85)*(gf512% z 341) + (gf512% z 195)*(gf512% z 8) = (gf512% z 41)
    apply cert_eq z hz (Q := (gf512% z 32))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 167)*(gf512% z 78) + (gf512% z 0)*(gf512% z 59) = (gf512% z 77)
    apply cert_eq z hz (Q := (gf512% z 23))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 167)*(gf512% z 341) + (gf512% z 0)*(gf512% z 8) = (gf512% z 218)
    apply cert_eq z hz (Q := (gf512% z 65))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_87 : (mat512% z 234 248 109 0) * (mat512% z 404 43 415 453) = (mat512% z 78 341 59 8) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 234)*(gf512% z 404) + (gf512% z 248)*(gf512% z 415) = (gf512% z 78)
    apply cert_eq z hz (Q := (gf512% z 14))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 234)*(gf512% z 43) + (gf512% z 248)*(gf512% z 453) = (gf512% z 341)
    apply cert_eq z hz (Q := (gf512% z 83))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 109)*(gf512% z 404) + (gf512% z 0)*(gf512% z 415) = (gf512% z 59)
    apply cert_eq z hz (Q := (gf512% z 47))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 109)*(gf512% z 43) + (gf512% z 0)*(gf512% z 453) = (gf512% z 8)
    apply cert_eq z hz (Q := (gf512% z 7))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_88 : (mat512% z 409 188 6 0) * (mat512% z 189 166 372 188) = (mat512% z 404 43 415 453) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 409)*(gf512% z 189) + (gf512% z 188)*(gf512% z 372) = (gf512% z 404)
    apply cert_eq z hz (Q := (gf512% z 49))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 409)*(gf512% z 166) + (gf512% z 188)*(gf512% z 188) = (gf512% z 43)
    apply cert_eq z hz (Q := (gf512% z 93))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 6)*(gf512% z 189) + (gf512% z 0)*(gf512% z 372) = (gf512% z 415)
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 6)*(gf512% z 166) + (gf512% z 0)*(gf512% z 188) = (gf512% z 453)
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_89 : (mat512% z 223 475 251 0) * (mat512% z 436 323 20 0) = (mat512% z 189 166 372 188) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 223)*(gf512% z 436) + (gf512% z 475)*(gf512% z 20) = (gf512% z 189)
    apply cert_eq z hz (Q := (gf512% z 93))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 223)*(gf512% z 323) + (gf512% z 475)*(gf512% z 0) = (gf512% z 166)
    apply cert_eq z hz (Q := (gf512% z 119))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 251)*(gf512% z 436) + (gf512% z 0)*(gf512% z 20) = (gf512% z 372)
    apply cert_eq z hz (Q := (gf512% z 72))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 251)*(gf512% z 323) + (gf512% z 0)*(gf512% z 0) = (gf512% z 188)
    apply cert_eq z hz (Q := (gf512% z 97))
    ring_nf <;> reduce_mod_char! <;> ring

lemma norm_9 : semilinearNorm 9 (mat512% z 492 312 478 0) = 1 := by
  have h8 : semilinearNorm 1 (mat512% z 436 323 20 0) = (mat512% z 436 323 20 0) := by simp [semilinearNorm]
  have h7 : semilinearNorm 2 (mat512% z 223 475 251 0) = (mat512% z 189 166 372 188) := by
    change (mat512% z 223 475 251 0) * semilinearNorm 1 (sigmaM (mat512% z 223 475 251 0)) = _
    rw [sigma_79 z hz, h8]
    exact product_89 z hz
  have h6 : semilinearNorm 3 (mat512% z 409 188 6 0) = (mat512% z 404 43 415 453) := by
    change (mat512% z 409 188 6 0) * semilinearNorm 2 (sigmaM (mat512% z 409 188 6 0)) = _
    rw [sigma_78 z hz, h7]
    exact product_88 z hz
  have h5 : semilinearNorm 4 (mat512% z 234 248 109 0) = (mat512% z 78 341 59 8) := by
    change (mat512% z 234 248 109 0) * semilinearNorm 3 (sigmaM (mat512% z 234 248 109 0)) = _
    rw [sigma_77 z hz, h6]
    exact product_87 z hz
  have h4 : semilinearNorm 5 (mat512% z 85 195 167 0) = (mat512% z 313 41 77 218) := by
    change (mat512% z 85 195 167 0) * semilinearNorm 4 (sigmaM (mat512% z 85 195 167 0)) = _
    rw [sigma_76 z hz, h5]
    exact product_86 z hz
  have h3 : semilinearNorm 6 (mat512% z 104 201 452 0) = (mat512% z 455 266 212 207) := by
    change (mat512% z 104 201 452 0) * semilinearNorm 5 (sigmaM (mat512% z 104 201 452 0)) = _
    rw [sigma_75 z hz, h4]
    exact product_85 z hz
  have h2 : semilinearNorm 7 (mat512% z 15 422 297 0) = (mat512% z 1 312 272 479) := by
    change (mat512% z 15 422 297 0) * semilinearNorm 6 (sigmaM (mat512% z 15 422 297 0)) = _
    rw [sigma_74 z hz, h3]
    exact product_84 z hz
  have h1 : semilinearNorm 8 (mat512% z 455 73 272 0) = (mat512% z 0 323 272 1) := by
    change (mat512% z 455 73 272 0) * semilinearNorm 7 (sigmaM (mat512% z 455 73 272 0)) = _
    rw [sigma_73 z hz, h2]
    exact product_83 z hz
  have h0 : semilinearNorm 9 (mat512% z 492 312 478 0) = (mat512% z 1 0 0 1) := by
    change (mat512% z 492 312 478 0) * semilinearNorm 8 (sigmaM (mat512% z 492 312 478 0)) = _
    rw [sigma_72 z hz, h1]
    exact product_82 z hz
  simpa only [code_identity] using h0

lemma mtrace_19 : (mat512% z 492 312 478 0).trace = (gf512% z 492) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 492)+(gf512% z 0) = (gf512% z 492)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma mdet_18 : (mat512% z 492 312 478 0).det = (gf512% z 492) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 492)*(gf512% z 0) - (gf512% z 312)*(gf512% z 478) = (gf512% z 492)
  apply cert_eq z hz (Q := (gf512% z 252))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_382 : (gf512% z 382)^2 = (gf512% z 314) := by
  apply cert_eq z hz (Q := (gf512% z 142))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_68 : (gf512% z 68)^2 = (gf512% z 152) := by
  apply cert_eq z hz (Q := (gf512% z 8))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_309 : (gf512% z 309)^2 = (gf512% z 503) := by
  apply cert_eq z hz (Q := (gf512% z 134))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_270 : (gf512% z 270)^2 = (gf512% z 144) := by
  apply cert_eq z hz (Q := (gf512% z 132))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_494 : (gf512% z 494)^2 = (gf512% z 11) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_373 : (gf512% z 373)^2 = (gf512% z 383) := by
  apply cert_eq z hz (Q := (gf512% z 142))
  ring_nf <;> reduce_mod_char! <;> ring

lemma atr_10 : trace2 9 (gf512% z 382) = 1 := by
  have h0 : trace2 0 (gf512% z 382) = (gf512% z 0) := by simp [trace2]
  have h1 : trace2 1 (gf512% z 382) = (gf512% z 382) := by
    change (trace2 0 (gf512% z 382))^2 + (gf512% z 382) = _
    rw [h0, sqr_0 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h2 : trace2 2 (gf512% z 382) = (gf512% z 68) := by
    change (trace2 1 (gf512% z 382))^2 + (gf512% z 382) = _
    rw [h1, sqr_382 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h3 : trace2 3 (gf512% z 382) = (gf512% z 486) := by
    change (trace2 2 (gf512% z 382))^2 + (gf512% z 382) = _
    rw [h2, sqr_68 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h4 : trace2 4 (gf512% z 382) = (gf512% z 309) := by
    change (trace2 3 (gf512% z 382))^2 + (gf512% z 382) = _
    rw [h3, sqr_486 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h5 : trace2 5 (gf512% z 382) = (gf512% z 137) := by
    change (trace2 4 (gf512% z 382))^2 + (gf512% z 382) = _
    rw [h4, sqr_309 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h6 : trace2 6 (gf512% z 382) = (gf512% z 270) := by
    change (trace2 5 (gf512% z 382))^2 + (gf512% z 382) = _
    rw [h5, sqr_137 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h7 : trace2 7 (gf512% z 382) = (gf512% z 494) := by
    change (trace2 6 (gf512% z 382))^2 + (gf512% z 382) = _
    rw [h6, sqr_270 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h8 : trace2 8 (gf512% z 382) = (gf512% z 373) := by
    change (trace2 7 (gf512% z 382))^2 + (gf512% z 382) = _
    rw [h7, sqr_494 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h9 : trace2 9 (gf512% z 382) = (gf512% z 1) := by
    change (trace2 8 (gf512% z 382))^2 + (gf512% z 382) = _
    rw [h8, sqr_373 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  simpa using h9

lemma elliptic_18 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 492 312 478 0) := by
  have ht : (gf512% z 492)*(gf512% z 382) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 217))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 492)*(gf512% z 382)^2 = (gf512% z 382) := by
    apply cert_eq z hz (Q := (gf512% z 65006))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_19 z hz, mdet_18 z hz]
  apply no_quadratic_root hK (gf512% z 492) (gf512% z 492) (gf512% z 382) ht
  rw [hd]
  exact atr_10 z hz

lemma mdet_19 : (mat512% z 322 7 382 323).det = (gf512% z 323) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 322)*(gf512% z 323) - (gf512% z 7)*(gf512% z 382) = (gf512% z 323)
  apply cert_eq z hz (Q := (gf512% z 143))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_266 : (gf512% z 266)^2 = (gf512% z 128) := by
  apply cert_eq z hz (Q := (gf512% z 132))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_315 : (gf512% z 315)^2 = (gf512% z 419) := by
  apply cert_eq z hz (Q := (gf512% z 134))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_224 : (gf512% z 224)^2 = (gf512% z 155) := by
  apply cert_eq z hz (Q := (gf512% z 43))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_472 : (gf512% z 472)^2 = (gf512% z 317) := by
  apply cert_eq z hz (Q := (gf512% z 173))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_126 : (gf512% z 126)^2 = (gf512% z 510) := by
  apply cert_eq z hz (Q := (gf512% z 10))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_189 : (gf512% z 189)^2 = (gf512% z 322) := by
  apply cert_eq z hz (Q := (gf512% z 35))
  ring_nf <;> reduce_mod_char! <;> ring

lemma atr_11 : trace2 9 (gf512% z 323) = 1 := by
  have h0 : trace2 0 (gf512% z 323) = (gf512% z 0) := by simp [trace2]
  have h1 : trace2 1 (gf512% z 323) = (gf512% z 323) := by
    change (trace2 0 (gf512% z 323))^2 + (gf512% z 323) = _
    rw [h0, sqr_0 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h2 : trace2 2 (gf512% z 323) = (gf512% z 266) := by
    change (trace2 1 (gf512% z 323))^2 + (gf512% z 323) = _
    rw [h1, sqr_323 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h3 : trace2 3 (gf512% z 323) = (gf512% z 451) := by
    change (trace2 2 (gf512% z 323))^2 + (gf512% z 323) = _
    rw [h2, sqr_266 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h4 : trace2 4 (gf512% z 323) = (gf512% z 315) := by
    change (trace2 3 (gf512% z 323))^2 + (gf512% z 323) = _
    rw [h3, sqr_451 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h5 : trace2 5 (gf512% z 323) = (gf512% z 224) := by
    change (trace2 4 (gf512% z 323))^2 + (gf512% z 323) = _
    rw [h4, sqr_315 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h6 : trace2 6 (gf512% z 323) = (gf512% z 472) := by
    change (trace2 5 (gf512% z 323))^2 + (gf512% z 323) = _
    rw [h5, sqr_224 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h7 : trace2 7 (gf512% z 323) = (gf512% z 126) := by
    change (trace2 6 (gf512% z 323))^2 + (gf512% z 323) = _
    rw [h6, sqr_472 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h8 : trace2 8 (gf512% z 323) = (gf512% z 189) := by
    change (trace2 7 (gf512% z 323))^2 + (gf512% z 323) = _
    rw [h7, sqr_126 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h9 : trace2 9 (gf512% z 323) = (gf512% z 1) := by
    change (trace2 8 (gf512% z 323))^2 + (gf512% z 323) = _
    rw [h8, sqr_189 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  simpa using h9

lemma elliptic_19 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 322 7 382 323) := by
  have ht : (gf512% z 1)*(gf512% z 1) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 323)*(gf512% z 1)^2 = (gf512% z 323) := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_18 z hz, mdet_19 z hz]
  apply no_quadratic_root hK (gf512% z 1) (gf512% z 323) (gf512% z 1) ht
  rw [hd]
  exact atr_11 z hz

lemma good_9 (hK : ∀ x : K, x^512 = x) : Good (mat512% z 492 312 478 0) := by
  unfold Good
  rw [sigma_72 z hz, product_81 z hz]
  refine ⟨?_, elliptic_18 z hz hK, norm_9 z hz, elliptic_19 z hz hK⟩
  simpa using mtrace_18 z hz

#check good_9

lemma sqr_212 : (gf512% z 212)^2 = (gf512% z 425) := by
  apply cert_eq z hz (Q := (gf512% z 41))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_425 : (gf512% z 425)^2 = (gf512% z 150) := by
  apply cert_eq z hz (Q := (gf512% z 167))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_150 : (gf512% z 150)^2 = (gf512% z 293) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_293 : (gf512% z 293)^2 = (gf512% z 247) := by
  apply cert_eq z hz (Q := (gf512% z 134))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_247 : (gf512% z 247)^2 = (gf512% z 398) := by
  apply cert_eq z hz (Q := (gf512% z 43))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_212 : (gf512% z 212)^32 = (gf512% z 398) := by
  rw [pow32_squares]
  rw [sqr_212 z hz, sqr_425 z hz, sqr_150 z hz, sqr_293 z hz, sqr_247 z hz]

lemma sigma_80 : sigmaM (mat512% z 50 212 478 478) = (mat512% z 215 398 272 272) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_50 z hz
  · exact power32_212 z hz
  · exact power32_478 z hz
  · exact power32_478 z hz

lemma product_90 : (mat512% z 50 212 478 478) * (mat512% z 215 398 272 272) = (mat512% z 346 166 382 347) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 50)*(gf512% z 215) + (gf512% z 212)*(gf512% z 272) = (gf512% z 346)
    apply cert_eq z hz (Q := (gf512% z 100))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 50)*(gf512% z 398) + (gf512% z 212)*(gf512% z 272) = (gf512% z 166)
    apply cert_eq z hz (Q := (gf512% z 122))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 478)*(gf512% z 215) + (gf512% z 478)*(gf512% z 272) = (gf512% z 382)
    apply cert_eq z hz (Q := (gf512% z 164))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 478)*(gf512% z 398) + (gf512% z 478)*(gf512% z 272) = (gf512% z 347)
    apply cert_eq z hz (Q := (gf512% z 127))
    ring_nf <;> reduce_mod_char! <;> ring

lemma mtrace_20 : (mat512% z 346 166 382 347).trace = (gf512% z 1) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 346)+(gf512% z 347) = (gf512% z 1)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_398 : (gf512% z 398)^2 = (gf512% z 161) := by
  apply cert_eq z hz (Q := (gf512% z 165))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_161 : (gf512% z 161)^2 = (gf512% z 18) := by
  apply cert_eq z hz (Q := (gf512% z 35))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_18 : (gf512% z 18)^2 = (gf512% z 260) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_260 : (gf512% z 260)^2 = (gf512% z 212) := by
  apply cert_eq z hz (Q := (gf512% z 132))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_398 : (gf512% z 398)^32 = (gf512% z 425) := by
  rw [pow32_squares]
  rw [sqr_398 z hz, sqr_161 z hz, sqr_18 z hz, sqr_260 z hz, sqr_212 z hz]

lemma sigma_81 : sigmaM (mat512% z 215 398 272 272) = (mat512% z 294 425 297 297) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_215 z hz
  · exact power32_398 z hz
  · exact power32_272 z hz
  · exact power32_272 z hz

lemma power32_425 : (gf512% z 425)^32 = (gf512% z 161) := by
  rw [pow32_squares]
  rw [sqr_425 z hz, sqr_150 z hz, sqr_293 z hz, sqr_247 z hz, sqr_398 z hz]

lemma sigma_82 : sigmaM (mat512% z 294 425 297 297) = (mat512% z 428 161 452 452) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_294 z hz
  · exact power32_425 z hz
  · exact power32_297 z hz
  · exact power32_297 z hz

lemma power32_161 : (gf512% z 161)^32 = (gf512% z 150) := by
  rw [pow32_squares]
  rw [sqr_161 z hz, sqr_18 z hz, sqr_260 z hz, sqr_212 z hz, sqr_425 z hz]

lemma sigma_83 : sigmaM (mat512% z 428 161 452 452) = (mat512% z 242 150 167 167) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_428 z hz
  · exact power32_161 z hz
  · exact power32_452 z hz
  · exact power32_452 z hz

lemma power32_150 : (gf512% z 150)^32 = (gf512% z 18) := by
  rw [pow32_squares]
  rw [sqr_150 z hz, sqr_293 z hz, sqr_247 z hz, sqr_398 z hz, sqr_161 z hz]

lemma sigma_84 : sigmaM (mat512% z 242 150 167 167) = (mat512% z 135 18 109 109) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_242 z hz
  · exact power32_150 z hz
  · exact power32_167 z hz
  · exact power32_167 z hz

lemma power32_18 : (gf512% z 18)^32 = (gf512% z 293) := by
  rw [pow32_squares]
  rw [sqr_18 z hz, sqr_260 z hz, sqr_212 z hz, sqr_425 z hz, sqr_150 z hz]

lemma sigma_85 : sigmaM (mat512% z 135 18 109 109) = (mat512% z 415 293 6 6) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_135 z hz
  · exact power32_18 z hz
  · exact power32_109 z hz
  · exact power32_109 z hz

lemma power32_293 : (gf512% z 293)^32 = (gf512% z 260) := by
  rw [pow32_squares]
  rw [sqr_293 z hz, sqr_247 z hz, sqr_398 z hz, sqr_161 z hz, sqr_18 z hz]

lemma sigma_86 : sigmaM (mat512% z 415 293 6 6) = (mat512% z 36 260 251 251) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_415 z hz
  · exact power32_293 z hz
  · exact power32_6 z hz
  · exact power32_6 z hz

lemma power32_36 : (gf512% z 36)^32 = (gf512% z 416) := by
  rw [pow32_squares]
  rw [sqr_36 z hz, sqr_50 z hz, sqr_294 z hz, sqr_242 z hz, sqr_415 z hz]

lemma power32_260 : (gf512% z 260)^32 = (gf512% z 247) := by
  rw [pow32_squares]
  rw [sqr_260 z hz, sqr_212 z hz, sqr_425 z hz, sqr_150 z hz, sqr_293 z hz]

lemma sigma_87 : sigmaM (mat512% z 36 260 251 251) = (mat512% z 416 247 20 20) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_36 z hz
  · exact power32_260 z hz
  · exact power32_251 z hz
  · exact power32_251 z hz

lemma product_91 : (mat512% z 50 212 478 478) * (mat512% z 360 210 360 401) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 50)*(gf512% z 360) + (gf512% z 212)*(gf512% z 360) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 97))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 50)*(gf512% z 210) + (gf512% z 212)*(gf512% z 401) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 80))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 478)*(gf512% z 360) + (gf512% z 478)*(gf512% z 360) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 478)*(gf512% z 210) + (gf512% z 478)*(gf512% z 401) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 211))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_92 : (mat512% z 215 398 272 272) * (mat512% z 147 378 106 207) = (mat512% z 360 210 360 401) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 215)*(gf512% z 147) + (gf512% z 398)*(gf512% z 106) = (gf512% z 360)
    apply cert_eq z hz (Q := (gf512% z 29))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 215)*(gf512% z 378) + (gf512% z 398)*(gf512% z 207) = (gf512% z 210)
    apply cert_eq z hz (Q := (gf512% z 46))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 272)*(gf512% z 147) + (gf512% z 272)*(gf512% z 106) = (gf512% z 360)
    apply cert_eq z hz (Q := (gf512% z 120))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 272)*(gf512% z 378) + (gf512% z 272)*(gf512% z 207) = (gf512% z 401)
    apply cert_eq z hz (Q := (gf512% z 209))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_93 : (mat512% z 294 425 297 297) * (mat512% z 448 296 182 485) = (mat512% z 147 378 106 207) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 294)*(gf512% z 448) + (gf512% z 425)*(gf512% z 182) = (gf512% z 147)
    apply cert_eq z hz (Q := (gf512% z 133))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 294)*(gf512% z 296) + (gf512% z 425)*(gf512% z 485) = (gf512% z 378)
    apply cert_eq z hz (Q := (gf512% z 23))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 297)*(gf512% z 448) + (gf512% z 297)*(gf512% z 182) = (gf512% z 106)
    apply cert_eq z hz (Q := (gf512% z 172))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 297)*(gf512% z 296) + (gf512% z 297)*(gf512% z 485) = (gf512% z 207)
    apply cert_eq z hz (Q := (gf512% z 106))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_94 : (mat512% z 428 161 452 452) * (mat512% z 492 19 23 206) = (mat512% z 448 296 182 485) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 428)*(gf512% z 492) + (gf512% z 161)*(gf512% z 23) = (gf512% z 448)
    apply cert_eq z hz (Q := (gf512% z 151))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 428)*(gf512% z 19) + (gf512% z 161)*(gf512% z 206) = (gf512% z 296)
    apply cert_eq z hz (Q := (gf512% z 50))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 452)*(gf512% z 492) + (gf512% z 452)*(gf512% z 23) = (gf512% z 182)
    apply cert_eq z hz (Q := (gf512% z 186))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 452)*(gf512% z 19) + (gf512% z 452)*(gf512% z 206) = (gf512% z 485)
    apply cert_eq z hz (Q := (gf512% z 65))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_95 : (mat512% z 242 150 167 167) * (mat512% z 235 330 115 476) = (mat512% z 492 19 23 206) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 242)*(gf512% z 235) + (gf512% z 150)*(gf512% z 115) = (gf512% z 492)
    apply cert_eq z hz (Q := (gf512% z 48))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 242)*(gf512% z 330) + (gf512% z 150)*(gf512% z 476) = (gf512% z 19)
    apply cert_eq z hz (Q := (gf512% z 31))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 167)*(gf512% z 235) + (gf512% z 167)*(gf512% z 115) = (gf512% z 23)
    apply cert_eq z hz (Q := (gf512% z 47))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 167)*(gf512% z 330) + (gf512% z 167)*(gf512% z 476) = (gf512% z 206)
    apply cert_eq z hz (Q := (gf512% z 44))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_96 : (mat512% z 135 18 109 109) * (mat512% z 484 278 259 205) = (mat512% z 235 330 115 476) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 135)*(gf512% z 484) + (gf512% z 18)*(gf512% z 259) = (gf512% z 235)
    apply cert_eq z hz (Q := (gf512% z 113))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 135)*(gf512% z 278) + (gf512% z 18)*(gf512% z 205) = (gf512% z 330)
    apply cert_eq z hz (Q := (gf512% z 66))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 109)*(gf512% z 484) + (gf512% z 109)*(gf512% z 259) = (gf512% z 115)
    apply cert_eq z hz (Q := (gf512% z 16))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 109)*(gf512% z 278) + (gf512% z 109)*(gf512% z 205) = (gf512% z 476)
    apply cert_eq z hz (Q := (gf512% z 35))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_97 : (mat512% z 415 293 6 6) * (mat512% z 499 296 372 498) = (mat512% z 484 278 259 205) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 415)*(gf512% z 499) + (gf512% z 293)*(gf512% z 372) = (gf512% z 484)
    apply cert_eq z hz (Q := (gf512% z 33))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 415)*(gf512% z 296) + (gf512% z 293)*(gf512% z 498) = (gf512% z 278)
    apply cert_eq z hz (Q := (gf512% z 52))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 6)*(gf512% z 499) + (gf512% z 6)*(gf512% z 372) = (gf512% z 259)
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 6)*(gf512% z 296) + (gf512% z 6)*(gf512% z 498) = (gf512% z 205)
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_98 : (mat512% z 36 260 251 251) * (mat512% z 416 247 20 20) = (mat512% z 499 296 372 498) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 36)*(gf512% z 416) + (gf512% z 260)*(gf512% z 20) = (gf512% z 499)
    apply cert_eq z hz (Q := (gf512% z 19))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 36)*(gf512% z 247) + (gf512% z 260)*(gf512% z 20) = (gf512% z 296)
    apply cert_eq z hz (Q := (gf512% z 4))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 251)*(gf512% z 416) + (gf512% z 251)*(gf512% z 20) = (gf512% z 372)
    apply cert_eq z hz (Q := (gf512% z 72))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 251)*(gf512% z 247) + (gf512% z 251)*(gf512% z 20) = (gf512% z 498)
    apply cert_eq z hz (Q := (gf512% z 47))
    ring_nf <;> reduce_mod_char! <;> ring

lemma norm_10 : semilinearNorm 9 (mat512% z 50 212 478 478) = 1 := by
  have h8 : semilinearNorm 1 (mat512% z 416 247 20 20) = (mat512% z 416 247 20 20) := by simp [semilinearNorm]
  have h7 : semilinearNorm 2 (mat512% z 36 260 251 251) = (mat512% z 499 296 372 498) := by
    change (mat512% z 36 260 251 251) * semilinearNorm 1 (sigmaM (mat512% z 36 260 251 251)) = _
    rw [sigma_87 z hz, h8]
    exact product_98 z hz
  have h6 : semilinearNorm 3 (mat512% z 415 293 6 6) = (mat512% z 484 278 259 205) := by
    change (mat512% z 415 293 6 6) * semilinearNorm 2 (sigmaM (mat512% z 415 293 6 6)) = _
    rw [sigma_86 z hz, h7]
    exact product_97 z hz
  have h5 : semilinearNorm 4 (mat512% z 135 18 109 109) = (mat512% z 235 330 115 476) := by
    change (mat512% z 135 18 109 109) * semilinearNorm 3 (sigmaM (mat512% z 135 18 109 109)) = _
    rw [sigma_85 z hz, h6]
    exact product_96 z hz
  have h4 : semilinearNorm 5 (mat512% z 242 150 167 167) = (mat512% z 492 19 23 206) := by
    change (mat512% z 242 150 167 167) * semilinearNorm 4 (sigmaM (mat512% z 242 150 167 167)) = _
    rw [sigma_84 z hz, h5]
    exact product_95 z hz
  have h3 : semilinearNorm 6 (mat512% z 428 161 452 452) = (mat512% z 448 296 182 485) := by
    change (mat512% z 428 161 452 452) * semilinearNorm 5 (sigmaM (mat512% z 428 161 452 452)) = _
    rw [sigma_83 z hz, h4]
    exact product_94 z hz
  have h2 : semilinearNorm 7 (mat512% z 294 425 297 297) = (mat512% z 147 378 106 207) := by
    change (mat512% z 294 425 297 297) * semilinearNorm 6 (sigmaM (mat512% z 294 425 297 297)) = _
    rw [sigma_82 z hz, h3]
    exact product_93 z hz
  have h1 : semilinearNorm 8 (mat512% z 215 398 272 272) = (mat512% z 360 210 360 401) := by
    change (mat512% z 215 398 272 272) * semilinearNorm 7 (sigmaM (mat512% z 215 398 272 272)) = _
    rw [sigma_81 z hz, h2]
    exact product_92 z hz
  have h0 : semilinearNorm 9 (mat512% z 50 212 478 478) = (mat512% z 1 0 0 1) := by
    change (mat512% z 50 212 478 478) * semilinearNorm 8 (sigmaM (mat512% z 50 212 478 478)) = _
    rw [sigma_80 z hz, h1]
    exact product_91 z hz
  simpa only [code_identity] using h0

lemma mtrace_21 : (mat512% z 50 212 478 478).trace = (gf512% z 492) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 50)+(gf512% z 478) = (gf512% z 492)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma mdet_20 : (mat512% z 50 212 478 478).det = (gf512% z 197) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 50)*(gf512% z 478) - (gf512% z 212)*(gf512% z 478) = (gf512% z 197)
  apply cert_eq z hz (Q := (gf512% z 81))
  ring_nf <;> reduce_mod_char! <;> ring

lemma elliptic_20 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 50 212 478 478) := by
  have ht : (gf512% z 492)*(gf512% z 382) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 217))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 197)*(gf512% z 382)^2 = (gf512% z 186) := by
    apply cert_eq z hz (Q := (gf512% z 26206))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_21 z hz, mdet_20 z hz]
  apply no_quadratic_root hK (gf512% z 492) (gf512% z 197) (gf512% z 382) ht
  rw [hd]
  exact atr_8 z hz

lemma mdet_21 : (mat512% z 346 166 382 347).det = (gf512% z 335) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 346)*(gf512% z 347) - (gf512% z 166)*(gf512% z 382) = (gf512% z 335)
  apply cert_eq z hz (Q := (gf512% z 197))
  ring_nf <;> reduce_mod_char! <;> ring

lemma elliptic_21 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 346 166 382 347) := by
  have ht : (gf512% z 1)*(gf512% z 1) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 335)*(gf512% z 1)^2 = (gf512% z 335) := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_20 z hz, mdet_21 z hz]
  apply no_quadratic_root hK (gf512% z 1) (gf512% z 335) (gf512% z 1) ht
  rw [hd]
  exact atr_9 z hz

lemma good_10 (hK : ∀ x : K, x^512 = x) : Good (mat512% z 50 212 478 478) := by
  unfold Good
  rw [sigma_80 z hz, product_90 z hz]
  refine ⟨?_, elliptic_20 z hz hK, norm_10 z hz, elliptic_21 z hz hK⟩
  simpa using mtrace_20 z hz

#check good_10

lemma sqr_128 : (gf512% z 128)^2 = (gf512% z 49) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_49 : (gf512% z 49)^2 = (gf512% z 291) := by
  apply cert_eq z hz (Q := (gf512% z 2))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_291 : (gf512% z 291)^2 = (gf512% z 227) := by
  apply cert_eq z hz (Q := (gf512% z 134))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_227 : (gf512% z 227)^2 = (gf512% z 158) := by
  apply cert_eq z hz (Q := (gf512% z 43))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_266 : (gf512% z 266)^32 = (gf512% z 158) := by
  rw [pow32_squares]
  rw [sqr_266 z hz, sqr_128 z hz, sqr_49 z hz, sqr_291 z hz, sqr_227 z hz]

lemma sigma_88 : sigmaM (mat512% z 50 266 478 478) = (mat512% z 215 158 272 272) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_50 z hz
  · exact power32_266 z hz
  · exact power32_478 z hz
  · exact power32_478 z hz

lemma product_99 : (mat512% z 50 266 478 478) * (mat512% z 215 158 272 272) = (mat512% z 60 376 382 61) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 50)*(gf512% z 215) + (gf512% z 266)*(gf512% z 272) = (gf512% z 60)
    apply cert_eq z hz (Q := (gf512% z 130))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 50)*(gf512% z 158) + (gf512% z 266)*(gf512% z 272) = (gf512% z 376)
    apply cert_eq z hz (Q := (gf512% z 132))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 478)*(gf512% z 215) + (gf512% z 478)*(gf512% z 272) = (gf512% z 382)
    apply cert_eq z hz (Q := (gf512% z 164))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 478)*(gf512% z 158) + (gf512% z 478)*(gf512% z 272) = (gf512% z 61)
    apply cert_eq z hz (Q := (gf512% z 153))
    ring_nf <;> reduce_mod_char! <;> ring

lemma mtrace_22 : (mat512% z 60 376 382 61).trace = (gf512% z 1) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 60)+(gf512% z 61) = (gf512% z 1)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_357 : (gf512% z 357)^2 = (gf512% z 127) := by
  apply cert_eq z hz (Q := (gf512% z 142))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_127 : (gf512% z 127)^2 = (gf512% z 511) := by
  apply cert_eq z hz (Q := (gf512% z 10))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_511 : (gf512% z 511)^2 = (gf512% z 266) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_158 : (gf512% z 158)^32 = (gf512% z 128) := by
  rw [pow32_squares]
  rw [sqr_158 z hz, sqr_357 z hz, sqr_127 z hz, sqr_511 z hz, sqr_266 z hz]

lemma sigma_89 : sigmaM (mat512% z 215 158 272 272) = (mat512% z 294 128 297 297) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_215 z hz
  · exact power32_158 z hz
  · exact power32_272 z hz
  · exact power32_272 z hz

lemma power32_128 : (gf512% z 128)^32 = (gf512% z 357) := by
  rw [pow32_squares]
  rw [sqr_128 z hz, sqr_49 z hz, sqr_291 z hz, sqr_227 z hz, sqr_158 z hz]

lemma sigma_90 : sigmaM (mat512% z 294 128 297 297) = (mat512% z 428 357 452 452) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_294 z hz
  · exact power32_128 z hz
  · exact power32_297 z hz
  · exact power32_297 z hz

lemma power32_357 : (gf512% z 357)^32 = (gf512% z 49) := by
  rw [pow32_squares]
  rw [sqr_357 z hz, sqr_127 z hz, sqr_511 z hz, sqr_266 z hz, sqr_128 z hz]

lemma sigma_91 : sigmaM (mat512% z 428 357 452 452) = (mat512% z 242 49 167 167) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_428 z hz
  · exact power32_357 z hz
  · exact power32_452 z hz
  · exact power32_452 z hz

lemma power32_49 : (gf512% z 49)^32 = (gf512% z 127) := by
  rw [pow32_squares]
  rw [sqr_49 z hz, sqr_291 z hz, sqr_227 z hz, sqr_158 z hz, sqr_357 z hz]

lemma sigma_92 : sigmaM (mat512% z 242 49 167 167) = (mat512% z 135 127 109 109) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_242 z hz
  · exact power32_49 z hz
  · exact power32_167 z hz
  · exact power32_167 z hz

lemma power32_127 : (gf512% z 127)^32 = (gf512% z 291) := by
  rw [pow32_squares]
  rw [sqr_127 z hz, sqr_511 z hz, sqr_266 z hz, sqr_128 z hz, sqr_49 z hz]

lemma sigma_93 : sigmaM (mat512% z 135 127 109 109) = (mat512% z 415 291 6 6) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_135 z hz
  · exact power32_127 z hz
  · exact power32_109 z hz
  · exact power32_109 z hz

lemma power32_291 : (gf512% z 291)^32 = (gf512% z 511) := by
  rw [pow32_squares]
  rw [sqr_291 z hz, sqr_227 z hz, sqr_158 z hz, sqr_357 z hz, sqr_127 z hz]

lemma sigma_94 : sigmaM (mat512% z 415 291 6 6) = (mat512% z 36 511 251 251) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_415 z hz
  · exact power32_291 z hz
  · exact power32_6 z hz
  · exact power32_6 z hz

lemma power32_511 : (gf512% z 511)^32 = (gf512% z 227) := by
  rw [pow32_squares]
  rw [sqr_511 z hz, sqr_266 z hz, sqr_128 z hz, sqr_49 z hz, sqr_291 z hz]

lemma sigma_95 : sigmaM (mat512% z 36 511 251 251) = (mat512% z 416 227 20 20) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_36 z hz
  · exact power32_511 z hz
  · exact power32_251 z hz
  · exact power32_251 z hz

lemma product_100 : (mat512% z 50 266 478 478) * (mat512% z 272 82 272 273) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 50)*(gf512% z 272) + (gf512% z 266)*(gf512% z 272) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 145))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 50)*(gf512% z 82) + (gf512% z 266)*(gf512% z 273) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 142))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 478)*(gf512% z 272) + (gf512% z 478)*(gf512% z 272) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 478)*(gf512% z 82) + (gf512% z 478)*(gf512% z 273) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 211))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_101 : (mat512% z 215 158 272 272) * (mat512% z 273 502 272 207) = (mat512% z 272 82 272 273) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 215)*(gf512% z 273) + (gf512% z 158)*(gf512% z 272) = (gf512% z 272)
    apply cert_eq z hz (Q := (gf512% z 39))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 215)*(gf512% z 502) + (gf512% z 158)*(gf512% z 207) = (gf512% z 82)
    apply cert_eq z hz (Q := (gf512% z 122))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 272)*(gf512% z 273) + (gf512% z 272)*(gf512% z 272) = (gf512% z 272)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 272)*(gf512% z 502) + (gf512% z 272)*(gf512% z 207) = (gf512% z 273)
    apply cert_eq z hz (Q := (gf512% z 145))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_102 : (mat512% z 294 128 297 297) * (mat512% z 275 214 212 27) = (mat512% z 273 502 272 207) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 294)*(gf512% z 275) + (gf512% z 128)*(gf512% z 212) = (gf512% z 273)
    apply cert_eq z hz (Q := (gf512% z 171))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 294)*(gf512% z 214) + (gf512% z 128)*(gf512% z 27) = (gf512% z 502)
    apply cert_eq z hz (Q := (gf512% z 98))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 297)*(gf512% z 275) + (gf512% z 297)*(gf512% z 212) = (gf512% z 272)
    apply cert_eq z hz (Q := (gf512% z 255))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 297)*(gf512% z 214) + (gf512% z 297)*(gf512% z 27) = (gf512% z 207)
    apply cert_eq z hz (Q := (gf512% z 106))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_103 : (mat512% z 428 357 452 452) * (mat512% z 372 391 77 151) = (mat512% z 275 214 212 27) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 428)*(gf512% z 372) + (gf512% z 357)*(gf512% z 77) = (gf512% z 275)
    apply cert_eq z hz (Q := (gf512% z 218))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 428)*(gf512% z 391) + (gf512% z 357)*(gf512% z 151) = (gf512% z 214)
    apply cert_eq z hz (Q := (gf512% z 233))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 452)*(gf512% z 372) + (gf512% z 452)*(gf512% z 77) = (gf512% z 212)
    apply cert_eq z hz (Q := (gf512% z 240))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 452)*(gf512% z 391) + (gf512% z 452)*(gf512% z 151) = (gf512% z 27)
    apply cert_eq z hz (Q := (gf512% z 235))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_104 : (mat512% z 242 49 167 167) * (mat512% z 117 296 59 51) = (mat512% z 372 391 77 151) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 242)*(gf512% z 117) + (gf512% z 49)*(gf512% z 59) = (gf512% z 372)
    apply cert_eq z hz (Q := (gf512% z 21))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 242)*(gf512% z 296) + (gf512% z 49)*(gf512% z 51) = (gf512% z 391)
    apply cert_eq z hz (Q := (gf512% z 116))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 167)*(gf512% z 117) + (gf512% z 167)*(gf512% z 59) = (gf512% z 77)
    apply cert_eq z hz (Q := (gf512% z 23))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 167)*(gf512% z 296) + (gf512% z 167)*(gf512% z 51) = (gf512% z 151)
    apply cert_eq z hz (Q := (gf512% z 86))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_105 : (mat512% z 135 127 109 109) * (mat512% z 11 485 415 90) = (mat512% z 117 296 59 51) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 135)*(gf512% z 11) + (gf512% z 127)*(gf512% z 415) = (gf512% z 117)
    apply cert_eq z hz (Q := (gf512% z 33))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 135)*(gf512% z 485) + (gf512% z 127)*(gf512% z 90) = (gf512% z 296)
    apply cert_eq z hz (Q := (gf512% z 117))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 109)*(gf512% z 11) + (gf512% z 109)*(gf512% z 415) = (gf512% z 59)
    apply cert_eq z hz (Q := (gf512% z 47))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 109)*(gf512% z 485) + (gf512% z 109)*(gf512% z 90) = (gf512% z 51)
    apply cert_eq z hz (Q := (gf512% z 40))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_106 : (mat512% z 415 291 6 6) * (mat512% z 457 467 372 456) = (mat512% z 11 485 415 90) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 415)*(gf512% z 457) + (gf512% z 291)*(gf512% z 372) = (gf512% z 11)
    apply cert_eq z hz (Q := (gf512% z 48))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 415)*(gf512% z 467) + (gf512% z 291)*(gf512% z 456) = (gf512% z 485)
    apply cert_eq z hz (Q := (gf512% z 108))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 6)*(gf512% z 457) + (gf512% z 6)*(gf512% z 372) = (gf512% z 415)
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 6)*(gf512% z 467) + (gf512% z 6)*(gf512% z 456) = (gf512% z 90)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_107 : (mat512% z 36 511 251 251) * (mat512% z 416 227 20 20) = (mat512% z 457 467 372 456) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 36)*(gf512% z 416) + (gf512% z 511)*(gf512% z 20) = (gf512% z 457)
    apply cert_eq z hz (Q := (gf512% z 21))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 36)*(gf512% z 227) + (gf512% z 511)*(gf512% z 20) = (gf512% z 467)
    apply cert_eq z hz (Q := (gf512% z 3))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 251)*(gf512% z 416) + (gf512% z 251)*(gf512% z 20) = (gf512% z 372)
    apply cert_eq z hz (Q := (gf512% z 72))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 251)*(gf512% z 227) + (gf512% z 251)*(gf512% z 20) = (gf512% z 456)
    apply cert_eq z hz (Q := (gf512% z 41))
    ring_nf <;> reduce_mod_char! <;> ring

lemma norm_11 : semilinearNorm 9 (mat512% z 50 266 478 478) = 1 := by
  have h8 : semilinearNorm 1 (mat512% z 416 227 20 20) = (mat512% z 416 227 20 20) := by simp [semilinearNorm]
  have h7 : semilinearNorm 2 (mat512% z 36 511 251 251) = (mat512% z 457 467 372 456) := by
    change (mat512% z 36 511 251 251) * semilinearNorm 1 (sigmaM (mat512% z 36 511 251 251)) = _
    rw [sigma_95 z hz, h8]
    exact product_107 z hz
  have h6 : semilinearNorm 3 (mat512% z 415 291 6 6) = (mat512% z 11 485 415 90) := by
    change (mat512% z 415 291 6 6) * semilinearNorm 2 (sigmaM (mat512% z 415 291 6 6)) = _
    rw [sigma_94 z hz, h7]
    exact product_106 z hz
  have h5 : semilinearNorm 4 (mat512% z 135 127 109 109) = (mat512% z 117 296 59 51) := by
    change (mat512% z 135 127 109 109) * semilinearNorm 3 (sigmaM (mat512% z 135 127 109 109)) = _
    rw [sigma_93 z hz, h6]
    exact product_105 z hz
  have h4 : semilinearNorm 5 (mat512% z 242 49 167 167) = (mat512% z 372 391 77 151) := by
    change (mat512% z 242 49 167 167) * semilinearNorm 4 (sigmaM (mat512% z 242 49 167 167)) = _
    rw [sigma_92 z hz, h5]
    exact product_104 z hz
  have h3 : semilinearNorm 6 (mat512% z 428 357 452 452) = (mat512% z 275 214 212 27) := by
    change (mat512% z 428 357 452 452) * semilinearNorm 5 (sigmaM (mat512% z 428 357 452 452)) = _
    rw [sigma_91 z hz, h4]
    exact product_103 z hz
  have h2 : semilinearNorm 7 (mat512% z 294 128 297 297) = (mat512% z 273 502 272 207) := by
    change (mat512% z 294 128 297 297) * semilinearNorm 6 (sigmaM (mat512% z 294 128 297 297)) = _
    rw [sigma_90 z hz, h3]
    exact product_102 z hz
  have h1 : semilinearNorm 8 (mat512% z 215 158 272 272) = (mat512% z 272 82 272 273) := by
    change (mat512% z 215 158 272 272) * semilinearNorm 7 (sigmaM (mat512% z 215 158 272 272)) = _
    rw [sigma_89 z hz, h2]
    exact product_101 z hz
  have h0 : semilinearNorm 9 (mat512% z 50 266 478 478) = (mat512% z 1 0 0 1) := by
    change (mat512% z 50 266 478 478) * semilinearNorm 8 (sigmaM (mat512% z 50 266 478 478)) = _
    rw [sigma_88 z hz, h1]
    exact product_100 z hz
  simpa only [code_identity] using h0

lemma mtrace_23 : (mat512% z 50 266 478 478).trace = (gf512% z 492) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 50)+(gf512% z 478) = (gf512% z 492)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma mdet_22 : (mat512% z 50 266 478 478).det = (gf512% z 492) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 50)*(gf512% z 478) - (gf512% z 266)*(gf512% z 478) = (gf512% z 492)
  apply cert_eq z hz (Q := (gf512% z 252))
  ring_nf <;> reduce_mod_char! <;> ring

lemma elliptic_22 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 50 266 478 478) := by
  have ht : (gf512% z 492)*(gf512% z 382) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 217))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 492)*(gf512% z 382)^2 = (gf512% z 382) := by
    apply cert_eq z hz (Q := (gf512% z 65006))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_23 z hz, mdet_22 z hz]
  apply no_quadratic_root hK (gf512% z 492) (gf512% z 492) (gf512% z 382) ht
  rw [hd]
  exact atr_10 z hz

lemma mdet_23 : (mat512% z 60 376 382 61).det = (gf512% z 323) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 60)*(gf512% z 61) - (gf512% z 376)*(gf512% z 382) = (gf512% z 323)
  apply cert_eq z hz (Q := (gf512% z 143))
  ring_nf <;> reduce_mod_char! <;> ring

lemma elliptic_23 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 60 376 382 61) := by
  have ht : (gf512% z 1)*(gf512% z 1) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 323)*(gf512% z 1)^2 = (gf512% z 323) := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_22 z hz, mdet_23 z hz]
  apply no_quadratic_root hK (gf512% z 1) (gf512% z 323) (gf512% z 1) ht
  rw [hd]
  exact atr_11 z hz

lemma good_11 (hK : ∀ x : K, x^512 = x) : Good (mat512% z 50 266 478 478) := by
  unfold Good
  rw [sigma_88 z hz, product_99 z hz]
  refine ⟨?_, elliptic_22 z hz hK, norm_11 z hz, elliptic_23 z hz hK⟩
  simpa using mtrace_22 z hz

#check good_11

lemma sqr_510 : (gf512% z 510)^2 = (gf512% z 267) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_267 : (gf512% z 267)^2 = (gf512% z 129) := by
  apply cert_eq z hz (Q := (gf512% z 132))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_48 : (gf512% z 48)^2 = (gf512% z 290) := by
  apply cert_eq z hz (Q := (gf512% z 2))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_290 : (gf512% z 290)^2 = (gf512% z 226) := by
  apply cert_eq z hz (Q := (gf512% z 134))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_510 : (gf512% z 510)^32 = (gf512% z 226) := by
  rw [pow32_squares]
  rw [sqr_510 z hz, sqr_267 z hz, sqr_129 z hz, sqr_48 z hz, sqr_290 z hz]

lemma sqr_16 : (gf512% z 16)^2 = (gf512% z 256) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_256 : (gf512% z 256)^2 = (gf512% z 196) := by
  apply cert_eq z hz (Q := (gf512% z 132))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_196 : (gf512% z 196)^2 = (gf512% z 169) := by
  apply cert_eq z hz (Q := (gf512% z 41))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_169 : (gf512% z 169)^2 = (gf512% z 82) := by
  apply cert_eq z hz (Q := (gf512% z 35))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_82 : (gf512% z 82)^2 = (gf512% z 396) := by
  apply cert_eq z hz (Q := (gf512% z 8))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_16 : (gf512% z 16)^32 = (gf512% z 396) := by
  rw [pow32_squares]
  rw [sqr_16 z hz, sqr_256 z hz, sqr_196 z hz, sqr_169 z hz, sqr_82 z hz]

lemma sqr_503 : (gf512% z 503)^2 = (gf512% z 330) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_330 : (gf512% z 330)^2 = (gf512% z 8) := by
  apply cert_eq z hz (Q := (gf512% z 140))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_64 : (gf512% z 64)^2 = (gf512% z 136) := by
  apply cert_eq z hz (Q := (gf512% z 8))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_136 : (gf512% z 136)^2 = (gf512% z 113) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_503 : (gf512% z 503)^32 = (gf512% z 113) := by
  rw [pow32_squares]
  rw [sqr_503 z hz, sqr_330 z hz, sqr_8 z hz, sqr_64 z hz, sqr_136 z hz]

lemma sigma_96 : sigmaM (mat512% z 510 16 503 0) = (mat512% z 226 396 113 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_510 z hz
  · exact power32_16 z hz
  · exact power32_503 z hz
  · exact power32_0 z hz

lemma product_108 : (mat512% z 510 16 503 0) * (mat512% z 226 396 113 0) = (mat512% z 3 392 225 2) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 510)*(gf512% z 226) + (gf512% z 16)*(gf512% z 113) = (gf512% z 3)
    apply cert_eq z hz (Q := (gf512% z 95))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 510)*(gf512% z 396) + (gf512% z 16)*(gf512% z 0) = (gf512% z 392)
    apply cert_eq z hz (Q := (gf512% z 128))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 503)*(gf512% z 226) + (gf512% z 0)*(gf512% z 113) = (gf512% z 225)
    apply cert_eq z hz (Q := (gf512% z 95))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 503)*(gf512% z 396) + (gf512% z 0)*(gf512% z 0) = (gf512% z 2)
    apply cert_eq z hz (Q := (gf512% z 134))
    ring_nf <;> reduce_mod_char! <;> ring

lemma mtrace_24 : (mat512% z 3 392 225 2).trace = (gf512% z 1) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 3)+(gf512% z 2) = (gf512% z 1)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_226 : (gf512% z 226)^2 = (gf512% z 159) := by
  apply cert_eq z hz (Q := (gf512% z 43))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_159 : (gf512% z 159)^2 = (gf512% z 356) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_356 : (gf512% z 356)^2 = (gf512% z 126) := by
  apply cert_eq z hz (Q := (gf512% z 142))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_226 : (gf512% z 226)^32 = (gf512% z 267) := by
  rw [pow32_squares]
  rw [sqr_226 z hz, sqr_159 z hz, sqr_356 z hz, sqr_126 z hz, sqr_510 z hz]

lemma sqr_396 : (gf512% z 396)^2 = (gf512% z 165) := by
  apply cert_eq z hz (Q := (gf512% z 165))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_165 : (gf512% z 165)^2 = (gf512% z 2) := by
  apply cert_eq z hz (Q := (gf512% z 35))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_2 : (gf512% z 2)^2 = (gf512% z 4) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_4 : (gf512% z 4)^2 = (gf512% z 16) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_396 : (gf512% z 396)^32 = (gf512% z 256) := by
  rw [pow32_squares]
  rw [sqr_396 z hz, sqr_165 z hz, sqr_2 z hz, sqr_4 z hz, sqr_16 z hz]

lemma sqr_113 : (gf512% z 113)^2 = (gf512% z 427) := by
  apply cert_eq z hz (Q := (gf512% z 10))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_146 : (gf512% z 146)^2 = (gf512% z 309) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_113 : (gf512% z 113)^32 = (gf512% z 330) := by
  rw [pow32_squares]
  rw [sqr_113 z hz, sqr_427 z hz, sqr_146 z hz, sqr_309 z hz, sqr_503 z hz]

lemma sigma_97 : sigmaM (mat512% z 226 396 113 0) = (mat512% z 267 256 330 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_226 z hz
  · exact power32_396 z hz
  · exact power32_113 z hz
  · exact power32_0 z hz

lemma power32_267 : (gf512% z 267)^32 = (gf512% z 159) := by
  rw [pow32_squares]
  rw [sqr_267 z hz, sqr_129 z hz, sqr_48 z hz, sqr_290 z hz, sqr_226 z hz]

lemma power32_256 : (gf512% z 256)^32 = (gf512% z 165) := by
  rw [pow32_squares]
  rw [sqr_256 z hz, sqr_196 z hz, sqr_169 z hz, sqr_82 z hz, sqr_396 z hz]

lemma power32_330 : (gf512% z 330)^32 = (gf512% z 427) := by
  rw [pow32_squares]
  rw [sqr_330 z hz, sqr_8 z hz, sqr_64 z hz, sqr_136 z hz, sqr_113 z hz]

lemma sigma_98 : sigmaM (mat512% z 267 256 330 0) = (mat512% z 159 165 427 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_267 z hz
  · exact power32_256 z hz
  · exact power32_330 z hz
  · exact power32_0 z hz

lemma power32_159 : (gf512% z 159)^32 = (gf512% z 129) := by
  rw [pow32_squares]
  rw [sqr_159 z hz, sqr_356 z hz, sqr_126 z hz, sqr_510 z hz, sqr_267 z hz]

lemma power32_165 : (gf512% z 165)^32 = (gf512% z 196) := by
  rw [pow32_squares]
  rw [sqr_165 z hz, sqr_2 z hz, sqr_4 z hz, sqr_16 z hz, sqr_256 z hz]

lemma power32_427 : (gf512% z 427)^32 = (gf512% z 8) := by
  rw [pow32_squares]
  rw [sqr_427 z hz, sqr_146 z hz, sqr_309 z hz, sqr_503 z hz, sqr_330 z hz]

lemma sigma_99 : sigmaM (mat512% z 159 165 427 0) = (mat512% z 129 196 8 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_159 z hz
  · exact power32_165 z hz
  · exact power32_427 z hz
  · exact power32_0 z hz

lemma power32_129 : (gf512% z 129)^32 = (gf512% z 356) := by
  rw [pow32_squares]
  rw [sqr_129 z hz, sqr_48 z hz, sqr_290 z hz, sqr_226 z hz, sqr_159 z hz]

lemma power32_196 : (gf512% z 196)^32 = (gf512% z 2) := by
  rw [pow32_squares]
  rw [sqr_196 z hz, sqr_169 z hz, sqr_82 z hz, sqr_396 z hz, sqr_165 z hz]

lemma power32_8 : (gf512% z 8)^32 = (gf512% z 146) := by
  rw [pow32_squares]
  rw [sqr_8 z hz, sqr_64 z hz, sqr_136 z hz, sqr_113 z hz, sqr_427 z hz]

lemma sigma_100 : sigmaM (mat512% z 129 196 8 0) = (mat512% z 356 2 146 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_129 z hz
  · exact power32_196 z hz
  · exact power32_8 z hz
  · exact power32_0 z hz

lemma power32_356 : (gf512% z 356)^32 = (gf512% z 48) := by
  rw [pow32_squares]
  rw [sqr_356 z hz, sqr_126 z hz, sqr_510 z hz, sqr_267 z hz, sqr_129 z hz]

lemma power32_2 : (gf512% z 2)^32 = (gf512% z 169) := by
  rw [pow32_squares]
  rw [sqr_2 z hz, sqr_4 z hz, sqr_16 z hz, sqr_256 z hz, sqr_196 z hz]

lemma power32_146 : (gf512% z 146)^32 = (gf512% z 64) := by
  rw [pow32_squares]
  rw [sqr_146 z hz, sqr_309 z hz, sqr_503 z hz, sqr_330 z hz, sqr_8 z hz]

lemma sigma_101 : sigmaM (mat512% z 356 2 146 0) = (mat512% z 48 169 64 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_356 z hz
  · exact power32_2 z hz
  · exact power32_146 z hz
  · exact power32_0 z hz

lemma power32_48 : (gf512% z 48)^32 = (gf512% z 126) := by
  rw [pow32_squares]
  rw [sqr_48 z hz, sqr_290 z hz, sqr_226 z hz, sqr_159 z hz, sqr_356 z hz]

lemma power32_169 : (gf512% z 169)^32 = (gf512% z 4) := by
  rw [pow32_squares]
  rw [sqr_169 z hz, sqr_82 z hz, sqr_396 z hz, sqr_165 z hz, sqr_2 z hz]

lemma power32_64 : (gf512% z 64)^32 = (gf512% z 309) := by
  rw [pow32_squares]
  rw [sqr_64 z hz, sqr_136 z hz, sqr_113 z hz, sqr_427 z hz, sqr_146 z hz]

lemma sigma_102 : sigmaM (mat512% z 48 169 64 0) = (mat512% z 126 4 309 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_48 z hz
  · exact power32_169 z hz
  · exact power32_64 z hz
  · exact power32_0 z hz

lemma power32_126 : (gf512% z 126)^32 = (gf512% z 290) := by
  rw [pow32_squares]
  rw [sqr_126 z hz, sqr_510 z hz, sqr_267 z hz, sqr_129 z hz, sqr_48 z hz]

lemma power32_4 : (gf512% z 4)^32 = (gf512% z 82) := by
  rw [pow32_squares]
  rw [sqr_4 z hz, sqr_16 z hz, sqr_256 z hz, sqr_196 z hz, sqr_169 z hz]

lemma power32_309 : (gf512% z 309)^32 = (gf512% z 136) := by
  rw [pow32_squares]
  rw [sqr_309 z hz, sqr_503 z hz, sqr_330 z hz, sqr_8 z hz, sqr_64 z hz]

lemma sigma_103 : sigmaM (mat512% z 126 4 309 0) = (mat512% z 290 82 136 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_126 z hz
  · exact power32_4 z hz
  · exact power32_309 z hz
  · exact power32_0 z hz

lemma product_109 : (mat512% z 510 16 503 0) * (mat512% z 0 198 33 136) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 510)*(gf512% z 0) + (gf512% z 16)*(gf512% z 33) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 510)*(gf512% z 198) + (gf512% z 16)*(gf512% z 136) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 68))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 503)*(gf512% z 0) + (gf512% z 0)*(gf512% z 33) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 503)*(gf512% z 198) + (gf512% z 0)*(gf512% z 136) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 67))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_110 : (mat512% z 226 396 113 0) * (mat512% z 353 97 248 217) = (mat512% z 0 198 33 136) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 226)*(gf512% z 353) + (gf512% z 396)*(gf512% z 248) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 34))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 226)*(gf512% z 97) + (gf512% z 396)*(gf512% z 217) = (gf512% z 198)
    apply cert_eq z hz (Q := (gf512% z 72))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 113)*(gf512% z 353) + (gf512% z 0)*(gf512% z 248) = (gf512% z 33)
    apply cert_eq z hz (Q := (gf512% z 48))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 113)*(gf512% z 97) + (gf512% z 0)*(gf512% z 217) = (gf512% z 136)
    apply cert_eq z hz (Q := (gf512% z 9))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_111 : (mat512% z 267 256 330 0) * (mat512% z 202 365 507 476) = (mat512% z 353 97 248 217) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 267)*(gf512% z 202) + (gf512% z 256)*(gf512% z 507) = (gf512% z 353)
    apply cert_eq z hz (Q := (gf512% z 159))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 267)*(gf512% z 365) + (gf512% z 256)*(gf512% z 476) = (gf512% z 97)
    apply cert_eq z hz (Q := (gf512% z 94))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 330)*(gf512% z 202) + (gf512% z 0)*(gf512% z 507) = (gf512% z 248)
    apply cert_eq z hz (Q := (gf512% z 124))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 330)*(gf512% z 365) + (gf512% z 0)*(gf512% z 476) = (gf512% z 217)
    apply cert_eq z hz (Q := (gf512% z 155))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_112 : (mat512% z 159 165 427 0) * (mat512% z 105 350 306 367) = (mat512% z 202 365 507 476) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 159)*(gf512% z 105) + (gf512% z 165)*(gf512% z 306) = (gf512% z 202)
    apply cert_eq z hz (Q := (gf512% z 71))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 159)*(gf512% z 350) + (gf512% z 165)*(gf512% z 367) = (gf512% z 365)
    apply cert_eq z hz (Q := (gf512% z 20))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 427)*(gf512% z 105) + (gf512% z 0)*(gf512% z 306) = (gf512% z 507)
    apply cert_eq z hz (Q := (gf512% z 40))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 427)*(gf512% z 350) + (gf512% z 0)*(gf512% z 367) = (gf512% z 476)
    apply cert_eq z hz (Q := (gf512% z 238))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_113 : (mat512% z 129 196 8 0) * (mat512% z 162 483 330 236) = (mat512% z 105 350 306 367) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 129)*(gf512% z 162) + (gf512% z 196)*(gf512% z 330) = (gf512% z 105)
    apply cert_eq z hz (Q := (gf512% z 83))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 129)*(gf512% z 483) + (gf512% z 196)*(gf512% z 236) = (gf512% z 350)
    apply cert_eq z hz (Q := (gf512% z 93))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 8)*(gf512% z 162) + (gf512% z 0)*(gf512% z 330) = (gf512% z 306)
    apply cert_eq z hz (Q := (gf512% z 2))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 8)*(gf512% z 483) + (gf512% z 0)*(gf512% z 236) = (gf512% z 367)
    apply cert_eq z hz (Q := (gf512% z 7))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_114 : (mat512% z 356 2 146 0) * (mat512% z 501 250 84 170) = (mat512% z 162 483 330 236) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 356)*(gf512% z 501) + (gf512% z 2)*(gf512% z 84) = (gf512% z 162)
    apply cert_eq z hz (Q := (gf512% z 222))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 356)*(gf512% z 250) + (gf512% z 2)*(gf512% z 170) = (gf512% z 483)
    apply cert_eq z hz (Q := (gf512% z 111))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 146)*(gf512% z 501) + (gf512% z 0)*(gf512% z 84) = (gf512% z 330)
    apply cert_eq z hz (Q := (gf512% z 112))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 146)*(gf512% z 250) + (gf512% z 0)*(gf512% z 170) = (gf512% z 236)
    apply cert_eq z hz (Q := (gf512% z 56))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_115 : (mat512% z 48 169 64 0) * (mat512% z 164 80 390 165) = (mat512% z 501 250 84 170) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 48)*(gf512% z 164) + (gf512% z 169)*(gf512% z 390) = (gf512% z 501)
    apply cert_eq z hz (Q := (gf512% z 115))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 48)*(gf512% z 80) + (gf512% z 169)*(gf512% z 165) = (gf512% z 250)
    apply cert_eq z hz (Q := (gf512% z 39))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 64)*(gf512% z 164) + (gf512% z 0)*(gf512% z 390) = (gf512% z 84)
    apply cert_eq z hz (Q := (gf512% z 20))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 64)*(gf512% z 80) + (gf512% z 0)*(gf512% z 165) = (gf512% z 170)
    apply cert_eq z hz (Q := (gf512% z 10))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_116 : (mat512% z 126 4 309 0) * (mat512% z 290 82 136 0) = (mat512% z 164 80 390 165) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 126)*(gf512% z 290) + (gf512% z 4)*(gf512% z 136) = (gf512% z 164)
    apply cert_eq z hz (Q := (gf512% z 56))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 126)*(gf512% z 82) + (gf512% z 4)*(gf512% z 0) = (gf512% z 80)
    apply cert_eq z hz (Q := (gf512% z 12))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 309)*(gf512% z 290) + (gf512% z 0)*(gf512% z 136) = (gf512% z 390)
    apply cert_eq z hz (Q := (gf512% z 140))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 309)*(gf512% z 82) + (gf512% z 0)*(gf512% z 0) = (gf512% z 165)
    apply cert_eq z hz (Q := (gf512% z 47))
    ring_nf <;> reduce_mod_char! <;> ring

lemma norm_12 : semilinearNorm 9 (mat512% z 510 16 503 0) = 1 := by
  have h8 : semilinearNorm 1 (mat512% z 290 82 136 0) = (mat512% z 290 82 136 0) := by simp [semilinearNorm]
  have h7 : semilinearNorm 2 (mat512% z 126 4 309 0) = (mat512% z 164 80 390 165) := by
    change (mat512% z 126 4 309 0) * semilinearNorm 1 (sigmaM (mat512% z 126 4 309 0)) = _
    rw [sigma_103 z hz, h8]
    exact product_116 z hz
  have h6 : semilinearNorm 3 (mat512% z 48 169 64 0) = (mat512% z 501 250 84 170) := by
    change (mat512% z 48 169 64 0) * semilinearNorm 2 (sigmaM (mat512% z 48 169 64 0)) = _
    rw [sigma_102 z hz, h7]
    exact product_115 z hz
  have h5 : semilinearNorm 4 (mat512% z 356 2 146 0) = (mat512% z 162 483 330 236) := by
    change (mat512% z 356 2 146 0) * semilinearNorm 3 (sigmaM (mat512% z 356 2 146 0)) = _
    rw [sigma_101 z hz, h6]
    exact product_114 z hz
  have h4 : semilinearNorm 5 (mat512% z 129 196 8 0) = (mat512% z 105 350 306 367) := by
    change (mat512% z 129 196 8 0) * semilinearNorm 4 (sigmaM (mat512% z 129 196 8 0)) = _
    rw [sigma_100 z hz, h5]
    exact product_113 z hz
  have h3 : semilinearNorm 6 (mat512% z 159 165 427 0) = (mat512% z 202 365 507 476) := by
    change (mat512% z 159 165 427 0) * semilinearNorm 5 (sigmaM (mat512% z 159 165 427 0)) = _
    rw [sigma_99 z hz, h4]
    exact product_112 z hz
  have h2 : semilinearNorm 7 (mat512% z 267 256 330 0) = (mat512% z 353 97 248 217) := by
    change (mat512% z 267 256 330 0) * semilinearNorm 6 (sigmaM (mat512% z 267 256 330 0)) = _
    rw [sigma_98 z hz, h3]
    exact product_111 z hz
  have h1 : semilinearNorm 8 (mat512% z 226 396 113 0) = (mat512% z 0 198 33 136) := by
    change (mat512% z 226 396 113 0) * semilinearNorm 7 (sigmaM (mat512% z 226 396 113 0)) = _
    rw [sigma_97 z hz, h2]
    exact product_110 z hz
  have h0 : semilinearNorm 9 (mat512% z 510 16 503 0) = (mat512% z 1 0 0 1) := by
    change (mat512% z 510 16 503 0) * semilinearNorm 8 (sigmaM (mat512% z 510 16 503 0)) = _
    rw [sigma_96 z hz, h1]
    exact product_109 z hz
  simpa only [code_identity] using h0

lemma mtrace_25 : (mat512% z 510 16 503 0).trace = (gf512% z 510) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 510)+(gf512% z 0) = (gf512% z 510)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma mdet_24 : (mat512% z 510 16 503 0).det = (gf512% z 399) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 510)*(gf512% z 0) - (gf512% z 16)*(gf512% z 503) = (gf512% z 399)
  apply cert_eq z hz (Q := (gf512% z 15))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_178 : (gf512% z 178)^2 = (gf512% z 279) := by
  apply cert_eq z hz (Q := (gf512% z 35))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_421 : (gf512% z 421)^2 = (gf512% z 198) := by
  apply cert_eq z hz (Q := (gf512% z 167))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_264 : (gf512% z 264)^2 = (gf512% z 132) := by
  apply cert_eq z hz (Q := (gf512% z 132))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_54 : (gf512% z 54)^2 = (gf512% z 310) := by
  apply cert_eq z hz (Q := (gf512% z 2))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_388 : (gf512% z 388)^2 = (gf512% z 229) := by
  apply cert_eq z hz (Q := (gf512% z 165))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_87 : (gf512% z 87)^2 = (gf512% z 413) := by
  apply cert_eq z hz (Q := (gf512% z 8))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_303 : (gf512% z 303)^2 = (gf512% z 179) := by
  apply cert_eq z hz (Q := (gf512% z 134))
  ring_nf <;> reduce_mod_char! <;> ring

lemma atr_12 : trace2 9 (gf512% z 178) = 1 := by
  have h0 : trace2 0 (gf512% z 178) = (gf512% z 0) := by simp [trace2]
  have h1 : trace2 1 (gf512% z 178) = (gf512% z 178) := by
    change (trace2 0 (gf512% z 178))^2 + (gf512% z 178) = _
    rw [h0, sqr_0 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h2 : trace2 2 (gf512% z 178) = (gf512% z 421) := by
    change (trace2 1 (gf512% z 178))^2 + (gf512% z 178) = _
    rw [h1, sqr_178 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h3 : trace2 3 (gf512% z 178) = (gf512% z 116) := by
    change (trace2 2 (gf512% z 178))^2 + (gf512% z 178) = _
    rw [h2, sqr_421 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h4 : trace2 4 (gf512% z 178) = (gf512% z 264) := by
    change (trace2 3 (gf512% z 178))^2 + (gf512% z 178) = _
    rw [h3, sqr_116 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h5 : trace2 5 (gf512% z 178) = (gf512% z 54) := by
    change (trace2 4 (gf512% z 178))^2 + (gf512% z 178) = _
    rw [h4, sqr_264 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h6 : trace2 6 (gf512% z 178) = (gf512% z 388) := by
    change (trace2 5 (gf512% z 178))^2 + (gf512% z 178) = _
    rw [h5, sqr_54 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h7 : trace2 7 (gf512% z 178) = (gf512% z 87) := by
    change (trace2 6 (gf512% z 178))^2 + (gf512% z 178) = _
    rw [h6, sqr_388 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h8 : trace2 8 (gf512% z 178) = (gf512% z 303) := by
    change (trace2 7 (gf512% z 178))^2 + (gf512% z 178) = _
    rw [h7, sqr_87 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h9 : trace2 9 (gf512% z 178) = (gf512% z 1) := by
    change (trace2 8 (gf512% z 178))^2 + (gf512% z 178) = _
    rw [h8, sqr_303 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  simpa using h9

lemma elliptic_24 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 510 16 503 0) := by
  have ht : (gf512% z 510)*(gf512% z 79) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 59))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 399)*(gf512% z 79)^2 = (gf512% z 178) := by
    apply cert_eq z hz (Q := (gf512% z 3105))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_25 z hz, mdet_24 z hz]
  apply no_quadratic_root hK (gf512% z 510) (gf512% z 399) (gf512% z 79) ht
  rw [hd]
  exact atr_12 z hz

lemma mdet_25 : (mat512% z 3 392 225 2).det = (gf512% z 87) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 3)*(gf512% z 2) - (gf512% z 392)*(gf512% z 225) = (gf512% z 87)
  apply cert_eq z hz (Q := (gf512% z 73))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_458 : (gf512% z 458)^2 = (gf512% z 57) := by
  apply cert_eq z hz (Q := (gf512% z 173))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_110 : (gf512% z 110)^2 = (gf512% z 254) := by
  apply cert_eq z hz (Q := (gf512% z 10))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_5 : (gf512% z 5)^2 = (gf512% z 17) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_203 : (gf512% z 203)^2 = (gf512% z 252) := by
  apply cert_eq z hz (Q := (gf512% z 41))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_171 : (gf512% z 171)^2 = (gf512% z 86) := by
  apply cert_eq z hz (Q := (gf512% z 35))
  ring_nf <;> reduce_mod_char! <;> ring

lemma atr_13 : trace2 9 (gf512% z 87) = 1 := by
  have h0 : trace2 0 (gf512% z 87) = (gf512% z 0) := by simp [trace2]
  have h1 : trace2 1 (gf512% z 87) = (gf512% z 87) := by
    change (trace2 0 (gf512% z 87))^2 + (gf512% z 87) = _
    rw [h0, sqr_0 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h2 : trace2 2 (gf512% z 87) = (gf512% z 458) := by
    change (trace2 1 (gf512% z 87))^2 + (gf512% z 87) = _
    rw [h1, sqr_87 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h3 : trace2 3 (gf512% z 87) = (gf512% z 110) := by
    change (trace2 2 (gf512% z 87))^2 + (gf512% z 87) = _
    rw [h2, sqr_458 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h4 : trace2 4 (gf512% z 87) = (gf512% z 169) := by
    change (trace2 3 (gf512% z 87))^2 + (gf512% z 87) = _
    rw [h3, sqr_110 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h5 : trace2 5 (gf512% z 87) = (gf512% z 5) := by
    change (trace2 4 (gf512% z 87))^2 + (gf512% z 87) = _
    rw [h4, sqr_169 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h6 : trace2 6 (gf512% z 87) = (gf512% z 70) := by
    change (trace2 5 (gf512% z 87))^2 + (gf512% z 87) = _
    rw [h5, sqr_5 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h7 : trace2 7 (gf512% z 87) = (gf512% z 203) := by
    change (trace2 6 (gf512% z 87))^2 + (gf512% z 87) = _
    rw [h6, sqr_70 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h8 : trace2 8 (gf512% z 87) = (gf512% z 171) := by
    change (trace2 7 (gf512% z 87))^2 + (gf512% z 87) = _
    rw [h7, sqr_203 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h9 : trace2 9 (gf512% z 87) = (gf512% z 1) := by
    change (trace2 8 (gf512% z 87))^2 + (gf512% z 87) = _
    rw [h8, sqr_171 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  simpa using h9

lemma elliptic_25 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 3 392 225 2) := by
  have ht : (gf512% z 1)*(gf512% z 1) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 87)*(gf512% z 1)^2 = (gf512% z 87) := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_24 z hz, mdet_25 z hz]
  apply no_quadratic_root hK (gf512% z 1) (gf512% z 87) (gf512% z 1) ht
  rw [hd]
  exact atr_13 z hz

lemma good_12 (hK : ∀ x : K, x^512 = x) : Good (mat512% z 510 16 503 0) := by
  unfold Good
  rw [sigma_96 z hz, product_108 z hz]
  refine ⟨?_, elliptic_24 z hz hK, norm_12 z hz, elliptic_25 z hz hK⟩
  simpa using mtrace_24 z hz

#check good_12

lemma sqr_74 : (gf512% z 74)^2 = (gf512% z 204) := by
  apply cert_eq z hz (Q := (gf512% z 8))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_204 : (gf512% z 204)^2 = (gf512% z 233) := by
  apply cert_eq z hz (Q := (gf512% z 41))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_233 : (gf512% z 233)^2 = (gf512% z 218) := by
  apply cert_eq z hz (Q := (gf512% z 43))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_487 : (gf512% z 487)^32 = (gf512% z 509) := by
  rw [pow32_squares]
  rw [sqr_487 z hz, sqr_74 z hz, sqr_204 z hz, sqr_233 z hz, sqr_218 z hz]

lemma sigma_104 : sigmaM (mat512% z 510 487 503 0) = (mat512% z 226 509 113 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_510 z hz
  · exact power32_487 z hz
  · exact power32_503 z hz
  · exact power32_0 z hz

lemma product_117 : (mat512% z 510 487 503 0) * (mat512% z 226 509 113 0) = (mat512% z 379 280 225 378) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 510)*(gf512% z 226) + (gf512% z 487)*(gf512% z 113) = (gf512% z 379)
    apply cert_eq z hz (Q := (gf512% z 112))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 510)*(gf512% z 509) + (gf512% z 487)*(gf512% z 0) = (gf512% z 280)
    apply cert_eq z hz (Q := (gf512% z 174))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 503)*(gf512% z 226) + (gf512% z 0)*(gf512% z 113) = (gf512% z 225)
    apply cert_eq z hz (Q := (gf512% z 95))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 503)*(gf512% z 509) + (gf512% z 0)*(gf512% z 0) = (gf512% z 378)
    apply cert_eq z hz (Q := (gf512% z 169))
    ring_nf <;> reduce_mod_char! <;> ring

lemma mtrace_26 : (mat512% z 379 280 225 378).trace = (gf512% z 1) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 379)+(gf512% z 378) = (gf512% z 1)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_509 : (gf512% z 509)^2 = (gf512% z 270) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_144 : (gf512% z 144)^2 = (gf512% z 305) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_305 : (gf512% z 305)^2 = (gf512% z 487) := by
  apply cert_eq z hz (Q := (gf512% z 134))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_509 : (gf512% z 509)^32 = (gf512% z 74) := by
  rw [pow32_squares]
  rw [sqr_509 z hz, sqr_270 z hz, sqr_144 z hz, sqr_305 z hz, sqr_487 z hz]

lemma sigma_105 : sigmaM (mat512% z 226 509 113 0) = (mat512% z 267 74 330 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_226 z hz
  · exact power32_509 z hz
  · exact power32_113 z hz
  · exact power32_0 z hz

lemma power32_74 : (gf512% z 74)^32 = (gf512% z 270) := by
  rw [pow32_squares]
  rw [sqr_74 z hz, sqr_204 z hz, sqr_233 z hz, sqr_218 z hz, sqr_509 z hz]

lemma sigma_106 : sigmaM (mat512% z 267 74 330 0) = (mat512% z 159 270 427 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_267 z hz
  · exact power32_74 z hz
  · exact power32_330 z hz
  · exact power32_0 z hz

lemma power32_270 : (gf512% z 270)^32 = (gf512% z 204) := by
  rw [pow32_squares]
  rw [sqr_270 z hz, sqr_144 z hz, sqr_305 z hz, sqr_487 z hz, sqr_74 z hz]

lemma sigma_107 : sigmaM (mat512% z 159 270 427 0) = (mat512% z 129 204 8 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_159 z hz
  · exact power32_270 z hz
  · exact power32_427 z hz
  · exact power32_0 z hz

lemma power32_204 : (gf512% z 204)^32 = (gf512% z 144) := by
  rw [pow32_squares]
  rw [sqr_204 z hz, sqr_233 z hz, sqr_218 z hz, sqr_509 z hz, sqr_270 z hz]

lemma sigma_108 : sigmaM (mat512% z 129 204 8 0) = (mat512% z 356 144 146 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_129 z hz
  · exact power32_204 z hz
  · exact power32_8 z hz
  · exact power32_0 z hz

lemma power32_144 : (gf512% z 144)^32 = (gf512% z 233) := by
  rw [pow32_squares]
  rw [sqr_144 z hz, sqr_305 z hz, sqr_487 z hz, sqr_74 z hz, sqr_204 z hz]

lemma sigma_109 : sigmaM (mat512% z 356 144 146 0) = (mat512% z 48 233 64 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_356 z hz
  · exact power32_144 z hz
  · exact power32_146 z hz
  · exact power32_0 z hz

lemma power32_233 : (gf512% z 233)^32 = (gf512% z 305) := by
  rw [pow32_squares]
  rw [sqr_233 z hz, sqr_218 z hz, sqr_509 z hz, sqr_270 z hz, sqr_144 z hz]

lemma sigma_110 : sigmaM (mat512% z 48 233 64 0) = (mat512% z 126 305 309 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_48 z hz
  · exact power32_233 z hz
  · exact power32_64 z hz
  · exact power32_0 z hz

lemma power32_305 : (gf512% z 305)^32 = (gf512% z 218) := by
  rw [pow32_squares]
  rw [sqr_305 z hz, sqr_487 z hz, sqr_74 z hz, sqr_204 z hz, sqr_233 z hz]

lemma sigma_111 : sigmaM (mat512% z 126 305 309 0) = (mat512% z 290 218 136 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_126 z hz
  · exact power32_305 z hz
  · exact power32_309 z hz
  · exact power32_0 z hz

lemma product_118 : (mat512% z 510 487 503 0) * (mat512% z 0 198 241 262) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 510)*(gf512% z 0) + (gf512% z 487)*(gf512% z 241) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 86))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 510)*(gf512% z 198) + (gf512% z 487)*(gf512% z 262) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 182))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 503)*(gf512% z 0) + (gf512% z 0)*(gf512% z 241) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 503)*(gf512% z 198) + (gf512% z 0)*(gf512% z 262) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 67))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_119 : (mat512% z 226 509 113 0) * (mat512% z 282 460 341 326) = (mat512% z 0 198 241 262) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 226)*(gf512% z 282) + (gf512% z 509)*(gf512% z 341) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 189))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 226)*(gf512% z 460) + (gf512% z 509)*(gf512% z 326) = (gf512% z 198)
    apply cert_eq z hz (Q := (gf512% z 144))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 113)*(gf512% z 282) + (gf512% z 0)*(gf512% z 341) = (gf512% z 241)
    apply cert_eq z hz (Q := (gf512% z 59))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 113)*(gf512% z 460) + (gf512% z 0)*(gf512% z 326) = (gf512% z 262)
    apply cert_eq z hz (Q := (gf512% z 42))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_120 : (mat512% z 267 74 330 0) * (mat512% z 156 494 258 417) = (mat512% z 282 460 341 326) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 267)*(gf512% z 156) + (gf512% z 74)*(gf512% z 258) = (gf512% z 282)
    apply cert_eq z hz (Q := (gf512% z 106))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 267)*(gf512% z 494) + (gf512% z 74)*(gf512% z 417) = (gf512% z 460)
    apply cert_eq z hz (Q := (gf512% z 196))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 330)*(gf512% z 156) + (gf512% z 0)*(gf512% z 258) = (gf512% z 341)
    apply cert_eq z hz (Q := (gf512% z 93))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 330)*(gf512% z 494) + (gf512% z 0)*(gf512% z 417) = (gf512% z 326)
    apply cert_eq z hz (Q := (gf512% z 202))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_121 : (mat512% z 159 270 427 0) * (mat512% z 38 12 171 297) = (mat512% z 156 494 258 417) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 159)*(gf512% z 38) + (gf512% z 270)*(gf512% z 171) = (gf512% z 156)
    apply cert_eq z hz (Q := (gf512% z 92))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 159)*(gf512% z 12) + (gf512% z 270)*(gf512% z 297) = (gf512% z 494)
    apply cert_eq z hz (Q := (gf512% z 148))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 427)*(gf512% z 38) + (gf512% z 0)*(gf512% z 171) = (gf512% z 258)
    apply cert_eq z hz (Q := (gf512% z 24))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 427)*(gf512% z 12) + (gf512% z 0)*(gf512% z 297) = (gf512% z 417)
    apply cert_eq z hz (Q := (gf512% z 5))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_122 : (mat512% z 129 204 8 0) * (mat512% z 211 103 461 511) = (mat512% z 38 12 171 297) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 129)*(gf512% z 211) + (gf512% z 204)*(gf512% z 461) = (gf512% z 38)
    apply cert_eq z hz (Q := (gf512% z 121))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 129)*(gf512% z 103) + (gf512% z 204)*(gf512% z 511) = (gf512% z 12)
    apply cert_eq z hz (Q := (gf512% z 95))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 8)*(gf512% z 211) + (gf512% z 0)*(gf512% z 461) = (gf512% z 171)
    apply cert_eq z hz (Q := (gf512% z 3))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 8)*(gf512% z 103) + (gf512% z 0)*(gf512% z 511) = (gf512% z 297)
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_123 : (mat512% z 356 144 146 0) * (mat512% z 295 267 287 266) = (mat512% z 211 103 461 511) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 356)*(gf512% z 295) + (gf512% z 144)*(gf512% z 287) = (gf512% z 211)
    apply cert_eq z hz (Q := (gf512% z 239))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 356)*(gf512% z 267) + (gf512% z 144)*(gf512% z 266) = (gf512% z 103)
    apply cert_eq z hz (Q := (gf512% z 251))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 146)*(gf512% z 295) + (gf512% z 0)*(gf512% z 287) = (gf512% z 461)
    apply cert_eq z hz (Q := (gf512% z 67))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 146)*(gf512% z 267) + (gf512% z 0)*(gf512% z 266) = (gf512% z 511)
    apply cert_eq z hz (Q := (gf512% z 73))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_124 : (mat512% z 48 233 64 0) * (mat512% z 375 350 390 374) = (mat512% z 295 267 287 266) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 48)*(gf512% z 375) + (gf512% z 233)*(gf512% z 390) = (gf512% z 295)
    apply cert_eq z hz (Q := (gf512% z 81))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 48)*(gf512% z 350) + (gf512% z 233)*(gf512% z 374) = (gf512% z 267)
    apply cert_eq z hz (Q := (gf512% z 125))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 64)*(gf512% z 375) + (gf512% z 0)*(gf512% z 390) = (gf512% z 287)
    apply cert_eq z hz (Q := (gf512% z 47))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 64)*(gf512% z 350) + (gf512% z 0)*(gf512% z 374) = (gf512% z 266)
    apply cert_eq z hz (Q := (gf512% z 42))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_125 : (mat512% z 126 305 309 0) * (mat512% z 290 218 136 0) = (mat512% z 375 350 390 374) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 126)*(gf512% z 290) + (gf512% z 305)*(gf512% z 136) = (gf512% z 375)
    apply cert_eq z hz (Q := (gf512% z 115))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 126)*(gf512% z 218) + (gf512% z 305)*(gf512% z 0) = (gf512% z 350)
    apply cert_eq z hz (Q := (gf512% z 18))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 309)*(gf512% z 290) + (gf512% z 0)*(gf512% z 136) = (gf512% z 390)
    apply cert_eq z hz (Q := (gf512% z 140))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 309)*(gf512% z 218) + (gf512% z 0)*(gf512% z 0) = (gf512% z 374)
    apply cert_eq z hz (Q := (gf512% z 100))
    ring_nf <;> reduce_mod_char! <;> ring

lemma norm_13 : semilinearNorm 9 (mat512% z 510 487 503 0) = 1 := by
  have h8 : semilinearNorm 1 (mat512% z 290 218 136 0) = (mat512% z 290 218 136 0) := by simp [semilinearNorm]
  have h7 : semilinearNorm 2 (mat512% z 126 305 309 0) = (mat512% z 375 350 390 374) := by
    change (mat512% z 126 305 309 0) * semilinearNorm 1 (sigmaM (mat512% z 126 305 309 0)) = _
    rw [sigma_111 z hz, h8]
    exact product_125 z hz
  have h6 : semilinearNorm 3 (mat512% z 48 233 64 0) = (mat512% z 295 267 287 266) := by
    change (mat512% z 48 233 64 0) * semilinearNorm 2 (sigmaM (mat512% z 48 233 64 0)) = _
    rw [sigma_110 z hz, h7]
    exact product_124 z hz
  have h5 : semilinearNorm 4 (mat512% z 356 144 146 0) = (mat512% z 211 103 461 511) := by
    change (mat512% z 356 144 146 0) * semilinearNorm 3 (sigmaM (mat512% z 356 144 146 0)) = _
    rw [sigma_109 z hz, h6]
    exact product_123 z hz
  have h4 : semilinearNorm 5 (mat512% z 129 204 8 0) = (mat512% z 38 12 171 297) := by
    change (mat512% z 129 204 8 0) * semilinearNorm 4 (sigmaM (mat512% z 129 204 8 0)) = _
    rw [sigma_108 z hz, h5]
    exact product_122 z hz
  have h3 : semilinearNorm 6 (mat512% z 159 270 427 0) = (mat512% z 156 494 258 417) := by
    change (mat512% z 159 270 427 0) * semilinearNorm 5 (sigmaM (mat512% z 159 270 427 0)) = _
    rw [sigma_107 z hz, h4]
    exact product_121 z hz
  have h2 : semilinearNorm 7 (mat512% z 267 74 330 0) = (mat512% z 282 460 341 326) := by
    change (mat512% z 267 74 330 0) * semilinearNorm 6 (sigmaM (mat512% z 267 74 330 0)) = _
    rw [sigma_106 z hz, h3]
    exact product_120 z hz
  have h1 : semilinearNorm 8 (mat512% z 226 509 113 0) = (mat512% z 0 198 241 262) := by
    change (mat512% z 226 509 113 0) * semilinearNorm 7 (sigmaM (mat512% z 226 509 113 0)) = _
    rw [sigma_105 z hz, h2]
    exact product_119 z hz
  have h0 : semilinearNorm 9 (mat512% z 510 487 503 0) = (mat512% z 1 0 0 1) := by
    change (mat512% z 510 487 503 0) * semilinearNorm 8 (sigmaM (mat512% z 510 487 503 0)) = _
    rw [sigma_104 z hz, h1]
    exact product_118 z hz
  simpa only [code_identity] using h0

lemma mtrace_27 : (mat512% z 510 487 503 0).trace = (gf512% z 510) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 510)+(gf512% z 0) = (gf512% z 510)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma mdet_26 : (mat512% z 510 487 503 0).det = (gf512% z 197) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 510)*(gf512% z 0) - (gf512% z 487)*(gf512% z 503) = (gf512% z 197)
  apply cert_eq z hz (Q := (gf512% z 160))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_133 : (gf512% z 133)^2 = (gf512% z 32) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_151 : (gf512% z 151)^2 = (gf512% z 292) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_417 : (gf512% z 417)^2 = (gf512% z 214) := by
  apply cert_eq z hz (Q := (gf512% z 167))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_83 : (gf512% z 83)^2 = (gf512% z 397) := by
  apply cert_eq z hz (Q := (gf512% z 8))
  ring_nf <;> reduce_mod_char! <;> ring

lemma atr_14 : trace2 9 (gf512% z 133) = 1 := by
  have h0 : trace2 0 (gf512% z 133) = (gf512% z 0) := by simp [trace2]
  have h1 : trace2 1 (gf512% z 133) = (gf512% z 133) := by
    change (trace2 0 (gf512% z 133))^2 + (gf512% z 133) = _
    rw [h0, sqr_0 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h2 : trace2 2 (gf512% z 133) = (gf512% z 165) := by
    change (trace2 1 (gf512% z 133))^2 + (gf512% z 133) = _
    rw [h1, sqr_133 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h3 : trace2 3 (gf512% z 133) = (gf512% z 135) := by
    change (trace2 2 (gf512% z 133))^2 + (gf512% z 133) = _
    rw [h2, sqr_165 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h4 : trace2 4 (gf512% z 133) = (gf512% z 161) := by
    change (trace2 3 (gf512% z 133))^2 + (gf512% z 133) = _
    rw [h3, sqr_135 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h5 : trace2 5 (gf512% z 133) = (gf512% z 151) := by
    change (trace2 4 (gf512% z 133))^2 + (gf512% z 133) = _
    rw [h4, sqr_161 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h6 : trace2 6 (gf512% z 133) = (gf512% z 417) := by
    change (trace2 5 (gf512% z 133))^2 + (gf512% z 133) = _
    rw [h5, sqr_151 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h7 : trace2 7 (gf512% z 133) = (gf512% z 83) := by
    change (trace2 6 (gf512% z 133))^2 + (gf512% z 133) = _
    rw [h6, sqr_417 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h8 : trace2 8 (gf512% z 133) = (gf512% z 264) := by
    change (trace2 7 (gf512% z 133))^2 + (gf512% z 133) = _
    rw [h7, sqr_83 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h9 : trace2 9 (gf512% z 133) = (gf512% z 1) := by
    change (trace2 8 (gf512% z 133))^2 + (gf512% z 133) = _
    rw [h8, sqr_264 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  simpa using h9

lemma elliptic_26 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 510 487 503 0) := by
  have ht : (gf512% z 510)*(gf512% z 79) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 59))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 197)*(gf512% z 79)^2 = (gf512% z 133) := by
    apply cert_eq z hz (Q := (gf512% z 1540))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_27 z hz, mdet_26 z hz]
  apply no_quadratic_root hK (gf512% z 510) (gf512% z 197) (gf512% z 79) ht
  rw [hd]
  exact atr_14 z hz

lemma mdet_27 : (mat512% z 379 280 225 378).det = (gf512% z 335) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 379)*(gf512% z 378) - (gf512% z 280)*(gf512% z 225) = (gf512% z 335)
  apply cert_eq z hz (Q := (gf512% z 249))
  ring_nf <;> reduce_mod_char! <;> ring

lemma elliptic_27 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 379 280 225 378) := by
  have ht : (gf512% z 1)*(gf512% z 1) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 335)*(gf512% z 1)^2 = (gf512% z 335) := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_26 z hz, mdet_27 z hz]
  apply no_quadratic_root hK (gf512% z 1) (gf512% z 335) (gf512% z 1) ht
  rw [hd]
  exact atr_9 z hz

lemma good_13 (hK : ∀ x : K, x^512 = x) : Good (mat512% z 510 487 503 0) := by
  unfold Good
  rw [sigma_104 z hz, product_117 z hz]
  refine ⟨?_, elliptic_26 z hz hK, norm_13 z hz, elliptic_27 z hz hK⟩
  simpa using mtrace_26 z hz

#check good_13

lemma sqr_9 : (gf512% z 9)^2 = (gf512% z 65) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_65 : (gf512% z 65)^2 = (gf512% z 137) := by
  apply cert_eq z hz (Q := (gf512% z 8))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_112 : (gf512% z 112)^2 = (gf512% z 426) := by
  apply cert_eq z hz (Q := (gf512% z 10))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_426 : (gf512% z 426)^2 = (gf512% z 147) := by
  apply cert_eq z hz (Q := (gf512% z 167))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_9 : (gf512% z 9)^32 = (gf512% z 147) := by
  rw [pow32_squares]
  rw [sqr_9 z hz, sqr_65 z hz, sqr_137 z hz, sqr_112 z hz, sqr_426 z hz]

lemma sqr_25 : (gf512% z 25)^2 = (gf512% z 321) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_321 : (gf512% z 321)^2 = (gf512% z 77) := by
  apply cert_eq z hz (Q := (gf512% z 140))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_217 : (gf512% z 217)^2 = (gf512% z 504) := by
  apply cert_eq z hz (Q := (gf512% z 41))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_504 : (gf512% z 504)^2 = (gf512% z 287) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_25 : (gf512% z 25)^32 = (gf512% z 287) := by
  rw [pow32_squares]
  rw [sqr_25 z hz, sqr_321 z hz, sqr_77 z hz, sqr_217 z hz, sqr_504 z hz]

lemma sigma_112 : sigmaM (mat512% z 9 25 503 503) = (mat512% z 147 287 113 113) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_9 z hz
  · exact power32_25 z hz
  · exact power32_503 z hz
  · exact power32_503 z hz

lemma product_126 : (mat512% z 9 25 503 503) * (mat512% z 147 287 113 113) = (mat512% z 226 360 225 227) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 9)*(gf512% z 147) + (gf512% z 25)*(gf512% z 113) = (gf512% z 226)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 9)*(gf512% z 287) + (gf512% z 25)*(gf512% z 113) = (gf512% z 360)
    apply cert_eq z hz (Q := (gf512% z 6))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 503)*(gf512% z 147) + (gf512% z 503)*(gf512% z 113) = (gf512% z 225)
    apply cert_eq z hz (Q := (gf512% z 95))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 503)*(gf512% z 287) + (gf512% z 503)*(gf512% z 113) = (gf512% z 227)
    apply cert_eq z hz (Q := (gf512% z 217))
    ring_nf <;> reduce_mod_char! <;> ring

lemma mtrace_28 : (mat512% z 226 360 225 227).trace = (gf512% z 1) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 226)+(gf512% z 227) = (gf512% z 1)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_308 : (gf512% z 308)^2 = (gf512% z 502) := by
  apply cert_eq z hz (Q := (gf512% z 134))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_502 : (gf512% z 502)^2 = (gf512% z 331) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_331 : (gf512% z 331)^2 = (gf512% z 9) := by
  apply cert_eq z hz (Q := (gf512% z 140))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_147 : (gf512% z 147)^32 = (gf512% z 65) := by
  rw [pow32_squares]
  rw [sqr_147 z hz, sqr_308 z hz, sqr_502 z hz, sqr_331 z hz, sqr_9 z hz]

lemma sqr_287 : (gf512% z 287)^2 = (gf512% z 401) := by
  apply cert_eq z hz (Q := (gf512% z 132))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_401 : (gf512% z 401)^2 = (gf512% z 500) := by
  apply cert_eq z hz (Q := (gf512% z 165))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_500 : (gf512% z 500)^2 = (gf512% z 335) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_287 : (gf512% z 287)^32 = (gf512% z 321) := by
  rw [pow32_squares]
  rw [sqr_287 z hz, sqr_401 z hz, sqr_500 z hz, sqr_335 z hz, sqr_25 z hz]

lemma sigma_113 : sigmaM (mat512% z 147 287 113 113) = (mat512% z 65 321 330 330) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_147 z hz
  · exact power32_287 z hz
  · exact power32_113 z hz
  · exact power32_113 z hz

lemma power32_65 : (gf512% z 65)^32 = (gf512% z 308) := by
  rw [pow32_squares]
  rw [sqr_65 z hz, sqr_137 z hz, sqr_112 z hz, sqr_426 z hz, sqr_147 z hz]

lemma power32_321 : (gf512% z 321)^32 = (gf512% z 401) := by
  rw [pow32_squares]
  rw [sqr_321 z hz, sqr_77 z hz, sqr_217 z hz, sqr_504 z hz, sqr_287 z hz]

lemma sigma_114 : sigmaM (mat512% z 65 321 330 330) = (mat512% z 308 401 427 427) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_65 z hz
  · exact power32_321 z hz
  · exact power32_330 z hz
  · exact power32_330 z hz

lemma power32_308 : (gf512% z 308)^32 = (gf512% z 137) := by
  rw [pow32_squares]
  rw [sqr_308 z hz, sqr_502 z hz, sqr_331 z hz, sqr_9 z hz, sqr_65 z hz]

lemma power32_401 : (gf512% z 401)^32 = (gf512% z 77) := by
  rw [pow32_squares]
  rw [sqr_401 z hz, sqr_500 z hz, sqr_335 z hz, sqr_25 z hz, sqr_321 z hz]

lemma sigma_115 : sigmaM (mat512% z 308 401 427 427) = (mat512% z 137 77 8 8) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_308 z hz
  · exact power32_401 z hz
  · exact power32_427 z hz
  · exact power32_427 z hz

lemma power32_137 : (gf512% z 137)^32 = (gf512% z 502) := by
  rw [pow32_squares]
  rw [sqr_137 z hz, sqr_112 z hz, sqr_426 z hz, sqr_147 z hz, sqr_308 z hz]

lemma power32_77 : (gf512% z 77)^32 = (gf512% z 500) := by
  rw [pow32_squares]
  rw [sqr_77 z hz, sqr_217 z hz, sqr_504 z hz, sqr_287 z hz, sqr_401 z hz]

lemma sigma_116 : sigmaM (mat512% z 137 77 8 8) = (mat512% z 502 500 146 146) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_137 z hz
  · exact power32_77 z hz
  · exact power32_8 z hz
  · exact power32_8 z hz

lemma power32_502 : (gf512% z 502)^32 = (gf512% z 112) := by
  rw [pow32_squares]
  rw [sqr_502 z hz, sqr_331 z hz, sqr_9 z hz, sqr_65 z hz, sqr_137 z hz]

lemma power32_500 : (gf512% z 500)^32 = (gf512% z 217) := by
  rw [pow32_squares]
  rw [sqr_500 z hz, sqr_335 z hz, sqr_25 z hz, sqr_321 z hz, sqr_77 z hz]

lemma sigma_117 : sigmaM (mat512% z 502 500 146 146) = (mat512% z 112 217 64 64) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_502 z hz
  · exact power32_500 z hz
  · exact power32_146 z hz
  · exact power32_146 z hz

lemma power32_112 : (gf512% z 112)^32 = (gf512% z 331) := by
  rw [pow32_squares]
  rw [sqr_112 z hz, sqr_426 z hz, sqr_147 z hz, sqr_308 z hz, sqr_502 z hz]

lemma power32_217 : (gf512% z 217)^32 = (gf512% z 335) := by
  rw [pow32_squares]
  rw [sqr_217 z hz, sqr_504 z hz, sqr_287 z hz, sqr_401 z hz, sqr_500 z hz]

lemma sigma_118 : sigmaM (mat512% z 112 217 64 64) = (mat512% z 331 335 309 309) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_112 z hz
  · exact power32_217 z hz
  · exact power32_64 z hz
  · exact power32_64 z hz

lemma power32_331 : (gf512% z 331)^32 = (gf512% z 426) := by
  rw [pow32_squares]
  rw [sqr_331 z hz, sqr_9 z hz, sqr_65 z hz, sqr_137 z hz, sqr_112 z hz]

lemma power32_335 : (gf512% z 335)^32 = (gf512% z 504) := by
  rw [pow32_squares]
  rw [sqr_335 z hz, sqr_25 z hz, sqr_321 z hz, sqr_77 z hz, sqr_217 z hz]

lemma sigma_119 : sigmaM (mat512% z 331 335 309 309) = (mat512% z 426 504 136 136) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_331 z hz
  · exact power32_335 z hz
  · exact power32_309 z hz
  · exact power32_309 z hz

lemma product_127 : (mat512% z 9 25 503 503) * (mat512% z 33 111 33 169) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 9)*(gf512% z 33) + (gf512% z 25)*(gf512% z 33) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 9)*(gf512% z 111) + (gf512% z 25)*(gf512% z 169) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 6))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 503)*(gf512% z 33) + (gf512% z 503)*(gf512% z 33) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 503)*(gf512% z 111) + (gf512% z 503)*(gf512% z 169) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 67))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_128 : (mat512% z 147 287 113 113) * (mat512% z 409 289 248 33) = (mat512% z 33 111 33 169) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 147)*(gf512% z 409) + (gf512% z 287)*(gf512% z 248) = (gf512% z 33)
    apply cert_eq z hz (Q := (gf512% z 18))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 147)*(gf512% z 289) + (gf512% z 287)*(gf512% z 33) = (gf512% z 111)
    apply cert_eq z hz (Q := (gf512% z 83))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 113)*(gf512% z 409) + (gf512% z 113)*(gf512% z 248) = (gf512% z 33)
    apply cert_eq z hz (Q := (gf512% z 48))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 113)*(gf512% z 289) + (gf512% z 113)*(gf512% z 33) = (gf512% z 169)
    apply cert_eq z hz (Q := (gf512% z 57))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_129 : (mat512% z 65 321 330 330) * (mat512% z 305 384 507 39) = (mat512% z 409 289 248 33) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 65)*(gf512% z 305) + (gf512% z 321)*(gf512% z 507) = (gf512% z 409)
    apply cert_eq z hz (Q := (gf512% z 227))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 65)*(gf512% z 384) + (gf512% z 321)*(gf512% z 39) = (gf512% z 289)
    apply cert_eq z hz (Q := (gf512% z 38))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 330)*(gf512% z 305) + (gf512% z 330)*(gf512% z 507) = (gf512% z 248)
    apply cert_eq z hz (Q := (gf512% z 124))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 330)*(gf512% z 384) + (gf512% z 330)*(gf512% z 39) = (gf512% z 33)
    apply cert_eq z hz (Q := (gf512% z 231))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_130 : (mat512% z 308 401 427 427) * (mat512% z 347 362 306 93) = (mat512% z 305 384 507 39) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 308)*(gf512% z 347) + (gf512% z 401)*(gf512% z 306) = (gf512% z 305)
    apply cert_eq z hz (Q := (gf512% z 111))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 308)*(gf512% z 362) + (gf512% z 401)*(gf512% z 93) = (gf512% z 384)
    apply cert_eq z hz (Q := (gf512% z 149))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 427)*(gf512% z 347) + (gf512% z 427)*(gf512% z 306) = (gf512% z 507)
    apply cert_eq z hz (Q := (gf512% z 40))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 427)*(gf512% z 362) + (gf512% z 427)*(gf512% z 93) = (gf512% z 39)
    apply cert_eq z hz (Q := (gf512% z 198))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_131 : (mat512% z 137 77 8 8) * (mat512% z 488 231 330 422) = (mat512% z 347 362 306 93) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 137)*(gf512% z 488) + (gf512% z 77)*(gf512% z 330) = (gf512% z 347)
    apply cert_eq z hz (Q := (gf512% z 81))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 137)*(gf512% z 231) + (gf512% z 77)*(gf512% z 422) = (gf512% z 362)
    apply cert_eq z hz (Q := (gf512% z 11))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 8)*(gf512% z 488) + (gf512% z 8)*(gf512% z 330) = (gf512% z 306)
    apply cert_eq z hz (Q := (gf512% z 2))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 8)*(gf512% z 231) + (gf512% z 8)*(gf512% z 422) = (gf512% z 93)
    apply cert_eq z hz (Q := (gf512% z 5))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_132 : (mat512% z 502 500 146 146) * (mat512% z 417 497 84 254) = (mat512% z 488 231 330 422) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 502)*(gf512% z 417) + (gf512% z 500)*(gf512% z 84) = (gf512% z 488)
    apply cert_eq z hz (Q := (gf512% z 174))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 502)*(gf512% z 497) + (gf512% z 500)*(gf512% z 254) = (gf512% z 231)
    apply cert_eq z hz (Q := (gf512% z 249))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 146)*(gf512% z 417) + (gf512% z 146)*(gf512% z 84) = (gf512% z 330)
    apply cert_eq z hz (Q := (gf512% z 112))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 146)*(gf512% z 497) + (gf512% z 146)*(gf512% z 254) = (gf512% z 422)
    apply cert_eq z hz (Q := (gf512% z 72))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_133 : (mat512% z 112 217 64 64) * (mat512% z 290 471 390 291) = (mat512% z 417 497 84 254) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 112)*(gf512% z 290) + (gf512% z 217)*(gf512% z 390) = (gf512% z 417)
    apply cert_eq z hz (Q := (gf512% z 103))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 112)*(gf512% z 471) + (gf512% z 217)*(gf512% z 291) = (gf512% z 497)
    apply cert_eq z hz (Q := (gf512% z 74))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 64)*(gf512% z 290) + (gf512% z 64)*(gf512% z 390) = (gf512% z 84)
    apply cert_eq z hz (Q := (gf512% z 20))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 64)*(gf512% z 471) + (gf512% z 64)*(gf512% z 291) = (gf512% z 254)
    apply cert_eq z hz (Q := (gf512% z 30))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_134 : (mat512% z 331 335 309 309) * (mat512% z 426 504 136 136) = (mat512% z 290 471 390 291) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 331)*(gf512% z 426) + (gf512% z 335)*(gf512% z 136) = (gf512% z 290)
    apply cert_eq z hz (Q := (gf512% z 180))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 331)*(gf512% z 504) + (gf512% z 335)*(gf512% z 136) = (gf512% z 471)
    apply cert_eq z hz (Q := (gf512% z 151))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 309)*(gf512% z 426) + (gf512% z 309)*(gf512% z 136) = (gf512% z 390)
    apply cert_eq z hz (Q := (gf512% z 140))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 309)*(gf512% z 504) + (gf512% z 309)*(gf512% z 136) = (gf512% z 291)
    apply cert_eq z hz (Q := (gf512% z 163))
    ring_nf <;> reduce_mod_char! <;> ring

lemma norm_14 : semilinearNorm 9 (mat512% z 9 25 503 503) = 1 := by
  have h8 : semilinearNorm 1 (mat512% z 426 504 136 136) = (mat512% z 426 504 136 136) := by simp [semilinearNorm]
  have h7 : semilinearNorm 2 (mat512% z 331 335 309 309) = (mat512% z 290 471 390 291) := by
    change (mat512% z 331 335 309 309) * semilinearNorm 1 (sigmaM (mat512% z 331 335 309 309)) = _
    rw [sigma_119 z hz, h8]
    exact product_134 z hz
  have h6 : semilinearNorm 3 (mat512% z 112 217 64 64) = (mat512% z 417 497 84 254) := by
    change (mat512% z 112 217 64 64) * semilinearNorm 2 (sigmaM (mat512% z 112 217 64 64)) = _
    rw [sigma_118 z hz, h7]
    exact product_133 z hz
  have h5 : semilinearNorm 4 (mat512% z 502 500 146 146) = (mat512% z 488 231 330 422) := by
    change (mat512% z 502 500 146 146) * semilinearNorm 3 (sigmaM (mat512% z 502 500 146 146)) = _
    rw [sigma_117 z hz, h6]
    exact product_132 z hz
  have h4 : semilinearNorm 5 (mat512% z 137 77 8 8) = (mat512% z 347 362 306 93) := by
    change (mat512% z 137 77 8 8) * semilinearNorm 4 (sigmaM (mat512% z 137 77 8 8)) = _
    rw [sigma_116 z hz, h5]
    exact product_131 z hz
  have h3 : semilinearNorm 6 (mat512% z 308 401 427 427) = (mat512% z 305 384 507 39) := by
    change (mat512% z 308 401 427 427) * semilinearNorm 5 (sigmaM (mat512% z 308 401 427 427)) = _
    rw [sigma_115 z hz, h4]
    exact product_130 z hz
  have h2 : semilinearNorm 7 (mat512% z 65 321 330 330) = (mat512% z 409 289 248 33) := by
    change (mat512% z 65 321 330 330) * semilinearNorm 6 (sigmaM (mat512% z 65 321 330 330)) = _
    rw [sigma_114 z hz, h3]
    exact product_129 z hz
  have h1 : semilinearNorm 8 (mat512% z 147 287 113 113) = (mat512% z 33 111 33 169) := by
    change (mat512% z 147 287 113 113) * semilinearNorm 7 (sigmaM (mat512% z 147 287 113 113)) = _
    rw [sigma_113 z hz, h2]
    exact product_128 z hz
  have h0 : semilinearNorm 9 (mat512% z 9 25 503 503) = (mat512% z 1 0 0 1) := by
    change (mat512% z 9 25 503 503) * semilinearNorm 8 (sigmaM (mat512% z 9 25 503 503)) = _
    rw [sigma_112 z hz, h1]
    exact product_127 z hz
  simpa only [code_identity] using h0

lemma mtrace_29 : (mat512% z 9 25 503 503).trace = (gf512% z 510) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 9)+(gf512% z 503) = (gf512% z 510)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma mdet_28 : (mat512% z 9 25 503 503).det = (gf512% z 399) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 9)*(gf512% z 503) - (gf512% z 25)*(gf512% z 503) = (gf512% z 399)
  apply cert_eq z hz (Q := (gf512% z 15))
  ring_nf <;> reduce_mod_char! <;> ring

lemma elliptic_28 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 9 25 503 503) := by
  have ht : (gf512% z 510)*(gf512% z 79) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 59))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 399)*(gf512% z 79)^2 = (gf512% z 178) := by
    apply cert_eq z hz (Q := (gf512% z 3105))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_29 z hz, mdet_28 z hz]
  apply no_quadratic_root hK (gf512% z 510) (gf512% z 399) (gf512% z 79) ht
  rw [hd]
  exact atr_12 z hz

lemma mdet_29 : (mat512% z 226 360 225 227).det = (gf512% z 87) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 226)*(gf512% z 227) - (gf512% z 360)*(gf512% z 225) = (gf512% z 87)
  apply cert_eq z hz (Q := (gf512% z 73))
  ring_nf <;> reduce_mod_char! <;> ring

lemma elliptic_29 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 226 360 225 227) := by
  have ht : (gf512% z 1)*(gf512% z 1) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 87)*(gf512% z 1)^2 = (gf512% z 87) := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_28 z hz, mdet_29 z hz]
  apply no_quadratic_root hK (gf512% z 1) (gf512% z 87) (gf512% z 1) ht
  rw [hd]
  exact atr_13 z hz

lemma good_14 (hK : ∀ x : K, x^512 = x) : Good (mat512% z 9 25 503 503) := by
  unfold Good
  rw [sigma_112 z hz, product_126 z hz]
  refine ⟨?_, elliptic_28 z hz hK, norm_14 z hz, elliptic_29 z hz hK⟩
  simpa using mtrace_28 z hz

#check good_14

lemma sqr_11 : (gf512% z 11)^2 = (gf512% z 69) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_494 : (gf512% z 494)^32 = (gf512% z 366) := by
  rw [pow32_squares]
  rw [sqr_494 z hz, sqr_11 z hz, sqr_69 z hz, sqr_153 z hz, sqr_368 z hz]

lemma sigma_120 : sigmaM (mat512% z 9 494 503 503) = (mat512% z 147 366 113 113) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_9 z hz
  · exact power32_494 z hz
  · exact power32_503 z hz
  · exact power32_503 z hz

lemma product_135 : (mat512% z 9 494 503 503) * (mat512% z 147 366 113 113) = (mat512% z 410 504 225 411) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 9)*(gf512% z 147) + (gf512% z 494)*(gf512% z 113) = (gf512% z 410)
    apply cert_eq z hz (Q := (gf512% z 47))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 9)*(gf512% z 366) + (gf512% z 494)*(gf512% z 113) = (gf512% z 504)
    apply cert_eq z hz (Q := (gf512% z 40))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 503)*(gf512% z 147) + (gf512% z 503)*(gf512% z 113) = (gf512% z 225)
    apply cert_eq z hz (Q := (gf512% z 95))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 503)*(gf512% z 366) + (gf512% z 503)*(gf512% z 113) = (gf512% z 411)
    apply cert_eq z hz (Q := (gf512% z 246))
    ring_nf <;> reduce_mod_char! <;> ring

lemma mtrace_30 : (mat512% z 410 504 225 411).trace = (gf512% z 1) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 410)+(gf512% z 411) = (gf512% z 1)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_366 : (gf512% z 366)^2 = (gf512% z 58) := by
  apply cert_eq z hz (Q := (gf512% z 142))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_58 : (gf512% z 58)^2 = (gf512% z 358) := by
  apply cert_eq z hz (Q := (gf512% z 2))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_358 : (gf512% z 358)^2 = (gf512% z 122) := by
  apply cert_eq z hz (Q := (gf512% z 142))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_122 : (gf512% z 122)^2 = (gf512% z 494) := by
  apply cert_eq z hz (Q := (gf512% z 10))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_366 : (gf512% z 366)^32 = (gf512% z 11) := by
  rw [pow32_squares]
  rw [sqr_366 z hz, sqr_58 z hz, sqr_358 z hz, sqr_122 z hz, sqr_494 z hz]

lemma sigma_121 : sigmaM (mat512% z 147 366 113 113) = (mat512% z 65 11 330 330) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_147 z hz
  · exact power32_366 z hz
  · exact power32_113 z hz
  · exact power32_113 z hz

lemma power32_11 : (gf512% z 11)^32 = (gf512% z 58) := by
  rw [pow32_squares]
  rw [sqr_11 z hz, sqr_69 z hz, sqr_153 z hz, sqr_368 z hz, sqr_366 z hz]

lemma sigma_122 : sigmaM (mat512% z 65 11 330 330) = (mat512% z 308 58 427 427) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_65 z hz
  · exact power32_11 z hz
  · exact power32_330 z hz
  · exact power32_330 z hz

lemma power32_58 : (gf512% z 58)^32 = (gf512% z 69) := by
  rw [pow32_squares]
  rw [sqr_58 z hz, sqr_358 z hz, sqr_122 z hz, sqr_494 z hz, sqr_11 z hz]

lemma sigma_123 : sigmaM (mat512% z 308 58 427 427) = (mat512% z 137 69 8 8) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_308 z hz
  · exact power32_58 z hz
  · exact power32_427 z hz
  · exact power32_427 z hz

lemma power32_69 : (gf512% z 69)^32 = (gf512% z 358) := by
  rw [pow32_squares]
  rw [sqr_69 z hz, sqr_153 z hz, sqr_368 z hz, sqr_366 z hz, sqr_58 z hz]

lemma sigma_124 : sigmaM (mat512% z 137 69 8 8) = (mat512% z 502 358 146 146) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_137 z hz
  · exact power32_69 z hz
  · exact power32_8 z hz
  · exact power32_8 z hz

lemma power32_358 : (gf512% z 358)^32 = (gf512% z 153) := by
  rw [pow32_squares]
  rw [sqr_358 z hz, sqr_122 z hz, sqr_494 z hz, sqr_11 z hz, sqr_69 z hz]

lemma sigma_125 : sigmaM (mat512% z 502 358 146 146) = (mat512% z 112 153 64 64) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_502 z hz
  · exact power32_358 z hz
  · exact power32_146 z hz
  · exact power32_146 z hz

lemma power32_153 : (gf512% z 153)^32 = (gf512% z 122) := by
  rw [pow32_squares]
  rw [sqr_153 z hz, sqr_368 z hz, sqr_366 z hz, sqr_58 z hz, sqr_358 z hz]

lemma sigma_126 : sigmaM (mat512% z 112 153 64 64) = (mat512% z 331 122 309 309) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_112 z hz
  · exact power32_153 z hz
  · exact power32_64 z hz
  · exact power32_64 z hz

lemma power32_122 : (gf512% z 122)^32 = (gf512% z 368) := by
  rw [pow32_squares]
  rw [sqr_122 z hz, sqr_494 z hz, sqr_11 z hz, sqr_69 z hz, sqr_153 z hz]

lemma sigma_127 : sigmaM (mat512% z 331 122 309 309) = (mat512% z 426 368 136 136) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_331 z hz
  · exact power32_122 z hz
  · exact power32_309 z hz
  · exact power32_309 z hz

lemma product_136 : (mat512% z 9 494 503 503) * (mat512% z 241 305 241 503) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 9)*(gf512% z 241) + (gf512% z 494)*(gf512% z 241) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 86))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 9)*(gf512% z 305) + (gf512% z 494)*(gf512% z 503) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 163))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 503)*(gf512% z 241) + (gf512% z 503)*(gf512% z 241) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 503)*(gf512% z 305) + (gf512% z 503)*(gf512% z 503) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 67))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_137 : (mat512% z 147 366 113 113) * (mat512% z 79 197 341 19) = (mat512% z 241 305 241 503) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 147)*(gf512% z 79) + (gf512% z 366)*(gf512% z 341) = (gf512% z 241)
    apply cert_eq z hz (Q := (gf512% z 134))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 147)*(gf512% z 197) + (gf512% z 366)*(gf512% z 19) = (gf512% z 305)
    apply cert_eq z hz (Q := (gf512% z 60))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 113)*(gf512% z 79) + (gf512% z 113)*(gf512% z 341) = (gf512% z 241)
    apply cert_eq z hz (Q := (gf512% z 59))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 113)*(gf512% z 197) + (gf512% z 113)*(gf512% z 19) = (gf512% z 503)
    apply cert_eq z hz (Q := (gf512% z 17))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_138 : (mat512% z 65 11 330 330) * (mat512% z 414 465 258 163) = (mat512% z 79 197 341 19) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 65)*(gf512% z 414) + (gf512% z 11)*(gf512% z 258) = (gf512% z 79)
    apply cert_eq z hz (Q := (gf512% z 55))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 65)*(gf512% z 465) + (gf512% z 11)*(gf512% z 163) = (gf512% z 197)
    apply cert_eq z hz (Q := (gf512% z 57))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 330)*(gf512% z 414) + (gf512% z 330)*(gf512% z 258) = (gf512% z 341)
    apply cert_eq z hz (Q := (gf512% z 93))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 330)*(gf512% z 465) + (gf512% z 330)*(gf512% z 163) = (gf512% z 19)
    apply cert_eq z hz (Q := (gf512% z 151))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_139 : (mat512% z 308 58 427 427) * (mat512% z 141 424 171 386) = (mat512% z 414 465 258 163) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 308)*(gf512% z 141) + (gf512% z 58)*(gf512% z 171) = (gf512% z 414)
    apply cert_eq z hz (Q := (gf512% z 68))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 308)*(gf512% z 424) + (gf512% z 58)*(gf512% z 386) = (gf512% z 465)
    apply cert_eq z hz (Q := (gf512% z 213))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 427)*(gf512% z 141) + (gf512% z 427)*(gf512% z 171) = (gf512% z 258)
    apply cert_eq z hz (Q := (gf512% z 24))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 427)*(gf512% z 424) + (gf512% z 427)*(gf512% z 386) = (gf512% z 163)
    apply cert_eq z hz (Q := (gf512% z 29))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_140 : (mat512% z 137 69 8 8) * (mat512% z 286 134 461 50) = (mat512% z 141 424 171 386) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 137)*(gf512% z 286) + (gf512% z 69)*(gf512% z 461) = (gf512% z 141)
    apply cert_eq z hz (Q := (gf512% z 122))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 137)*(gf512% z 134) + (gf512% z 69)*(gf512% z 50) = (gf512% z 424)
    apply cert_eq z hz (Q := (gf512% z 36))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 8)*(gf512% z 286) + (gf512% z 8)*(gf512% z 461) = (gf512% z 171)
    apply cert_eq z hz (Q := (gf512% z 3))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 8)*(gf512% z 134) + (gf512% z 8)*(gf512% z 50) = (gf512% z 386)
    apply cert_eq z hz (Q := (gf512% z 2))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_141 : (mat512% z 502 358 146 146) * (mat512% z 56 57 287 21) = (mat512% z 286 134 461 50) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 502)*(gf512% z 56) + (gf512% z 358)*(gf512% z 287) = (gf512% z 286)
    apply cert_eq z hz (Q := (gf512% z 172))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 502)*(gf512% z 57) + (gf512% z 358)*(gf512% z 21) = (gf512% z 134)
    apply cert_eq z hz (Q := (gf512% z 30))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 146)*(gf512% z 56) + (gf512% z 146)*(gf512% z 287) = (gf512% z 461)
    apply cert_eq z hz (Q := (gf512% z 67))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 146)*(gf512% z 57) + (gf512% z 146)*(gf512% z 21) = (gf512% z 50)
    apply cert_eq z hz (Q := (gf512% z 10))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_142 : (mat512% z 112 153 64 64) * (mat512% z 241 217 390 240) = (mat512% z 56 57 287 21) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 112)*(gf512% z 241) + (gf512% z 153)*(gf512% z 390) = (gf512% z 56)
    apply cert_eq z hz (Q := (gf512% z 126))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 112)*(gf512% z 217) + (gf512% z 153)*(gf512% z 240) = (gf512% z 57)
    apply cert_eq z hz (Q := (gf512% z 41))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 64)*(gf512% z 241) + (gf512% z 64)*(gf512% z 390) = (gf512% z 287)
    apply cert_eq z hz (Q := (gf512% z 47))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 64)*(gf512% z 217) + (gf512% z 64)*(gf512% z 240) = (gf512% z 21)
    apply cert_eq z hz (Q := (gf512% z 5))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_143 : (mat512% z 331 122 309 309) * (mat512% z 426 368 136 136) = (mat512% z 241 217 390 240) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 331)*(gf512% z 426) + (gf512% z 122)*(gf512% z 136) = (gf512% z 241)
    apply cert_eq z hz (Q := (gf512% z 255))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 331)*(gf512% z 368) + (gf512% z 122)*(gf512% z 136) = (gf512% z 217)
    apply cert_eq z hz (Q := (gf512% z 137))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 309)*(gf512% z 426) + (gf512% z 309)*(gf512% z 136) = (gf512% z 390)
    apply cert_eq z hz (Q := (gf512% z 140))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 309)*(gf512% z 368) + (gf512% z 309)*(gf512% z 136) = (gf512% z 240)
    apply cert_eq z hz (Q := (gf512% z 232))
    ring_nf <;> reduce_mod_char! <;> ring

lemma norm_15 : semilinearNorm 9 (mat512% z 9 494 503 503) = 1 := by
  have h8 : semilinearNorm 1 (mat512% z 426 368 136 136) = (mat512% z 426 368 136 136) := by simp [semilinearNorm]
  have h7 : semilinearNorm 2 (mat512% z 331 122 309 309) = (mat512% z 241 217 390 240) := by
    change (mat512% z 331 122 309 309) * semilinearNorm 1 (sigmaM (mat512% z 331 122 309 309)) = _
    rw [sigma_127 z hz, h8]
    exact product_143 z hz
  have h6 : semilinearNorm 3 (mat512% z 112 153 64 64) = (mat512% z 56 57 287 21) := by
    change (mat512% z 112 153 64 64) * semilinearNorm 2 (sigmaM (mat512% z 112 153 64 64)) = _
    rw [sigma_126 z hz, h7]
    exact product_142 z hz
  have h5 : semilinearNorm 4 (mat512% z 502 358 146 146) = (mat512% z 286 134 461 50) := by
    change (mat512% z 502 358 146 146) * semilinearNorm 3 (sigmaM (mat512% z 502 358 146 146)) = _
    rw [sigma_125 z hz, h6]
    exact product_141 z hz
  have h4 : semilinearNorm 5 (mat512% z 137 69 8 8) = (mat512% z 141 424 171 386) := by
    change (mat512% z 137 69 8 8) * semilinearNorm 4 (sigmaM (mat512% z 137 69 8 8)) = _
    rw [sigma_124 z hz, h5]
    exact product_140 z hz
  have h3 : semilinearNorm 6 (mat512% z 308 58 427 427) = (mat512% z 414 465 258 163) := by
    change (mat512% z 308 58 427 427) * semilinearNorm 5 (sigmaM (mat512% z 308 58 427 427)) = _
    rw [sigma_123 z hz, h4]
    exact product_139 z hz
  have h2 : semilinearNorm 7 (mat512% z 65 11 330 330) = (mat512% z 79 197 341 19) := by
    change (mat512% z 65 11 330 330) * semilinearNorm 6 (sigmaM (mat512% z 65 11 330 330)) = _
    rw [sigma_122 z hz, h3]
    exact product_138 z hz
  have h1 : semilinearNorm 8 (mat512% z 147 366 113 113) = (mat512% z 241 305 241 503) := by
    change (mat512% z 147 366 113 113) * semilinearNorm 7 (sigmaM (mat512% z 147 366 113 113)) = _
    rw [sigma_121 z hz, h2]
    exact product_137 z hz
  have h0 : semilinearNorm 9 (mat512% z 9 494 503 503) = (mat512% z 1 0 0 1) := by
    change (mat512% z 9 494 503 503) * semilinearNorm 8 (sigmaM (mat512% z 9 494 503 503)) = _
    rw [sigma_120 z hz, h1]
    exact product_136 z hz
  simpa only [code_identity] using h0

lemma mtrace_31 : (mat512% z 9 494 503 503).trace = (gf512% z 510) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 9)+(gf512% z 503) = (gf512% z 510)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma mdet_30 : (mat512% z 9 494 503 503).det = (gf512% z 197) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 9)*(gf512% z 503) - (gf512% z 494)*(gf512% z 503) = (gf512% z 197)
  apply cert_eq z hz (Q := (gf512% z 160))
  ring_nf <;> reduce_mod_char! <;> ring

lemma elliptic_30 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 9 494 503 503) := by
  have ht : (gf512% z 510)*(gf512% z 79) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 59))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 197)*(gf512% z 79)^2 = (gf512% z 133) := by
    apply cert_eq z hz (Q := (gf512% z 1540))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_31 z hz, mdet_30 z hz]
  apply no_quadratic_root hK (gf512% z 510) (gf512% z 197) (gf512% z 79) ht
  rw [hd]
  exact atr_14 z hz

lemma mdet_31 : (mat512% z 410 504 225 411).det = (gf512% z 335) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 410)*(gf512% z 411) - (gf512% z 504)*(gf512% z 225) = (gf512% z 335)
  apply cert_eq z hz (Q := (gf512% z 249))
  ring_nf <;> reduce_mod_char! <;> ring

lemma elliptic_31 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 410 504 225 411) := by
  have ht : (gf512% z 1)*(gf512% z 1) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 335)*(gf512% z 1)^2 = (gf512% z 335) := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_30 z hz, mdet_31 z hz]
  apply no_quadratic_root hK (gf512% z 1) (gf512% z 335) (gf512% z 1) ht
  rw [hd]
  exact atr_9 z hz

lemma good_15 (hK : ∀ x : K, x^512 = x) : Good (mat512% z 9 494 503 503) := by
  unfold Good
  rw [sigma_120 z hz, product_135 z hz]
  refine ⟨?_, elliptic_30 z hz hK, norm_15 z hz, elliptic_31 z hz hK⟩
  simpa using mtrace_30 z hz

#check good_15

lemma product_144 : (mat512% z 1 0 0 1) * (mat512% z 1 0 0 1) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 1)*(gf512% z 1) + (gf512% z 0)*(gf512% z 0) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 1)*(gf512% z 0) + (gf512% z 0)*(gf512% z 1) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 1) + (gf512% z 1)*(gf512% z 0) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 0) + (gf512% z 1)*(gf512% z 1) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_145 : (mat512% z 6 26 0 6) * (mat512% z 248 86 0 248) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 6)*(gf512% z 248) + (gf512% z 26)*(gf512% z 0) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 6)*(gf512% z 86) + (gf512% z 26)*(gf512% z 248) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 4))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 248) + (gf512% z 6)*(gf512% z 0) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 86) + (gf512% z 6)*(gf512% z 248) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_146 : (mat512% z 248 86 0 248) * (mat512% z 6 26 0 6) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 248)*(gf512% z 6) + (gf512% z 86)*(gf512% z 0) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 248)*(gf512% z 26) + (gf512% z 86)*(gf512% z 6) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 4))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 6) + (gf512% z 248)*(gf512% z 0) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 26) + (gf512% z 248)*(gf512% z 6) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_147 : (mat512% z 99 84 0 99) * (mat512% z 511 130 0 511) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 99)*(gf512% z 511) + (gf512% z 84)*(gf512% z 0) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 32))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 99)*(gf512% z 130) + (gf512% z 84)*(gf512% z 511) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 42))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 511) + (gf512% z 99)*(gf512% z 0) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 130) + (gf512% z 99)*(gf512% z 511) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 32))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_148 : (mat512% z 511 130 0 511) * (mat512% z 99 84 0 99) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 511)*(gf512% z 99) + (gf512% z 130)*(gf512% z 0) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 32))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 511)*(gf512% z 84) + (gf512% z 130)*(gf512% z 99) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 42))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 99) + (gf512% z 511)*(gf512% z 0) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 84) + (gf512% z 511)*(gf512% z 99) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 32))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_149 : (mat512% z 285 416 0 285) * (mat512% z 159 474 0 159) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 285)*(gf512% z 159) + (gf512% z 416)*(gf512% z 0) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 74))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 285)*(gf512% z 474) + (gf512% z 416)*(gf512% z 159) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 130))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 159) + (gf512% z 285)*(gf512% z 0) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 474) + (gf512% z 285)*(gf512% z 159) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 74))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_150 : (mat512% z 159 474 0 159) * (mat512% z 285 416 0 285) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 159)*(gf512% z 285) + (gf512% z 474)*(gf512% z 0) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 74))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 159)*(gf512% z 416) + (gf512% z 474)*(gf512% z 285) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 130))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 285) + (gf512% z 159)*(gf512% z 0) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 416) + (gf512% z 159)*(gf512% z 285) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 74))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_151 : (mat512% z 0 118 486 75) * (mat512% z 248 344 100 0) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 0)*(gf512% z 248) + (gf512% z 118)*(gf512% z 100) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 9))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 344) + (gf512% z 118)*(gf512% z 0) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 486)*(gf512% z 248) + (gf512% z 75)*(gf512% z 100) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 92))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 486)*(gf512% z 344) + (gf512% z 75)*(gf512% z 0) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 193))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_152 : (mat512% z 0 118 375 488) * (mat512% z 248 316 100 0) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 0)*(gf512% z 248) + (gf512% z 118)*(gf512% z 100) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 9))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 316) + (gf512% z 118)*(gf512% z 0) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 375)*(gf512% z 248) + (gf512% z 488)*(gf512% z 100) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 72))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 375)*(gf512% z 316) + (gf512% z 488)*(gf512% z 0) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 165))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_153 : (mat512% z 486 475 486 429) * (mat512% z 156 452 100 100) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 486)*(gf512% z 156) + (gf512% z 475)*(gf512% z 100) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 85))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 486)*(gf512% z 452) + (gf512% z 475)*(gf512% z 100) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 148))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 486)*(gf512% z 156) + (gf512% z 429)*(gf512% z 100) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 92))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 486)*(gf512% z 452) + (gf512% z 429)*(gf512% z 100) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 157))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_154 : (mat512% z 375 233 375 159) * (mat512% z 156 416 100 100) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 375)*(gf512% z 156) + (gf512% z 233)*(gf512% z 100) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 65))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 375)*(gf512% z 416) + (gf512% z 233)*(gf512% z 100) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 228))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 375)*(gf512% z 156) + (gf512% z 159)*(gf512% z 100) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 72))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 375)*(gf512% z 416) + (gf512% z 159)*(gf512% z 100) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 237))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_155 : (mat512% z 1 0 0 1) * (mat512% z 248 344 100 0) = (mat512% z 248 344 100 0) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 1)*(gf512% z 248) + (gf512% z 0)*(gf512% z 100) = (gf512% z 248)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 1)*(gf512% z 344) + (gf512% z 0)*(gf512% z 0) = (gf512% z 344)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 248) + (gf512% z 1)*(gf512% z 100) = (gf512% z 100)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 344) + (gf512% z 1)*(gf512% z 0) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_156 : (mat512% z 1 0 0 1) * (mat512% z 248 316 100 0) = (mat512% z 248 316 100 0) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 1)*(gf512% z 248) + (gf512% z 0)*(gf512% z 100) = (gf512% z 248)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 1)*(gf512% z 316) + (gf512% z 0)*(gf512% z 0) = (gf512% z 316)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 248) + (gf512% z 1)*(gf512% z 100) = (gf512% z 100)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 316) + (gf512% z 1)*(gf512% z 0) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_157 : (mat512% z 1 0 0 1) * (mat512% z 156 452 100 100) = (mat512% z 156 452 100 100) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 1)*(gf512% z 156) + (gf512% z 0)*(gf512% z 100) = (gf512% z 156)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 1)*(gf512% z 452) + (gf512% z 0)*(gf512% z 100) = (gf512% z 452)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 156) + (gf512% z 1)*(gf512% z 100) = (gf512% z 100)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 452) + (gf512% z 1)*(gf512% z 100) = (gf512% z 100)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_158 : (mat512% z 1 0 0 1) * (mat512% z 156 416 100 100) = (mat512% z 156 416 100 100) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 1)*(gf512% z 156) + (gf512% z 0)*(gf512% z 100) = (gf512% z 156)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 1)*(gf512% z 416) + (gf512% z 0)*(gf512% z 100) = (gf512% z 416)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 156) + (gf512% z 1)*(gf512% z 100) = (gf512% z 100)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 416) + (gf512% z 1)*(gf512% z 100) = (gf512% z 100)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_159 : (mat512% z 248 86 0 248) * (mat512% z 248 344 100 0) = (mat512% z 316 100 481 0) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 248)*(gf512% z 248) + (gf512% z 86)*(gf512% z 100) = (gf512% z 316)
    apply cert_eq z hz (Q := (gf512% z 36))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 248)*(gf512% z 344) + (gf512% z 86)*(gf512% z 0) = (gf512% z 100)
    apply cert_eq z hz (Q := (gf512% z 100))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 248) + (gf512% z 248)*(gf512% z 100) = (gf512% z 481)
    apply cert_eq z hz (Q := (gf512% z 17))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 344) + (gf512% z 248)*(gf512% z 0) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_160 : (mat512% z 248 86 0 248) * (mat512% z 248 316 100 0) = (mat512% z 316 389 481 0) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 248)*(gf512% z 248) + (gf512% z 86)*(gf512% z 100) = (gf512% z 316)
    apply cert_eq z hz (Q := (gf512% z 36))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 248)*(gf512% z 316) + (gf512% z 86)*(gf512% z 0) = (gf512% z 389)
    apply cert_eq z hz (Q := (gf512% z 117))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 248) + (gf512% z 248)*(gf512% z 100) = (gf512% z 481)
    apply cert_eq z hz (Q := (gf512% z 17))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 316) + (gf512% z 248)*(gf512% z 0) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_161 : (mat512% z 248 86 0 248) * (mat512% z 156 452 100 100) = (mat512% z 221 185 481 481) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 248)*(gf512% z 156) + (gf512% z 86)*(gf512% z 100) = (gf512% z 221)
    apply cert_eq z hz (Q := (gf512% z 53))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 248)*(gf512% z 452) + (gf512% z 86)*(gf512% z 100) = (gf512% z 185)
    apply cert_eq z hz (Q := (gf512% z 81))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 156) + (gf512% z 248)*(gf512% z 100) = (gf512% z 481)
    apply cert_eq z hz (Q := (gf512% z 17))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 452) + (gf512% z 248)*(gf512% z 100) = (gf512% z 481)
    apply cert_eq z hz (Q := (gf512% z 17))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_162 : (mat512% z 248 86 0 248) * (mat512% z 156 416 100 100) = (mat512% z 221 344 481 481) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 248)*(gf512% z 156) + (gf512% z 86)*(gf512% z 100) = (gf512% z 221)
    apply cert_eq z hz (Q := (gf512% z 53))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 248)*(gf512% z 416) + (gf512% z 86)*(gf512% z 100) = (gf512% z 344)
    apply cert_eq z hz (Q := (gf512% z 64))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 156) + (gf512% z 248)*(gf512% z 100) = (gf512% z 481)
    apply cert_eq z hz (Q := (gf512% z 17))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 416) + (gf512% z 248)*(gf512% z 100) = (gf512% z 481)
    apply cert_eq z hz (Q := (gf512% z 17))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_163 : (mat512% z 511 130 0 511) * (mat512% z 248 344 100 0) = (mat512% z 492 230 478 0) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 511)*(gf512% z 248) + (gf512% z 130)*(gf512% z 100) = (gf512% z 492)
    apply cert_eq z hz (Q := (gf512% z 76))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 511)*(gf512% z 344) + (gf512% z 130)*(gf512% z 0) = (gf512% z 230)
    apply cert_eq z hz (Q := (gf512% z 206))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 248) + (gf512% z 511)*(gf512% z 100) = (gf512% z 478)
    apply cert_eq z hz (Q := (gf512% z 34))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 344) + (gf512% z 511)*(gf512% z 0) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_164 : (mat512% z 511 130 0 511) * (mat512% z 248 316 100 0) = (mat512% z 492 312 478 0) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 511)*(gf512% z 248) + (gf512% z 130)*(gf512% z 100) = (gf512% z 492)
    apply cert_eq z hz (Q := (gf512% z 76))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 511)*(gf512% z 316) + (gf512% z 130)*(gf512% z 0) = (gf512% z 312)
    apply cert_eq z hz (Q := (gf512% z 236))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 248) + (gf512% z 511)*(gf512% z 100) = (gf512% z 478)
    apply cert_eq z hz (Q := (gf512% z 34))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 316) + (gf512% z 511)*(gf512% z 0) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_165 : (mat512% z 511 130 0 511) * (mat512% z 156 452 100 100) = (mat512% z 50 212 478 478) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 511)*(gf512% z 156) + (gf512% z 130)*(gf512% z 100) = (gf512% z 50)
    apply cert_eq z hz (Q := (gf512% z 110))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 511)*(gf512% z 452) + (gf512% z 130)*(gf512% z 100) = (gf512% z 212)
    apply cert_eq z hz (Q := (gf512% z 160))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 156) + (gf512% z 511)*(gf512% z 100) = (gf512% z 478)
    apply cert_eq z hz (Q := (gf512% z 34))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 452) + (gf512% z 511)*(gf512% z 100) = (gf512% z 478)
    apply cert_eq z hz (Q := (gf512% z 34))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_166 : (mat512% z 511 130 0 511) * (mat512% z 156 416 100 100) = (mat512% z 50 266 478 478) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 511)*(gf512% z 156) + (gf512% z 130)*(gf512% z 100) = (gf512% z 50)
    apply cert_eq z hz (Q := (gf512% z 110))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 511)*(gf512% z 416) + (gf512% z 130)*(gf512% z 100) = (gf512% z 266)
    apply cert_eq z hz (Q := (gf512% z 130))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 156) + (gf512% z 511)*(gf512% z 100) = (gf512% z 478)
    apply cert_eq z hz (Q := (gf512% z 34))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 416) + (gf512% z 511)*(gf512% z 100) = (gf512% z 478)
    apply cert_eq z hz (Q := (gf512% z 34))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_167 : (mat512% z 159 474 0 159) * (mat512% z 248 344 100 0) = (mat512% z 510 16 503 0) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 159)*(gf512% z 248) + (gf512% z 474)*(gf512% z 100) = (gf512% z 510)
    apply cert_eq z hz (Q := (gf512% z 30))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 159)*(gf512% z 344) + (gf512% z 474)*(gf512% z 0) = (gf512% z 16)
    apply cert_eq z hz (Q := (gf512% z 88))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 248) + (gf512% z 159)*(gf512% z 100) = (gf512% z 503)
    apply cert_eq z hz (Q := (gf512% z 27))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 344) + (gf512% z 159)*(gf512% z 0) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_168 : (mat512% z 159 474 0 159) * (mat512% z 248 316 100 0) = (mat512% z 510 487 503 0) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 159)*(gf512% z 248) + (gf512% z 474)*(gf512% z 100) = (gf512% z 510)
    apply cert_eq z hz (Q := (gf512% z 30))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 159)*(gf512% z 316) + (gf512% z 474)*(gf512% z 0) = (gf512% z 487)
    apply cert_eq z hz (Q := (gf512% z 67))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 248) + (gf512% z 159)*(gf512% z 100) = (gf512% z 503)
    apply cert_eq z hz (Q := (gf512% z 27))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 316) + (gf512% z 159)*(gf512% z 0) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_169 : (mat512% z 159 474 0 159) * (mat512% z 156 452 100 100) = (mat512% z 9 25 503 503) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 159)*(gf512% z 156) + (gf512% z 474)*(gf512% z 100) = (gf512% z 9)
    apply cert_eq z hz (Q := (gf512% z 5))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 159)*(gf512% z 452) + (gf512% z 474)*(gf512% z 100) = (gf512% z 25)
    apply cert_eq z hz (Q := (gf512% z 93))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 156) + (gf512% z 159)*(gf512% z 100) = (gf512% z 503)
    apply cert_eq z hz (Q := (gf512% z 27))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 452) + (gf512% z 159)*(gf512% z 100) = (gf512% z 503)
    apply cert_eq z hz (Q := (gf512% z 27))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_170 : (mat512% z 159 474 0 159) * (mat512% z 156 416 100 100) = (mat512% z 9 494 503 503) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 159)*(gf512% z 156) + (gf512% z 474)*(gf512% z 100) = (gf512% z 9)
    apply cert_eq z hz (Q := (gf512% z 5))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 159)*(gf512% z 416) + (gf512% z 474)*(gf512% z 100) = (gf512% z 494)
    apply cert_eq z hz (Q := (gf512% z 70))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 156) + (gf512% z 159)*(gf512% z 100) = (gf512% z 503)
    apply cert_eq z hz (Q := (gf512% z 27))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 0)*(gf512% z 416) + (gf512% z 159)*(gf512% z 100) = (gf512% z 503)
    apply cert_eq z hz (Q := (gf512% z 27))
    ring_nf <;> reduce_mod_char! <;> ring

def rows : Fin 4 → M (K := K) := ![(mat512% z 1 0 0 1), (mat512% z 6 26 0 6), (mat512% z 99 84 0 99), (mat512% z 285 416 0 285)]

def rowInv : Fin 4 → M (K := K) := ![(mat512% z 1 0 0 1), (mat512% z 248 86 0 248), (mat512% z 511 130 0 511), (mat512% z 159 474 0 159)]

def columns : Fin 4 → M (K := K) := ![(mat512% z 248 344 100 0), (mat512% z 248 316 100 0), (mat512% z 156 452 100 100), (mat512% z 156 416 100 100)]

def colInv : Fin 4 → M (K := K) := ![(mat512% z 0 118 486 75), (mat512% z 0 118 375 488), (mat512% z 486 475 486 429), (mat512% z 375 233 375 159)]

lemma rows_inverse (i : Fin 4) : rows z i * rowInv z i = 1 ∧ rowInv z i * rows z i = 1 := by
  fin_cases i
  · constructor
    · simpa only [rows, rowInv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, code_identity] using product_144 z hz
    · simpa only [rows, rowInv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, code_identity] using product_144 z hz
  · constructor
    · simpa only [rows, rowInv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, code_identity] using product_145 z hz
    · simpa only [rows, rowInv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, code_identity] using product_146 z hz
  · constructor
    · simpa only [rows, rowInv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, code_identity] using product_147 z hz
    · simpa only [rows, rowInv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, code_identity] using product_148 z hz
  · constructor
    · simpa only [rows, rowInv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, code_identity] using product_149 z hz
    · simpa only [rows, rowInv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, code_identity] using product_150 z hz

lemma rows_injective : Function.Injective (rows z) := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 1) = (gf512% z 6) at he
    have hn : ((gf512% z 1)-(gf512% z 6))*(gf512% z 358) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 3))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 1)-(gf512% z 6) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 1) = (gf512% z 99) at he
    have hn : ((gf512% z 1)-(gf512% z 99))*(gf512% z 78) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 13))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 1)-(gf512% z 99) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 1) = (gf512% z 285) at he
    have hn : ((gf512% z 1)-(gf512% z 285))*(gf512% z 254) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 121))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 1)-(gf512% z 285) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 6) = (gf512% z 1) at he
    have hn : ((gf512% z 6)-(gf512% z 1))*(gf512% z 358) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 3))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 6)-(gf512% z 1) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · rfl
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 6) = (gf512% z 99) at he
    have hn : ((gf512% z 6)-(gf512% z 99))*(gf512% z 271) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 50))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 6)-(gf512% z 99) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 6) = (gf512% z 285) at he
    have hn : ((gf512% z 6)-(gf512% z 285))*(gf512% z 392) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 201))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 6)-(gf512% z 285) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 99) = (gf512% z 1) at he
    have hn : ((gf512% z 99)-(gf512% z 1))*(gf512% z 78) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 13))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 99)-(gf512% z 1) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 99) = (gf512% z 6) at he
    have hn : ((gf512% z 99)-(gf512% z 6))*(gf512% z 271) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 50))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 99)-(gf512% z 6) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · rfl
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 99) = (gf512% z 285) at he
    have hn : ((gf512% z 99)-(gf512% z 285))*(gf512% z 492) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 217))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 99)-(gf512% z 285) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 285) = (gf512% z 1) at he
    have hn : ((gf512% z 285)-(gf512% z 1))*(gf512% z 254) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 121))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 285)-(gf512% z 1) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 285) = (gf512% z 6) at he
    have hn : ((gf512% z 285)-(gf512% z 6))*(gf512% z 392) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 201))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 285)-(gf512% z 6) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 285) = (gf512% z 99) at he
    have hn : ((gf512% z 285)-(gf512% z 99))*(gf512% z 492) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 217))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 285)-(gf512% z 99) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · rfl

lemma columns_inverse (i : Fin 4) : columns z i * colInv z i = 1 ∧ colInv z i * columns z i = 1 := by
  fin_cases i
  · constructor
    · simpa only [columns, colInv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, code_identity] using product_1 z hz
    · simpa only [columns, colInv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, code_identity] using product_151 z hz
  · constructor
    · simpa only [columns, colInv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, code_identity] using product_10 z hz
    · simpa only [columns, colInv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, code_identity] using product_152 z hz
  · constructor
    · simpa only [columns, colInv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, code_identity] using product_19 z hz
    · simpa only [columns, colInv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, code_identity] using product_153 z hz
  · constructor
    · simpa only [columns, colInv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, code_identity] using product_28 z hz
    · simpa only [columns, colInv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, code_identity] using product_154 z hz

lemma columns_injective : Function.Injective (columns z) := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 1) h
    change (gf512% z 344) = (gf512% z 316) at he
    have hn : ((gf512% z 344)-(gf512% z 316))*(gf512% z 118) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 9))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 344)-(gf512% z 316) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 248) = (gf512% z 156) at he
    have hn : ((gf512% z 248)-(gf512% z 156))*(gf512% z 118) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 9))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 248)-(gf512% z 156) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 248) = (gf512% z 156) at he
    have hn : ((gf512% z 248)-(gf512% z 156))*(gf512% z 118) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 9))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 248)-(gf512% z 156) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 1) h
    change (gf512% z 316) = (gf512% z 344) at he
    have hn : ((gf512% z 316)-(gf512% z 344))*(gf512% z 118) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 9))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 316)-(gf512% z 344) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · rfl
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 248) = (gf512% z 156) at he
    have hn : ((gf512% z 248)-(gf512% z 156))*(gf512% z 118) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 9))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 248)-(gf512% z 156) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 248) = (gf512% z 156) at he
    have hn : ((gf512% z 248)-(gf512% z 156))*(gf512% z 118) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 9))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 248)-(gf512% z 156) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 156) = (gf512% z 248) at he
    have hn : ((gf512% z 156)-(gf512% z 248))*(gf512% z 118) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 9))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 156)-(gf512% z 248) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 156) = (gf512% z 248) at he
    have hn : ((gf512% z 156)-(gf512% z 248))*(gf512% z 118) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 9))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 156)-(gf512% z 248) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · rfl
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 1) h
    change (gf512% z 452) = (gf512% z 416) at he
    have hn : ((gf512% z 452)-(gf512% z 416))*(gf512% z 118) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 9))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 452)-(gf512% z 416) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 156) = (gf512% z 248) at he
    have hn : ((gf512% z 156)-(gf512% z 248))*(gf512% z 118) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 9))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 156)-(gf512% z 248) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 0) h
    change (gf512% z 156) = (gf512% z 248) at he
    have hn : ((gf512% z 156)-(gf512% z 248))*(gf512% z 118) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 9))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 156)-(gf512% z 248) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · exfalso
    have he := congrArg (fun A : M (K := K) => A 0 1) h
    change (gf512% z 416) = (gf512% z 452) at he
    have hn : ((gf512% z 416)-(gf512% z 452))*(gf512% z 118) = 1 := by
      apply cert_eq z hz (Q := (gf512% z 9))
      ring_nf <;> reduce_mod_char! <;> ring
    have hdiff : (gf512% z 416)-(gf512% z 452) = 0 := sub_eq_zero.mpr he
    rw [hdiff, zero_mul] at hn
    exact zero_ne_one hn
  · rfl

theorem copy (hK : ∀ x : K, x^512 = x) :
    (completeBipartiteGraph (Fin 4) (Fin 4)) ⊑ graph (K := K) := by
  apply copy_of_matrices (rows z) (rowInv z) (columns z) (colInv z)
    (rows_inverse z hz) (columns_inverse z hz)
    (rows_injective z hz) (columns_injective z hz)
  intro i j
  fin_cases i <;> fin_cases j
  · change Good ((mat512% z 1 0 0 1) * (mat512% z 248 344 100 0))
    rw [product_155 z hz]
    exact good_0 z hz hK
  · change Good ((mat512% z 1 0 0 1) * (mat512% z 248 316 100 0))
    rw [product_156 z hz]
    exact good_1 z hz hK
  · change Good ((mat512% z 1 0 0 1) * (mat512% z 156 452 100 100))
    rw [product_157 z hz]
    exact good_2 z hz hK
  · change Good ((mat512% z 1 0 0 1) * (mat512% z 156 416 100 100))
    rw [product_158 z hz]
    exact good_3 z hz hK
  · change Good ((mat512% z 248 86 0 248) * (mat512% z 248 344 100 0))
    rw [product_159 z hz]
    exact good_4 z hz hK
  · change Good ((mat512% z 248 86 0 248) * (mat512% z 248 316 100 0))
    rw [product_160 z hz]
    exact good_5 z hz hK
  · change Good ((mat512% z 248 86 0 248) * (mat512% z 156 452 100 100))
    rw [product_161 z hz]
    exact good_6 z hz hK
  · change Good ((mat512% z 248 86 0 248) * (mat512% z 156 416 100 100))
    rw [product_162 z hz]
    exact good_7 z hz hK
  · change Good ((mat512% z 511 130 0 511) * (mat512% z 248 344 100 0))
    rw [product_163 z hz]
    exact good_8 z hz hK
  · change Good ((mat512% z 511 130 0 511) * (mat512% z 248 316 100 0))
    rw [product_164 z hz]
    exact good_9 z hz hK
  · change Good ((mat512% z 511 130 0 511) * (mat512% z 156 452 100 100))
    rw [product_165 z hz]
    exact good_10 z hz hK
  · change Good ((mat512% z 511 130 0 511) * (mat512% z 156 416 100 100))
    rw [product_166 z hz]
    exact good_11 z hz hK
  · change Good ((mat512% z 159 474 0 159) * (mat512% z 248 344 100 0))
    rw [product_167 z hz]
    exact good_12 z hz hK
  · change Good ((mat512% z 159 474 0 159) * (mat512% z 248 316 100 0))
    rw [product_168 z hz]
    exact good_13 z hz hK
  · change Good ((mat512% z 159 474 0 159) * (mat512% z 156 452 100 100))
    rw [product_169 z hz]
    exact good_14 z hz hK
  · change Good ((mat512% z 159 474 0 159) * (mat512% z 156 416 100 100))
    rw [product_170 z hz]
    exact good_15 z hz hK

omit hz in
/-- The refined graph has an actual K44 over a field of cardinality 512. -/
theorem actual_copy :
    (completeBipartiteGraph (Fin 4) (Fin 4)) ⊑
      graph (K := Erdos714BothCertificate.F) := by
  obtain ⟨z, hz⟩ := Erdos714BothCertificate.exists_modulus_root
  have hp : z^9+z^4+1 = 0 := by
    simpa only [Erdos714BothCertificate.modulus, Polynomial.eval₂_add,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one] using hz
  exact copy z hp Erdos714BothCertificate.field_pow

omit hz in
theorem actual_not_free :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (K := Erdos714BothCertificate.F)) := fun h => h actual_copy

#print axioms copy
#print axioms actual_copy
#print axioms actual_not_free
end Erdos714BothData
