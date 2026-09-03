import Submission.SemilinearBothModel

/-!
# An actual K44 in the doubly elliptic identity-norm semilinear graph

Every scalar and matrix identity below is kernel checked. External computations
provided the finite certificate, not proof assumptions. This auxiliary obstruction
is not a disproof of the original extremal conjecture.
-/

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

omit [CharP K 2] in
include hz in
lemma cert_eq {L T Q : K} (h : L = T + (z^9+z^4+1)*Q) : L = T := by
  simpa only [hz, zero_mul, add_zero] using h

omit [CharP K 2] in
lemma code_identity : (mat512% z 1 0 0 1) = (1 : M (K := K)) := by
  rw [Matrix.one_fin_two]
  simp

omit [CharP K 2] in
lemma pow32_squares (x : K) : x^32 = ((((x^2)^2)^2)^2)^2 := by ring

include hz

lemma sqr_248 : (gf512% z 248)^2 = (gf512% z 475) := by
  apply cert_eq z hz (Q := (gf512% z 43))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_475 : (gf512% z 475)^2 = (gf512% z 312) := by
  apply cert_eq z hz (Q := (gf512% z 173))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_312 : (gf512% z 312)^2 = (gf512% z 422) := by
  apply cert_eq z hz (Q := (gf512% z 134))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_422 : (gf512% z 422)^2 = (gf512% z 195) := by
  apply cert_eq z hz (Q := (gf512% z 167))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_195 : (gf512% z 195)^2 = (gf512% z 188) := by
  apply cert_eq z hz (Q := (gf512% z 41))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_248 : (gf512% z 248)^32 = (gf512% z 188) := by
  rw [pow32_squares]
  rw [sqr_248 z hz, sqr_475 z hz, sqr_312 z hz, sqr_422 z hz, sqr_195 z hz]

lemma sqr_344 : (gf512% z 344)^2 = (gf512% z 268) := by
  apply cert_eq z hz (Q := (gf512% z 140))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_268 : (gf512% z 268)^2 = (gf512% z 148) := by
  apply cert_eq z hz (Q := (gf512% z 132))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_148 : (gf512% z 148)^2 = (gf512% z 289) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_289 : (gf512% z 289)^2 = (gf512% z 231) := by
  apply cert_eq z hz (Q := (gf512% z 134))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_231 : (gf512% z 231)^2 = (gf512% z 142) := by
  apply cert_eq z hz (Q := (gf512% z 43))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_344 : (gf512% z 344)^32 = (gf512% z 142) := by
  rw [pow32_squares]
  rw [sqr_344 z hz, sqr_268 z hz, sqr_148 z hz, sqr_289 z hz, sqr_231 z hz]

lemma sqr_100 : (gf512% z 100)^2 = (gf512% z 186) := by
  apply cert_eq z hz (Q := (gf512% z 10))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_186 : (gf512% z 186)^2 = (gf512% z 343) := by
  apply cert_eq z hz (Q := (gf512% z 35))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_343 : (gf512% z 343)^2 = (gf512% z 345) := by
  apply cert_eq z hz (Q := (gf512% z 140))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_345 : (gf512% z 345)^2 = (gf512% z 269) := by
  apply cert_eq z hz (Q := (gf512% z 140))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_269 : (gf512% z 269)^2 = (gf512% z 149) := by
  apply cert_eq z hz (Q := (gf512% z 132))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_100 : (gf512% z 100)^32 = (gf512% z 149) := by
  rw [pow32_squares]
  rw [sqr_100 z hz, sqr_186 z hz, sqr_343 z hz, sqr_345 z hz, sqr_269 z hz]

lemma sqr_0 : (gf512% z 0)^2 = (gf512% z 0) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_0 : (gf512% z 0)^32 = (gf512% z 0) := by
  rw [pow32_squares]
  rw [sqr_0 z hz, sqr_0 z hz, sqr_0 z hz, sqr_0 z hz, sqr_0 z hz]

lemma sigma_0 : sigmaM (mat512% z 248 344 100 0) = (mat512% z 188 142 149 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_248 z hz
  · exact power32_344 z hz
  · exact power32_100 z hz
  · exact power32_0 z hz

lemma product_0 : (mat512% z 248 344 100 0) * (mat512% z 188 142 149 0) = (mat512% z 481 61 445 480) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 248)*(gf512% z 188) + (gf512% z 344)*(gf512% z 149) = (gf512% z 481)
    apply cert_eq z hz (Q := (gf512% z 105))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 248)*(gf512% z 142) + (gf512% z 344)*(gf512% z 0) = (gf512% z 61)
    apply cert_eq z hz (Q := (gf512% z 61))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 100)*(gf512% z 188) + (gf512% z 0)*(gf512% z 149) = (gf512% z 445)
    apply cert_eq z hz (Q := (gf512% z 29))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 100)*(gf512% z 142) + (gf512% z 0)*(gf512% z 0) = (gf512% z 480)
    apply cert_eq z hz (Q := (gf512% z 24))
    ring_nf <;> reduce_mod_char! <;> ring

lemma mtrace_0 : (mat512% z 481 61 445 480).trace = (gf512% z 1) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 481)+(gf512% z 480) = (gf512% z 1)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_188 : (gf512% z 188)^2 = (gf512% z 323) := by
  apply cert_eq z hz (Q := (gf512% z 35))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_323 : (gf512% z 323)^2 = (gf512% z 73) := by
  apply cert_eq z hz (Q := (gf512% z 140))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_73 : (gf512% z 73)^2 = (gf512% z 201) := by
  apply cert_eq z hz (Q := (gf512% z 8))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_201 : (gf512% z 201)^2 = (gf512% z 248) := by
  apply cert_eq z hz (Q := (gf512% z 41))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_188 : (gf512% z 188)^32 = (gf512% z 475) := by
  rw [pow32_squares]
  rw [sqr_188 z hz, sqr_323 z hz, sqr_73 z hz, sqr_201 z hz, sqr_248 z hz]

lemma sqr_142 : (gf512% z 142)^2 = (gf512% z 101) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_101 : (gf512% z 101)^2 = (gf512% z 187) := by
  apply cert_eq z hz (Q := (gf512% z 10))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_187 : (gf512% z 187)^2 = (gf512% z 342) := by
  apply cert_eq z hz (Q := (gf512% z 35))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_342 : (gf512% z 342)^2 = (gf512% z 344) := by
  apply cert_eq z hz (Q := (gf512% z 140))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_142 : (gf512% z 142)^32 = (gf512% z 268) := by
  rw [pow32_squares]
  rw [sqr_142 z hz, sqr_101 z hz, sqr_187 z hz, sqr_342 z hz, sqr_344 z hz]

lemma sqr_149 : (gf512% z 149)^2 = (gf512% z 288) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_288 : (gf512% z 288)^2 = (gf512% z 230) := by
  apply cert_eq z hz (Q := (gf512% z 134))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_230 : (gf512% z 230)^2 = (gf512% z 143) := by
  apply cert_eq z hz (Q := (gf512% z 43))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_143 : (gf512% z 143)^2 = (gf512% z 100) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_149 : (gf512% z 149)^32 = (gf512% z 186) := by
  rw [pow32_squares]
  rw [sqr_149 z hz, sqr_288 z hz, sqr_230 z hz, sqr_143 z hz, sqr_100 z hz]

lemma sigma_1 : sigmaM (mat512% z 188 142 149 0) = (mat512% z 475 268 186 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_188 z hz
  · exact power32_142 z hz
  · exact power32_149 z hz
  · exact power32_0 z hz

lemma power32_475 : (gf512% z 475)^32 = (gf512% z 323) := by
  rw [pow32_squares]
  rw [sqr_475 z hz, sqr_312 z hz, sqr_422 z hz, sqr_195 z hz, sqr_188 z hz]

lemma power32_268 : (gf512% z 268)^32 = (gf512% z 101) := by
  rw [pow32_squares]
  rw [sqr_268 z hz, sqr_148 z hz, sqr_289 z hz, sqr_231 z hz, sqr_142 z hz]

lemma power32_186 : (gf512% z 186)^32 = (gf512% z 288) := by
  rw [pow32_squares]
  rw [sqr_186 z hz, sqr_343 z hz, sqr_345 z hz, sqr_269 z hz, sqr_149 z hz]

lemma sigma_2 : sigmaM (mat512% z 475 268 186 0) = (mat512% z 323 101 288 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_475 z hz
  · exact power32_268 z hz
  · exact power32_186 z hz
  · exact power32_0 z hz

lemma power32_323 : (gf512% z 323)^32 = (gf512% z 312) := by
  rw [pow32_squares]
  rw [sqr_323 z hz, sqr_73 z hz, sqr_201 z hz, sqr_248 z hz, sqr_475 z hz]

lemma power32_101 : (gf512% z 101)^32 = (gf512% z 148) := by
  rw [pow32_squares]
  rw [sqr_101 z hz, sqr_187 z hz, sqr_342 z hz, sqr_344 z hz, sqr_268 z hz]

lemma power32_288 : (gf512% z 288)^32 = (gf512% z 343) := by
  rw [pow32_squares]
  rw [sqr_288 z hz, sqr_230 z hz, sqr_143 z hz, sqr_100 z hz, sqr_186 z hz]

lemma sigma_3 : sigmaM (mat512% z 323 101 288 0) = (mat512% z 312 148 343 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_323 z hz
  · exact power32_101 z hz
  · exact power32_288 z hz
  · exact power32_0 z hz

lemma power32_312 : (gf512% z 312)^32 = (gf512% z 73) := by
  rw [pow32_squares]
  rw [sqr_312 z hz, sqr_422 z hz, sqr_195 z hz, sqr_188 z hz, sqr_323 z hz]

lemma power32_148 : (gf512% z 148)^32 = (gf512% z 187) := by
  rw [pow32_squares]
  rw [sqr_148 z hz, sqr_289 z hz, sqr_231 z hz, sqr_142 z hz, sqr_101 z hz]

lemma power32_343 : (gf512% z 343)^32 = (gf512% z 230) := by
  rw [pow32_squares]
  rw [sqr_343 z hz, sqr_345 z hz, sqr_269 z hz, sqr_149 z hz, sqr_288 z hz]

lemma sigma_4 : sigmaM (mat512% z 312 148 343 0) = (mat512% z 73 187 230 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_312 z hz
  · exact power32_148 z hz
  · exact power32_343 z hz
  · exact power32_0 z hz

lemma power32_73 : (gf512% z 73)^32 = (gf512% z 422) := by
  rw [pow32_squares]
  rw [sqr_73 z hz, sqr_201 z hz, sqr_248 z hz, sqr_475 z hz, sqr_312 z hz]

lemma power32_187 : (gf512% z 187)^32 = (gf512% z 289) := by
  rw [pow32_squares]
  rw [sqr_187 z hz, sqr_342 z hz, sqr_344 z hz, sqr_268 z hz, sqr_148 z hz]

lemma power32_230 : (gf512% z 230)^32 = (gf512% z 345) := by
  rw [pow32_squares]
  rw [sqr_230 z hz, sqr_143 z hz, sqr_100 z hz, sqr_186 z hz, sqr_343 z hz]

lemma sigma_5 : sigmaM (mat512% z 73 187 230 0) = (mat512% z 422 289 345 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_73 z hz
  · exact power32_187 z hz
  · exact power32_230 z hz
  · exact power32_0 z hz

lemma power32_422 : (gf512% z 422)^32 = (gf512% z 201) := by
  rw [pow32_squares]
  rw [sqr_422 z hz, sqr_195 z hz, sqr_188 z hz, sqr_323 z hz, sqr_73 z hz]

lemma power32_289 : (gf512% z 289)^32 = (gf512% z 342) := by
  rw [pow32_squares]
  rw [sqr_289 z hz, sqr_231 z hz, sqr_142 z hz, sqr_101 z hz, sqr_187 z hz]

lemma power32_345 : (gf512% z 345)^32 = (gf512% z 143) := by
  rw [pow32_squares]
  rw [sqr_345 z hz, sqr_269 z hz, sqr_149 z hz, sqr_288 z hz, sqr_230 z hz]

lemma sigma_6 : sigmaM (mat512% z 422 289 345 0) = (mat512% z 201 342 143 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_422 z hz
  · exact power32_289 z hz
  · exact power32_345 z hz
  · exact power32_0 z hz

lemma power32_201 : (gf512% z 201)^32 = (gf512% z 195) := by
  rw [pow32_squares]
  rw [sqr_201 z hz, sqr_248 z hz, sqr_475 z hz, sqr_312 z hz, sqr_422 z hz]

lemma power32_342 : (gf512% z 342)^32 = (gf512% z 231) := by
  rw [pow32_squares]
  rw [sqr_342 z hz, sqr_344 z hz, sqr_268 z hz, sqr_148 z hz, sqr_289 z hz]

lemma power32_143 : (gf512% z 143)^32 = (gf512% z 269) := by
  rw [pow32_squares]
  rw [sqr_143 z hz, sqr_100 z hz, sqr_186 z hz, sqr_343 z hz, sqr_345 z hz]

lemma sigma_7 : sigmaM (mat512% z 201 342 143 0) = (mat512% z 195 231 269 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_201 z hz
  · exact power32_342 z hz
  · exact power32_143 z hz
  · exact power32_0 z hz

lemma product_1 : (mat512% z 248 344 100 0) * (mat512% z 0 118 486 75) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 248)*(gf512% z 0) + (gf512% z 344)*(gf512% z 486) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 193))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 248)*(gf512% z 118) + (gf512% z 344)*(gf512% z 75) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 56))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 100)*(gf512% z 0) + (gf512% z 0)*(gf512% z 486) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 100)*(gf512% z 118) + (gf512% z 0)*(gf512% z 75) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 9))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_2 : (mat512% z 188 142 149 0) * (mat512% z 207 96 355 376) = (mat512% z 0 118 486 75) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 188)*(gf512% z 207) + (gf512% z 142)*(gf512% z 355) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 102))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 188)*(gf512% z 96) + (gf512% z 142)*(gf512% z 376) = (gf512% z 118)
    apply cert_eq z hz (Q := (gf512% z 70))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 149)*(gf512% z 207) + (gf512% z 0)*(gf512% z 355) = (gf512% z 486)
    apply cert_eq z hz (Q := (gf512% z 53))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 149)*(gf512% z 96) + (gf512% z 0)*(gf512% z 376) = (gf512% z 75)
    apply cert_eq z hz (Q := (gf512% z 27))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_3 : (mat512% z 475 268 186 0) * (mat512% z 295 351 148 256) = (mat512% z 207 96 355 376) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 475)*(gf512% z 295) + (gf512% z 268)*(gf512% z 148) = (gf512% z 207)
    apply cert_eq z hz (Q := (gf512% z 190))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 475)*(gf512% z 351) + (gf512% z 268)*(gf512% z 256) = (gf512% z 96)
    apply cert_eq z hz (Q := (gf512% z 89))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 186)*(gf512% z 295) + (gf512% z 0)*(gf512% z 148) = (gf512% z 355)
    apply cert_eq z hz (Q := (gf512% z 85))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 186)*(gf512% z 351) + (gf512% z 0)*(gf512% z 256) = (gf512% z 376)
    apply cert_eq z hz (Q := (gf512% z 78))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_4 : (mat512% z 323 101 288 0) * (mat512% z 103 300 425 227) = (mat512% z 295 351 148 256) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 323)*(gf512% z 103) + (gf512% z 101)*(gf512% z 425) = (gf512% z 295)
    apply cert_eq z hz (Q := (gf512% z 19))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 323)*(gf512% z 300) + (gf512% z 101)*(gf512% z 227) = (gf512% z 351)
    apply cert_eq z hz (Q := (gf512% z 164))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 288)*(gf512% z 103) + (gf512% z 0)*(gf512% z 425) = (gf512% z 148)
    apply cert_eq z hz (Q := (gf512% z 52))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 288)*(gf512% z 300) + (gf512% z 0)*(gf512% z 227) = (gf512% z 256)
    apply cert_eq z hz (Q := (gf512% z 128))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_5 : (mat512% z 312 148 343 0) * (mat512% z 97 350 302 439) = (mat512% z 103 300 425 227) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 312)*(gf512% z 97) + (gf512% z 148)*(gf512% z 302) = (gf512% z 103)
    apply cert_eq z hz (Q := (gf512% z 119))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 312)*(gf512% z 350) + (gf512% z 148)*(gf512% z 439) = (gf512% z 300)
    apply cert_eq z hz (Q := (gf512% z 208))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 343)*(gf512% z 97) + (gf512% z 0)*(gf512% z 302) = (gf512% z 425)
    apply cert_eq z hz (Q := (gf512% z 62))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 343)*(gf512% z 350) + (gf512% z 0)*(gf512% z 439) = (gf512% z 227)
    apply cert_eq z hz (Q := (gf512% z 137))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_6 : (mat512% z 73 187 230 0) * (mat512% z 385 31 114 250) = (mat512% z 97 350 302 439) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 73)*(gf512% z 385) + (gf512% z 187)*(gf512% z 114) = (gf512% z 97)
    apply cert_eq z hz (Q := (gf512% z 46))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 73)*(gf512% z 31) + (gf512% z 187)*(gf512% z 250) = (gf512% z 350)
    apply cert_eq z hz (Q := (gf512% z 55))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 230)*(gf512% z 385) + (gf512% z 0)*(gf512% z 114) = (gf512% z 302)
    apply cert_eq z hz (Q := (gf512% z 72))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 230)*(gf512% z 31) + (gf512% z 0)*(gf512% z 250) = (gf512% z 439)
    apply cert_eq z hz (Q := (gf512% z 5))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_7 : (mat512% z 422 289 345 0) * (mat512% z 406 456 210 407) = (mat512% z 385 31 114 250) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 422)*(gf512% z 406) + (gf512% z 289)*(gf512% z 210) = (gf512% z 385)
    apply cert_eq z hz (Q := (gf512% z 215))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 422)*(gf512% z 456) + (gf512% z 289)*(gf512% z 407) = (gf512% z 31)
    apply cert_eq z hz (Q := (gf512% z 88))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 345)*(gf512% z 406) + (gf512% z 0)*(gf512% z 210) = (gf512% z 114)
    apply cert_eq z hz (Q := (gf512% z 244))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 345)*(gf512% z 456) + (gf512% z 0)*(gf512% z 407) = (gf512% z 250)
    apply cert_eq z hz (Q := (gf512% z 210))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_8 : (mat512% z 201 342 143 0) * (mat512% z 195 231 269 0) = (mat512% z 406 456 210 407) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 201)*(gf512% z 195) + (gf512% z 342)*(gf512% z 269) = (gf512% z 406)
    apply cert_eq z hz (Q := (gf512% z 131))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 201)*(gf512% z 231) + (gf512% z 342)*(gf512% z 0) = (gf512% z 456)
    apply cert_eq z hz (Q := (gf512% z 39))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 143)*(gf512% z 195) + (gf512% z 0)*(gf512% z 269) = (gf512% z 210)
    apply cert_eq z hz (Q := (gf512% z 51))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 143)*(gf512% z 231) + (gf512% z 0)*(gf512% z 0) = (gf512% z 407)
    apply cert_eq z hz (Q := (gf512% z 58))
    ring_nf <;> reduce_mod_char! <;> ring

lemma norm_0 : semilinearNorm 9 (mat512% z 248 344 100 0) = 1 := by
  have h8 : semilinearNorm 1 (mat512% z 195 231 269 0) = (mat512% z 195 231 269 0) := by simp [semilinearNorm]
  have h7 : semilinearNorm 2 (mat512% z 201 342 143 0) = (mat512% z 406 456 210 407) := by
    change (mat512% z 201 342 143 0) * semilinearNorm 1 (sigmaM (mat512% z 201 342 143 0)) = _
    rw [sigma_7 z hz, h8]
    exact product_8 z hz
  have h6 : semilinearNorm 3 (mat512% z 422 289 345 0) = (mat512% z 385 31 114 250) := by
    change (mat512% z 422 289 345 0) * semilinearNorm 2 (sigmaM (mat512% z 422 289 345 0)) = _
    rw [sigma_6 z hz, h7]
    exact product_7 z hz
  have h5 : semilinearNorm 4 (mat512% z 73 187 230 0) = (mat512% z 97 350 302 439) := by
    change (mat512% z 73 187 230 0) * semilinearNorm 3 (sigmaM (mat512% z 73 187 230 0)) = _
    rw [sigma_5 z hz, h6]
    exact product_6 z hz
  have h4 : semilinearNorm 5 (mat512% z 312 148 343 0) = (mat512% z 103 300 425 227) := by
    change (mat512% z 312 148 343 0) * semilinearNorm 4 (sigmaM (mat512% z 312 148 343 0)) = _
    rw [sigma_4 z hz, h5]
    exact product_5 z hz
  have h3 : semilinearNorm 6 (mat512% z 323 101 288 0) = (mat512% z 295 351 148 256) := by
    change (mat512% z 323 101 288 0) * semilinearNorm 5 (sigmaM (mat512% z 323 101 288 0)) = _
    rw [sigma_3 z hz, h4]
    exact product_4 z hz
  have h2 : semilinearNorm 7 (mat512% z 475 268 186 0) = (mat512% z 207 96 355 376) := by
    change (mat512% z 475 268 186 0) * semilinearNorm 6 (sigmaM (mat512% z 475 268 186 0)) = _
    rw [sigma_2 z hz, h3]
    exact product_3 z hz
  have h1 : semilinearNorm 8 (mat512% z 188 142 149 0) = (mat512% z 0 118 486 75) := by
    change (mat512% z 188 142 149 0) * semilinearNorm 7 (sigmaM (mat512% z 188 142 149 0)) = _
    rw [sigma_1 z hz, h2]
    exact product_2 z hz
  have h0 : semilinearNorm 9 (mat512% z 248 344 100 0) = (mat512% z 1 0 0 1) := by
    change (mat512% z 248 344 100 0) * semilinearNorm 8 (sigmaM (mat512% z 248 344 100 0)) = _
    rw [sigma_0 z hz, h1]
    exact product_1 z hz
  simpa only [code_identity] using h0

lemma mtrace_1 : (mat512% z 248 344 100 0).trace = (gf512% z 248) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 248)+(gf512% z 0) = (gf512% z 248)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma mdet_0 : (mat512% z 248 344 100 0).det = (gf512% z 397) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 248)*(gf512% z 0) - (gf512% z 344)*(gf512% z 100) = (gf512% z 397)
  apply cert_eq z hz (Q := (gf512% z 61))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_27 : (gf512% z 27)^2 = (gf512% z 325) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_350 : (gf512% z 350)^2 = (gf512% z 280) := by
  apply cert_eq z hz (Q := (gf512% z 140))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_259 : (gf512% z 259)^2 = (gf512% z 193) := by
  apply cert_eq z hz (Q := (gf512% z 132))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_218 : (gf512% z 218)^2 = (gf512% z 509) := by
  apply cert_eq z hz (Q := (gf512% z 41))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_486 : (gf512% z 486)^2 = (gf512% z 75) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_80 : (gf512% z 80)^2 = (gf512% z 392) := by
  apply cert_eq z hz (Q := (gf512% z 8))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_403 : (gf512% z 403)^2 = (gf512% z 496) := by
  apply cert_eq z hz (Q := (gf512% z 165))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_491 : (gf512% z 491)^2 = (gf512% z 26) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma atr_0 : trace2 9 (gf512% z 27) = 1 := by
  have h0 : trace2 0 (gf512% z 27) = (gf512% z 0) := by simp [trace2]
  have h1 : trace2 1 (gf512% z 27) = (gf512% z 27) := by
    change (trace2 0 (gf512% z 27))^2 + (gf512% z 27) = _
    rw [h0, sqr_0 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h2 : trace2 2 (gf512% z 27) = (gf512% z 350) := by
    change (trace2 1 (gf512% z 27))^2 + (gf512% z 27) = _
    rw [h1, sqr_27 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h3 : trace2 3 (gf512% z 27) = (gf512% z 259) := by
    change (trace2 2 (gf512% z 27))^2 + (gf512% z 27) = _
    rw [h2, sqr_350 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h4 : trace2 4 (gf512% z 27) = (gf512% z 218) := by
    change (trace2 3 (gf512% z 27))^2 + (gf512% z 27) = _
    rw [h3, sqr_259 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h5 : trace2 5 (gf512% z 27) = (gf512% z 486) := by
    change (trace2 4 (gf512% z 27))^2 + (gf512% z 27) = _
    rw [h4, sqr_218 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h6 : trace2 6 (gf512% z 27) = (gf512% z 80) := by
    change (trace2 5 (gf512% z 27))^2 + (gf512% z 27) = _
    rw [h5, sqr_486 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h7 : trace2 7 (gf512% z 27) = (gf512% z 403) := by
    change (trace2 6 (gf512% z 27))^2 + (gf512% z 27) = _
    rw [h6, sqr_80 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h8 : trace2 8 (gf512% z 27) = (gf512% z 491) := by
    change (trace2 7 (gf512% z 27))^2 + (gf512% z 27) = _
    rw [h7, sqr_403 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h9 : trace2 9 (gf512% z 27) = (gf512% z 1) := by
    change (trace2 8 (gf512% z 27))^2 + (gf512% z 27) = _
    rw [h8, sqr_491 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  simpa using h9

lemma elliptic_0 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 248 344 100 0) := by
  have ht : (gf512% z 248)*(gf512% z 6) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 397)*(gf512% z 6)^2 = (gf512% z 27) := by
    apply cert_eq z hz (Q := (gf512% z 15))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_1 z hz, mdet_0 z hz]
  apply no_quadratic_root hK (gf512% z 248) (gf512% z 397) (gf512% z 6) ht
  rw [hd]
  exact atr_0 z hz

lemma mdet_1 : (mat512% z 481 61 445 480).det = (gf512% z 77) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 481)*(gf512% z 480) - (gf512% z 61)*(gf512% z 445) = (gf512% z 77)
  apply cert_eq z hz (Q := (gf512% z 188))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_77 : (gf512% z 77)^2 = (gf512% z 217) := by
  apply cert_eq z hz (Q := (gf512% z 8))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_364 : (gf512% z 364)^2 = (gf512% z 62) := by
  apply cert_eq z hz (Q := (gf512% z 142))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_115 : (gf512% z 115)^2 = (gf512% z 431) := by
  apply cert_eq z hz (Q := (gf512% z 10))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_482 : (gf512% z 482)^2 = (gf512% z 91) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_22 : (gf512% z 22)^2 = (gf512% z 276) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_320 : (gf512% z 320)^2 = (gf512% z 76) := by
  apply cert_eq z hz (Q := (gf512% z 140))
  ring_nf <;> reduce_mod_char! <;> ring

lemma atr_1 : trace2 9 (gf512% z 77) = 1 := by
  have h0 : trace2 0 (gf512% z 77) = (gf512% z 0) := by simp [trace2]
  have h1 : trace2 1 (gf512% z 77) = (gf512% z 77) := by
    change (trace2 0 (gf512% z 77))^2 + (gf512% z 77) = _
    rw [h0, sqr_0 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h2 : trace2 2 (gf512% z 77) = (gf512% z 148) := by
    change (trace2 1 (gf512% z 77))^2 + (gf512% z 77) = _
    rw [h1, sqr_77 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h3 : trace2 3 (gf512% z 77) = (gf512% z 364) := by
    change (trace2 2 (gf512% z 77))^2 + (gf512% z 77) = _
    rw [h2, sqr_148 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h4 : trace2 4 (gf512% z 77) = (gf512% z 115) := by
    change (trace2 3 (gf512% z 77))^2 + (gf512% z 77) = _
    rw [h3, sqr_364 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h5 : trace2 5 (gf512% z 77) = (gf512% z 482) := by
    change (trace2 4 (gf512% z 77))^2 + (gf512% z 77) = _
    rw [h4, sqr_115 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h6 : trace2 6 (gf512% z 77) = (gf512% z 22) := by
    change (trace2 5 (gf512% z 77))^2 + (gf512% z 77) = _
    rw [h5, sqr_482 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h7 : trace2 7 (gf512% z 77) = (gf512% z 345) := by
    change (trace2 6 (gf512% z 77))^2 + (gf512% z 77) = _
    rw [h6, sqr_22 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h8 : trace2 8 (gf512% z 77) = (gf512% z 320) := by
    change (trace2 7 (gf512% z 77))^2 + (gf512% z 77) = _
    rw [h7, sqr_345 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h9 : trace2 9 (gf512% z 77) = (gf512% z 1) := by
    change (trace2 8 (gf512% z 77))^2 + (gf512% z 77) = _
    rw [h8, sqr_320 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  simpa using h9

lemma elliptic_1 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 481 61 445 480) := by
  have ht : (gf512% z 1)*(gf512% z 1) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 77)*(gf512% z 1)^2 = (gf512% z 77) := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_0 z hz, mdet_1 z hz]
  apply no_quadratic_root hK (gf512% z 1) (gf512% z 77) (gf512% z 1) ht
  rw [hd]
  exact atr_1 z hz

lemma good_0 (hK : ∀ x : K, x^512 = x) : Good (mat512% z 248 344 100 0) := by
  unfold Good
  rw [sigma_0 z hz, product_0 z hz]
  refine ⟨?_, elliptic_0 z hz hK, norm_0 z hz, elliptic_1 z hz hK⟩
  simpa using mtrace_0 z hz

#check good_0

lemma sqr_316 : (gf512% z 316)^2 = (gf512% z 438) := by
  apply cert_eq z hz (Q := (gf512% z 134))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_438 : (gf512% z 438)^2 = (gf512% z 451) := by
  apply cert_eq z hz (Q := (gf512% z 167))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_451 : (gf512% z 451)^2 = (gf512% z 120) := by
  apply cert_eq z hz (Q := (gf512% z 173))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_120 : (gf512% z 120)^2 = (gf512% z 490) := by
  apply cert_eq z hz (Q := (gf512% z 10))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_490 : (gf512% z 490)^2 = (gf512% z 27) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_316 : (gf512% z 316)^32 = (gf512% z 27) := by
  rw [pow32_squares]
  rw [sqr_316 z hz, sqr_438 z hz, sqr_451 z hz, sqr_120 z hz, sqr_490 z hz]

lemma sigma_8 : sigmaM (mat512% z 248 316 100 0) = (mat512% z 188 27 149 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_248 z hz
  · exact power32_316 z hz
  · exact power32_100 z hz
  · exact power32_0 z hz

lemma product_9 : (mat512% z 248 316 100 0) * (mat512% z 188 27 149 0) = (mat512% z 495 268 445 494) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 248)*(gf512% z 188) + (gf512% z 316)*(gf512% z 149) = (gf512% z 495)
    apply cert_eq z hz (Q := (gf512% z 115))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 248)*(gf512% z 27) + (gf512% z 316)*(gf512% z 0) = (gf512% z 268)
    apply cert_eq z hz (Q := (gf512% z 4))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 100)*(gf512% z 188) + (gf512% z 0)*(gf512% z 149) = (gf512% z 445)
    apply cert_eq z hz (Q := (gf512% z 29))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 100)*(gf512% z 27) + (gf512% z 0)*(gf512% z 0) = (gf512% z 494)
    apply cert_eq z hz (Q := (gf512% z 2))
    ring_nf <;> reduce_mod_char! <;> ring

lemma mtrace_2 : (mat512% z 495 268 445 494).trace = (gf512% z 1) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 495)+(gf512% z 494) = (gf512% z 1)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_325 : (gf512% z 325)^2 = (gf512% z 93) := by
  apply cert_eq z hz (Q := (gf512% z 140))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_93 : (gf512% z 93)^2 = (gf512% z 473) := by
  apply cert_eq z hz (Q := (gf512% z 8))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_473 : (gf512% z 473)^2 = (gf512% z 316) := by
  apply cert_eq z hz (Q := (gf512% z 173))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_27 : (gf512% z 27)^32 = (gf512% z 438) := by
  rw [pow32_squares]
  rw [sqr_27 z hz, sqr_325 z hz, sqr_93 z hz, sqr_473 z hz, sqr_316 z hz]

lemma sigma_9 : sigmaM (mat512% z 188 27 149 0) = (mat512% z 475 438 186 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_188 z hz
  · exact power32_27 z hz
  · exact power32_149 z hz
  · exact power32_0 z hz

lemma power32_438 : (gf512% z 438)^32 = (gf512% z 325) := by
  rw [pow32_squares]
  rw [sqr_438 z hz, sqr_451 z hz, sqr_120 z hz, sqr_490 z hz, sqr_27 z hz]

lemma sigma_10 : sigmaM (mat512% z 475 438 186 0) = (mat512% z 323 325 288 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_475 z hz
  · exact power32_438 z hz
  · exact power32_186 z hz
  · exact power32_0 z hz

lemma power32_325 : (gf512% z 325)^32 = (gf512% z 451) := by
  rw [pow32_squares]
  rw [sqr_325 z hz, sqr_93 z hz, sqr_473 z hz, sqr_316 z hz, sqr_438 z hz]

lemma sigma_11 : sigmaM (mat512% z 323 325 288 0) = (mat512% z 312 451 343 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_323 z hz
  · exact power32_325 z hz
  · exact power32_288 z hz
  · exact power32_0 z hz

lemma power32_451 : (gf512% z 451)^32 = (gf512% z 93) := by
  rw [pow32_squares]
  rw [sqr_451 z hz, sqr_120 z hz, sqr_490 z hz, sqr_27 z hz, sqr_325 z hz]

lemma sigma_12 : sigmaM (mat512% z 312 451 343 0) = (mat512% z 73 93 230 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_312 z hz
  · exact power32_451 z hz
  · exact power32_343 z hz
  · exact power32_0 z hz

lemma power32_93 : (gf512% z 93)^32 = (gf512% z 120) := by
  rw [pow32_squares]
  rw [sqr_93 z hz, sqr_473 z hz, sqr_316 z hz, sqr_438 z hz, sqr_451 z hz]

lemma sigma_13 : sigmaM (mat512% z 73 93 230 0) = (mat512% z 422 120 345 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_73 z hz
  · exact power32_93 z hz
  · exact power32_230 z hz
  · exact power32_0 z hz

lemma power32_120 : (gf512% z 120)^32 = (gf512% z 473) := by
  rw [pow32_squares]
  rw [sqr_120 z hz, sqr_490 z hz, sqr_27 z hz, sqr_325 z hz, sqr_93 z hz]

lemma sigma_14 : sigmaM (mat512% z 422 120 345 0) = (mat512% z 201 473 143 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_422 z hz
  · exact power32_120 z hz
  · exact power32_345 z hz
  · exact power32_0 z hz

lemma power32_473 : (gf512% z 473)^32 = (gf512% z 490) := by
  rw [pow32_squares]
  rw [sqr_473 z hz, sqr_316 z hz, sqr_438 z hz, sqr_451 z hz, sqr_120 z hz]

lemma sigma_15 : sigmaM (mat512% z 201 473 143 0) = (mat512% z 195 490 269 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_201 z hz
  · exact power32_473 z hz
  · exact power32_143 z hz
  · exact power32_0 z hz

lemma product_10 : (mat512% z 248 316 100 0) * (mat512% z 0 118 375 488) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 248)*(gf512% z 0) + (gf512% z 316)*(gf512% z 375) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 165))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 248)*(gf512% z 118) + (gf512% z 316)*(gf512% z 488) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 240))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 100)*(gf512% z 0) + (gf512% z 0)*(gf512% z 375) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 100)*(gf512% z 118) + (gf512% z 0)*(gf512% z 488) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 9))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_11 : (mat512% z 188 27 149 0) * (mat512% z 61 171 307 319) = (mat512% z 0 118 375 488) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 188)*(gf512% z 61) + (gf512% z 27)*(gf512% z 307) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 188)*(gf512% z 171) + (gf512% z 27)*(gf512% z 319) = (gf512% z 118)
    apply cert_eq z hz (Q := (gf512% z 43))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 149)*(gf512% z 61) + (gf512% z 0)*(gf512% z 307) = (gf512% z 375)
    apply cert_eq z hz (Q := (gf512% z 14))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 149)*(gf512% z 171) + (gf512% z 0)*(gf512% z 319) = (gf512% z 488)
    apply cert_eq z hz (Q := (gf512% z 47))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_12 : (mat512% z 475 438 186 0) * (mat512% z 204 401 491 337) = (mat512% z 61 171 307 319) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 475)*(gf512% z 204) + (gf512% z 438)*(gf512% z 491) = (gf512% z 61)
    apply cert_eq z hz (Q := (gf512% z 211))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 475)*(gf512% z 401) + (gf512% z 438)*(gf512% z 337) = (gf512% z 171)
    apply cert_eq z hz (Q := (gf512% z 118))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 186)*(gf512% z 204) + (gf512% z 0)*(gf512% z 491) = (gf512% z 307)
    apply cert_eq z hz (Q := (gf512% z 59))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 186)*(gf512% z 401) + (gf512% z 0)*(gf512% z 337) = (gf512% z 319)
    apply cert_eq z hz (Q := (gf512% z 117))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_13 : (mat512% z 323 325 288 0) * (mat512% z 123 302 175 322) = (mat512% z 204 401 491 337) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 323)*(gf512% z 123) + (gf512% z 325)*(gf512% z 175) = (gf512% z 204)
    apply cert_eq z hz (Q := (gf512% z 114))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 323)*(gf512% z 302) + (gf512% z 325)*(gf512% z 322) = (gf512% z 401)
    apply cert_eq z hz (Q := (gf512% z 57))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 288)*(gf512% z 123) + (gf512% z 0)*(gf512% z 175) = (gf512% z 491)
    apply cert_eq z hz (Q := (gf512% z 59))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 288)*(gf512% z 302) + (gf512% z 0)*(gf512% z 322) = (gf512% z 337)
    apply cert_eq z hz (Q := (gf512% z 129))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_14 : (mat512% z 312 451 343 0) * (mat512% z 254 321 136 313) = (mat512% z 123 302 175 322) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 312)*(gf512% z 254) + (gf512% z 451)*(gf512% z 136) = (gf512% z 123)
    apply cert_eq z hz (Q := (gf512% z 3))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 312)*(gf512% z 321) + (gf512% z 451)*(gf512% z 313) = (gf512% z 302)
    apply cert_eq z hz (Q := (gf512% z 77))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 343)*(gf512% z 254) + (gf512% z 0)*(gf512% z 136) = (gf512% z 175)
    apply cert_eq z hz (Q := (gf512% z 101))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 343)*(gf512% z 321) + (gf512% z 0)*(gf512% z 313) = (gf512% z 322)
    apply cert_eq z hz (Q := (gf512% z 133))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_15 : (mat512% z 73 93 230 0) * (mat512% z 205 401 242 84) = (mat512% z 254 321 136 313) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 73)*(gf512% z 205) + (gf512% z 93)*(gf512% z 242) = (gf512% z 254)
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 73)*(gf512% z 401) + (gf512% z 93)*(gf512% z 84) = (gf512% z 321)
    apply cert_eq z hz (Q := (gf512% z 60))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 230)*(gf512% z 205) + (gf512% z 0)*(gf512% z 242) = (gf512% z 136)
    apply cert_eq z hz (Q := (gf512% z 38))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 230)*(gf512% z 401) + (gf512% z 0)*(gf512% z 84) = (gf512% z 313)
    apply cert_eq z hz (Q := (gf512% z 79))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_16 : (mat512% z 422 120 345 0) * (mat512% z 123 344 210 122) = (mat512% z 205 401 242 84) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 422)*(gf512% z 123) + (gf512% z 120)*(gf512% z 210) = (gf512% z 205)
    apply cert_eq z hz (Q := (gf512% z 55))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 422)*(gf512% z 344) + (gf512% z 120)*(gf512% z 122) = (gf512% z 401)
    apply cert_eq z hz (Q := (gf512% z 225))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 345)*(gf512% z 123) + (gf512% z 0)*(gf512% z 210) = (gf512% z 242)
    apply cert_eq z hz (Q := (gf512% z 49))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 345)*(gf512% z 344) + (gf512% z 0)*(gf512% z 122) = (gf512% z 84)
    apply cert_eq z hz (Q := (gf512% z 140))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_17 : (mat512% z 201 473 143 0) * (mat512% z 195 490 269 0) = (mat512% z 123 344 210 122) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 201)*(gf512% z 195) + (gf512% z 473)*(gf512% z 269) = (gf512% z 123)
    apply cert_eq z hz (Q := (gf512% z 197))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 201)*(gf512% z 490) + (gf512% z 473)*(gf512% z 0) = (gf512% z 344)
    apply cert_eq z hz (Q := (gf512% z 66))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 143)*(gf512% z 195) + (gf512% z 0)*(gf512% z 269) = (gf512% z 210)
    apply cert_eq z hz (Q := (gf512% z 51))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 143)*(gf512% z 490) + (gf512% z 0)*(gf512% z 0) = (gf512% z 122)
    apply cert_eq z hz (Q := (gf512% z 124))
    ring_nf <;> reduce_mod_char! <;> ring

lemma norm_1 : semilinearNorm 9 (mat512% z 248 316 100 0) = 1 := by
  have h8 : semilinearNorm 1 (mat512% z 195 490 269 0) = (mat512% z 195 490 269 0) := by simp [semilinearNorm]
  have h7 : semilinearNorm 2 (mat512% z 201 473 143 0) = (mat512% z 123 344 210 122) := by
    change (mat512% z 201 473 143 0) * semilinearNorm 1 (sigmaM (mat512% z 201 473 143 0)) = _
    rw [sigma_15 z hz, h8]
    exact product_17 z hz
  have h6 : semilinearNorm 3 (mat512% z 422 120 345 0) = (mat512% z 205 401 242 84) := by
    change (mat512% z 422 120 345 0) * semilinearNorm 2 (sigmaM (mat512% z 422 120 345 0)) = _
    rw [sigma_14 z hz, h7]
    exact product_16 z hz
  have h5 : semilinearNorm 4 (mat512% z 73 93 230 0) = (mat512% z 254 321 136 313) := by
    change (mat512% z 73 93 230 0) * semilinearNorm 3 (sigmaM (mat512% z 73 93 230 0)) = _
    rw [sigma_13 z hz, h6]
    exact product_15 z hz
  have h4 : semilinearNorm 5 (mat512% z 312 451 343 0) = (mat512% z 123 302 175 322) := by
    change (mat512% z 312 451 343 0) * semilinearNorm 4 (sigmaM (mat512% z 312 451 343 0)) = _
    rw [sigma_12 z hz, h5]
    exact product_14 z hz
  have h3 : semilinearNorm 6 (mat512% z 323 325 288 0) = (mat512% z 204 401 491 337) := by
    change (mat512% z 323 325 288 0) * semilinearNorm 5 (sigmaM (mat512% z 323 325 288 0)) = _
    rw [sigma_11 z hz, h4]
    exact product_13 z hz
  have h2 : semilinearNorm 7 (mat512% z 475 438 186 0) = (mat512% z 61 171 307 319) := by
    change (mat512% z 475 438 186 0) * semilinearNorm 6 (sigmaM (mat512% z 475 438 186 0)) = _
    rw [sigma_10 z hz, h3]
    exact product_12 z hz
  have h1 : semilinearNorm 8 (mat512% z 188 27 149 0) = (mat512% z 0 118 375 488) := by
    change (mat512% z 188 27 149 0) * semilinearNorm 7 (sigmaM (mat512% z 188 27 149 0)) = _
    rw [sigma_9 z hz, h2]
    exact product_11 z hz
  have h0 : semilinearNorm 9 (mat512% z 248 316 100 0) = (mat512% z 1 0 0 1) := by
    change (mat512% z 248 316 100 0) * semilinearNorm 8 (sigmaM (mat512% z 248 316 100 0)) = _
    rw [sigma_8 z hz, h1]
    exact product_10 z hz
  simpa only [code_identity] using h0

lemma mtrace_3 : (mat512% z 248 316 100 0).trace = (gf512% z 248) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 248)+(gf512% z 0) = (gf512% z 248)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma mdet_2 : (mat512% z 248 316 100 0).det = (gf512% z 311) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 248)*(gf512% z 0) - (gf512% z 316)*(gf512% z 100) = (gf512% z 311)
  apply cert_eq z hz (Q := (gf512% z 55))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_279 : (gf512% z 279)^2 = (gf512% z 465) := by
  apply cert_eq z hz (Q := (gf512% z 132))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_198 : (gf512% z 198)^2 = (gf512% z 173) := by
  apply cert_eq z hz (Q := (gf512% z 41))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_442 : (gf512% z 442)^2 = (gf512% z 403) := by
  apply cert_eq z hz (Q := (gf512% z 167))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_132 : (gf512% z 132)^2 = (gf512% z 33) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_310 : (gf512% z 310)^2 = (gf512% z 498) := by
  apply cert_eq z hz (Q := (gf512% z 134))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_229 : (gf512% z 229)^2 = (gf512% z 138) := by
  apply cert_eq z hz (Q := (gf512% z 43))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_413 : (gf512% z 413)^2 = (gf512% z 420) := by
  apply cert_eq z hz (Q := (gf512% z 165))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_179 : (gf512% z 179)^2 = (gf512% z 278) := by
  apply cert_eq z hz (Q := (gf512% z 35))
  ring_nf <;> reduce_mod_char! <;> ring

lemma atr_2 : trace2 9 (gf512% z 279) = 1 := by
  have h0 : trace2 0 (gf512% z 279) = (gf512% z 0) := by simp [trace2]
  have h1 : trace2 1 (gf512% z 279) = (gf512% z 279) := by
    change (trace2 0 (gf512% z 279))^2 + (gf512% z 279) = _
    rw [h0, sqr_0 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h2 : trace2 2 (gf512% z 279) = (gf512% z 198) := by
    change (trace2 1 (gf512% z 279))^2 + (gf512% z 279) = _
    rw [h1, sqr_279 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h3 : trace2 3 (gf512% z 279) = (gf512% z 442) := by
    change (trace2 2 (gf512% z 279))^2 + (gf512% z 279) = _
    rw [h2, sqr_198 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h4 : trace2 4 (gf512% z 279) = (gf512% z 132) := by
    change (trace2 3 (gf512% z 279))^2 + (gf512% z 279) = _
    rw [h3, sqr_442 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h5 : trace2 5 (gf512% z 279) = (gf512% z 310) := by
    change (trace2 4 (gf512% z 279))^2 + (gf512% z 279) = _
    rw [h4, sqr_132 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h6 : trace2 6 (gf512% z 279) = (gf512% z 229) := by
    change (trace2 5 (gf512% z 279))^2 + (gf512% z 279) = _
    rw [h5, sqr_310 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h7 : trace2 7 (gf512% z 279) = (gf512% z 413) := by
    change (trace2 6 (gf512% z 279))^2 + (gf512% z 279) = _
    rw [h6, sqr_229 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h8 : trace2 8 (gf512% z 279) = (gf512% z 179) := by
    change (trace2 7 (gf512% z 279))^2 + (gf512% z 279) = _
    rw [h7, sqr_413 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h9 : trace2 9 (gf512% z 279) = (gf512% z 1) := by
    change (trace2 8 (gf512% z 279))^2 + (gf512% z 279) = _
    rw [h8, sqr_179 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  simpa using h9

lemma elliptic_2 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 248 316 100 0) := by
  have ht : (gf512% z 248)*(gf512% z 6) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 311)*(gf512% z 6)^2 = (gf512% z 279) := by
    apply cert_eq z hz (Q := (gf512% z 11))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_3 z hz, mdet_2 z hz]
  apply no_quadratic_root hK (gf512% z 248) (gf512% z 311) (gf512% z 6) ht
  rw [hd]
  exact atr_2 z hz

lemma mdet_3 : (mat512% z 495 268 445 494).det = (gf512% z 244) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 495)*(gf512% z 494) - (gf512% z 268)*(gf512% z 445) = (gf512% z 244)
  apply cert_eq z hz (Q := (gf512% z 114))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_244 : (gf512% z 244)^2 = (gf512% z 395) := by
  apply cert_eq z hz (Q := (gf512% z 43))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_383 : (gf512% z 383)^2 = (gf512% z 315) := by
  apply cert_eq z hz (Q := (gf512% z 142))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_463 : (gf512% z 463)^2 = (gf512% z 40) := by
  apply cert_eq z hz (Q := (gf512% z 173))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_220 : (gf512% z 220)^2 = (gf512% z 489) := by
  apply cert_eq z hz (Q := (gf512% z 41))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_285 : (gf512% z 285)^2 = (gf512% z 405) := by
  apply cert_eq z hz (Q := (gf512% z 132))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_353 : (gf512% z 353)^2 = (gf512% z 111) := by
  apply cert_eq z hz (Q := (gf512% z 142))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_155 : (gf512% z 155)^2 = (gf512% z 372) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_384 : (gf512% z 384)^2 = (gf512% z 245) := by
  apply cert_eq z hz (Q := (gf512% z 165))
  ring_nf <;> reduce_mod_char! <;> ring

lemma atr_3 : trace2 9 (gf512% z 244) = 1 := by
  have h0 : trace2 0 (gf512% z 244) = (gf512% z 0) := by simp [trace2]
  have h1 : trace2 1 (gf512% z 244) = (gf512% z 244) := by
    change (trace2 0 (gf512% z 244))^2 + (gf512% z 244) = _
    rw [h0, sqr_0 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h2 : trace2 2 (gf512% z 244) = (gf512% z 383) := by
    change (trace2 1 (gf512% z 244))^2 + (gf512% z 244) = _
    rw [h1, sqr_244 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h3 : trace2 3 (gf512% z 244) = (gf512% z 463) := by
    change (trace2 2 (gf512% z 244))^2 + (gf512% z 244) = _
    rw [h2, sqr_383 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h4 : trace2 4 (gf512% z 244) = (gf512% z 220) := by
    change (trace2 3 (gf512% z 244))^2 + (gf512% z 244) = _
    rw [h3, sqr_463 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h5 : trace2 5 (gf512% z 244) = (gf512% z 285) := by
    change (trace2 4 (gf512% z 244))^2 + (gf512% z 244) = _
    rw [h4, sqr_220 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h6 : trace2 6 (gf512% z 244) = (gf512% z 353) := by
    change (trace2 5 (gf512% z 244))^2 + (gf512% z 244) = _
    rw [h5, sqr_285 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h7 : trace2 7 (gf512% z 244) = (gf512% z 155) := by
    change (trace2 6 (gf512% z 244))^2 + (gf512% z 244) = _
    rw [h6, sqr_353 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h8 : trace2 8 (gf512% z 244) = (gf512% z 384) := by
    change (trace2 7 (gf512% z 244))^2 + (gf512% z 244) = _
    rw [h7, sqr_155 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h9 : trace2 9 (gf512% z 244) = (gf512% z 1) := by
    change (trace2 8 (gf512% z 244))^2 + (gf512% z 244) = _
    rw [h8, sqr_384 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  simpa using h9

lemma elliptic_3 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 495 268 445 494) := by
  have ht : (gf512% z 1)*(gf512% z 1) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 244)*(gf512% z 1)^2 = (gf512% z 244) := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_2 z hz, mdet_3 z hz]
  apply no_quadratic_root hK (gf512% z 1) (gf512% z 244) (gf512% z 1) ht
  rw [hd]
  exact atr_3 z hz

lemma good_1 (hK : ∀ x : K, x^512 = x) : Good (mat512% z 248 316 100 0) := by
  unfold Good
  rw [sigma_8 z hz, product_9 z hz]
  refine ⟨?_, elliptic_2 z hz hK, norm_1 z hz, elliptic_3 z hz hK⟩
  simpa using mtrace_2 z hz

#check good_1

lemma sqr_156 : (gf512% z 156)^2 = (gf512% z 353) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_111 : (gf512% z 111)^2 = (gf512% z 255) := by
  apply cert_eq z hz (Q := (gf512% z 10))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_255 : (gf512% z 255)^2 = (gf512% z 462) := by
  apply cert_eq z hz (Q := (gf512% z 43))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_462 : (gf512% z 462)^2 = (gf512% z 41) := by
  apply cert_eq z hz (Q := (gf512% z 173))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_156 : (gf512% z 156)^32 = (gf512% z 41) := by
  rw [pow32_squares]
  rw [sqr_156 z hz, sqr_353 z hz, sqr_111 z hz, sqr_255 z hz, sqr_462 z hz]

lemma sqr_452 : (gf512% z 452)^2 = (gf512% z 109) := by
  apply cert_eq z hz (Q := (gf512% z 173))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_109 : (gf512% z 109)^2 = (gf512% z 251) := by
  apply cert_eq z hz (Q := (gf512% z 10))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_251 : (gf512% z 251)^2 = (gf512% z 478) := by
  apply cert_eq z hz (Q := (gf512% z 43))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_478 : (gf512% z 478)^2 = (gf512% z 297) := by
  apply cert_eq z hz (Q := (gf512% z 173))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_297 : (gf512% z 297)^2 = (gf512% z 167) := by
  apply cert_eq z hz (Q := (gf512% z 134))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_452 : (gf512% z 452)^32 = (gf512% z 167) := by
  rw [pow32_squares]
  rw [sqr_452 z hz, sqr_109 z hz, sqr_251 z hz, sqr_478 z hz, sqr_297 z hz]

lemma sigma_16 : sigmaM (mat512% z 156 452 100 100) = (mat512% z 41 167 149 149) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_156 z hz
  · exact power32_452 z hz
  · exact power32_100 z hz
  · exact power32_100 z hz

lemma product_18 : (mat512% z 156 452 100 100) * (mat512% z 41 167 149 149) = (mat512% z 92 385 445 93) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 156)*(gf512% z 41) + (gf512% z 452)*(gf512% z 149) = (gf512% z 92)
    apply cert_eq z hz (Q := (gf512% z 116))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 156)*(gf512% z 167) + (gf512% z 452)*(gf512% z 149) = (gf512% z 385)
    apply cert_eq z hz (Q := (gf512% z 81))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 100)*(gf512% z 41) + (gf512% z 100)*(gf512% z 149) = (gf512% z 445)
    apply cert_eq z hz (Q := (gf512% z 29))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 100)*(gf512% z 167) + (gf512% z 100)*(gf512% z 149) = (gf512% z 93)
    apply cert_eq z hz (Q := (gf512% z 5))
    ring_nf <;> reduce_mod_char! <;> ring

lemma mtrace_4 : (mat512% z 92 385 445 93).trace = (gf512% z 1) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 92)+(gf512% z 93) = (gf512% z 1)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_41 : (gf512% z 41)^2 = (gf512% z 99) := by
  apply cert_eq z hz (Q := (gf512% z 2))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_99 : (gf512% z 99)^2 = (gf512% z 175) := by
  apply cert_eq z hz (Q := (gf512% z 10))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_175 : (gf512% z 175)^2 = (gf512% z 70) := by
  apply cert_eq z hz (Q := (gf512% z 35))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_70 : (gf512% z 70)^2 = (gf512% z 156) := by
  apply cert_eq z hz (Q := (gf512% z 8))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_41 : (gf512% z 41)^32 = (gf512% z 353) := by
  rw [pow32_squares]
  rw [sqr_41 z hz, sqr_99 z hz, sqr_175 z hz, sqr_70 z hz, sqr_156 z hz]

lemma sqr_167 : (gf512% z 167)^2 = (gf512% z 6) := by
  apply cert_eq z hz (Q := (gf512% z 35))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_6 : (gf512% z 6)^2 = (gf512% z 20) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_20 : (gf512% z 20)^2 = (gf512% z 272) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_272 : (gf512% z 272)^2 = (gf512% z 452) := by
  apply cert_eq z hz (Q := (gf512% z 132))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_167 : (gf512% z 167)^32 = (gf512% z 109) := by
  rw [pow32_squares]
  rw [sqr_167 z hz, sqr_6 z hz, sqr_20 z hz, sqr_272 z hz, sqr_452 z hz]

lemma sigma_17 : sigmaM (mat512% z 41 167 149 149) = (mat512% z 353 109 186 186) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_41 z hz
  · exact power32_167 z hz
  · exact power32_149 z hz
  · exact power32_149 z hz

lemma power32_353 : (gf512% z 353)^32 = (gf512% z 99) := by
  rw [pow32_squares]
  rw [sqr_353 z hz, sqr_111 z hz, sqr_255 z hz, sqr_462 z hz, sqr_41 z hz]

lemma power32_109 : (gf512% z 109)^32 = (gf512% z 6) := by
  rw [pow32_squares]
  rw [sqr_109 z hz, sqr_251 z hz, sqr_478 z hz, sqr_297 z hz, sqr_167 z hz]

lemma sigma_18 : sigmaM (mat512% z 353 109 186 186) = (mat512% z 99 6 288 288) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_353 z hz
  · exact power32_109 z hz
  · exact power32_186 z hz
  · exact power32_186 z hz

lemma power32_99 : (gf512% z 99)^32 = (gf512% z 111) := by
  rw [pow32_squares]
  rw [sqr_99 z hz, sqr_175 z hz, sqr_70 z hz, sqr_156 z hz, sqr_353 z hz]

lemma power32_6 : (gf512% z 6)^32 = (gf512% z 251) := by
  rw [pow32_squares]
  rw [sqr_6 z hz, sqr_20 z hz, sqr_272 z hz, sqr_452 z hz, sqr_109 z hz]

lemma sigma_19 : sigmaM (mat512% z 99 6 288 288) = (mat512% z 111 251 343 343) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_99 z hz
  · exact power32_6 z hz
  · exact power32_288 z hz
  · exact power32_288 z hz

lemma power32_111 : (gf512% z 111)^32 = (gf512% z 175) := by
  rw [pow32_squares]
  rw [sqr_111 z hz, sqr_255 z hz, sqr_462 z hz, sqr_41 z hz, sqr_99 z hz]

lemma power32_251 : (gf512% z 251)^32 = (gf512% z 20) := by
  rw [pow32_squares]
  rw [sqr_251 z hz, sqr_478 z hz, sqr_297 z hz, sqr_167 z hz, sqr_6 z hz]

lemma sigma_20 : sigmaM (mat512% z 111 251 343 343) = (mat512% z 175 20 230 230) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_111 z hz
  · exact power32_251 z hz
  · exact power32_343 z hz
  · exact power32_343 z hz

lemma power32_175 : (gf512% z 175)^32 = (gf512% z 255) := by
  rw [pow32_squares]
  rw [sqr_175 z hz, sqr_70 z hz, sqr_156 z hz, sqr_353 z hz, sqr_111 z hz]

lemma power32_20 : (gf512% z 20)^32 = (gf512% z 478) := by
  rw [pow32_squares]
  rw [sqr_20 z hz, sqr_272 z hz, sqr_452 z hz, sqr_109 z hz, sqr_251 z hz]

lemma sigma_21 : sigmaM (mat512% z 175 20 230 230) = (mat512% z 255 478 345 345) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_175 z hz
  · exact power32_20 z hz
  · exact power32_230 z hz
  · exact power32_230 z hz

lemma power32_255 : (gf512% z 255)^32 = (gf512% z 70) := by
  rw [pow32_squares]
  rw [sqr_255 z hz, sqr_462 z hz, sqr_41 z hz, sqr_99 z hz, sqr_175 z hz]

lemma power32_478 : (gf512% z 478)^32 = (gf512% z 272) := by
  rw [pow32_squares]
  rw [sqr_478 z hz, sqr_297 z hz, sqr_167 z hz, sqr_6 z hz, sqr_20 z hz]

lemma sigma_22 : sigmaM (mat512% z 255 478 345 345) = (mat512% z 70 272 143 143) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_255 z hz
  · exact power32_478 z hz
  · exact power32_345 z hz
  · exact power32_345 z hz

lemma power32_70 : (gf512% z 70)^32 = (gf512% z 462) := by
  rw [pow32_squares]
  rw [sqr_70 z hz, sqr_156 z hz, sqr_353 z hz, sqr_111 z hz, sqr_255 z hz]

lemma power32_272 : (gf512% z 272)^32 = (gf512% z 297) := by
  rw [pow32_squares]
  rw [sqr_272 z hz, sqr_452 z hz, sqr_109 z hz, sqr_251 z hz, sqr_478 z hz]

lemma sigma_23 : sigmaM (mat512% z 70 272 143 143) = (mat512% z 462 297 269 269) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_70 z hz
  · exact power32_272 z hz
  · exact power32_143 z hz
  · exact power32_143 z hz

lemma product_19 : (mat512% z 156 452 100 100) * (mat512% z 486 475 486 429) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 156)*(gf512% z 486) + (gf512% z 452)*(gf512% z 486) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 193))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 156)*(gf512% z 475) + (gf512% z 452)*(gf512% z 429) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 240))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 100)*(gf512% z 486) + (gf512% z 100)*(gf512% z 486) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 100)*(gf512% z 475) + (gf512% z 100)*(gf512% z 429) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 9))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_20 : (mat512% z 41 167 149 149) * (mat512% z 428 180 355 27) = (mat512% z 486 475 486 429) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 41)*(gf512% z 428) + (gf512% z 167)*(gf512% z 355) = (gf512% z 486)
    apply cert_eq z hz (Q := (gf512% z 83))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 41)*(gf512% z 180) + (gf512% z 167)*(gf512% z 27) = (gf512% z 475)
    apply cert_eq z hz (Q := (gf512% z 14))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 149)*(gf512% z 428) + (gf512% z 149)*(gf512% z 355) = (gf512% z 486)
    apply cert_eq z hz (Q := (gf512% z 53))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 149)*(gf512% z 180) + (gf512% z 149)*(gf512% z 27) = (gf512% z 429)
    apply cert_eq z hz (Q := (gf512% z 46))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_21 : (mat512% z 353 109 186 186) * (mat512% z 435 492 148 404) = (mat512% z 428 180 355 27) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 353)*(gf512% z 435) + (gf512% z 109)*(gf512% z 148) = (gf512% z 428)
    apply cert_eq z hz (Q := (gf512% z 235))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 353)*(gf512% z 492) + (gf512% z 109)*(gf512% z 404) = (gf512% z 180)
    apply cert_eq z hz (Q := (gf512% z 252))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 186)*(gf512% z 435) + (gf512% z 186)*(gf512% z 148) = (gf512% z 355)
    apply cert_eq z hz (Q := (gf512% z 85))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 186)*(gf512% z 492) + (gf512% z 186)*(gf512% z 404) = (gf512% z 27)
    apply cert_eq z hz (Q := (gf512% z 27))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_22 : (mat512% z 99 6 288 288) * (mat512% z 462 1 425 330) = (mat512% z 435 492 148 404) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 99)*(gf512% z 462) + (gf512% z 6)*(gf512% z 425) = (gf512% z 435)
    apply cert_eq z hz (Q := (gf512% z 39))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 99)*(gf512% z 1) + (gf512% z 6)*(gf512% z 330) = (gf512% z 492)
    apply cert_eq z hz (Q := (gf512% z 3))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 288)*(gf512% z 462) + (gf512% z 288)*(gf512% z 425) = (gf512% z 148)
    apply cert_eq z hz (Q := (gf512% z 52))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 288)*(gf512% z 1) + (gf512% z 288)*(gf512% z 330) = (gf512% z 404)
    apply cert_eq z hz (Q := (gf512% z 180))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_23 : (mat512% z 111 251 343 343) * (mat512% z 335 422 302 153) = (mat512% z 462 1 425 330) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 111)*(gf512% z 335) + (gf512% z 251)*(gf512% z 302) = (gf512% z 462)
    apply cert_eq z hz (Q := (gf512% z 73))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 111)*(gf512% z 422) + (gf512% z 251)*(gf512% z 153) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 16))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 343)*(gf512% z 335) + (gf512% z 343)*(gf512% z 302) = (gf512% z 425)
    apply cert_eq z hz (Q := (gf512% z 62))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 343)*(gf512% z 422) + (gf512% z 343)*(gf512% z 153) = (gf512% z 330)
    apply cert_eq z hz (Q := (gf512% z 183))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_24 : (mat512% z 175 20 230 230) * (mat512% z 499 278 114 136) = (mat512% z 335 422 302 153) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 175)*(gf512% z 499) + (gf512% z 20)*(gf512% z 114) = (gf512% z 335)
    apply cert_eq z hz (Q := (gf512% z 102))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 175)*(gf512% z 278) + (gf512% z 20)*(gf512% z 136) = (gf512% z 422)
    apply cert_eq z hz (Q := (gf512% z 84))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 230)*(gf512% z 499) + (gf512% z 230)*(gf512% z 114) = (gf512% z 302)
    apply cert_eq z hz (Q := (gf512% z 72))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 230)*(gf512% z 278) + (gf512% z 230)*(gf512% z 136) = (gf512% z 153)
    apply cert_eq z hz (Q := (gf512% z 77))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_25 : (mat512% z 255 478 345 345) * (mat512% z 324 283 210 325) = (mat512% z 499 278 114 136) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 255)*(gf512% z 324) + (gf512% z 478)*(gf512% z 210) = (gf512% z 499)
    apply cert_eq z hz (Q := (gf512% z 35))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 255)*(gf512% z 283) + (gf512% z 478)*(gf512% z 325) = (gf512% z 278)
    apply cert_eq z hz (Q := (gf512% z 169))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 345)*(gf512% z 324) + (gf512% z 345)*(gf512% z 210) = (gf512% z 114)
    apply cert_eq z hz (Q := (gf512% z 244))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 345)*(gf512% z 283) + (gf512% z 345)*(gf512% z 325) = (gf512% z 136)
    apply cert_eq z hz (Q := (gf512% z 38))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_26 : (mat512% z 70 272 143 143) * (mat512% z 462 297 269 269) = (mat512% z 324 283 210 325) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 70)*(gf512% z 462) + (gf512% z 272)*(gf512% z 269) = (gf512% z 324)
    apply cert_eq z hz (Q := (gf512% z 176))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 70)*(gf512% z 297) + (gf512% z 272)*(gf512% z 269) = (gf512% z 283)
    apply cert_eq z hz (Q := (gf512% z 173))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 143)*(gf512% z 462) + (gf512% z 143)*(gf512% z 269) = (gf512% z 210)
    apply cert_eq z hz (Q := (gf512% z 51))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 143)*(gf512% z 297) + (gf512% z 143)*(gf512% z 269) = (gf512% z 325)
    apply cert_eq z hz (Q := (gf512% z 9))
    ring_nf <;> reduce_mod_char! <;> ring

lemma norm_2 : semilinearNorm 9 (mat512% z 156 452 100 100) = 1 := by
  have h8 : semilinearNorm 1 (mat512% z 462 297 269 269) = (mat512% z 462 297 269 269) := by simp [semilinearNorm]
  have h7 : semilinearNorm 2 (mat512% z 70 272 143 143) = (mat512% z 324 283 210 325) := by
    change (mat512% z 70 272 143 143) * semilinearNorm 1 (sigmaM (mat512% z 70 272 143 143)) = _
    rw [sigma_23 z hz, h8]
    exact product_26 z hz
  have h6 : semilinearNorm 3 (mat512% z 255 478 345 345) = (mat512% z 499 278 114 136) := by
    change (mat512% z 255 478 345 345) * semilinearNorm 2 (sigmaM (mat512% z 255 478 345 345)) = _
    rw [sigma_22 z hz, h7]
    exact product_25 z hz
  have h5 : semilinearNorm 4 (mat512% z 175 20 230 230) = (mat512% z 335 422 302 153) := by
    change (mat512% z 175 20 230 230) * semilinearNorm 3 (sigmaM (mat512% z 175 20 230 230)) = _
    rw [sigma_21 z hz, h6]
    exact product_24 z hz
  have h4 : semilinearNorm 5 (mat512% z 111 251 343 343) = (mat512% z 462 1 425 330) := by
    change (mat512% z 111 251 343 343) * semilinearNorm 4 (sigmaM (mat512% z 111 251 343 343)) = _
    rw [sigma_20 z hz, h5]
    exact product_23 z hz
  have h3 : semilinearNorm 6 (mat512% z 99 6 288 288) = (mat512% z 435 492 148 404) := by
    change (mat512% z 99 6 288 288) * semilinearNorm 5 (sigmaM (mat512% z 99 6 288 288)) = _
    rw [sigma_19 z hz, h4]
    exact product_22 z hz
  have h2 : semilinearNorm 7 (mat512% z 353 109 186 186) = (mat512% z 428 180 355 27) := by
    change (mat512% z 353 109 186 186) * semilinearNorm 6 (sigmaM (mat512% z 353 109 186 186)) = _
    rw [sigma_18 z hz, h3]
    exact product_21 z hz
  have h1 : semilinearNorm 8 (mat512% z 41 167 149 149) = (mat512% z 486 475 486 429) := by
    change (mat512% z 41 167 149 149) * semilinearNorm 7 (sigmaM (mat512% z 41 167 149 149)) = _
    rw [sigma_17 z hz, h2]
    exact product_20 z hz
  have h0 : semilinearNorm 9 (mat512% z 156 452 100 100) = (mat512% z 1 0 0 1) := by
    change (mat512% z 156 452 100 100) * semilinearNorm 8 (sigmaM (mat512% z 156 452 100 100)) = _
    rw [sigma_16 z hz, h1]
    exact product_19 z hz
  simpa only [code_identity] using h0

lemma mtrace_5 : (mat512% z 156 452 100 100).trace = (gf512% z 248) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 156)+(gf512% z 100) = (gf512% z 248)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma mdet_4 : (mat512% z 156 452 100 100).det = (gf512% z 397) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 156)*(gf512% z 100) - (gf512% z 452)*(gf512% z 100) = (gf512% z 397)
  apply cert_eq z hz (Q := (gf512% z 61))
  ring_nf <;> reduce_mod_char! <;> ring

lemma elliptic_4 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 156 452 100 100) := by
  have ht : (gf512% z 248)*(gf512% z 6) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 397)*(gf512% z 6)^2 = (gf512% z 27) := by
    apply cert_eq z hz (Q := (gf512% z 15))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_5 z hz, mdet_4 z hz]
  apply no_quadratic_root hK (gf512% z 248) (gf512% z 397) (gf512% z 6) ht
  rw [hd]
  exact atr_0 z hz

lemma mdet_5 : (mat512% z 92 385 445 93).det = (gf512% z 77) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 92)*(gf512% z 93) - (gf512% z 385)*(gf512% z 445) = (gf512% z 77)
  apply cert_eq z hz (Q := (gf512% z 188))
  ring_nf <;> reduce_mod_char! <;> ring

lemma elliptic_5 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 92 385 445 93) := by
  have ht : (gf512% z 1)*(gf512% z 1) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 77)*(gf512% z 1)^2 = (gf512% z 77) := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_4 z hz, mdet_5 z hz]
  apply no_quadratic_root hK (gf512% z 1) (gf512% z 77) (gf512% z 1) ht
  rw [hd]
  exact atr_1 z hz

lemma good_2 (hK : ∀ x : K, x^512 = x) : Good (mat512% z 156 452 100 100) := by
  unfold Good
  rw [sigma_16 z hz, product_18 z hz]
  refine ⟨?_, elliptic_4 z hz hK, norm_2 z hz, elliptic_5 z hz hK⟩
  simpa using mtrace_4 z hz

#check good_2

lemma sqr_416 : (gf512% z 416)^2 = (gf512% z 215) := by
  apply cert_eq z hz (Q := (gf512% z 167))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_215 : (gf512% z 215)^2 = (gf512% z 428) := by
  apply cert_eq z hz (Q := (gf512% z 41))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_428 : (gf512% z 428)^2 = (gf512% z 135) := by
  apply cert_eq z hz (Q := (gf512% z 167))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_135 : (gf512% z 135)^2 = (gf512% z 36) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_36 : (gf512% z 36)^2 = (gf512% z 50) := by
  apply cert_eq z hz (Q := (gf512% z 2))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_416 : (gf512% z 416)^32 = (gf512% z 50) := by
  rw [pow32_squares]
  rw [sqr_416 z hz, sqr_215 z hz, sqr_428 z hz, sqr_135 z hz, sqr_36 z hz]

lemma sigma_24 : sigmaM (mat512% z 156 416 100 100) = (mat512% z 41 50 149 149) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_156 z hz
  · exact power32_416 z hz
  · exact power32_100 z hz
  · exact power32_100 z hz

lemma product_27 : (mat512% z 156 416 100 100) * (mat512% z 41 50 149 149) = (mat512% z 82 176 445 83) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 156)*(gf512% z 41) + (gf512% z 416)*(gf512% z 149) = (gf512% z 82)
    apply cert_eq z hz (Q := (gf512% z 110))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 156)*(gf512% z 50) + (gf512% z 416)*(gf512% z 149) = (gf512% z 176)
    apply cert_eq z hz (Q := (gf512% z 104))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 100)*(gf512% z 41) + (gf512% z 100)*(gf512% z 149) = (gf512% z 445)
    apply cert_eq z hz (Q := (gf512% z 29))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 100)*(gf512% z 50) + (gf512% z 100)*(gf512% z 149) = (gf512% z 83)
    apply cert_eq z hz (Q := (gf512% z 31))
    ring_nf <;> reduce_mod_char! <;> ring

lemma mtrace_6 : (mat512% z 82 176 445 83).trace = (gf512% z 1) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 82)+(gf512% z 83) = (gf512% z 1)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_50 : (gf512% z 50)^2 = (gf512% z 294) := by
  apply cert_eq z hz (Q := (gf512% z 2))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_294 : (gf512% z 294)^2 = (gf512% z 242) := by
  apply cert_eq z hz (Q := (gf512% z 134))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_242 : (gf512% z 242)^2 = (gf512% z 415) := by
  apply cert_eq z hz (Q := (gf512% z 43))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_415 : (gf512% z 415)^2 = (gf512% z 416) := by
  apply cert_eq z hz (Q := (gf512% z 165))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_50 : (gf512% z 50)^32 = (gf512% z 215) := by
  rw [pow32_squares]
  rw [sqr_50 z hz, sqr_294 z hz, sqr_242 z hz, sqr_415 z hz, sqr_416 z hz]

lemma sigma_25 : sigmaM (mat512% z 41 50 149 149) = (mat512% z 353 215 186 186) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_41 z hz
  · exact power32_50 z hz
  · exact power32_149 z hz
  · exact power32_149 z hz

lemma power32_215 : (gf512% z 215)^32 = (gf512% z 294) := by
  rw [pow32_squares]
  rw [sqr_215 z hz, sqr_428 z hz, sqr_135 z hz, sqr_36 z hz, sqr_50 z hz]

lemma sigma_26 : sigmaM (mat512% z 353 215 186 186) = (mat512% z 99 294 288 288) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_353 z hz
  · exact power32_215 z hz
  · exact power32_186 z hz
  · exact power32_186 z hz

lemma power32_294 : (gf512% z 294)^32 = (gf512% z 428) := by
  rw [pow32_squares]
  rw [sqr_294 z hz, sqr_242 z hz, sqr_415 z hz, sqr_416 z hz, sqr_215 z hz]

lemma sigma_27 : sigmaM (mat512% z 99 294 288 288) = (mat512% z 111 428 343 343) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_99 z hz
  · exact power32_294 z hz
  · exact power32_288 z hz
  · exact power32_288 z hz

lemma power32_428 : (gf512% z 428)^32 = (gf512% z 242) := by
  rw [pow32_squares]
  rw [sqr_428 z hz, sqr_135 z hz, sqr_36 z hz, sqr_50 z hz, sqr_294 z hz]

lemma sigma_28 : sigmaM (mat512% z 111 428 343 343) = (mat512% z 175 242 230 230) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_111 z hz
  · exact power32_428 z hz
  · exact power32_343 z hz
  · exact power32_343 z hz

lemma power32_242 : (gf512% z 242)^32 = (gf512% z 135) := by
  rw [pow32_squares]
  rw [sqr_242 z hz, sqr_415 z hz, sqr_416 z hz, sqr_215 z hz, sqr_428 z hz]

lemma sigma_29 : sigmaM (mat512% z 175 242 230 230) = (mat512% z 255 135 345 345) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_175 z hz
  · exact power32_242 z hz
  · exact power32_230 z hz
  · exact power32_230 z hz

lemma power32_135 : (gf512% z 135)^32 = (gf512% z 415) := by
  rw [pow32_squares]
  rw [sqr_135 z hz, sqr_36 z hz, sqr_50 z hz, sqr_294 z hz, sqr_242 z hz]

lemma sigma_30 : sigmaM (mat512% z 255 135 345 345) = (mat512% z 70 415 143 143) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_255 z hz
  · exact power32_135 z hz
  · exact power32_345 z hz
  · exact power32_345 z hz

lemma power32_415 : (gf512% z 415)^32 = (gf512% z 36) := by
  rw [pow32_squares]
  rw [sqr_415 z hz, sqr_416 z hz, sqr_215 z hz, sqr_428 z hz, sqr_135 z hz]

lemma sigma_31 : sigmaM (mat512% z 70 415 143 143) = (mat512% z 462 36 269 269) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_70 z hz
  · exact power32_415 z hz
  · exact power32_143 z hz
  · exact power32_143 z hz

lemma product_28 : (mat512% z 156 416 100 100) * (mat512% z 375 233 375 159) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 156)*(gf512% z 375) + (gf512% z 416)*(gf512% z 375) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 165))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 156)*(gf512% z 233) + (gf512% z 416)*(gf512% z 159) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 92))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 100)*(gf512% z 375) + (gf512% z 100)*(gf512% z 375) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 100)*(gf512% z 233) + (gf512% z 100)*(gf512% z 159) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 9))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_29 : (mat512% z 41 50 149 149) * (mat512% z 270 154 307 12) = (mat512% z 375 233 375 159) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 41)*(gf512% z 270) + (gf512% z 50)*(gf512% z 307) = (gf512% z 375)
    apply cert_eq z hz (Q := (gf512% z 15))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 41)*(gf512% z 154) + (gf512% z 50)*(gf512% z 12) = (gf512% z 233)
    apply cert_eq z hz (Q := (gf512% z 11))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 149)*(gf512% z 270) + (gf512% z 149)*(gf512% z 307) = (gf512% z 375)
    apply cert_eq z hz (Q := (gf512% z 14))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 149)*(gf512% z 154) + (gf512% z 149)*(gf512% z 12) = (gf512% z 159)
    apply cert_eq z hz (Q := (gf512% z 33))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_30 : (mat512% z 353 215 186 186) * (mat512% z 295 487 491 186) = (mat512% z 270 154 307 12) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 353)*(gf512% z 295) + (gf512% z 215)*(gf512% z 491) = (gf512% z 270)
    apply cert_eq z hz (Q := (gf512% z 232))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 353)*(gf512% z 487) + (gf512% z 215)*(gf512% z 186) = (gf512% z 154)
    apply cert_eq z hz (Q := (gf512% z 235))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 186)*(gf512% z 295) + (gf512% z 186)*(gf512% z 491) = (gf512% z 307)
    apply cert_eq z hz (Q := (gf512% z 59))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 186)*(gf512% z 487) + (gf512% z 186)*(gf512% z 186) = (gf512% z 12)
    apply cert_eq z hz (Q := (gf512% z 78))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_31 : (mat512% z 99 294 288 288) * (mat512% z 212 184 175 493) = (mat512% z 295 487 491 186) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 99)*(gf512% z 212) + (gf512% z 294)*(gf512% z 175) = (gf512% z 295)
    apply cert_eq z hz (Q := (gf512% z 73))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 99)*(gf512% z 184) + (gf512% z 294)*(gf512% z 493) = (gf512% z 487)
    apply cert_eq z hz (Q := (gf512% z 241))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 288)*(gf512% z 212) + (gf512% z 288)*(gf512% z 175) = (gf512% z 491)
    apply cert_eq z hz (Q := (gf512% z 59))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 288)*(gf512% z 184) + (gf512% z 288)*(gf512% z 493) = (gf512% z 186)
    apply cert_eq z hz (Q := (gf512% z 186))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_32 : (mat512% z 111 428 343 343) * (mat512% z 118 14 136 433) = (mat512% z 212 184 175 493) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 111)*(gf512% z 118) + (gf512% z 428)*(gf512% z 136) = (gf512% z 212)
    apply cert_eq z hz (Q := (gf512% z 102))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 111)*(gf512% z 14) + (gf512% z 428)*(gf512% z 433) = (gf512% z 184)
    apply cert_eq z hz (Q := (gf512% z 174))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 343)*(gf512% z 118) + (gf512% z 343)*(gf512% z 136) = (gf512% z 175)
    apply cert_eq z hz (Q := (gf512% z 101))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 343)*(gf512% z 14) + (gf512% z 343)*(gf512% z 433) = (gf512% z 493)
    apply cert_eq z hz (Q := (gf512% z 224))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_33 : (mat512% z 175 242 230 230) * (mat512% z 63 506 242 166) = (mat512% z 118 14 136 433) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 175)*(gf512% z 63) + (gf512% z 242)*(gf512% z 242) = (gf512% z 118)
    apply cert_eq z hz (Q := (gf512% z 39))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 175)*(gf512% z 506) + (gf512% z 242)*(gf512% z 166) = (gf512% z 14)
    apply cert_eq z hz (Q := (gf512% z 84))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 230)*(gf512% z 63) + (gf512% z 230)*(gf512% z 242) = (gf512% z 136)
    apply cert_eq z hz (Q := (gf512% z 38))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 230)*(gf512% z 506) + (gf512% z 230)*(gf512% z 166) = (gf512% z 433)
    apply cert_eq z hz (Q := (gf512% z 105))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_34 : (mat512% z 255 135 345 345) * (mat512% z 169 395 210 168) = (mat512% z 63 506 242 166) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 255)*(gf512% z 169) + (gf512% z 135)*(gf512% z 210) = (gf512% z 63)
    apply cert_eq z hz (Q := (gf512% z 6))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 255)*(gf512% z 395) + (gf512% z 135)*(gf512% z 168) = (gf512% z 506)
    apply cert_eq z hz (Q := (gf512% z 107))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 345)*(gf512% z 169) + (gf512% z 345)*(gf512% z 210) = (gf512% z 242)
    apply cert_eq z hz (Q := (gf512% z 49))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 345)*(gf512% z 395) + (gf512% z 345)*(gf512% z 168) = (gf512% z 166)
    apply cert_eq z hz (Q := (gf512% z 189))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_35 : (mat512% z 70 415 143 143) * (mat512% z 462 36 269 269) = (mat512% z 169 395 210 168) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 70)*(gf512% z 462) + (gf512% z 415)*(gf512% z 269) = (gf512% z 169)
    apply cert_eq z hz (Q := (gf512% z 246))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 70)*(gf512% z 36) + (gf512% z 415)*(gf512% z 269) = (gf512% z 395)
    apply cert_eq z hz (Q := (gf512% z 200))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 143)*(gf512% z 462) + (gf512% z 143)*(gf512% z 269) = (gf512% z 210)
    apply cert_eq z hz (Q := (gf512% z 51))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 143)*(gf512% z 36) + (gf512% z 143)*(gf512% z 269) = (gf512% z 168)
    apply cert_eq z hz (Q := (gf512% z 79))
    ring_nf <;> reduce_mod_char! <;> ring

lemma norm_3 : semilinearNorm 9 (mat512% z 156 416 100 100) = 1 := by
  have h8 : semilinearNorm 1 (mat512% z 462 36 269 269) = (mat512% z 462 36 269 269) := by simp [semilinearNorm]
  have h7 : semilinearNorm 2 (mat512% z 70 415 143 143) = (mat512% z 169 395 210 168) := by
    change (mat512% z 70 415 143 143) * semilinearNorm 1 (sigmaM (mat512% z 70 415 143 143)) = _
    rw [sigma_31 z hz, h8]
    exact product_35 z hz
  have h6 : semilinearNorm 3 (mat512% z 255 135 345 345) = (mat512% z 63 506 242 166) := by
    change (mat512% z 255 135 345 345) * semilinearNorm 2 (sigmaM (mat512% z 255 135 345 345)) = _
    rw [sigma_30 z hz, h7]
    exact product_34 z hz
  have h5 : semilinearNorm 4 (mat512% z 175 242 230 230) = (mat512% z 118 14 136 433) := by
    change (mat512% z 175 242 230 230) * semilinearNorm 3 (sigmaM (mat512% z 175 242 230 230)) = _
    rw [sigma_29 z hz, h6]
    exact product_33 z hz
  have h4 : semilinearNorm 5 (mat512% z 111 428 343 343) = (mat512% z 212 184 175 493) := by
    change (mat512% z 111 428 343 343) * semilinearNorm 4 (sigmaM (mat512% z 111 428 343 343)) = _
    rw [sigma_28 z hz, h5]
    exact product_32 z hz
  have h3 : semilinearNorm 6 (mat512% z 99 294 288 288) = (mat512% z 295 487 491 186) := by
    change (mat512% z 99 294 288 288) * semilinearNorm 5 (sigmaM (mat512% z 99 294 288 288)) = _
    rw [sigma_27 z hz, h4]
    exact product_31 z hz
  have h2 : semilinearNorm 7 (mat512% z 353 215 186 186) = (mat512% z 270 154 307 12) := by
    change (mat512% z 353 215 186 186) * semilinearNorm 6 (sigmaM (mat512% z 353 215 186 186)) = _
    rw [sigma_26 z hz, h3]
    exact product_30 z hz
  have h1 : semilinearNorm 8 (mat512% z 41 50 149 149) = (mat512% z 375 233 375 159) := by
    change (mat512% z 41 50 149 149) * semilinearNorm 7 (sigmaM (mat512% z 41 50 149 149)) = _
    rw [sigma_25 z hz, h2]
    exact product_29 z hz
  have h0 : semilinearNorm 9 (mat512% z 156 416 100 100) = (mat512% z 1 0 0 1) := by
    change (mat512% z 156 416 100 100) * semilinearNorm 8 (sigmaM (mat512% z 156 416 100 100)) = _
    rw [sigma_24 z hz, h1]
    exact product_28 z hz
  simpa only [code_identity] using h0

lemma mtrace_7 : (mat512% z 156 416 100 100).trace = (gf512% z 248) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 156)+(gf512% z 100) = (gf512% z 248)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma mdet_6 : (mat512% z 156 416 100 100).det = (gf512% z 311) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 156)*(gf512% z 100) - (gf512% z 416)*(gf512% z 100) = (gf512% z 311)
  apply cert_eq z hz (Q := (gf512% z 55))
  ring_nf <;> reduce_mod_char! <;> ring

lemma elliptic_6 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 156 416 100 100) := by
  have ht : (gf512% z 248)*(gf512% z 6) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 311)*(gf512% z 6)^2 = (gf512% z 279) := by
    apply cert_eq z hz (Q := (gf512% z 11))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_7 z hz, mdet_6 z hz]
  apply no_quadratic_root hK (gf512% z 248) (gf512% z 311) (gf512% z 6) ht
  rw [hd]
  exact atr_2 z hz

lemma mdet_7 : (mat512% z 82 176 445 83).det = (gf512% z 244) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 82)*(gf512% z 83) - (gf512% z 176)*(gf512% z 445) = (gf512% z 244)
  apply cert_eq z hz (Q := (gf512% z 114))
  ring_nf <;> reduce_mod_char! <;> ring

lemma elliptic_7 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 82 176 445 83) := by
  have ht : (gf512% z 1)*(gf512% z 1) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 244)*(gf512% z 1)^2 = (gf512% z 244) := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_6 z hz, mdet_7 z hz]
  apply no_quadratic_root hK (gf512% z 1) (gf512% z 244) (gf512% z 1) ht
  rw [hd]
  exact atr_3 z hz

lemma good_3 (hK : ∀ x : K, x^512 = x) : Good (mat512% z 156 416 100 100) := by
  unfold Good
  rw [sigma_24 z hz, product_27 z hz]
  refine ⟨?_, elliptic_6 z hz hK, norm_3 z hz, elliptic_7 z hz hK⟩
  simpa using mtrace_6 z hz

#check good_3

lemma sqr_481 : (gf512% z 481)^2 = (gf512% z 94) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_94 : (gf512% z 94)^2 = (gf512% z 476) := by
  apply cert_eq z hz (Q := (gf512% z 8))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_476 : (gf512% z 476)^2 = (gf512% z 301) := by
  apply cert_eq z hz (Q := (gf512% z 173))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_301 : (gf512% z 301)^2 = (gf512% z 183) := by
  apply cert_eq z hz (Q := (gf512% z 134))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_183 : (gf512% z 183)^2 = (gf512% z 262) := by
  apply cert_eq z hz (Q := (gf512% z 35))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_481 : (gf512% z 481)^32 = (gf512% z 262) := by
  rw [pow32_squares]
  rw [sqr_481 z hz, sqr_94 z hz, sqr_476 z hz, sqr_301 z hz, sqr_183 z hz]

lemma sigma_32 : sigmaM (mat512% z 316 100 481 0) = (mat512% z 27 149 262 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_316 z hz
  · exact power32_100 z hz
  · exact power32_481 z hz
  · exact power32_0 z hz

lemma product_36 : (mat512% z 316 100 481 0) * (mat512% z 27 149 262 0) = (mat512% z 499 42 418 498) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 316)*(gf512% z 27) + (gf512% z 100)*(gf512% z 262) = (gf512% z 499)
    apply cert_eq z hz (Q := (gf512% z 63))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 316)*(gf512% z 149) + (gf512% z 100)*(gf512% z 0) = (gf512% z 42)
    apply cert_eq z hz (Q := (gf512% z 70))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 481)*(gf512% z 27) + (gf512% z 0)*(gf512% z 262) = (gf512% z 418)
    apply cert_eq z hz (Q := (gf512% z 9))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 481)*(gf512% z 149) + (gf512% z 0)*(gf512% z 0) = (gf512% z 498)
    apply cert_eq z hz (Q := (gf512% z 119))
    ring_nf <;> reduce_mod_char! <;> ring

lemma mtrace_8 : (mat512% z 499 42 418 498).trace = (gf512% z 1) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 499)+(gf512% z 498) = (gf512% z 1)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_262 : (gf512% z 262)^2 = (gf512% z 208) := by
  apply cert_eq z hz (Q := (gf512% z 132))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_208 : (gf512% z 208)^2 = (gf512% z 441) := by
  apply cert_eq z hz (Q := (gf512% z 41))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_441 : (gf512% z 441)^2 = (gf512% z 406) := by
  apply cert_eq z hz (Q := (gf512% z 167))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_406 : (gf512% z 406)^2 = (gf512% z 481) := by
  apply cert_eq z hz (Q := (gf512% z 165))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_262 : (gf512% z 262)^32 = (gf512% z 94) := by
  rw [pow32_squares]
  rw [sqr_262 z hz, sqr_208 z hz, sqr_441 z hz, sqr_406 z hz, sqr_481 z hz]

lemma sigma_33 : sigmaM (mat512% z 27 149 262 0) = (mat512% z 438 186 94 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_27 z hz
  · exact power32_149 z hz
  · exact power32_262 z hz
  · exact power32_0 z hz

lemma power32_94 : (gf512% z 94)^32 = (gf512% z 208) := by
  rw [pow32_squares]
  rw [sqr_94 z hz, sqr_476 z hz, sqr_301 z hz, sqr_183 z hz, sqr_262 z hz]

lemma sigma_34 : sigmaM (mat512% z 438 186 94 0) = (mat512% z 325 288 208 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_438 z hz
  · exact power32_186 z hz
  · exact power32_94 z hz
  · exact power32_0 z hz

lemma power32_208 : (gf512% z 208)^32 = (gf512% z 476) := by
  rw [pow32_squares]
  rw [sqr_208 z hz, sqr_441 z hz, sqr_406 z hz, sqr_481 z hz, sqr_94 z hz]

lemma sigma_35 : sigmaM (mat512% z 325 288 208 0) = (mat512% z 451 343 476 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_325 z hz
  · exact power32_288 z hz
  · exact power32_208 z hz
  · exact power32_0 z hz

lemma power32_476 : (gf512% z 476)^32 = (gf512% z 441) := by
  rw [pow32_squares]
  rw [sqr_476 z hz, sqr_301 z hz, sqr_183 z hz, sqr_262 z hz, sqr_208 z hz]

lemma sigma_36 : sigmaM (mat512% z 451 343 476 0) = (mat512% z 93 230 441 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_451 z hz
  · exact power32_343 z hz
  · exact power32_476 z hz
  · exact power32_0 z hz

lemma power32_441 : (gf512% z 441)^32 = (gf512% z 301) := by
  rw [pow32_squares]
  rw [sqr_441 z hz, sqr_406 z hz, sqr_481 z hz, sqr_94 z hz, sqr_476 z hz]

lemma sigma_37 : sigmaM (mat512% z 93 230 441 0) = (mat512% z 120 345 301 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_93 z hz
  · exact power32_230 z hz
  · exact power32_441 z hz
  · exact power32_0 z hz

lemma power32_301 : (gf512% z 301)^32 = (gf512% z 406) := by
  rw [pow32_squares]
  rw [sqr_301 z hz, sqr_183 z hz, sqr_262 z hz, sqr_208 z hz, sqr_441 z hz]

lemma sigma_38 : sigmaM (mat512% z 120 345 301 0) = (mat512% z 473 143 406 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_120 z hz
  · exact power32_345 z hz
  · exact power32_301 z hz
  · exact power32_0 z hz

lemma power32_406 : (gf512% z 406)^32 = (gf512% z 183) := by
  rw [pow32_squares]
  rw [sqr_406 z hz, sqr_481 z hz, sqr_94 z hz, sqr_476 z hz, sqr_301 z hz]

lemma sigma_39 : sigmaM (mat512% z 473 143 406 0) = (mat512% z 490 269 183 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_473 z hz
  · exact power32_143 z hz
  · exact power32_406 z hz
  · exact power32_0 z hz

lemma product_37 : (mat512% z 316 100 481 0) * (mat512% z 0 308 118 447) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 316)*(gf512% z 0) + (gf512% z 100)*(gf512% z 118) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 9))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 316)*(gf512% z 308) + (gf512% z 100)*(gf512% z 447) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 172))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 481)*(gf512% z 0) + (gf512% z 0)*(gf512% z 118) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 481)*(gf512% z 308) + (gf512% z 0)*(gf512% z 447) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 229))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_38 : (mat512% z 27 149 262 0) * (mat512% z 282 269 94 197) = (mat512% z 0 308 118 447) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 27)*(gf512% z 282) + (gf512% z 149)*(gf512% z 94) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 24))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 27)*(gf512% z 269) + (gf512% z 149)*(gf512% z 197) = (gf512% z 308)
    apply cert_eq z hz (Q := (gf512% z 58))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 262)*(gf512% z 282) + (gf512% z 0)*(gf512% z 94) = (gf512% z 118)
    apply cert_eq z hz (Q := (gf512% z 138))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 262)*(gf512% z 269) + (gf512% z 0)*(gf512% z 197) = (gf512% z 447)
    apply cert_eq z hz (Q := (gf512% z 129))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_39 : (mat512% z 438 186 94 0) * (mat512% z 1 204 154 225) = (mat512% z 282 269 94 197) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 438)*(gf512% z 1) + (gf512% z 186)*(gf512% z 154) = (gf512% z 282)
    apply cert_eq z hz (Q := (gf512% z 40))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 438)*(gf512% z 204) + (gf512% z 186)*(gf512% z 225) = (gf512% z 269)
    apply cert_eq z hz (Q := (gf512% z 111))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 94)*(gf512% z 1) + (gf512% z 0)*(gf512% z 154) = (gf512% z 94)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 94)*(gf512% z 204) + (gf512% z 0)*(gf512% z 225) = (gf512% z 197)
    apply cert_eq z hz (Q := (gf512% z 29))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_40 : (mat512% z 325 288 208 0) * (mat512% z 414 309 378 438) = (mat512% z 1 204 154 225) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 325)*(gf512% z 414) + (gf512% z 288)*(gf512% z 378) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 87))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 325)*(gf512% z 309) + (gf512% z 288)*(gf512% z 438) = (gf512% z 204)
    apply cert_eq z hz (Q := (gf512% z 125))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 208)*(gf512% z 414) + (gf512% z 0)*(gf512% z 378) = (gf512% z 154)
    apply cert_eq z hz (Q := (gf512% z 90))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 208)*(gf512% z 309) + (gf512% z 0)*(gf512% z 438) = (gf512% z 225)
    apply cert_eq z hz (Q := (gf512% z 97))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_41 : (mat512% z 451 343 476 0) * (mat512% z 364 215 346 294) = (mat512% z 414 309 378 438) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 451)*(gf512% z 364) + (gf512% z 343)*(gf512% z 346) = (gf512% z 414)
    apply cert_eq z hz (Q := (gf512% z 76))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 451)*(gf512% z 215) + (gf512% z 343)*(gf512% z 294) = (gf512% z 309)
    apply cert_eq z hz (Q := (gf512% z 254))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 476)*(gf512% z 364) + (gf512% z 0)*(gf512% z 346) = (gf512% z 378)
    apply cert_eq z hz (Q := (gf512% z 202))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 476)*(gf512% z 215) + (gf512% z 0)*(gf512% z 294) = (gf512% z 438)
    apply cert_eq z hz (Q := (gf512% z 66))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_42 : (mat512% z 93 230 441 0) * (mat512% z 25 199 409 99) = (mat512% z 364 215 346 294) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 93)*(gf512% z 25) + (gf512% z 230)*(gf512% z 409) = (gf512% z 364)
    apply cert_eq z hz (Q := (gf512% z 79))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 93)*(gf512% z 199) + (gf512% z 230)*(gf512% z 99) = (gf512% z 215)
    apply cert_eq z hz (Q := (gf512% z 14))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 441)*(gf512% z 25) + (gf512% z 0)*(gf512% z 409) = (gf512% z 346)
    apply cert_eq z hz (Q := (gf512% z 11))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 441)*(gf512% z 199) + (gf512% z 0)*(gf512% z 99) = (gf512% z 294)
    apply cert_eq z hz (Q := (gf512% z 89))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_43 : (mat512% z 120 345 301 0) * (mat512% z 311 362 314 310) = (mat512% z 25 199 409 99) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 120)*(gf512% z 311) + (gf512% z 345)*(gf512% z 314) = (gf512% z 25)
    apply cert_eq z hz (Q := (gf512% z 139))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 120)*(gf512% z 362) + (gf512% z 345)*(gf512% z 310) = (gf512% z 199)
    apply cert_eq z hz (Q := (gf512% z 129))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 301)*(gf512% z 311) + (gf512% z 0)*(gf512% z 314) = (gf512% z 409)
    apply cert_eq z hz (Q := (gf512% z 138))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 301)*(gf512% z 362) + (gf512% z 0)*(gf512% z 310) = (gf512% z 99)
    apply cert_eq z hz (Q := (gf512% z 161))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_44 : (mat512% z 473 143 406 0) * (mat512% z 490 269 183 0) = (mat512% z 311 362 314 310) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 473)*(gf512% z 490) + (gf512% z 143)*(gf512% z 183) = (gf512% z 311)
    apply cert_eq z hz (Q := (gf512% z 144))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 473)*(gf512% z 269) + (gf512% z 143)*(gf512% z 0) = (gf512% z 362)
    apply cert_eq z hz (Q := (gf512% z 239))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 406)*(gf512% z 490) + (gf512% z 0)*(gf512% z 183) = (gf512% z 314)
    apply cert_eq z hz (Q := (gf512% z 134))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 406)*(gf512% z 269) + (gf512% z 0)*(gf512% z 0) = (gf512% z 310)
    apply cert_eq z hz (Q := (gf512% z 200))
    ring_nf <;> reduce_mod_char! <;> ring

lemma norm_4 : semilinearNorm 9 (mat512% z 316 100 481 0) = 1 := by
  have h8 : semilinearNorm 1 (mat512% z 490 269 183 0) = (mat512% z 490 269 183 0) := by simp [semilinearNorm]
  have h7 : semilinearNorm 2 (mat512% z 473 143 406 0) = (mat512% z 311 362 314 310) := by
    change (mat512% z 473 143 406 0) * semilinearNorm 1 (sigmaM (mat512% z 473 143 406 0)) = _
    rw [sigma_39 z hz, h8]
    exact product_44 z hz
  have h6 : semilinearNorm 3 (mat512% z 120 345 301 0) = (mat512% z 25 199 409 99) := by
    change (mat512% z 120 345 301 0) * semilinearNorm 2 (sigmaM (mat512% z 120 345 301 0)) = _
    rw [sigma_38 z hz, h7]
    exact product_43 z hz
  have h5 : semilinearNorm 4 (mat512% z 93 230 441 0) = (mat512% z 364 215 346 294) := by
    change (mat512% z 93 230 441 0) * semilinearNorm 3 (sigmaM (mat512% z 93 230 441 0)) = _
    rw [sigma_37 z hz, h6]
    exact product_42 z hz
  have h4 : semilinearNorm 5 (mat512% z 451 343 476 0) = (mat512% z 414 309 378 438) := by
    change (mat512% z 451 343 476 0) * semilinearNorm 4 (sigmaM (mat512% z 451 343 476 0)) = _
    rw [sigma_36 z hz, h5]
    exact product_41 z hz
  have h3 : semilinearNorm 6 (mat512% z 325 288 208 0) = (mat512% z 1 204 154 225) := by
    change (mat512% z 325 288 208 0) * semilinearNorm 5 (sigmaM (mat512% z 325 288 208 0)) = _
    rw [sigma_35 z hz, h4]
    exact product_40 z hz
  have h2 : semilinearNorm 7 (mat512% z 438 186 94 0) = (mat512% z 282 269 94 197) := by
    change (mat512% z 438 186 94 0) * semilinearNorm 6 (sigmaM (mat512% z 438 186 94 0)) = _
    rw [sigma_34 z hz, h3]
    exact product_39 z hz
  have h1 : semilinearNorm 8 (mat512% z 27 149 262 0) = (mat512% z 0 308 118 447) := by
    change (mat512% z 27 149 262 0) * semilinearNorm 7 (sigmaM (mat512% z 27 149 262 0)) = _
    rw [sigma_33 z hz, h2]
    exact product_38 z hz
  have h0 : semilinearNorm 9 (mat512% z 316 100 481 0) = (mat512% z 1 0 0 1) := by
    change (mat512% z 316 100 481 0) * semilinearNorm 8 (sigmaM (mat512% z 316 100 481 0)) = _
    rw [sigma_32 z hz, h1]
    exact product_37 z hz
  simpa only [code_identity] using h0

lemma mtrace_9 : (mat512% z 316 100 481 0).trace = (gf512% z 316) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 316)+(gf512% z 0) = (gf512% z 316)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma mdet_8 : (mat512% z 316 100 481 0).det = (gf512% z 452) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 316)*(gf512% z 0) - (gf512% z 100)*(gf512% z 481) = (gf512% z 452)
  apply cert_eq z hz (Q := (gf512% z 32))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_484 : (gf512% z 484)^2 = (gf512% z 79) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_427 : (gf512% z 427)^2 = (gf512% z 146) := by
  apply cert_eq z hz (Q := (gf512% z 167))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_374 : (gf512% z 374)^2 = (gf512% z 378) := by
  apply cert_eq z hz (Q := (gf512% z 142))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_158 : (gf512% z 158)^2 = (gf512% z 357) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_129 : (gf512% z 129)^2 = (gf512% z 48) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_468 : (gf512% z 468)^2 = (gf512% z 365) := by
  apply cert_eq z hz (Q := (gf512% z 173))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_137 : (gf512% z 137)^2 = (gf512% z 112) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_404 : (gf512% z 404)^2 = (gf512% z 485) := by
  apply cert_eq z hz (Q := (gf512% z 165))
  ring_nf <;> reduce_mod_char! <;> ring

lemma atr_4 : trace2 9 (gf512% z 484) = 1 := by
  have h0 : trace2 0 (gf512% z 484) = (gf512% z 0) := by simp [trace2]
  have h1 : trace2 1 (gf512% z 484) = (gf512% z 484) := by
    change (trace2 0 (gf512% z 484))^2 + (gf512% z 484) = _
    rw [h0, sqr_0 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h2 : trace2 2 (gf512% z 484) = (gf512% z 427) := by
    change (trace2 1 (gf512% z 484))^2 + (gf512% z 484) = _
    rw [h1, sqr_484 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h3 : trace2 3 (gf512% z 484) = (gf512% z 374) := by
    change (trace2 2 (gf512% z 484))^2 + (gf512% z 484) = _
    rw [h2, sqr_427 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h4 : trace2 4 (gf512% z 484) = (gf512% z 158) := by
    change (trace2 3 (gf512% z 484))^2 + (gf512% z 484) = _
    rw [h3, sqr_374 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h5 : trace2 5 (gf512% z 484) = (gf512% z 129) := by
    change (trace2 4 (gf512% z 484))^2 + (gf512% z 484) = _
    rw [h4, sqr_158 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h6 : trace2 6 (gf512% z 484) = (gf512% z 468) := by
    change (trace2 5 (gf512% z 484))^2 + (gf512% z 484) = _
    rw [h5, sqr_129 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h7 : trace2 7 (gf512% z 484) = (gf512% z 137) := by
    change (trace2 6 (gf512% z 484))^2 + (gf512% z 484) = _
    rw [h6, sqr_468 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h8 : trace2 8 (gf512% z 484) = (gf512% z 404) := by
    change (trace2 7 (gf512% z 484))^2 + (gf512% z 484) = _
    rw [h7, sqr_137 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h9 : trace2 9 (gf512% z 484) = (gf512% z 1) := by
    change (trace2 8 (gf512% z 484))^2 + (gf512% z 484) = _
    rw [h8, sqr_404 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  simpa using h9

lemma elliptic_8 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 316 100 481 0) := by
  have ht : (gf512% z 316)*(gf512% z 375) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 165))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 452)*(gf512% z 375)^2 = (gf512% z 484) := by
    apply cert_eq z hz (Q := (gf512% z 59504))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_9 z hz, mdet_8 z hz]
  apply no_quadratic_root hK (gf512% z 316) (gf512% z 452) (gf512% z 375) ht
  rw [hd]
  exact atr_4 z hz

lemma mdet_9 : (mat512% z 499 42 418 498).det = (gf512% z 368) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 499)*(gf512% z 498) - (gf512% z 42)*(gf512% z 418) = (gf512% z 368)
  apply cert_eq z hz (Q := (gf512% z 178))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_368 : (gf512% z 368)^2 = (gf512% z 366) := by
  apply cert_eq z hz (Q := (gf512% z 142))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_30 : (gf512% z 30)^2 = (gf512% z 340) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_322 : (gf512% z 322)^2 = (gf512% z 72) := by
  apply cert_eq z hz (Q := (gf512% z 140))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_214 : (gf512% z 214)^2 = (gf512% z 429) := by
  apply cert_eq z hz (Q := (gf512% z 41))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_221 : (gf512% z 221)^2 = (gf512% z 488) := by
  apply cert_eq z hz (Q := (gf512% z 41))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_152 : (gf512% z 152)^2 = (gf512% z 369) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma atr_5 : trace2 9 (gf512% z 368) = 1 := by
  have h0 : trace2 0 (gf512% z 368) = (gf512% z 0) := by simp [trace2]
  have h1 : trace2 1 (gf512% z 368) = (gf512% z 368) := by
    change (trace2 0 (gf512% z 368))^2 + (gf512% z 368) = _
    rw [h0, sqr_0 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h2 : trace2 2 (gf512% z 368) = (gf512% z 30) := by
    change (trace2 1 (gf512% z 368))^2 + (gf512% z 368) = _
    rw [h1, sqr_368 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h3 : trace2 3 (gf512% z 368) = (gf512% z 36) := by
    change (trace2 2 (gf512% z 368))^2 + (gf512% z 368) = _
    rw [h2, sqr_30 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h4 : trace2 4 (gf512% z 368) = (gf512% z 322) := by
    change (trace2 3 (gf512% z 368))^2 + (gf512% z 368) = _
    rw [h3, sqr_36 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h5 : trace2 5 (gf512% z 368) = (gf512% z 312) := by
    change (trace2 4 (gf512% z 368))^2 + (gf512% z 368) = _
    rw [h4, sqr_322 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h6 : trace2 6 (gf512% z 368) = (gf512% z 214) := by
    change (trace2 5 (gf512% z 368))^2 + (gf512% z 368) = _
    rw [h5, sqr_312 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h7 : trace2 7 (gf512% z 368) = (gf512% z 221) := by
    change (trace2 6 (gf512% z 368))^2 + (gf512% z 368) = _
    rw [h6, sqr_214 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h8 : trace2 8 (gf512% z 368) = (gf512% z 152) := by
    change (trace2 7 (gf512% z 368))^2 + (gf512% z 368) = _
    rw [h7, sqr_221 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h9 : trace2 9 (gf512% z 368) = (gf512% z 1) := by
    change (trace2 8 (gf512% z 368))^2 + (gf512% z 368) = _
    rw [h8, sqr_152 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  simpa using h9

lemma elliptic_9 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 499 42 418 498) := by
  have ht : (gf512% z 1)*(gf512% z 1) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 368)*(gf512% z 1)^2 = (gf512% z 368) := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_8 z hz, mdet_9 z hz]
  apply no_quadratic_root hK (gf512% z 1) (gf512% z 368) (gf512% z 1) ht
  rw [hd]
  exact atr_5 z hz

lemma good_4 (hK : ∀ x : K, x^512 = x) : Good (mat512% z 316 100 481 0) := by
  unfold Good
  rw [sigma_32 z hz, product_36 z hz]
  refine ⟨?_, elliptic_8 z hz hK, norm_4 z hz, elliptic_9 z hz hK⟩
  simpa using mtrace_8 z hz

#check good_4

lemma sqr_389 : (gf512% z 389)^2 = (gf512% z 228) := by
  apply cert_eq z hz (Q := (gf512% z 165))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_228 : (gf512% z 228)^2 = (gf512% z 139) := by
  apply cert_eq z hz (Q := (gf512% z 43))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_139 : (gf512% z 139)^2 = (gf512% z 116) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_116 : (gf512% z 116)^2 = (gf512% z 442) := by
  apply cert_eq z hz (Q := (gf512% z 10))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_389 : (gf512% z 389)^32 = (gf512% z 403) := by
  rw [pow32_squares]
  rw [sqr_389 z hz, sqr_228 z hz, sqr_139 z hz, sqr_116 z hz, sqr_442 z hz]

lemma sigma_40 : sigmaM (mat512% z 316 389 481 0) = (mat512% z 27 403 262 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_316 z hz
  · exact power32_389 z hz
  · exact power32_481 z hz
  · exact power32_0 z hz

lemma product_45 : (mat512% z 316 389 481 0) * (mat512% z 27 403 262 0) = (mat512% z 272 427 418 273) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 316)*(gf512% z 27) + (gf512% z 389)*(gf512% z 262) = (gf512% z 272)
    apply cert_eq z hz (Q := (gf512% z 202))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 316)*(gf512% z 403) + (gf512% z 389)*(gf512% z 0) = (gf512% z 427)
    apply cert_eq z hz (Q := (gf512% z 223))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 481)*(gf512% z 27) + (gf512% z 0)*(gf512% z 262) = (gf512% z 418)
    apply cert_eq z hz (Q := (gf512% z 9))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 481)*(gf512% z 403) + (gf512% z 0)*(gf512% z 0) = (gf512% z 273)
    apply cert_eq z hz (Q := (gf512% z 130))
    ring_nf <;> reduce_mod_char! <;> ring

lemma mtrace_10 : (mat512% z 272 427 418 273).trace = (gf512% z 1) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 272)+(gf512% z 273) = (gf512% z 1)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_496 : (gf512% z 496)^2 = (gf512% z 351) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_351 : (gf512% z 351)^2 = (gf512% z 281) := by
  apply cert_eq z hz (Q := (gf512% z 140))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_281 : (gf512% z 281)^2 = (gf512% z 389) := by
  apply cert_eq z hz (Q := (gf512% z 132))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_403 : (gf512% z 403)^32 = (gf512% z 228) := by
  rw [pow32_squares]
  rw [sqr_403 z hz, sqr_496 z hz, sqr_351 z hz, sqr_281 z hz, sqr_389 z hz]

lemma sigma_41 : sigmaM (mat512% z 27 403 262 0) = (mat512% z 438 228 94 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_27 z hz
  · exact power32_403 z hz
  · exact power32_262 z hz
  · exact power32_0 z hz

lemma power32_228 : (gf512% z 228)^32 = (gf512% z 496) := by
  rw [pow32_squares]
  rw [sqr_228 z hz, sqr_139 z hz, sqr_116 z hz, sqr_442 z hz, sqr_403 z hz]

lemma sigma_42 : sigmaM (mat512% z 438 228 94 0) = (mat512% z 325 496 208 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_438 z hz
  · exact power32_228 z hz
  · exact power32_94 z hz
  · exact power32_0 z hz

lemma power32_496 : (gf512% z 496)^32 = (gf512% z 139) := by
  rw [pow32_squares]
  rw [sqr_496 z hz, sqr_351 z hz, sqr_281 z hz, sqr_389 z hz, sqr_228 z hz]

lemma sigma_43 : sigmaM (mat512% z 325 496 208 0) = (mat512% z 451 139 476 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_325 z hz
  · exact power32_496 z hz
  · exact power32_208 z hz
  · exact power32_0 z hz

lemma power32_139 : (gf512% z 139)^32 = (gf512% z 351) := by
  rw [pow32_squares]
  rw [sqr_139 z hz, sqr_116 z hz, sqr_442 z hz, sqr_403 z hz, sqr_496 z hz]

lemma sigma_44 : sigmaM (mat512% z 451 139 476 0) = (mat512% z 93 351 441 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_451 z hz
  · exact power32_139 z hz
  · exact power32_476 z hz
  · exact power32_0 z hz

lemma power32_351 : (gf512% z 351)^32 = (gf512% z 116) := by
  rw [pow32_squares]
  rw [sqr_351 z hz, sqr_281 z hz, sqr_389 z hz, sqr_228 z hz, sqr_139 z hz]

lemma sigma_45 : sigmaM (mat512% z 93 351 441 0) = (mat512% z 120 116 301 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_93 z hz
  · exact power32_351 z hz
  · exact power32_441 z hz
  · exact power32_0 z hz

lemma power32_116 : (gf512% z 116)^32 = (gf512% z 281) := by
  rw [pow32_squares]
  rw [sqr_116 z hz, sqr_442 z hz, sqr_403 z hz, sqr_496 z hz, sqr_351 z hz]

lemma sigma_46 : sigmaM (mat512% z 120 116 301 0) = (mat512% z 473 281 406 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_120 z hz
  · exact power32_116 z hz
  · exact power32_301 z hz
  · exact power32_0 z hz

lemma power32_281 : (gf512% z 281)^32 = (gf512% z 442) := by
  rw [pow32_squares]
  rw [sqr_281 z hz, sqr_389 z hz, sqr_228 z hz, sqr_139 z hz, sqr_116 z hz]

lemma sigma_47 : sigmaM (mat512% z 473 281 406 0) = (mat512% z 490 442 183 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_473 z hz
  · exact power32_281 z hz
  · exact power32_406 z hz
  · exact power32_0 z hz

lemma product_46 : (mat512% z 316 389 481 0) * (mat512% z 0 308 257 139) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 316)*(gf512% z 0) + (gf512% z 389)*(gf512% z 257) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 196))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 316)*(gf512% z 308) + (gf512% z 389)*(gf512% z 139) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 231))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 481)*(gf512% z 0) + (gf512% z 0)*(gf512% z 257) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 481)*(gf512% z 308) + (gf512% z 0)*(gf512% z 139) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 229))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_47 : (mat512% z 27 403 262 0) * (mat512% z 431 354 85 54) = (mat512% z 0 308 257 139) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 27)*(gf512% z 431) + (gf512% z 403)*(gf512% z 85) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 54))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 27)*(gf512% z 354) + (gf512% z 403)*(gf512% z 54) = (gf512% z 308)
    apply cert_eq z hz (Q := (gf512% z 24))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 262)*(gf512% z 431) + (gf512% z 0)*(gf512% z 85) = (gf512% z 257)
    apply cert_eq z hz (Q := (gf512% z 211))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 262)*(gf512% z 354) + (gf512% z 0)*(gf512% z 54) = (gf512% z 139)
    apply cert_eq z hz (Q := (gf512% z 183))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_48 : (mat512% z 438 228 94 0) * (mat512% z 461 166 453 243) = (mat512% z 431 354 85 54) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 438)*(gf512% z 461) + (gf512% z 228)*(gf512% z 453) = (gf512% z 431)
    apply cert_eq z hz (Q := (gf512% z 213))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 438)*(gf512% z 166) + (gf512% z 228)*(gf512% z 243) = (gf512% z 354)
    apply cert_eq z hz (Q := (gf512% z 90))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 94)*(gf512% z 461) + (gf512% z 0)*(gf512% z 453) = (gf512% z 85)
    apply cert_eq z hz (Q := (gf512% z 51))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 94)*(gf512% z 166) + (gf512% z 0)*(gf512% z 243) = (gf512% z 54)
    apply cert_eq z hz (Q := (gf512% z 18))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_49 : (mat512% z 325 496 208 0) * (mat512% z 299 230 215 303) = (mat512% z 461 166 453 243) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 325)*(gf512% z 299) + (gf512% z 496)*(gf512% z 215) = (gf512% z 461)
    apply cert_eq z hz (Q := (gf512% z 250))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 325)*(gf512% z 230) + (gf512% z 496)*(gf512% z 303) = (gf512% z 166)
    apply cert_eq z hz (Q := (gf512% z 136))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 208)*(gf512% z 299) + (gf512% z 0)*(gf512% z 215) = (gf512% z 453)
    apply cert_eq z hz (Q := (gf512% z 101))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 208)*(gf512% z 230) + (gf512% z 0)*(gf512% z 303) = (gf512% z 243)
    apply cert_eq z hz (Q := (gf512% z 35))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_50 : (mat512% z 451 139 476 0) * (mat512% z 96 347 276 423) = (mat512% z 299 230 215 303) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 451)*(gf512% z 96) + (gf512% z 139)*(gf512% z 276) = (gf512% z 299)
    apply cert_eq z hz (Q := (gf512% z 103))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 451)*(gf512% z 347) + (gf512% z 139)*(gf512% z 423) = (gf512% z 230)
    apply cert_eq z hz (Q := (gf512% z 186))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 476)*(gf512% z 96) + (gf512% z 0)*(gf512% z 276) = (gf512% z 215)
    apply cert_eq z hz (Q := (gf512% z 39))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 476)*(gf512% z 347) + (gf512% z 0)*(gf512% z 423) = (gf512% z 303)
    apply cert_eq z hz (Q := (gf512% z 219))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_51 : (mat512% z 93 351 441 0) * (mat512% z 261 148 223 210) = (mat512% z 96 347 276 423) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 93)*(gf512% z 261) + (gf512% z 351)*(gf512% z 223) = (gf512% z 96)
    apply cert_eq z hz (Q := (gf512% z 92))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 93)*(gf512% z 148) + (gf512% z 351)*(gf512% z 210) = (gf512% z 347)
    apply cert_eq z hz (Q := (gf512% z 97))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 441)*(gf512% z 261) + (gf512% z 0)*(gf512% z 223) = (gf512% z 276)
    apply cert_eq z hz (Q := (gf512% z 217))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 441)*(gf512% z 148) + (gf512% z 0)*(gf512% z 210) = (gf512% z 423)
    apply cert_eq z hz (Q := (gf512% z 99))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_52 : (mat512% z 120 116 301 0) * (mat512% z 20 113 314 21) = (mat512% z 261 148 223 210) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 120)*(gf512% z 20) + (gf512% z 116)*(gf512% z 314) = (gf512% z 261)
    apply cert_eq z hz (Q := (gf512% z 61))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 120)*(gf512% z 113) + (gf512% z 116)*(gf512% z 21) = (gf512% z 148)
    apply cert_eq z hz (Q := (gf512% z 8))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 301)*(gf512% z 20) + (gf512% z 0)*(gf512% z 314) = (gf512% z 223)
    apply cert_eq z hz (Q := (gf512% z 11))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 301)*(gf512% z 113) + (gf512% z 0)*(gf512% z 21) = (gf512% z 210)
    apply cert_eq z hz (Q := (gf512% z 63))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_53 : (mat512% z 473 281 406 0) * (mat512% z 490 442 183 0) = (mat512% z 20 113 314 21) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 473)*(gf512% z 490) + (gf512% z 281)*(gf512% z 183) = (gf512% z 20)
    apply cert_eq z hz (Q := (gf512% z 225))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 473)*(gf512% z 442) + (gf512% z 281)*(gf512% z 0) = (gf512% z 113)
    apply cert_eq z hz (Q := (gf512% z 139))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 406)*(gf512% z 490) + (gf512% z 0)*(gf512% z 183) = (gf512% z 314)
    apply cert_eq z hz (Q := (gf512% z 134))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 406)*(gf512% z 442) + (gf512% z 0)*(gf512% z 0) = (gf512% z 21)
    apply cert_eq z hz (Q := (gf512% z 185))
    ring_nf <;> reduce_mod_char! <;> ring

lemma norm_5 : semilinearNorm 9 (mat512% z 316 389 481 0) = 1 := by
  have h8 : semilinearNorm 1 (mat512% z 490 442 183 0) = (mat512% z 490 442 183 0) := by simp [semilinearNorm]
  have h7 : semilinearNorm 2 (mat512% z 473 281 406 0) = (mat512% z 20 113 314 21) := by
    change (mat512% z 473 281 406 0) * semilinearNorm 1 (sigmaM (mat512% z 473 281 406 0)) = _
    rw [sigma_47 z hz, h8]
    exact product_53 z hz
  have h6 : semilinearNorm 3 (mat512% z 120 116 301 0) = (mat512% z 261 148 223 210) := by
    change (mat512% z 120 116 301 0) * semilinearNorm 2 (sigmaM (mat512% z 120 116 301 0)) = _
    rw [sigma_46 z hz, h7]
    exact product_52 z hz
  have h5 : semilinearNorm 4 (mat512% z 93 351 441 0) = (mat512% z 96 347 276 423) := by
    change (mat512% z 93 351 441 0) * semilinearNorm 3 (sigmaM (mat512% z 93 351 441 0)) = _
    rw [sigma_45 z hz, h6]
    exact product_51 z hz
  have h4 : semilinearNorm 5 (mat512% z 451 139 476 0) = (mat512% z 299 230 215 303) := by
    change (mat512% z 451 139 476 0) * semilinearNorm 4 (sigmaM (mat512% z 451 139 476 0)) = _
    rw [sigma_44 z hz, h5]
    exact product_50 z hz
  have h3 : semilinearNorm 6 (mat512% z 325 496 208 0) = (mat512% z 461 166 453 243) := by
    change (mat512% z 325 496 208 0) * semilinearNorm 5 (sigmaM (mat512% z 325 496 208 0)) = _
    rw [sigma_43 z hz, h4]
    exact product_49 z hz
  have h2 : semilinearNorm 7 (mat512% z 438 228 94 0) = (mat512% z 431 354 85 54) := by
    change (mat512% z 438 228 94 0) * semilinearNorm 6 (sigmaM (mat512% z 438 228 94 0)) = _
    rw [sigma_42 z hz, h3]
    exact product_48 z hz
  have h1 : semilinearNorm 8 (mat512% z 27 403 262 0) = (mat512% z 0 308 257 139) := by
    change (mat512% z 27 403 262 0) * semilinearNorm 7 (sigmaM (mat512% z 27 403 262 0)) = _
    rw [sigma_41 z hz, h2]
    exact product_47 z hz
  have h0 : semilinearNorm 9 (mat512% z 316 389 481 0) = (mat512% z 1 0 0 1) := by
    change (mat512% z 316 389 481 0) * semilinearNorm 8 (sigmaM (mat512% z 316 389 481 0)) = _
    rw [sigma_40 z hz, h1]
    exact product_46 z hz
  simpa only [code_identity] using h0

lemma mtrace_11 : (mat512% z 316 389 481 0).trace = (gf512% z 316) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 316)+(gf512% z 0) = (gf512% z 316)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma mdet_10 : (mat512% z 316 389 481 0).det = (gf512% z 410) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 316)*(gf512% z 0) - (gf512% z 389)*(gf512% z 481) = (gf512% z 410)
  apply cert_eq z hz (Q := (gf512% z 143))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_69 : (gf512% z 69)^2 = (gf512% z 153) := by
  apply cert_eq z hz (Q := (gf512% z 8))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_194 : (gf512% z 194)^2 = (gf512% z 189) := by
  apply cert_eq z hz (Q := (gf512% z 41))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_414 : (gf512% z 414)^2 = (gf512% z 417) := by
  apply cert_eq z hz (Q := (gf512% z 165))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_10 : (gf512% z 10)^2 = (gf512% z 68) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma atr_6 : trace2 9 (gf512% z 69) = 1 := by
  have h0 : trace2 0 (gf512% z 69) = (gf512% z 0) := by simp [trace2]
  have h1 : trace2 1 (gf512% z 69) = (gf512% z 69) := by
    change (trace2 0 (gf512% z 69))^2 + (gf512% z 69) = _
    rw [h0, sqr_0 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h2 : trace2 2 (gf512% z 69) = (gf512% z 220) := by
    change (trace2 1 (gf512% z 69))^2 + (gf512% z 69) = _
    rw [h1, sqr_69 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h3 : trace2 3 (gf512% z 69) = (gf512% z 428) := by
    change (trace2 2 (gf512% z 69))^2 + (gf512% z 69) = _
    rw [h2, sqr_220 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h4 : trace2 4 (gf512% z 69) = (gf512% z 194) := by
    change (trace2 3 (gf512% z 69))^2 + (gf512% z 69) = _
    rw [h3, sqr_428 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h5 : trace2 5 (gf512% z 69) = (gf512% z 248) := by
    change (trace2 4 (gf512% z 69))^2 + (gf512% z 69) = _
    rw [h4, sqr_194 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h6 : trace2 6 (gf512% z 69) = (gf512% z 414) := by
    change (trace2 5 (gf512% z 69))^2 + (gf512% z 69) = _
    rw [h5, sqr_248 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h7 : trace2 7 (gf512% z 69) = (gf512% z 484) := by
    change (trace2 6 (gf512% z 69))^2 + (gf512% z 69) = _
    rw [h6, sqr_414 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h8 : trace2 8 (gf512% z 69) = (gf512% z 10) := by
    change (trace2 7 (gf512% z 69))^2 + (gf512% z 69) = _
    rw [h7, sqr_484 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h9 : trace2 9 (gf512% z 69) = (gf512% z 1) := by
    change (trace2 8 (gf512% z 69))^2 + (gf512% z 69) = _
    rw [h8, sqr_10 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  simpa using h9

lemma elliptic_10 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 316 389 481 0) := by
  have ht : (gf512% z 316)*(gf512% z 375) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 165))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 410)*(gf512% z 375)^2 = (gf512% z 69) := by
    apply cert_eq z hz (Q := (gf512% z 50279))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_11 z hz, mdet_10 z hz]
  apply no_quadratic_root hK (gf512% z 316) (gf512% z 410) (gf512% z 375) ht
  rw [hd]
  exact atr_6 z hz

lemma mdet_11 : (mat512% z 272 427 418 273).det = (gf512% z 211) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 272)*(gf512% z 273) - (gf512% z 427)*(gf512% z 418) = (gf512% z 211)
  apply cert_eq z hz (Q := (gf512% z 37))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_211 : (gf512% z 211)^2 = (gf512% z 444) := by
  apply cert_eq z hz (Q := (gf512% z 41))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_367 : (gf512% z 367)^2 = (gf512% z 59) := by
  apply cert_eq z hz (Q := (gf512% z 142))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_232 : (gf512% z 232)^2 = (gf512% z 219) := by
  apply cert_eq z hz (Q := (gf512% z 43))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_8 : (gf512% z 8)^2 = (gf512% z 64) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_147 : (gf512% z 147)^2 = (gf512% z 308) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_487 : (gf512% z 487)^2 = (gf512% z 74) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_153 : (gf512% z 153)^2 = (gf512% z 368) := by
  apply cert_eq z hz (Q := (gf512% z 33))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_419 : (gf512% z 419)^2 = (gf512% z 210) := by
  apply cert_eq z hz (Q := (gf512% z 167))
  ring_nf <;> reduce_mod_char! <;> ring

lemma atr_7 : trace2 9 (gf512% z 211) = 1 := by
  have h0 : trace2 0 (gf512% z 211) = (gf512% z 0) := by simp [trace2]
  have h1 : trace2 1 (gf512% z 211) = (gf512% z 211) := by
    change (trace2 0 (gf512% z 211))^2 + (gf512% z 211) = _
    rw [h0, sqr_0 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h2 : trace2 2 (gf512% z 211) = (gf512% z 367) := by
    change (trace2 1 (gf512% z 211))^2 + (gf512% z 211) = _
    rw [h1, sqr_211 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h3 : trace2 3 (gf512% z 211) = (gf512% z 232) := by
    change (trace2 2 (gf512% z 211))^2 + (gf512% z 211) = _
    rw [h2, sqr_367 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h4 : trace2 4 (gf512% z 211) = (gf512% z 8) := by
    change (trace2 3 (gf512% z 211))^2 + (gf512% z 211) = _
    rw [h3, sqr_232 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h5 : trace2 5 (gf512% z 211) = (gf512% z 147) := by
    change (trace2 4 (gf512% z 211))^2 + (gf512% z 211) = _
    rw [h4, sqr_8 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h6 : trace2 6 (gf512% z 211) = (gf512% z 487) := by
    change (trace2 5 (gf512% z 211))^2 + (gf512% z 211) = _
    rw [h5, sqr_147 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h7 : trace2 7 (gf512% z 211) = (gf512% z 153) := by
    change (trace2 6 (gf512% z 211))^2 + (gf512% z 211) = _
    rw [h6, sqr_487 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h8 : trace2 8 (gf512% z 211) = (gf512% z 419) := by
    change (trace2 7 (gf512% z 211))^2 + (gf512% z 211) = _
    rw [h7, sqr_153 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  have h9 : trace2 9 (gf512% z 211) = (gf512% z 1) := by
    change (trace2 8 (gf512% z 211))^2 + (gf512% z 211) = _
    rw [h8, sqr_419 z hz]
    ring_nf <;> reduce_mod_char! <;> ring
  simpa using h9

lemma elliptic_11 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 272 427 418 273) := by
  have ht : (gf512% z 1)*(gf512% z 1) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 211)*(gf512% z 1)^2 = (gf512% z 211) := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_10 z hz, mdet_11 z hz]
  apply no_quadratic_root hK (gf512% z 1) (gf512% z 211) (gf512% z 1) ht
  rw [hd]
  exact atr_7 z hz

lemma good_5 (hK : ∀ x : K, x^512 = x) : Good (mat512% z 316 389 481 0) := by
  unfold Good
  rw [sigma_40 z hz, product_45 z hz]
  refine ⟨?_, elliptic_10 z hz hK, norm_5 z hz, elliptic_11 z hz hK⟩
  simpa using mtrace_10 z hz

#check good_5

lemma sqr_488 : (gf512% z 488)^2 = (gf512% z 31) := by
  apply cert_eq z hz (Q := (gf512% z 175))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_31 : (gf512% z 31)^2 = (gf512% z 341) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_341 : (gf512% z 341)^2 = (gf512% z 349) := by
  apply cert_eq z hz (Q := (gf512% z 140))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_349 : (gf512% z 349)^2 = (gf512% z 285) := by
  apply cert_eq z hz (Q := (gf512% z 140))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_221 : (gf512% z 221)^32 = (gf512% z 285) := by
  rw [pow32_squares]
  rw [sqr_221 z hz, sqr_488 z hz, sqr_31 z hz, sqr_341 z hz, sqr_349 z hz]

lemma sqr_185 : (gf512% z 185)^2 = (gf512% z 338) := by
  apply cert_eq z hz (Q := (gf512% z 35))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_338 : (gf512% z 338)^2 = (gf512% z 328) := by
  apply cert_eq z hz (Q := (gf512% z 140))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_328 : (gf512% z 328)^2 = (gf512% z 12) := by
  apply cert_eq z hz (Q := (gf512% z 140))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_12 : (gf512% z 12)^2 = (gf512% z 80) := by
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_185 : (gf512% z 185)^32 = (gf512% z 392) := by
  rw [pow32_squares]
  rw [sqr_185 z hz, sqr_338 z hz, sqr_328 z hz, sqr_12 z hz, sqr_80 z hz]

lemma sigma_48 : sigmaM (mat512% z 221 185 481 481) = (mat512% z 285 392 262 262) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_221 z hz
  · exact power32_185 z hz
  · exact power32_481 z hz
  · exact power32_481 z hz

lemma product_54 : (mat512% z 221 185 481 481) * (mat512% z 285 392 262 262) = (mat512% z 81 393 418 80) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 221)*(gf512% z 285) + (gf512% z 185)*(gf512% z 262) = (gf512% z 81)
    apply cert_eq z hz (Q := (gf512% z 54))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 221)*(gf512% z 392) + (gf512% z 185)*(gf512% z 262) = (gf512% z 393)
    apply cert_eq z hz (Q := (gf512% z 7))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 481)*(gf512% z 285) + (gf512% z 481)*(gf512% z 262) = (gf512% z 418)
    apply cert_eq z hz (Q := (gf512% z 9))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 481)*(gf512% z 392) + (gf512% z 481)*(gf512% z 262) = (gf512% z 80)
    apply cert_eq z hz (Q := (gf512% z 126))
    ring_nf <;> reduce_mod_char! <;> ring

lemma mtrace_12 : (mat512% z 81 393 418 80).trace = (gf512% z 1) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 81)+(gf512% z 80) = (gf512% z 1)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_405 : (gf512% z 405)^2 = (gf512% z 484) := by
  apply cert_eq z hz (Q := (gf512% z 165))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_79 : (gf512% z 79)^2 = (gf512% z 221) := by
  apply cert_eq z hz (Q := (gf512% z 8))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_285 : (gf512% z 285)^32 = (gf512% z 488) := by
  rw [pow32_squares]
  rw [sqr_285 z hz, sqr_405 z hz, sqr_484 z hz, sqr_79 z hz, sqr_221 z hz]

lemma sqr_392 : (gf512% z 392)^2 = (gf512% z 181) := by
  apply cert_eq z hz (Q := (gf512% z 165))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_181 : (gf512% z 181)^2 = (gf512% z 258) := by
  apply cert_eq z hz (Q := (gf512% z 35))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_258 : (gf512% z 258)^2 = (gf512% z 192) := by
  apply cert_eq z hz (Q := (gf512% z 132))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sqr_192 : (gf512% z 192)^2 = (gf512% z 185) := by
  apply cert_eq z hz (Q := (gf512% z 41))
  ring_nf <;> reduce_mod_char! <;> ring

lemma power32_392 : (gf512% z 392)^32 = (gf512% z 338) := by
  rw [pow32_squares]
  rw [sqr_392 z hz, sqr_181 z hz, sqr_258 z hz, sqr_192 z hz, sqr_185 z hz]

lemma sigma_49 : sigmaM (mat512% z 285 392 262 262) = (mat512% z 488 338 94 94) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_285 z hz
  · exact power32_392 z hz
  · exact power32_262 z hz
  · exact power32_262 z hz

lemma power32_488 : (gf512% z 488)^32 = (gf512% z 405) := by
  rw [pow32_squares]
  rw [sqr_488 z hz, sqr_31 z hz, sqr_341 z hz, sqr_349 z hz, sqr_285 z hz]

lemma power32_338 : (gf512% z 338)^32 = (gf512% z 181) := by
  rw [pow32_squares]
  rw [sqr_338 z hz, sqr_328 z hz, sqr_12 z hz, sqr_80 z hz, sqr_392 z hz]

lemma sigma_50 : sigmaM (mat512% z 488 338 94 94) = (mat512% z 405 181 208 208) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_488 z hz
  · exact power32_338 z hz
  · exact power32_94 z hz
  · exact power32_94 z hz

lemma power32_405 : (gf512% z 405)^32 = (gf512% z 31) := by
  rw [pow32_squares]
  rw [sqr_405 z hz, sqr_484 z hz, sqr_79 z hz, sqr_221 z hz, sqr_488 z hz]

lemma power32_181 : (gf512% z 181)^32 = (gf512% z 328) := by
  rw [pow32_squares]
  rw [sqr_181 z hz, sqr_258 z hz, sqr_192 z hz, sqr_185 z hz, sqr_338 z hz]

lemma sigma_51 : sigmaM (mat512% z 405 181 208 208) = (mat512% z 31 328 476 476) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_405 z hz
  · exact power32_181 z hz
  · exact power32_208 z hz
  · exact power32_208 z hz

lemma power32_31 : (gf512% z 31)^32 = (gf512% z 484) := by
  rw [pow32_squares]
  rw [sqr_31 z hz, sqr_341 z hz, sqr_349 z hz, sqr_285 z hz, sqr_405 z hz]

lemma power32_328 : (gf512% z 328)^32 = (gf512% z 258) := by
  rw [pow32_squares]
  rw [sqr_328 z hz, sqr_12 z hz, sqr_80 z hz, sqr_392 z hz, sqr_181 z hz]

lemma sigma_52 : sigmaM (mat512% z 31 328 476 476) = (mat512% z 484 258 441 441) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_31 z hz
  · exact power32_328 z hz
  · exact power32_476 z hz
  · exact power32_476 z hz

lemma power32_484 : (gf512% z 484)^32 = (gf512% z 341) := by
  rw [pow32_squares]
  rw [sqr_484 z hz, sqr_79 z hz, sqr_221 z hz, sqr_488 z hz, sqr_31 z hz]

lemma power32_258 : (gf512% z 258)^32 = (gf512% z 12) := by
  rw [pow32_squares]
  rw [sqr_258 z hz, sqr_192 z hz, sqr_185 z hz, sqr_338 z hz, sqr_328 z hz]

lemma sigma_53 : sigmaM (mat512% z 484 258 441 441) = (mat512% z 341 12 301 301) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_484 z hz
  · exact power32_258 z hz
  · exact power32_441 z hz
  · exact power32_441 z hz

lemma power32_341 : (gf512% z 341)^32 = (gf512% z 79) := by
  rw [pow32_squares]
  rw [sqr_341 z hz, sqr_349 z hz, sqr_285 z hz, sqr_405 z hz, sqr_484 z hz]

lemma power32_12 : (gf512% z 12)^32 = (gf512% z 192) := by
  rw [pow32_squares]
  rw [sqr_12 z hz, sqr_80 z hz, sqr_392 z hz, sqr_181 z hz, sqr_258 z hz]

lemma sigma_54 : sigmaM (mat512% z 341 12 301 301) = (mat512% z 79 192 406 406) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_341 z hz
  · exact power32_12 z hz
  · exact power32_301 z hz
  · exact power32_301 z hz

lemma power32_79 : (gf512% z 79)^32 = (gf512% z 349) := by
  rw [pow32_squares]
  rw [sqr_79 z hz, sqr_221 z hz, sqr_488 z hz, sqr_31 z hz, sqr_341 z hz]

lemma power32_192 : (gf512% z 192)^32 = (gf512% z 80) := by
  rw [pow32_squares]
  rw [sqr_192 z hz, sqr_185 z hz, sqr_338 z hz, sqr_328 z hz, sqr_12 z hz]

lemma sigma_55 : sigmaM (mat512% z 79 192 406 406) = (mat512% z 349 80 183 183) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_79 z hz
  · exact power32_192 z hz
  · exact power32_406 z hz
  · exact power32_406 z hz

lemma product_55 : (mat512% z 221 185 481 481) * (mat512% z 118 253 118 457) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 221)*(gf512% z 118) + (gf512% z 185)*(gf512% z 118) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 9))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 221)*(gf512% z 253) + (gf512% z 185)*(gf512% z 457) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 64))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 481)*(gf512% z 118) + (gf512% z 481)*(gf512% z 118) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 481)*(gf512% z 253) + (gf512% z 481)*(gf512% z 457) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 229))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_56 : (mat512% z 285 392 262 262) * (mat512% z 324 140 94 155) = (mat512% z 118 253 118 457) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 285)*(gf512% z 324) + (gf512% z 392)*(gf512% z 94) = (gf512% z 118)
    apply cert_eq z hz (Q := (gf512% z 146))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 285)*(gf512% z 140) + (gf512% z 392)*(gf512% z 155) = (gf512% z 253)
    apply cert_eq z hz (Q := (gf512% z 41))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 262)*(gf512% z 324) + (gf512% z 262)*(gf512% z 94) = (gf512% z 118)
    apply cert_eq z hz (Q := (gf512% z 138))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 262)*(gf512% z 140) + (gf512% z 262)*(gf512% z 155) = (gf512% z 457)
    apply cert_eq z hz (Q := (gf512% z 11))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_57 : (mat512% z 488 338 94 94) * (mat512% z 155 182 154 123) = (mat512% z 324 140 94 155) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 488)*(gf512% z 155) + (gf512% z 338)*(gf512% z 154) = (gf512% z 324)
    apply cert_eq z hz (Q := (gf512% z 40))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 488)*(gf512% z 182) + (gf512% z 338)*(gf512% z 123) = (gf512% z 140)
    apply cert_eq z hz (Q := (gf512% z 90))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 94)*(gf512% z 155) + (gf512% z 94)*(gf512% z 154) = (gf512% z 94)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 94)*(gf512% z 182) + (gf512% z 94)*(gf512% z 123) = (gf512% z 155)
    apply cert_eq z hz (Q := (gf512% z 29))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_58 : (mat512% z 405 181 208 208) * (mat512% z 228 103 378 204) = (mat512% z 155 182 154 123) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 405)*(gf512% z 228) + (gf512% z 181)*(gf512% z 378) = (gf512% z 155)
    apply cert_eq z hz (Q := (gf512% z 13))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 405)*(gf512% z 103) + (gf512% z 181)*(gf512% z 204) = (gf512% z 182)
    apply cert_eq z hz (Q := (gf512% z 17))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 208)*(gf512% z 228) + (gf512% z 208)*(gf512% z 378) = (gf512% z 154)
    apply cert_eq z hz (Q := (gf512% z 90))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 208)*(gf512% z 103) + (gf512% z 208)*(gf512% z 204) = (gf512% z 123)
    apply cert_eq z hz (Q := (gf512% z 59))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_59 : (mat512% z 31 328 476 476) * (mat512% z 54 455 346 124) = (mat512% z 228 103 378 204) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 31)*(gf512% z 54) + (gf512% z 328)*(gf512% z 346) = (gf512% z 228)
    apply cert_eq z hz (Q := (gf512% z 134))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 31)*(gf512% z 455) + (gf512% z 328)*(gf512% z 124) = (gf512% z 103)
    apply cert_eq z hz (Q := (gf512% z 58))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 476)*(gf512% z 54) + (gf512% z 476)*(gf512% z 346) = (gf512% z 378)
    apply cert_eq z hz (Q := (gf512% z 202))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 476)*(gf512% z 455) + (gf512% z 476)*(gf512% z 124) = (gf512% z 204)
    apply cert_eq z hz (Q := (gf512% z 136))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_60 : (mat512% z 484 258 441 441) * (mat512% z 384 292 409 506) = (mat512% z 54 455 346 124) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 484)*(gf512% z 384) + (gf512% z 258)*(gf512% z 409) = (gf512% z 54)
    apply cert_eq z hz (Q := (gf512% z 68))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 484)*(gf512% z 292) + (gf512% z 258)*(gf512% z 506) = (gf512% z 455)
    apply cert_eq z hz (Q := (gf512% z 19))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 441)*(gf512% z 384) + (gf512% z 441)*(gf512% z 409) = (gf512% z 346)
    apply cert_eq z hz (Q := (gf512% z 11))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 441)*(gf512% z 292) + (gf512% z 441)*(gf512% z 506) = (gf512% z 124)
    apply cert_eq z hz (Q := (gf512% z 82))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_61 : (mat512% z 341 12 301 301) * (mat512% z 13 81 314 12) = (mat512% z 384 292 409 506) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 341)*(gf512% z 13) + (gf512% z 12)*(gf512% z 314) = (gf512% z 384)
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 341)*(gf512% z 81) + (gf512% z 12)*(gf512% z 12) = (gf512% z 292)
    apply cert_eq z hz (Q := (gf512% z 33))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 301)*(gf512% z 13) + (gf512% z 301)*(gf512% z 314) = (gf512% z 409)
    apply cert_eq z hz (Q := (gf512% z 138))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 301)*(gf512% z 81) + (gf512% z 301)*(gf512% z 12) = (gf512% z 506)
    apply cert_eq z hz (Q := (gf512% z 43))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_62 : (mat512% z 79 192 406 406) * (mat512% z 349 80 183 183) = (mat512% z 13 81 314 12) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 79)*(gf512% z 349) + (gf512% z 192)*(gf512% z 183) = (gf512% z 13)
    apply cert_eq z hz (Q := (gf512% z 22))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 79)*(gf512% z 80) + (gf512% z 192)*(gf512% z 183) = (gf512% z 81)
    apply cert_eq z hz (Q := (gf512% z 49))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 406)*(gf512% z 349) + (gf512% z 406)*(gf512% z 183) = (gf512% z 314)
    apply cert_eq z hz (Q := (gf512% z 134))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 406)*(gf512% z 80) + (gf512% z 406)*(gf512% z 183) = (gf512% z 12)
    apply cert_eq z hz (Q := (gf512% z 78))
    ring_nf <;> reduce_mod_char! <;> ring

lemma norm_6 : semilinearNorm 9 (mat512% z 221 185 481 481) = 1 := by
  have h8 : semilinearNorm 1 (mat512% z 349 80 183 183) = (mat512% z 349 80 183 183) := by simp [semilinearNorm]
  have h7 : semilinearNorm 2 (mat512% z 79 192 406 406) = (mat512% z 13 81 314 12) := by
    change (mat512% z 79 192 406 406) * semilinearNorm 1 (sigmaM (mat512% z 79 192 406 406)) = _
    rw [sigma_55 z hz, h8]
    exact product_62 z hz
  have h6 : semilinearNorm 3 (mat512% z 341 12 301 301) = (mat512% z 384 292 409 506) := by
    change (mat512% z 341 12 301 301) * semilinearNorm 2 (sigmaM (mat512% z 341 12 301 301)) = _
    rw [sigma_54 z hz, h7]
    exact product_61 z hz
  have h5 : semilinearNorm 4 (mat512% z 484 258 441 441) = (mat512% z 54 455 346 124) := by
    change (mat512% z 484 258 441 441) * semilinearNorm 3 (sigmaM (mat512% z 484 258 441 441)) = _
    rw [sigma_53 z hz, h6]
    exact product_60 z hz
  have h4 : semilinearNorm 5 (mat512% z 31 328 476 476) = (mat512% z 228 103 378 204) := by
    change (mat512% z 31 328 476 476) * semilinearNorm 4 (sigmaM (mat512% z 31 328 476 476)) = _
    rw [sigma_52 z hz, h5]
    exact product_59 z hz
  have h3 : semilinearNorm 6 (mat512% z 405 181 208 208) = (mat512% z 155 182 154 123) := by
    change (mat512% z 405 181 208 208) * semilinearNorm 5 (sigmaM (mat512% z 405 181 208 208)) = _
    rw [sigma_51 z hz, h4]
    exact product_58 z hz
  have h2 : semilinearNorm 7 (mat512% z 488 338 94 94) = (mat512% z 324 140 94 155) := by
    change (mat512% z 488 338 94 94) * semilinearNorm 6 (sigmaM (mat512% z 488 338 94 94)) = _
    rw [sigma_50 z hz, h3]
    exact product_57 z hz
  have h1 : semilinearNorm 8 (mat512% z 285 392 262 262) = (mat512% z 118 253 118 457) := by
    change (mat512% z 285 392 262 262) * semilinearNorm 7 (sigmaM (mat512% z 285 392 262 262)) = _
    rw [sigma_49 z hz, h2]
    exact product_56 z hz
  have h0 : semilinearNorm 9 (mat512% z 221 185 481 481) = (mat512% z 1 0 0 1) := by
    change (mat512% z 221 185 481 481) * semilinearNorm 8 (sigmaM (mat512% z 221 185 481 481)) = _
    rw [sigma_48 z hz, h1]
    exact product_55 z hz
  simpa only [code_identity] using h0

lemma mtrace_13 : (mat512% z 221 185 481 481).trace = (gf512% z 316) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 221)+(gf512% z 481) = (gf512% z 316)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma mdet_12 : (mat512% z 221 185 481 481).det = (gf512% z 452) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 221)*(gf512% z 481) - (gf512% z 185)*(gf512% z 481) = (gf512% z 452)
  apply cert_eq z hz (Q := (gf512% z 32))
  ring_nf <;> reduce_mod_char! <;> ring

lemma elliptic_12 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 221 185 481 481) := by
  have ht : (gf512% z 316)*(gf512% z 375) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 165))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 452)*(gf512% z 375)^2 = (gf512% z 484) := by
    apply cert_eq z hz (Q := (gf512% z 59504))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_13 z hz, mdet_12 z hz]
  apply no_quadratic_root hK (gf512% z 316) (gf512% z 452) (gf512% z 375) ht
  rw [hd]
  exact atr_4 z hz

lemma mdet_13 : (mat512% z 81 393 418 80).det = (gf512% z 368) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 81)*(gf512% z 80) - (gf512% z 393)*(gf512% z 418) = (gf512% z 368)
  apply cert_eq z hz (Q := (gf512% z 178))
  ring_nf <;> reduce_mod_char! <;> ring

lemma elliptic_13 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 81 393 418 80) := by
  have ht : (gf512% z 1)*(gf512% z 1) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 368)*(gf512% z 1)^2 = (gf512% z 368) := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_12 z hz, mdet_13 z hz]
  apply no_quadratic_root hK (gf512% z 1) (gf512% z 368) (gf512% z 1) ht
  rw [hd]
  exact atr_5 z hz

lemma good_6 (hK : ∀ x : K, x^512 = x) : Good (mat512% z 221 185 481 481) := by
  unfold Good
  rw [sigma_48 z hz, product_54 z hz]
  refine ⟨?_, elliptic_12 z hz hK, norm_6 z hz, elliptic_13 z hz hK⟩
  simpa using mtrace_12 z hz

#check good_6

lemma sigma_56 : sigmaM (mat512% z 221 344 481 481) = (mat512% z 285 142 262 262) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_221 z hz
  · exact power32_344 z hz
  · exact power32_481 z hz
  · exact power32_481 z hz

lemma product_63 : (mat512% z 221 344 481 481) * (mat512% z 285 142 262 262) = (mat512% z 178 8 418 179) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 221)*(gf512% z 285) + (gf512% z 344)*(gf512% z 262) = (gf512% z 178)
    apply cert_eq z hz (Q := (gf512% z 195))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 221)*(gf512% z 142) + (gf512% z 344)*(gf512% z 262) = (gf512% z 8)
    apply cert_eq z hz (Q := (gf512% z 158))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 481)*(gf512% z 285) + (gf512% z 481)*(gf512% z 262) = (gf512% z 418)
    apply cert_eq z hz (Q := (gf512% z 9))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 481)*(gf512% z 142) + (gf512% z 481)*(gf512% z 262) = (gf512% z 179)
    apply cert_eq z hz (Q := (gf512% z 139))
    ring_nf <;> reduce_mod_char! <;> ring

lemma mtrace_14 : (mat512% z 178 8 418 179).trace = (gf512% z 1) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 178)+(gf512% z 179) = (gf512% z 1)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma sigma_57 : sigmaM (mat512% z 285 142 262 262) = (mat512% z 488 268 94 94) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_285 z hz
  · exact power32_142 z hz
  · exact power32_262 z hz
  · exact power32_262 z hz

lemma sigma_58 : sigmaM (mat512% z 488 268 94 94) = (mat512% z 405 101 208 208) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_488 z hz
  · exact power32_268 z hz
  · exact power32_94 z hz
  · exact power32_94 z hz

lemma sigma_59 : sigmaM (mat512% z 405 101 208 208) = (mat512% z 31 148 476 476) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_405 z hz
  · exact power32_101 z hz
  · exact power32_208 z hz
  · exact power32_208 z hz

lemma sigma_60 : sigmaM (mat512% z 31 148 476 476) = (mat512% z 484 187 441 441) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_31 z hz
  · exact power32_148 z hz
  · exact power32_476 z hz
  · exact power32_476 z hz

lemma sigma_61 : sigmaM (mat512% z 484 187 441 441) = (mat512% z 341 289 301 301) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_484 z hz
  · exact power32_187 z hz
  · exact power32_441 z hz
  · exact power32_441 z hz

lemma sigma_62 : sigmaM (mat512% z 341 289 301 301) = (mat512% z 79 342 406 406) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_341 z hz
  · exact power32_289 z hz
  · exact power32_301 z hz
  · exact power32_301 z hz

lemma sigma_63 : sigmaM (mat512% z 79 342 406 406) = (mat512% z 349 231 183 183) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact power32_79 z hz
  · exact power32_342 z hz
  · exact power32_406 z hz
  · exact power32_406 z hz

lemma product_64 : (mat512% z 221 344 481 481) * (mat512% z 257 190 257 394) = (mat512% z 1 0 0 1) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 221)*(gf512% z 257) + (gf512% z 344)*(gf512% z 257) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 196))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 221)*(gf512% z 190) + (gf512% z 344)*(gf512% z 394) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 198))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 481)*(gf512% z 257) + (gf512% z 481)*(gf512% z 257) = (gf512% z 0)
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 481)*(gf512% z 190) + (gf512% z 481)*(gf512% z 394) = (gf512% z 1)
    apply cert_eq z hz (Q := (gf512% z 229))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_65 : (mat512% z 285 142 262 262) * (mat512% z 506 174 85 99) = (mat512% z 257 190 257 394) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 285)*(gf512% z 506) + (gf512% z 142)*(gf512% z 85) = (gf512% z 257)
    apply cert_eq z hz (Q := (gf512% z 229))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 285)*(gf512% z 174) + (gf512% z 142)*(gf512% z 99) = (gf512% z 190)
    apply cert_eq z hz (Q := (gf512% z 74))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 262)*(gf512% z 506) + (gf512% z 262)*(gf512% z 85) = (gf512% z 257)
    apply cert_eq z hz (Q := (gf512% z 211))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 262)*(gf512% z 174) + (gf512% z 262)*(gf512% z 99) = (gf512% z 394)
    apply cert_eq z hz (Q := (gf512% z 100))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_66 : (mat512% z 488 268 94 94) * (mat512% z 8 93 453 310) = (mat512% z 506 174 85 99) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 488)*(gf512% z 8) + (gf512% z 268)*(gf512% z 453) = (gf512% z 506)
    apply cert_eq z hz (Q := (gf512% z 230))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 488)*(gf512% z 93) + (gf512% z 268)*(gf512% z 310) = (gf512% z 174)
    apply cert_eq z hz (Q := (gf512% z 174))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 94)*(gf512% z 8) + (gf512% z 94)*(gf512% z 453) = (gf512% z 85)
    apply cert_eq z hz (Q := (gf512% z 51))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 94)*(gf512% z 93) + (gf512% z 94)*(gf512% z 310) = (gf512% z 99)
    apply cert_eq z hz (Q := (gf512% z 33))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_67 : (mat512% z 405 101 208 208) * (mat512% z 508 53 215 504) = (mat512% z 8 93 453 310) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 405)*(gf512% z 508) + (gf512% z 101)*(gf512% z 215) = (gf512% z 8)
    apply cert_eq z hz (Q := (gf512% z 159))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 405)*(gf512% z 53) + (gf512% z 101)*(gf512% z 504) = (gf512% z 93)
    apply cert_eq z hz (Q := (gf512% z 52))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 208)*(gf512% z 508) + (gf512% z 208)*(gf512% z 215) = (gf512% z 453)
    apply cert_eq z hz (Q := (gf512% z 101))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 208)*(gf512% z 53) + (gf512% z 208)*(gf512% z 504) = (gf512% z 310)
    apply cert_eq z hz (Q := (gf512% z 70))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_68 : (mat512% z 31 148 476 476) * (mat512% z 372 392 276 179) = (mat512% z 508 53 215 504) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 31)*(gf512% z 372) + (gf512% z 148)*(gf512% z 276) = (gf512% z 508)
    apply cert_eq z hz (Q := (gf512% z 64))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 31)*(gf512% z 392) + (gf512% z 148)*(gf512% z 179) = (gf512% z 53)
    apply cert_eq z hz (Q := (gf512% z 33))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 476)*(gf512% z 372) + (gf512% z 476)*(gf512% z 276) = (gf512% z 215)
    apply cert_eq z hz (Q := (gf512% z 39))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 476)*(gf512% z 392) + (gf512% z 476)*(gf512% z 179) = (gf512% z 504)
    apply cert_eq z hz (Q := (gf512% z 252))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_69 : (mat512% z 484 187 441 441) * (mat512% z 474 412 223 13) = (mat512% z 372 392 276 179) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 484)*(gf512% z 474) + (gf512% z 187)*(gf512% z 223) = (gf512% z 372)
    apply cert_eq z hz (Q := (gf512% z 133))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 484)*(gf512% z 412) + (gf512% z 187)*(gf512% z 13) = (gf512% z 392)
    apply cert_eq z hz (Q := (gf512% z 135))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 441)*(gf512% z 474) + (gf512% z 441)*(gf512% z 223) = (gf512% z 276)
    apply cert_eq z hz (Q := (gf512% z 217))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 441)*(gf512% z 412) + (gf512% z 441)*(gf512% z 13) = (gf512% z 179)
    apply cert_eq z hz (Q := (gf512% z 186))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_70 : (mat512% z 341 289 301 301) * (mat512% z 302 330 314 303) = (mat512% z 474 412 223 13) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 341)*(gf512% z 302) + (gf512% z 289)*(gf512% z 314) = (gf512% z 474)
    apply cert_eq z hz (Q := (gf512% z 54))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 341)*(gf512% z 330) + (gf512% z 289)*(gf512% z 303) = (gf512% z 412)
    apply cert_eq z hz (Q := (gf512% z 1))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 301)*(gf512% z 302) + (gf512% z 301)*(gf512% z 314) = (gf512% z 223)
    apply cert_eq z hz (Q := (gf512% z 11))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 301)*(gf512% z 330) + (gf512% z 301)*(gf512% z 303) = (gf512% z 13)
    apply cert_eq z hz (Q := (gf512% z 52))
    ring_nf <;> reduce_mod_char! <;> ring

lemma product_71 : (mat512% z 79 342 406 406) * (mat512% z 349 231 183 183) = (mat512% z 302 330 314 303) := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change (gf512% z 79)*(gf512% z 349) + (gf512% z 342)*(gf512% z 183) = (gf512% z 302)
    apply cert_eq z hz (Q := (gf512% z 103))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 79)*(gf512% z 231) + (gf512% z 342)*(gf512% z 183) = (gf512% z 330)
    apply cert_eq z hz (Q := (gf512% z 85))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 406)*(gf512% z 349) + (gf512% z 406)*(gf512% z 183) = (gf512% z 314)
    apply cert_eq z hz (Q := (gf512% z 134))
    ring_nf <;> reduce_mod_char! <;> ring
  · change (gf512% z 406)*(gf512% z 231) + (gf512% z 406)*(gf512% z 183) = (gf512% z 303)
    apply cert_eq z hz (Q := (gf512% z 63))
    ring_nf <;> reduce_mod_char! <;> ring

lemma norm_7 : semilinearNorm 9 (mat512% z 221 344 481 481) = 1 := by
  have h8 : semilinearNorm 1 (mat512% z 349 231 183 183) = (mat512% z 349 231 183 183) := by simp [semilinearNorm]
  have h7 : semilinearNorm 2 (mat512% z 79 342 406 406) = (mat512% z 302 330 314 303) := by
    change (mat512% z 79 342 406 406) * semilinearNorm 1 (sigmaM (mat512% z 79 342 406 406)) = _
    rw [sigma_63 z hz, h8]
    exact product_71 z hz
  have h6 : semilinearNorm 3 (mat512% z 341 289 301 301) = (mat512% z 474 412 223 13) := by
    change (mat512% z 341 289 301 301) * semilinearNorm 2 (sigmaM (mat512% z 341 289 301 301)) = _
    rw [sigma_62 z hz, h7]
    exact product_70 z hz
  have h5 : semilinearNorm 4 (mat512% z 484 187 441 441) = (mat512% z 372 392 276 179) := by
    change (mat512% z 484 187 441 441) * semilinearNorm 3 (sigmaM (mat512% z 484 187 441 441)) = _
    rw [sigma_61 z hz, h6]
    exact product_69 z hz
  have h4 : semilinearNorm 5 (mat512% z 31 148 476 476) = (mat512% z 508 53 215 504) := by
    change (mat512% z 31 148 476 476) * semilinearNorm 4 (sigmaM (mat512% z 31 148 476 476)) = _
    rw [sigma_60 z hz, h5]
    exact product_68 z hz
  have h3 : semilinearNorm 6 (mat512% z 405 101 208 208) = (mat512% z 8 93 453 310) := by
    change (mat512% z 405 101 208 208) * semilinearNorm 5 (sigmaM (mat512% z 405 101 208 208)) = _
    rw [sigma_59 z hz, h4]
    exact product_67 z hz
  have h2 : semilinearNorm 7 (mat512% z 488 268 94 94) = (mat512% z 506 174 85 99) := by
    change (mat512% z 488 268 94 94) * semilinearNorm 6 (sigmaM (mat512% z 488 268 94 94)) = _
    rw [sigma_58 z hz, h3]
    exact product_66 z hz
  have h1 : semilinearNorm 8 (mat512% z 285 142 262 262) = (mat512% z 257 190 257 394) := by
    change (mat512% z 285 142 262 262) * semilinearNorm 7 (sigmaM (mat512% z 285 142 262 262)) = _
    rw [sigma_57 z hz, h2]
    exact product_65 z hz
  have h0 : semilinearNorm 9 (mat512% z 221 344 481 481) = (mat512% z 1 0 0 1) := by
    change (mat512% z 221 344 481 481) * semilinearNorm 8 (sigmaM (mat512% z 221 344 481 481)) = _
    rw [sigma_56 z hz, h1]
    exact product_64 z hz
  simpa only [code_identity] using h0

lemma mtrace_15 : (mat512% z 221 344 481 481).trace = (gf512% z 316) := by
  rw [Matrix.trace_fin_two]
  change (gf512% z 221)+(gf512% z 481) = (gf512% z 316)
  apply cert_eq z hz (Q := (gf512% z 0))
  ring_nf <;> reduce_mod_char! <;> ring

lemma mdet_14 : (mat512% z 221 344 481 481).det = (gf512% z 410) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 221)*(gf512% z 481) - (gf512% z 344)*(gf512% z 481) = (gf512% z 410)
  apply cert_eq z hz (Q := (gf512% z 143))
  ring_nf <;> reduce_mod_char! <;> ring

lemma elliptic_14 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 221 344 481 481) := by
  have ht : (gf512% z 316)*(gf512% z 375) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 165))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 410)*(gf512% z 375)^2 = (gf512% z 69) := by
    apply cert_eq z hz (Q := (gf512% z 50279))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_15 z hz, mdet_14 z hz]
  apply no_quadratic_root hK (gf512% z 316) (gf512% z 410) (gf512% z 375) ht
  rw [hd]
  exact atr_6 z hz

lemma mdet_15 : (mat512% z 178 8 418 179).det = (gf512% z 211) := by
  rw [Matrix.det_fin_two]
  change (gf512% z 178)*(gf512% z 179) - (gf512% z 8)*(gf512% z 418) = (gf512% z 211)
  apply cert_eq z hz (Q := (gf512% z 37))
  ring_nf <;> reduce_mod_char! <;> ring

lemma elliptic_15 (hK : ∀ x : K, x^512 = x) : elliptic (mat512% z 178 8 418 179) := by
  have ht : (gf512% z 1)*(gf512% z 1) = 1 := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  have hd : (gf512% z 211)*(gf512% z 1)^2 = (gf512% z 211) := by
    apply cert_eq z hz (Q := (gf512% z 0))
    ring_nf <;> reduce_mod_char! <;> ring
  unfold elliptic
  rw [mtrace_14 z hz, mdet_15 z hz]
  apply no_quadratic_root hK (gf512% z 1) (gf512% z 211) (gf512% z 1) ht
  rw [hd]
  exact atr_7 z hz

lemma good_7 (hK : ∀ x : K, x^512 = x) : Good (mat512% z 221 344 481 481) := by
  unfold Good
  rw [sigma_56 z hz, product_63 z hz]
  refine ⟨?_, elliptic_14 z hz hK, norm_7 z hz, elliptic_15 z hz hK⟩
  simpa using mtrace_14 z hz

#check good_7

#print axioms good_7
end Erdos714BothData
