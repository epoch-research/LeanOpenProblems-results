import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 2000000
open Nat List

def sd (n:ℕ) := (Nat.digits 10 n).sum
lemma sd_two_digits (q t u : ℕ) (ht : t < 10) (hu : u < 10) :
    sd (100*q + 10*t + u) = sd q + t + u := by
  unfold sd
  by_cases h0 : u = 0 ∧ t = 0 ∧ q = 0
  · rcases h0 with ⟨rfl,rfl,rfl⟩; simp
  · have hxy1 : u ≠ 0 ∨ t + 10*q ≠ 0 := by
      by_contra h; push_neg at h; exact h0 ⟨h.1, by omega, by omega⟩
    rw [show 100*q + 10*t + u = u + 10*(t+10*q) by omega]
    rw [Nat.digits_add 10 (by norm_num) u (t+10*q) hu hxy1]
    by_cases h1 : t = 0 ∧ q = 0
    · rcases h1 with ⟨rfl,rfl⟩; simp
    · have hxy2 : t ≠ 0 ∨ q ≠ 0 := by
        by_contra h; push_neg at h; exact h1 ⟨h.1,h.2⟩
      rw [Nat.digits_add 10 (by norm_num) t q ht hxy2]
      simp [List.sum_cons]
      omega

def a (n : ℕ) : ℕ := (Nat.digits 10 n).sum % (Nat.digits 10 (n + 1)).sum
def count_a_eq (N m : ℕ) : ℕ := (List.range N).countP fun n => a n = m
lemma a_two_digits_non9 (q t u : ℕ) (ht : t < 10) (hu : u < 9) :
    a (100*q + 10*t + u) = sd q + t + u := by
  unfold a
  change sd (100*q+10*t+u) % sd (100*q+10*t+u+1) = sd q + t + u
  rw [sd_two_digits q t u ht (by omega)]
  rw [show 100*q + 10*t + u + 1 = 100*q + 10*t + (u+1) by omega]
  rw [sd_two_digits q t (u+1) ht (by omega)]
  rw [Nat.mod_eq_of_lt]
  omega
lemma a_two_digits_9_formula (q t : ℕ) (ht : t < 9) :
    a (100*q + 10*t + 9) = (sd q + t + 9) % (sd q + t + 1) := by
  unfold a
  change sd (100*q+10*t+9) % sd (100*q+10*t+9+1) = _
  rw [sd_two_digits q t 9 (by omega) (by norm_num)]
  rw [show 100*q+10*t+9+1 = 100*q+10*(t+1)+0 by omega]
  rw [sd_two_digits q (t+1) 0 (by omega) (by norm_num)]
  congr 1
lemma a_two_digits_9_eq8_of (q t : ℕ) (ht : t < 9) (h : 8 ≤ sd q + t) :
    a (100*q + 10*t + 9) = 8 := by
  rw [a_two_digits_9_formula q t ht]
  have : sd q + t + 9 = (sd q + t + 1) + 8 := by omega
  rw [this, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by omega)
lemma a_two_digits_9_lt8_or_eq8 (q t : ℕ) (ht : t < 9) :
    a (100*q + 10*t + 9) < 8 ∨ a (100*q + 10*t + 9) = 8 := by
  by_cases h : 8 ≤ sd q + t
  · exact Or.inr (a_two_digits_9_eq8_of q t ht h)
  · left
    rw [a_two_digits_9_formula q t ht]
    exact (Nat.mod_lt _ (by omega)).trans_le (by omega)
lemma a_block_non9 (q t u : ℕ) (ht : t < 10) (hu : u < 9) : a (100*q + (10*t + u)) = sd q + t + u := by
  rw [show 100*q + (10*t+u) = 100*q + 10*t + u by omega]
  exact a_two_digits_non9 q t u ht hu
@[simp] lemma apos0 (q:ℕ) : a (100*q) = sd q + 0 + 0 := by
  rw [show 100*q = 100*q + (10*0+0) by omega]
  exact a_block_non9 q 0 0 (by norm_num) (by norm_num)
@[simp] lemma apos1 (q:ℕ) : a (100*q + 1) = sd q + 0 + 1 := by
  rw [show 100*q + 1 = 100*q + (10*0+1) by omega]
  exact a_block_non9 q 0 1 (by norm_num) (by norm_num)
@[simp] lemma apos2 (q:ℕ) : a (100*q + 2) = sd q + 0 + 2 := by
  rw [show 100*q + 2 = 100*q + (10*0+2) by omega]
  exact a_block_non9 q 0 2 (by norm_num) (by norm_num)
@[simp] lemma apos3 (q:ℕ) : a (100*q + 3) = sd q + 0 + 3 := by
  rw [show 100*q + 3 = 100*q + (10*0+3) by omega]
  exact a_block_non9 q 0 3 (by norm_num) (by norm_num)
@[simp] lemma apos4 (q:ℕ) : a (100*q + 4) = sd q + 0 + 4 := by
  rw [show 100*q + 4 = 100*q + (10*0+4) by omega]
  exact a_block_non9 q 0 4 (by norm_num) (by norm_num)
@[simp] lemma apos5 (q:ℕ) : a (100*q + 5) = sd q + 0 + 5 := by
  rw [show 100*q + 5 = 100*q + (10*0+5) by omega]
  exact a_block_non9 q 0 5 (by norm_num) (by norm_num)
@[simp] lemma apos6 (q:ℕ) : a (100*q + 6) = sd q + 0 + 6 := by
  rw [show 100*q + 6 = 100*q + (10*0+6) by omega]
  exact a_block_non9 q 0 6 (by norm_num) (by norm_num)
@[simp] lemma apos7 (q:ℕ) : a (100*q + 7) = sd q + 0 + 7 := by
  rw [show 100*q + 7 = 100*q + (10*0+7) by omega]
  exact a_block_non9 q 0 7 (by norm_num) (by norm_num)
@[simp] lemma apos8 (q:ℕ) : a (100*q + 8) = sd q + 0 + 8 := by
  rw [show 100*q + 8 = 100*q + (10*0+8) by omega]
  exact a_block_non9 q 0 8 (by norm_num) (by norm_num)
@[simp] lemma apos9 (q:ℕ) : a (100*q + 9) = (sd q + 0 + 9) % (sd q + 0 + 1) := by
  rw [show 100*q + 9 = 100*q + 10*0 + 9 by omega]
  exact a_two_digits_9_formula q 0 (by norm_num)
@[simp] lemma apos10 (q:ℕ) : a (100*q + 10) = sd q + 1 + 0 := by
  rw [show 100*q + 10 = 100*q + (10*1+0) by omega]
  exact a_block_non9 q 1 0 (by norm_num) (by norm_num)
@[simp] lemma apos11 (q:ℕ) : a (100*q + 11) = sd q + 1 + 1 := by
  rw [show 100*q + 11 = 100*q + (10*1+1) by omega]
  exact a_block_non9 q 1 1 (by norm_num) (by norm_num)
@[simp] lemma apos12 (q:ℕ) : a (100*q + 12) = sd q + 1 + 2 := by
  rw [show 100*q + 12 = 100*q + (10*1+2) by omega]
  exact a_block_non9 q 1 2 (by norm_num) (by norm_num)
@[simp] lemma apos13 (q:ℕ) : a (100*q + 13) = sd q + 1 + 3 := by
  rw [show 100*q + 13 = 100*q + (10*1+3) by omega]
  exact a_block_non9 q 1 3 (by norm_num) (by norm_num)
@[simp] lemma apos14 (q:ℕ) : a (100*q + 14) = sd q + 1 + 4 := by
  rw [show 100*q + 14 = 100*q + (10*1+4) by omega]
  exact a_block_non9 q 1 4 (by norm_num) (by norm_num)
@[simp] lemma apos15 (q:ℕ) : a (100*q + 15) = sd q + 1 + 5 := by
  rw [show 100*q + 15 = 100*q + (10*1+5) by omega]
  exact a_block_non9 q 1 5 (by norm_num) (by norm_num)
@[simp] lemma apos16 (q:ℕ) : a (100*q + 16) = sd q + 1 + 6 := by
  rw [show 100*q + 16 = 100*q + (10*1+6) by omega]
  exact a_block_non9 q 1 6 (by norm_num) (by norm_num)
@[simp] lemma apos17 (q:ℕ) : a (100*q + 17) = sd q + 1 + 7 := by
  rw [show 100*q + 17 = 100*q + (10*1+7) by omega]
  exact a_block_non9 q 1 7 (by norm_num) (by norm_num)
@[simp] lemma apos18 (q:ℕ) : a (100*q + 18) = sd q + 1 + 8 := by
  rw [show 100*q + 18 = 100*q + (10*1+8) by omega]
  exact a_block_non9 q 1 8 (by norm_num) (by norm_num)
@[simp] lemma apos19 (q:ℕ) : a (100*q + 19) = (sd q + 1 + 9) % (sd q + 1 + 1) := by
  rw [show 100*q + 19 = 100*q + 10*1 + 9 by omega]
  exact a_two_digits_9_formula q 1 (by norm_num)
@[simp] lemma apos20 (q:ℕ) : a (100*q + 20) = sd q + 2 + 0 := by
  rw [show 100*q + 20 = 100*q + (10*2+0) by omega]
  exact a_block_non9 q 2 0 (by norm_num) (by norm_num)
@[simp] lemma apos21 (q:ℕ) : a (100*q + 21) = sd q + 2 + 1 := by
  rw [show 100*q + 21 = 100*q + (10*2+1) by omega]
  exact a_block_non9 q 2 1 (by norm_num) (by norm_num)
@[simp] lemma apos22 (q:ℕ) : a (100*q + 22) = sd q + 2 + 2 := by
  rw [show 100*q + 22 = 100*q + (10*2+2) by omega]
  exact a_block_non9 q 2 2 (by norm_num) (by norm_num)
@[simp] lemma apos23 (q:ℕ) : a (100*q + 23) = sd q + 2 + 3 := by
  rw [show 100*q + 23 = 100*q + (10*2+3) by omega]
  exact a_block_non9 q 2 3 (by norm_num) (by norm_num)
@[simp] lemma apos24 (q:ℕ) : a (100*q + 24) = sd q + 2 + 4 := by
  rw [show 100*q + 24 = 100*q + (10*2+4) by omega]
  exact a_block_non9 q 2 4 (by norm_num) (by norm_num)
@[simp] lemma apos25 (q:ℕ) : a (100*q + 25) = sd q + 2 + 5 := by
  rw [show 100*q + 25 = 100*q + (10*2+5) by omega]
  exact a_block_non9 q 2 5 (by norm_num) (by norm_num)
@[simp] lemma apos26 (q:ℕ) : a (100*q + 26) = sd q + 2 + 6 := by
  rw [show 100*q + 26 = 100*q + (10*2+6) by omega]
  exact a_block_non9 q 2 6 (by norm_num) (by norm_num)
@[simp] lemma apos27 (q:ℕ) : a (100*q + 27) = sd q + 2 + 7 := by
  rw [show 100*q + 27 = 100*q + (10*2+7) by omega]
  exact a_block_non9 q 2 7 (by norm_num) (by norm_num)
@[simp] lemma apos28 (q:ℕ) : a (100*q + 28) = sd q + 2 + 8 := by
  rw [show 100*q + 28 = 100*q + (10*2+8) by omega]
  exact a_block_non9 q 2 8 (by norm_num) (by norm_num)
@[simp] lemma apos29 (q:ℕ) : a (100*q + 29) = (sd q + 2 + 9) % (sd q + 2 + 1) := by
  rw [show 100*q + 29 = 100*q + 10*2 + 9 by omega]
  exact a_two_digits_9_formula q 2 (by norm_num)
@[simp] lemma apos30 (q:ℕ) : a (100*q + 30) = sd q + 3 + 0 := by
  rw [show 100*q + 30 = 100*q + (10*3+0) by omega]
  exact a_block_non9 q 3 0 (by norm_num) (by norm_num)
@[simp] lemma apos31 (q:ℕ) : a (100*q + 31) = sd q + 3 + 1 := by
  rw [show 100*q + 31 = 100*q + (10*3+1) by omega]
  exact a_block_non9 q 3 1 (by norm_num) (by norm_num)
@[simp] lemma apos32 (q:ℕ) : a (100*q + 32) = sd q + 3 + 2 := by
  rw [show 100*q + 32 = 100*q + (10*3+2) by omega]
  exact a_block_non9 q 3 2 (by norm_num) (by norm_num)
@[simp] lemma apos33 (q:ℕ) : a (100*q + 33) = sd q + 3 + 3 := by
  rw [show 100*q + 33 = 100*q + (10*3+3) by omega]
  exact a_block_non9 q 3 3 (by norm_num) (by norm_num)
@[simp] lemma apos34 (q:ℕ) : a (100*q + 34) = sd q + 3 + 4 := by
  rw [show 100*q + 34 = 100*q + (10*3+4) by omega]
  exact a_block_non9 q 3 4 (by norm_num) (by norm_num)
@[simp] lemma apos35 (q:ℕ) : a (100*q + 35) = sd q + 3 + 5 := by
  rw [show 100*q + 35 = 100*q + (10*3+5) by omega]
  exact a_block_non9 q 3 5 (by norm_num) (by norm_num)
@[simp] lemma apos36 (q:ℕ) : a (100*q + 36) = sd q + 3 + 6 := by
  rw [show 100*q + 36 = 100*q + (10*3+6) by omega]
  exact a_block_non9 q 3 6 (by norm_num) (by norm_num)
@[simp] lemma apos37 (q:ℕ) : a (100*q + 37) = sd q + 3 + 7 := by
  rw [show 100*q + 37 = 100*q + (10*3+7) by omega]
  exact a_block_non9 q 3 7 (by norm_num) (by norm_num)
@[simp] lemma apos38 (q:ℕ) : a (100*q + 38) = sd q + 3 + 8 := by
  rw [show 100*q + 38 = 100*q + (10*3+8) by omega]
  exact a_block_non9 q 3 8 (by norm_num) (by norm_num)
@[simp] lemma apos39 (q:ℕ) : a (100*q + 39) = (sd q + 3 + 9) % (sd q + 3 + 1) := by
  rw [show 100*q + 39 = 100*q + 10*3 + 9 by omega]
  exact a_two_digits_9_formula q 3 (by norm_num)
@[simp] lemma apos40 (q:ℕ) : a (100*q + 40) = sd q + 4 + 0 := by
  rw [show 100*q + 40 = 100*q + (10*4+0) by omega]
  exact a_block_non9 q 4 0 (by norm_num) (by norm_num)
@[simp] lemma apos41 (q:ℕ) : a (100*q + 41) = sd q + 4 + 1 := by
  rw [show 100*q + 41 = 100*q + (10*4+1) by omega]
  exact a_block_non9 q 4 1 (by norm_num) (by norm_num)
@[simp] lemma apos42 (q:ℕ) : a (100*q + 42) = sd q + 4 + 2 := by
  rw [show 100*q + 42 = 100*q + (10*4+2) by omega]
  exact a_block_non9 q 4 2 (by norm_num) (by norm_num)
@[simp] lemma apos43 (q:ℕ) : a (100*q + 43) = sd q + 4 + 3 := by
  rw [show 100*q + 43 = 100*q + (10*4+3) by omega]
  exact a_block_non9 q 4 3 (by norm_num) (by norm_num)
@[simp] lemma apos44 (q:ℕ) : a (100*q + 44) = sd q + 4 + 4 := by
  rw [show 100*q + 44 = 100*q + (10*4+4) by omega]
  exact a_block_non9 q 4 4 (by norm_num) (by norm_num)
@[simp] lemma apos45 (q:ℕ) : a (100*q + 45) = sd q + 4 + 5 := by
  rw [show 100*q + 45 = 100*q + (10*4+5) by omega]
  exact a_block_non9 q 4 5 (by norm_num) (by norm_num)
@[simp] lemma apos46 (q:ℕ) : a (100*q + 46) = sd q + 4 + 6 := by
  rw [show 100*q + 46 = 100*q + (10*4+6) by omega]
  exact a_block_non9 q 4 6 (by norm_num) (by norm_num)
@[simp] lemma apos47 (q:ℕ) : a (100*q + 47) = sd q + 4 + 7 := by
  rw [show 100*q + 47 = 100*q + (10*4+7) by omega]
  exact a_block_non9 q 4 7 (by norm_num) (by norm_num)
@[simp] lemma apos48 (q:ℕ) : a (100*q + 48) = sd q + 4 + 8 := by
  rw [show 100*q + 48 = 100*q + (10*4+8) by omega]
  exact a_block_non9 q 4 8 (by norm_num) (by norm_num)
@[simp] lemma apos49 (q:ℕ) : a (100*q + 49) = (sd q + 4 + 9) % (sd q + 4 + 1) := by
  rw [show 100*q + 49 = 100*q + 10*4 + 9 by omega]
  exact a_two_digits_9_formula q 4 (by norm_num)
@[simp] lemma apos50 (q:ℕ) : a (100*q + 50) = sd q + 5 + 0 := by
  rw [show 100*q + 50 = 100*q + (10*5+0) by omega]
  exact a_block_non9 q 5 0 (by norm_num) (by norm_num)
@[simp] lemma apos51 (q:ℕ) : a (100*q + 51) = sd q + 5 + 1 := by
  rw [show 100*q + 51 = 100*q + (10*5+1) by omega]
  exact a_block_non9 q 5 1 (by norm_num) (by norm_num)
@[simp] lemma apos52 (q:ℕ) : a (100*q + 52) = sd q + 5 + 2 := by
  rw [show 100*q + 52 = 100*q + (10*5+2) by omega]
  exact a_block_non9 q 5 2 (by norm_num) (by norm_num)
@[simp] lemma apos53 (q:ℕ) : a (100*q + 53) = sd q + 5 + 3 := by
  rw [show 100*q + 53 = 100*q + (10*5+3) by omega]
  exact a_block_non9 q 5 3 (by norm_num) (by norm_num)
@[simp] lemma apos54 (q:ℕ) : a (100*q + 54) = sd q + 5 + 4 := by
  rw [show 100*q + 54 = 100*q + (10*5+4) by omega]
  exact a_block_non9 q 5 4 (by norm_num) (by norm_num)
@[simp] lemma apos55 (q:ℕ) : a (100*q + 55) = sd q + 5 + 5 := by
  rw [show 100*q + 55 = 100*q + (10*5+5) by omega]
  exact a_block_non9 q 5 5 (by norm_num) (by norm_num)
@[simp] lemma apos56 (q:ℕ) : a (100*q + 56) = sd q + 5 + 6 := by
  rw [show 100*q + 56 = 100*q + (10*5+6) by omega]
  exact a_block_non9 q 5 6 (by norm_num) (by norm_num)
@[simp] lemma apos57 (q:ℕ) : a (100*q + 57) = sd q + 5 + 7 := by
  rw [show 100*q + 57 = 100*q + (10*5+7) by omega]
  exact a_block_non9 q 5 7 (by norm_num) (by norm_num)
@[simp] lemma apos58 (q:ℕ) : a (100*q + 58) = sd q + 5 + 8 := by
  rw [show 100*q + 58 = 100*q + (10*5+8) by omega]
  exact a_block_non9 q 5 8 (by norm_num) (by norm_num)
@[simp] lemma apos59 (q:ℕ) : a (100*q + 59) = (sd q + 5 + 9) % (sd q + 5 + 1) := by
  rw [show 100*q + 59 = 100*q + 10*5 + 9 by omega]
  exact a_two_digits_9_formula q 5 (by norm_num)
@[simp] lemma apos60 (q:ℕ) : a (100*q + 60) = sd q + 6 + 0 := by
  rw [show 100*q + 60 = 100*q + (10*6+0) by omega]
  exact a_block_non9 q 6 0 (by norm_num) (by norm_num)
@[simp] lemma apos61 (q:ℕ) : a (100*q + 61) = sd q + 6 + 1 := by
  rw [show 100*q + 61 = 100*q + (10*6+1) by omega]
  exact a_block_non9 q 6 1 (by norm_num) (by norm_num)
@[simp] lemma apos62 (q:ℕ) : a (100*q + 62) = sd q + 6 + 2 := by
  rw [show 100*q + 62 = 100*q + (10*6+2) by omega]
  exact a_block_non9 q 6 2 (by norm_num) (by norm_num)
@[simp] lemma apos63 (q:ℕ) : a (100*q + 63) = sd q + 6 + 3 := by
  rw [show 100*q + 63 = 100*q + (10*6+3) by omega]
  exact a_block_non9 q 6 3 (by norm_num) (by norm_num)
@[simp] lemma apos64 (q:ℕ) : a (100*q + 64) = sd q + 6 + 4 := by
  rw [show 100*q + 64 = 100*q + (10*6+4) by omega]
  exact a_block_non9 q 6 4 (by norm_num) (by norm_num)
@[simp] lemma apos65 (q:ℕ) : a (100*q + 65) = sd q + 6 + 5 := by
  rw [show 100*q + 65 = 100*q + (10*6+5) by omega]
  exact a_block_non9 q 6 5 (by norm_num) (by norm_num)
@[simp] lemma apos66 (q:ℕ) : a (100*q + 66) = sd q + 6 + 6 := by
  rw [show 100*q + 66 = 100*q + (10*6+6) by omega]
  exact a_block_non9 q 6 6 (by norm_num) (by norm_num)
@[simp] lemma apos67 (q:ℕ) : a (100*q + 67) = sd q + 6 + 7 := by
  rw [show 100*q + 67 = 100*q + (10*6+7) by omega]
  exact a_block_non9 q 6 7 (by norm_num) (by norm_num)
@[simp] lemma apos68 (q:ℕ) : a (100*q + 68) = sd q + 6 + 8 := by
  rw [show 100*q + 68 = 100*q + (10*6+8) by omega]
  exact a_block_non9 q 6 8 (by norm_num) (by norm_num)
@[simp] lemma apos69 (q:ℕ) : a (100*q + 69) = (sd q + 6 + 9) % (sd q + 6 + 1) := by
  rw [show 100*q + 69 = 100*q + 10*6 + 9 by omega]
  exact a_two_digits_9_formula q 6 (by norm_num)
@[simp] lemma apos70 (q:ℕ) : a (100*q + 70) = sd q + 7 + 0 := by
  rw [show 100*q + 70 = 100*q + (10*7+0) by omega]
  exact a_block_non9 q 7 0 (by norm_num) (by norm_num)
@[simp] lemma apos71 (q:ℕ) : a (100*q + 71) = sd q + 7 + 1 := by
  rw [show 100*q + 71 = 100*q + (10*7+1) by omega]
  exact a_block_non9 q 7 1 (by norm_num) (by norm_num)
@[simp] lemma apos72 (q:ℕ) : a (100*q + 72) = sd q + 7 + 2 := by
  rw [show 100*q + 72 = 100*q + (10*7+2) by omega]
  exact a_block_non9 q 7 2 (by norm_num) (by norm_num)
@[simp] lemma apos73 (q:ℕ) : a (100*q + 73) = sd q + 7 + 3 := by
  rw [show 100*q + 73 = 100*q + (10*7+3) by omega]
  exact a_block_non9 q 7 3 (by norm_num) (by norm_num)
@[simp] lemma apos74 (q:ℕ) : a (100*q + 74) = sd q + 7 + 4 := by
  rw [show 100*q + 74 = 100*q + (10*7+4) by omega]
  exact a_block_non9 q 7 4 (by norm_num) (by norm_num)
@[simp] lemma apos75 (q:ℕ) : a (100*q + 75) = sd q + 7 + 5 := by
  rw [show 100*q + 75 = 100*q + (10*7+5) by omega]
  exact a_block_non9 q 7 5 (by norm_num) (by norm_num)
@[simp] lemma apos76 (q:ℕ) : a (100*q + 76) = sd q + 7 + 6 := by
  rw [show 100*q + 76 = 100*q + (10*7+6) by omega]
  exact a_block_non9 q 7 6 (by norm_num) (by norm_num)
@[simp] lemma apos77 (q:ℕ) : a (100*q + 77) = sd q + 7 + 7 := by
  rw [show 100*q + 77 = 100*q + (10*7+7) by omega]
  exact a_block_non9 q 7 7 (by norm_num) (by norm_num)
@[simp] lemma apos78 (q:ℕ) : a (100*q + 78) = sd q + 7 + 8 := by
  rw [show 100*q + 78 = 100*q + (10*7+8) by omega]
  exact a_block_non9 q 7 8 (by norm_num) (by norm_num)
@[simp] lemma apos79 (q:ℕ) : a (100*q + 79) = (sd q + 7 + 9) % (sd q + 7 + 1) := by
  rw [show 100*q + 79 = 100*q + 10*7 + 9 by omega]
  exact a_two_digits_9_formula q 7 (by norm_num)
@[simp] lemma apos80 (q:ℕ) : a (100*q + 80) = sd q + 8 + 0 := by
  rw [show 100*q + 80 = 100*q + (10*8+0) by omega]
  exact a_block_non9 q 8 0 (by norm_num) (by norm_num)
@[simp] lemma apos81 (q:ℕ) : a (100*q + 81) = sd q + 8 + 1 := by
  rw [show 100*q + 81 = 100*q + (10*8+1) by omega]
  exact a_block_non9 q 8 1 (by norm_num) (by norm_num)
@[simp] lemma apos82 (q:ℕ) : a (100*q + 82) = sd q + 8 + 2 := by
  rw [show 100*q + 82 = 100*q + (10*8+2) by omega]
  exact a_block_non9 q 8 2 (by norm_num) (by norm_num)
@[simp] lemma apos83 (q:ℕ) : a (100*q + 83) = sd q + 8 + 3 := by
  rw [show 100*q + 83 = 100*q + (10*8+3) by omega]
  exact a_block_non9 q 8 3 (by norm_num) (by norm_num)
@[simp] lemma apos84 (q:ℕ) : a (100*q + 84) = sd q + 8 + 4 := by
  rw [show 100*q + 84 = 100*q + (10*8+4) by omega]
  exact a_block_non9 q 8 4 (by norm_num) (by norm_num)
@[simp] lemma apos85 (q:ℕ) : a (100*q + 85) = sd q + 8 + 5 := by
  rw [show 100*q + 85 = 100*q + (10*8+5) by omega]
  exact a_block_non9 q 8 5 (by norm_num) (by norm_num)
@[simp] lemma apos86 (q:ℕ) : a (100*q + 86) = sd q + 8 + 6 := by
  rw [show 100*q + 86 = 100*q + (10*8+6) by omega]
  exact a_block_non9 q 8 6 (by norm_num) (by norm_num)
@[simp] lemma apos87 (q:ℕ) : a (100*q + 87) = sd q + 8 + 7 := by
  rw [show 100*q + 87 = 100*q + (10*8+7) by omega]
  exact a_block_non9 q 8 7 (by norm_num) (by norm_num)
@[simp] lemma apos88 (q:ℕ) : a (100*q + 88) = sd q + 8 + 8 := by
  rw [show 100*q + 88 = 100*q + (10*8+8) by omega]
  exact a_block_non9 q 8 8 (by norm_num) (by norm_num)
@[simp] lemma apos89 (q:ℕ) : a (100*q + 89) = (sd q + 8 + 9) % (sd q + 8 + 1) := by
  rw [show 100*q + 89 = 100*q + 10*8 + 9 by omega]
  exact a_two_digits_9_formula q 8 (by norm_num)
@[simp] lemma apos90 (q:ℕ) : a (100*q + 90) = sd q + 9 + 0 := by
  rw [show 100*q + 90 = 100*q + (10*9+0) by omega]
  exact a_block_non9 q 9 0 (by norm_num) (by norm_num)
@[simp] lemma apos91 (q:ℕ) : a (100*q + 91) = sd q + 9 + 1 := by
  rw [show 100*q + 91 = 100*q + (10*9+1) by omega]
  exact a_block_non9 q 9 1 (by norm_num) (by norm_num)
@[simp] lemma apos92 (q:ℕ) : a (100*q + 92) = sd q + 9 + 2 := by
  rw [show 100*q + 92 = 100*q + (10*9+2) by omega]
  exact a_block_non9 q 9 2 (by norm_num) (by norm_num)
@[simp] lemma apos93 (q:ℕ) : a (100*q + 93) = sd q + 9 + 3 := by
  rw [show 100*q + 93 = 100*q + (10*9+3) by omega]
  exact a_block_non9 q 9 3 (by norm_num) (by norm_num)
@[simp] lemma apos94 (q:ℕ) : a (100*q + 94) = sd q + 9 + 4 := by
  rw [show 100*q + 94 = 100*q + (10*9+4) by omega]
  exact a_block_non9 q 9 4 (by norm_num) (by norm_num)
@[simp] lemma apos95 (q:ℕ) : a (100*q + 95) = sd q + 9 + 5 := by
  rw [show 100*q + 95 = 100*q + (10*9+5) by omega]
  exact a_block_non9 q 9 5 (by norm_num) (by norm_num)
@[simp] lemma apos96 (q:ℕ) : a (100*q + 96) = sd q + 9 + 6 := by
  rw [show 100*q + 96 = 100*q + (10*9+6) by omega]
  exact a_block_non9 q 9 6 (by norm_num) (by norm_num)
@[simp] lemma apos97 (q:ℕ) : a (100*q + 97) = sd q + 9 + 7 := by
  rw [show 100*q + 97 = 100*q + (10*9+7) by omega]
  exact a_block_non9 q 9 7 (by norm_num) (by norm_num)
@[simp] lemma apos98 (q:ℕ) : a (100*q + 98) = sd q + 9 + 8 := by
  rw [show 100*q + 98 = 100*q + (10*9+8) by omega]
  exact a_block_non9 q 9 8 (by norm_num) (by norm_num)
def val99 (x r : ℕ) : ℕ := if r % 10 < 9 then x + r / 10 + r % 10 else (x + r / 10 + 9) % (x + r / 10 + 1)
lemma low_ref_0_0 : ((List.range 99).countP fun r => val99 0 r = 0) ≤ 8 := by decide
lemma low_ref_0_1 : ((List.range 99).countP fun r => val99 0 r = 1) ≤ 8 := by decide
lemma low_ref_0_2 : ((List.range 99).countP fun r => val99 0 r = 2) ≤ 8 := by decide
lemma low_ref_0_3 : ((List.range 99).countP fun r => val99 0 r = 3) ≤ 8 := by decide
lemma low_ref_0_4 : ((List.range 99).countP fun r => val99 0 r = 4) ≤ 8 := by decide
lemma low_ref_0_5 : ((List.range 99).countP fun r => val99 0 r = 5) ≤ 8 := by decide
lemma low_ref_0_6 : ((List.range 99).countP fun r => val99 0 r = 6) ≤ 8 := by decide
lemma low_ref_0_7 : ((List.range 99).countP fun r => val99 0 r = 7) ≤ 8 := by decide
lemma low_ref_1_0 : ((List.range 99).countP fun r => val99 1 r = 0) ≤ 8 := by decide
lemma low_ref_1_1 : ((List.range 99).countP fun r => val99 1 r = 1) ≤ 8 := by decide
lemma low_ref_1_2 : ((List.range 99).countP fun r => val99 1 r = 2) ≤ 8 := by decide
lemma low_ref_1_3 : ((List.range 99).countP fun r => val99 1 r = 3) ≤ 8 := by decide
lemma low_ref_1_4 : ((List.range 99).countP fun r => val99 1 r = 4) ≤ 8 := by decide
lemma low_ref_1_5 : ((List.range 99).countP fun r => val99 1 r = 5) ≤ 8 := by decide
lemma low_ref_1_6 : ((List.range 99).countP fun r => val99 1 r = 6) ≤ 8 := by decide
lemma low_ref_1_7 : ((List.range 99).countP fun r => val99 1 r = 7) ≤ 8 := by decide
lemma low_ref_2_0 : ((List.range 99).countP fun r => val99 2 r = 0) ≤ 8 := by decide
lemma low_ref_2_1 : ((List.range 99).countP fun r => val99 2 r = 1) ≤ 8 := by decide
lemma low_ref_2_2 : ((List.range 99).countP fun r => val99 2 r = 2) ≤ 8 := by decide
lemma low_ref_2_3 : ((List.range 99).countP fun r => val99 2 r = 3) ≤ 8 := by decide
lemma low_ref_2_4 : ((List.range 99).countP fun r => val99 2 r = 4) ≤ 8 := by decide
lemma low_ref_2_5 : ((List.range 99).countP fun r => val99 2 r = 5) ≤ 8 := by decide
lemma low_ref_2_6 : ((List.range 99).countP fun r => val99 2 r = 6) ≤ 8 := by decide
lemma low_ref_2_7 : ((List.range 99).countP fun r => val99 2 r = 7) ≤ 8 := by decide
lemma low_ref_3_0 : ((List.range 99).countP fun r => val99 3 r = 0) ≤ 8 := by decide
lemma low_ref_3_1 : ((List.range 99).countP fun r => val99 3 r = 1) ≤ 8 := by decide
lemma low_ref_3_2 : ((List.range 99).countP fun r => val99 3 r = 2) ≤ 8 := by decide
lemma low_ref_3_3 : ((List.range 99).countP fun r => val99 3 r = 3) ≤ 8 := by decide
lemma low_ref_3_4 : ((List.range 99).countP fun r => val99 3 r = 4) ≤ 8 := by decide
lemma low_ref_3_5 : ((List.range 99).countP fun r => val99 3 r = 5) ≤ 8 := by decide
lemma low_ref_3_6 : ((List.range 99).countP fun r => val99 3 r = 6) ≤ 8 := by decide
lemma low_ref_3_7 : ((List.range 99).countP fun r => val99 3 r = 7) ≤ 8 := by decide
lemma low_ref_4_0 : ((List.range 99).countP fun r => val99 4 r = 0) ≤ 8 := by decide
lemma low_ref_4_1 : ((List.range 99).countP fun r => val99 4 r = 1) ≤ 8 := by decide
lemma low_ref_4_2 : ((List.range 99).countP fun r => val99 4 r = 2) ≤ 8 := by decide
lemma low_ref_4_3 : ((List.range 99).countP fun r => val99 4 r = 3) ≤ 8 := by decide
lemma low_ref_4_4 : ((List.range 99).countP fun r => val99 4 r = 4) ≤ 8 := by decide
lemma low_ref_4_5 : ((List.range 99).countP fun r => val99 4 r = 5) ≤ 8 := by decide
lemma low_ref_4_6 : ((List.range 99).countP fun r => val99 4 r = 6) ≤ 8 := by decide
lemma low_ref_4_7 : ((List.range 99).countP fun r => val99 4 r = 7) ≤ 8 := by decide
lemma low_ref_5_0 : ((List.range 99).countP fun r => val99 5 r = 0) ≤ 8 := by decide
lemma low_ref_5_1 : ((List.range 99).countP fun r => val99 5 r = 1) ≤ 8 := by decide
lemma low_ref_5_2 : ((List.range 99).countP fun r => val99 5 r = 2) ≤ 8 := by decide
lemma low_ref_5_3 : ((List.range 99).countP fun r => val99 5 r = 3) ≤ 8 := by decide
lemma low_ref_5_4 : ((List.range 99).countP fun r => val99 5 r = 4) ≤ 8 := by decide
lemma low_ref_5_5 : ((List.range 99).countP fun r => val99 5 r = 5) ≤ 8 := by decide
lemma low_ref_5_6 : ((List.range 99).countP fun r => val99 5 r = 6) ≤ 8 := by decide
lemma low_ref_5_7 : ((List.range 99).countP fun r => val99 5 r = 7) ≤ 8 := by decide
lemma low_ref_6_0 : ((List.range 99).countP fun r => val99 6 r = 0) ≤ 8 := by decide
lemma low_ref_6_1 : ((List.range 99).countP fun r => val99 6 r = 1) ≤ 8 := by decide
lemma low_ref_6_2 : ((List.range 99).countP fun r => val99 6 r = 2) ≤ 8 := by decide
lemma low_ref_6_3 : ((List.range 99).countP fun r => val99 6 r = 3) ≤ 8 := by decide
lemma low_ref_6_4 : ((List.range 99).countP fun r => val99 6 r = 4) ≤ 8 := by decide
lemma low_ref_6_5 : ((List.range 99).countP fun r => val99 6 r = 5) ≤ 8 := by decide
lemma low_ref_6_6 : ((List.range 99).countP fun r => val99 6 r = 6) ≤ 8 := by decide
lemma low_ref_6_7 : ((List.range 99).countP fun r => val99 6 r = 7) ≤ 8 := by decide
lemma low_ref_7_0 : ((List.range 99).countP fun r => val99 7 r = 0) ≤ 8 := by decide
lemma low_ref_7_1 : ((List.range 99).countP fun r => val99 7 r = 1) ≤ 8 := by decide
lemma low_ref_7_2 : ((List.range 99).countP fun r => val99 7 r = 2) ≤ 8 := by decide
lemma low_ref_7_3 : ((List.range 99).countP fun r => val99 7 r = 3) ≤ 8 := by decide
lemma low_ref_7_4 : ((List.range 99).countP fun r => val99 7 r = 4) ≤ 8 := by decide
lemma low_ref_7_5 : ((List.range 99).countP fun r => val99 7 r = 5) ≤ 8 := by decide
lemma low_ref_7_6 : ((List.range 99).countP fun r => val99 7 r = 6) ≤ 8 := by decide
lemma low_ref_7_7 : ((List.range 99).countP fun r => val99 7 r = 7) ≤ 8 := by decide
lemma aval99 (q r:ℕ) (hr : r < 99) : a (100*q+r) = val99 (sd q) r := by
  interval_cases r <;> simp [val99]

lemma List.countP_congr_bool {α} {p q : α → Bool} : ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.countP p = l.countP q
  | [], h => rfl
  | a::l, h => by
      simp only [List.countP_cons]
      rw [h a (by simp)]
      rw [List.countP_congr_bool (l:=l) (fun x hx => h x (by simp [hx]))]

lemma val99_ge8 (x r : ℕ) (hx : 8 ≤ x) : val99 x r = x + r / 10 + r % 10 ∨ val99 x r = 8 := by
  unfold val99
  split_ifs with h
  · left; rfl
  · right
    have hd : 0 < x + r / 10 + 1 := by omega
    have heq : x + r / 10 + 9 = (x + r / 10 + 1) + 8 := by omega
    rw [heq, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)
lemma val99_ne_low_of_ge8 (x r m : ℕ) (hx : 8 ≤ x) (hm : m < 8) : val99 x r ≠ m := by
  rcases val99_ge8 x r hx with h | h <;> omega
lemma countP_val99_low_ge8 (x m : ℕ) (hx : 8 ≤ x) (hm : m < 8) : ((List.range 99).countP fun r => val99 x r = m) = 0 := by
  induction List.range 99 with
  | nil => rfl
  | cons r l ih =>
      simp [val99_ne_low_of_ge8 x r m hx hm, ih]
lemma first99_low (q m:ℕ) (hm:m<8) : ((List.range 99).countP fun r => a (100*q+r)=m) ≤ 8 := by
  have hcong : ((List.range 99).countP fun r => a (100*q+r)=m) = ((List.range 99).countP fun r => val99 (sd q) r = m) := by
    apply List.countP_congr_bool
    intro r hr
    rw [aval99 q r (List.mem_range.mp hr)]
  rw [hcong]
  by_cases hx : sd q ≤ 7
  · interval_cases m <;> interval_cases hsd : sd q <;> simp_all
    all_goals decide
  · have hx8 : 8 ≤ sd q := by omega
    rw [countP_val99_low_ge8 (sd q) m hx8 hm]
    norm_num


lemma countP_le_count_of_imp (p : ℕ → Bool) (z : ℕ) : ∀ l : List ℕ,
    (∀ a ∈ l, p a = true → a = z) → l.countP p ≤ l.count z
  | [], h => by simp
  | a::l, h => by
    have ih : l.countP p ≤ l.count z := countP_le_count_of_imp p z l (by intro b hb hpb; exact h b (by simp [hb]) hpb)
    simp only [List.countP_cons, List.count_cons]
    by_cases hp : p a = true
    · have haz : a = z := h a (by simp) hp
      subst a
      simp [hp] at *
      omega
    · have hpf : p a = false := by cases hpa : p a <;> simp_all
      simp [hpf]
      omega
lemma val99_eq_gt8_le_imp_zero (x m r : ℕ) (hr : r < 99) (hm8 : 8 < m) (hmx : m ≤ x)
    (h : val99 x r = m) : r = 0 := by
  unfold val99 at h
  split_ifs at h with hu
  · have hmod : r % 10 < 10 := Nat.mod_lt r (by norm_num)
    have hsum0 : r / 10 = 0 ∧ r % 10 = 0 := by omega
    exact (Nat.div_add_mod r 10).symm.trans (by omega)
  · have hmodlt : r % 10 < 10 := Nat.mod_lt r (by norm_num)
    have hmod9 : r % 10 = 9 := by omega
    have hx8 : 8 ≤ x + r / 10 := by omega
    have hv : (x + r / 10 + 9) % (x + r / 10 + 1) = 8 := by
      have heq : x + r / 10 + 9 = (x + r / 10 + 1) + 8 := by omega
      rw [heq, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    omega
lemma first99_gt8_le_one_of_le (x m : ℕ) (hm8 : 8 < m) (hmx : m ≤ x) :
    ((List.range 99).countP fun r => val99 x r = m) ≤ 1 := by
  have hle := countP_le_count_of_imp (fun r => decide (val99 x r = m)) 0 (List.range 99) ?_
  · simpa using hle
  · intro r hr htrue
    exact val99_eq_gt8_le_imp_zero x m r (List.mem_range.mp hr) hm8 hmx (of_decide_eq_true htrue)

def non9col : List ℕ := (List.range 9).flatMap fun u => (List.range 10).map fun t => 10*t+u
def unit9 : List ℕ := (List.range 9).map fun t => 10*t+9
lemma perm99 : (List.range 99).Perm (non9col ++ unit9) := by decide
@[simp] lemma val99_col0 (x t : ℕ) : val99 x (10*t) = x + t + 0 := by
  unfold val99
  have hmod : (10*t) % 10 = 0 := by omega
  have hdiv : (10*t) / 10 = t := by omega
  rw [hmod, hdiv]
  simp

@[simp] lemma val99_col1 (x t : ℕ) : val99 x (10*t+1) = x + t + 1 := by
  unfold val99
  have hmod : (10*t+1) % 10 = 1 := by omega
  have hdiv : (10*t+1) / 10 = t := by omega
  rw [hmod, hdiv]
  simp

@[simp] lemma val99_col2 (x t : ℕ) : val99 x (10*t+2) = x + t + 2 := by
  unfold val99
  have hmod : (10*t+2) % 10 = 2 := by omega
  have hdiv : (10*t+2) / 10 = t := by omega
  rw [hmod, hdiv]
  simp

@[simp] lemma val99_col3 (x t : ℕ) : val99 x (10*t+3) = x + t + 3 := by
  unfold val99
  have hmod : (10*t+3) % 10 = 3 := by omega
  have hdiv : (10*t+3) / 10 = t := by omega
  rw [hmod, hdiv]
  simp

@[simp] lemma val99_col4 (x t : ℕ) : val99 x (10*t+4) = x + t + 4 := by
  unfold val99
  have hmod : (10*t+4) % 10 = 4 := by omega
  have hdiv : (10*t+4) / 10 = t := by omega
  rw [hmod, hdiv]
  simp

@[simp] lemma val99_col5 (x t : ℕ) : val99 x (10*t+5) = x + t + 5 := by
  unfold val99
  have hmod : (10*t+5) % 10 = 5 := by omega
  have hdiv : (10*t+5) / 10 = t := by omega
  rw [hmod, hdiv]
  simp

@[simp] lemma val99_col6 (x t : ℕ) : val99 x (10*t+6) = x + t + 6 := by
  unfold val99
  have hmod : (10*t+6) % 10 = 6 := by omega
  have hdiv : (10*t+6) / 10 = t := by omega
  rw [hmod, hdiv]
  simp

@[simp] lemma val99_col7 (x t : ℕ) : val99 x (10*t+7) = x + t + 7 := by
  unfold val99
  have hmod : (10*t+7) % 10 = 7 := by omega
  have hdiv : (10*t+7) / 10 = t := by omega
  rw [hmod, hdiv]
  simp

@[simp] lemma val99_col8 (x t : ℕ) : val99 x (10*t+8) = x + t + 8 := by
  unfold val99
  have hmod : (10*t+8) % 10 = 8 := by omega
  have hdiv : (10*t+8) / 10 = t := by omega
  rw [hmod, hdiv]
  simp

lemma val99_unit9_le8 (x t : ℕ) : val99 x (10*t+9) ≤ 8 := by
  unfold val99
  have hmod : (10*t+9)%10 = 9 := by omega
  have hdiv : (10*t+9)/10 = t := by omega
  rw [hmod, hdiv]
  simp
  have heq : x + t + 9 = (x+t+1) + 8 := by omega
  rw [heq, Nat.add_mod_left]
  exact Nat.mod_le _ _
lemma unit9_val_gt8_zero (x m : ℕ) (hm8 : 8 < m) : (unit9.countP fun r => val99 x r = m) = 0 := by
  unfold unit9
  norm_num [List.range_succ, List.countP_cons]
  have h0 := val99_unit9_le8 x 0
  have h1 := val99_unit9_le8 x 1
  have h2 := val99_unit9_le8 x 2
  have h3 := val99_unit9_le8 x 3
  have h4 := val99_unit9_le8 x 4
  have h5 := val99_unit9_le8 x 5
  have h6 := val99_unit9_le8 x 6
  have h7 := val99_unit9_le8 x 7
  have h8 := val99_unit9_le8 x 8
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8
  omega
lemma col_val_le_one (x u m : ℕ) : ((List.range 10).countP fun t => x + t + u = m) ≤ 1 := by
  norm_num [List.range_succ, List.countP_cons]
  split_ifs <;> omega
lemma first99_gt8_le9 (x m : ℕ) (hm8 : 8 < m) : ((List.range 99).countP fun r => val99 x r = m) ≤ 9 := by
  rw [perm99.countP_eq]
  rw [List.countP_append]
  rw [unit9_val_gt8_zero x m hm8, add_zero]
  unfold non9col
  rw [List.countP_flatMap]
  rw [show List.range 9 = [0,1,2,3,4,5,6,7,8] by decide]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Function.comp_apply]
  simp only [List.countP_map]
  norm_num [Function.comp_def]
  have h0 := col_val_le_one x 0 m
  have h0z : ((List.range 10).countP fun t => x + t = m) ≤ 1 := by simpa using h0
  have h1 := col_val_le_one x 1 m
  have h2 := col_val_le_one x 2 m
  have h3 := col_val_le_one x 3 m
  have h4 := col_val_le_one x 4 m
  have h5 := col_val_le_one x 5 m
  have h6 := col_val_le_one x 6 m
  have h7 := col_val_le_one x 7 m
  have h8 := col_val_le_one x 8 m
  omega



lemma first99_low_ref (x m : ℕ) (hm : m < 8) : ((List.range 99).countP fun r => val99 x r = m) ≤ 8 := by
  by_cases hx : x ≤ 7
  · interval_cases m <;> interval_cases h : x <;> decide
  · have hx8 : 8 ≤ x := by omega
    rw [countP_val99_low_ge8 x m hx8 hm]
    norm_num
def val100 (x y r : ℕ) : ℕ := if r < 99 then val99 x r else (x + 18) % y
lemma range100_perm : (List.range 100).Perm (List.range 99 ++ [99]) := by decide
lemma val100_first99 (x y r : ℕ) (hr : r < 99) : val100 x y r = val99 x r := by simp [val100, hr]
lemma val100_last (x y : ℕ) : val100 x y 99 = (x + 18) % y := by simp [val100]
lemma first99_count_val100 (x y m : ℕ) :
    ((List.range 99).countP fun r => val100 x y r = m) = ((List.range 99).countP fun r => val99 x r = m) := by
  apply List.countP_congr_bool
  intro r hr
  rw [val100_first99 x y r (List.mem_range.mp hr)]
lemma val100_block_ne8_le9 (x y m : ℕ) (hypos : 0 < y) (hyle : y ≤ x + 1) (hm : m ≠ 8) :
    ((List.range 100).countP fun r => val100 x y r = m) ≤ 9 := by
  rw [range100_perm.countP_eq, List.countP_append]
  simp only [List.countP_cons, List.countP_nil]
  rw [first99_count_val100]
  rcases lt_trichotomy m 8 with hm8 | hm8eq | hm8gt
  · have hlow := first99_low_ref x m hm8
    by_cases hlast : val100 x y 99 = m
    · simp [hlast]; omega
    · have hlastf : (decide (val100 x y 99 = m)) = false := by simp [hlast]
      simp [hlastf]; omega
  · exact (hm hm8eq).elim
  · by_cases hmx : m ≤ x
    · have hfirst := first99_gt8_le_one_of_le x m hm8gt hmx
      by_cases hlast : val100 x y 99 = m
      · simp [hlast]; omega
      · have hlastf : (decide (val100 x y 99 = m)) = false := by simp [hlast]
        simp [hlastf]; omega
    · have hfirst := first99_gt8_le9 x m hm8gt
      have hlast_ne : val100 x y 99 ≠ m := by
        rw [val100_last]
        have hlt : (x + 18) % y < y := Nat.mod_lt _ hypos
        omega
      have hlastf : (decide (val100 x y 99 = m)) = false := by simp [hlast_ne]
      simp [hlastf]; omega
lemma val99_unit9_eq8_of (x t : ℕ) (h : 8 ≤ x + t) : val99 x (10*t+9) = 8 := by
  unfold val99
  have hmod : (10*t+9)%10 = 9 := by omega
  have hdiv : (10*t+9)/10 = t := by omega
  rw [hmod, hdiv]
  simp
  have heq : x + t + 9 = (x+t+1) + 8 := by omega
  rw [heq, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by omega)
lemma first99_count8_ge9_ref (x : ℕ) : ((List.range 99).countP fun r => val99 x r = 8) ≥ 9 := by
  by_cases hx : x ≤ 8
  · interval_cases h : x <;> decide
  · have hx9 : 9 ≤ x := by omega
    rw [perm99.countP_eq, List.countP_append]
    have hunit : (unit9.countP fun r => val99 x r = 8) = 9 := by
      unfold unit9
      norm_num [List.range_succ, List.countP_cons]
      have e0 : val99 x 9 = 8 := by simpa using val99_unit9_eq8_of x 0 (by omega)
      have e1 : val99 x 19 = 8 := by simpa using val99_unit9_eq8_of x 1 (by omega)
      have e2 : val99 x 29 = 8 := by simpa using val99_unit9_eq8_of x 2 (by omega)
      have e3 : val99 x 39 = 8 := by simpa using val99_unit9_eq8_of x 3 (by omega)
      have e4 : val99 x 49 = 8 := by simpa using val99_unit9_eq8_of x 4 (by omega)
      have e5 : val99 x 59 = 8 := by simpa using val99_unit9_eq8_of x 5 (by omega)
      have e6 : val99 x 69 = 8 := by simpa using val99_unit9_eq8_of x 6 (by omega)
      have e7 : val99 x 79 = 8 := by simpa using val99_unit9_eq8_of x 7 (by omega)
      have e8 : val99 x 89 = 8 := by simpa using val99_unit9_eq8_of x 8 (by omega)
      simp [e0,e1,e2,e3,e4,e5,e6,e7,e8]
    rw [hunit]
    omega
lemma val100_block8_ge9 (x y : ℕ) : ((List.range 100).countP fun r => val100 x y r = 8) ≥ 9 := by
  rw [range100_perm.countP_eq, List.countP_append]
  rw [first99_count_val100]
  have h := first99_count8_ge9_ref x
  omega
lemma sd_digits_pos (n:ℕ) (hn:0<n) : sd n = n%10 + sd (n/10) := by
  unfold sd
  rw [Nat.digits_of_two_le_of_pos (by norm_num : 2 ≤ 10) hn]
  simp [List.sum_cons]
lemma sd_succ_le (n:ℕ) : sd (n+1) ≤ sd n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; norm_num [sd]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      rw [sd_digits_pos n hnpos]
      by_cases h9 : n % 10 = 9
      · have hdivlt : n / 10 < n := Nat.div_lt_self hnpos (by norm_num)
        have hspos : 0 < n+1 := by omega
        rw [sd_digits_pos (n+1) hspos]
        have hsucc : (n+1) % 10 = 0 := by omega
        have hdiv : (n+1)/10 = n/10 + 1 := by omega
        rw [hsucc, hdiv]
        have := ih (n/10) hdivlt
        omega
      · have hspos : 0 < n+1 := by omega
        rw [sd_digits_pos (n+1) hspos]
        have hlt9 : n % 10 < 9 := by have := Nat.mod_lt n (by norm_num:0<10); omega
        have hsuccmod : (n+1)%10 = n%10 + 1 := by omega
        have hdiv : (n+1)/10 = n/10 := by omega
        rw [hsuccmod, hdiv]
        omega
lemma sd_pos_of_pos (n : ℕ) (hn : 0 < n) : 0 < sd n := by
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rw [sd_digits_pos n hn]
    by_cases hmod : 0 < n % 10
    · omega
    · have hmod0 : n % 10 = 0 := by have := Nat.mod_lt n (by norm_num : 0 < 10); omega
      have hdivpos : 0 < n / 10 := by
        have hdecomp := Nat.div_add_mod n 10
        omega
      have hlt : n / 10 < n := Nat.div_lt_self hn (by norm_num)
      have ih' := ih (n/10) hlt hdivpos
      omega
lemma sd_mul100 (q : ℕ) : sd (100*q) = sd q := by
  rw [show 100*q = 100*q + 10*0 + 0 by omega]
  rw [sd_two_digits q 0 0 (by norm_num) (by norm_num)]
  omega
lemma sd_100q99 (q : ℕ) : sd (100*q+99) = sd q + 18 := by
  rw [show 100*q+99 = 100*q + 10*9 + 9 by omega]
  rw [sd_two_digits q 9 9 (by norm_num) (by norm_num)]
lemma aval100 (q r : ℕ) (hr : r < 100) : a (100*q+r) = val100 (sd q) (sd (q+1)) r := by
  by_cases hr99 : r < 99
  · rw [val100_first99 _ _ _ hr99]
    exact aval99 q r hr99
  · have hr_eq : r = 99 := by omega
    subst r
    unfold a
    change sd (100*q+99) % sd (100*q+99+1) = val100 (sd q) (sd (q+1)) 99
    rw [val100_last]
    rw [sd_100q99]
    rw [show 100*q+99+1 = 100*(q+1) by omega]
    rw [sd_mul100]
lemma block_count_ne8_le9 (q m : ℕ) (hm : m ≠ 8) :
    ((List.range 100).countP fun r => a (100*q+r) = m) ≤ 9 := by
  have hcong : ((List.range 100).countP fun r => a (100*q+r) = m) =
      ((List.range 100).countP fun r => val100 (sd q) (sd (q+1)) r = m) := by
    apply List.countP_congr_bool
    intro r hr
    rw [aval100 q r (List.mem_range.mp hr)]
  rw [hcong]
  apply val100_block_ne8_le9
  · exact sd_pos_of_pos (q+1) (by omega)
  · exact sd_succ_le q
  · exact hm
lemma block_count8_ge9 (q : ℕ) :
    9 ≤ ((List.range 100).countP fun r => a (100*q+r) = 8) := by
  have hcong : ((List.range 100).countP fun r => a (100*q+r) = 8) =
      ((List.range 100).countP fun r => val100 (sd q) (sd (q+1)) r = 8) := by
    apply List.countP_congr_bool
    intro r hr
    rw [aval100 q r (List.mem_range.mp hr)]
  rw [hcong]
  exact val100_block8_ge9 (sd q) (sd (q+1))
lemma range_add_eq_append (a b:ℕ) : List.range (a+b) = List.range a ++ (List.range b).map (fun r => a+r) := by
  rw [List.range_eq_range', List.range_eq_range' (n:=a), List.range_eq_range' (n:=b)]
  rw [List.map_add_range' (a:=a)]
  rw [← List.range'_append]
  simp
lemma count_full_blocks_ne8 (q m : ℕ) (hm : m ≠ 8) : count_a_eq (100*q) m ≤ 9*q := by
  induction q with
  | zero => simp [count_a_eq]
  | succ q ih =>
    rw [show 100*(q+1) = 100*q + 100 by omega]
    rw [count_a_eq, range_add_eq_append]
    rw [List.countP_append]
    have hb := block_count_ne8_le9 q m hm
    simp only [List.countP_map]
    change (List.range (100 * q)).countP (fun n => a n = m) +
        (List.range 100).countP (fun r => a (100 * q + r) = m) ≤ 9 * (q + 1)
    have ih' : (List.range (100 * q)).countP (fun n => a n = m) ≤ 9*q := by simpa [count_a_eq] using ih
    omega
lemma count_full_blocks_8 (q : ℕ) : 9*q ≤ count_a_eq (100*q) 8 := by
  induction q with
  | zero => simp [count_a_eq]
  | succ q ih =>
    rw [show 100*(q+1) = 100*q + 100 by omega]
    rw [count_a_eq, range_add_eq_append]
    rw [List.countP_append]
    have hb := block_count8_ge9 q
    simp only [List.countP_map]
    change 9 * (q + 1) ≤ (List.range (100 * q)).countP (fun n => a n = 8) +
        (List.range 100).countP (fun r => a (100 * q + r) = 8)
    have ih' : 9*q ≤ (List.range (100 * q)).countP (fun n => a n = 8) := by simpa [count_a_eq] using ih
    omega

lemma count_bound_ne8_qr (q r m : ℕ) (hm : m ≠ 8) : count_a_eq (100*q+r) m ≤ 9*q + r := by
  rw [count_a_eq, range_add_eq_append, List.countP_append]
  simp only [List.countP_map]
  have hfull := count_full_blocks_ne8 q m hm
  have hrem : ((List.range r).countP ((fun n => decide (a n = m)) ∘ fun r => 100*q + r)) ≤ r := by
    simpa using (List.countP_le_length (l := List.range r) (p := ((fun n => decide (a n = m)) ∘ fun r => 100*q + r)))
  have hfull' : (List.range (100*q)).countP (fun n => a n = m) ≤ 9*q := by simpa [count_a_eq] using hfull
  omega
lemma count_lower_8_qr (q r : ℕ) : 9*q ≤ count_a_eq (100*q+r) 8 := by
  rw [count_a_eq, range_add_eq_append, List.countP_append]
  simp only [List.countP_map]
  have hfull := count_full_blocks_8 q
  have hfull' : 9*q ≤ (List.range (100*q)).countP (fun n => a n = 8) := by simpa [count_a_eq] using hfull
  omega
lemma count_bound_ne8 (N m : ℕ) (hm : m ≠ 8) : count_a_eq N m ≤ 9*(N/100) + N%100 := by
  have hN : N = 100*(N/100) + N%100 := (Nat.div_add_mod N 100).symm
  conv_lhs => rw [hN]
  exact count_bound_ne8_qr (N/100) (N%100) m hm
lemma count_lower_8 (N : ℕ) : 9*(N/100) ≤ count_a_eq N 8 := by
  have hN : N = 100*(N/100) + N%100 := (Nat.div_add_mod N 100).symm
  conv_rhs => rw [hN]
  exact count_lower_8_qr (N/100) (N%100)
lemma upper_ratio_bound (N : ℕ) (hN : 0 < N) :
    ((9*(N/100)+N%100 : ℕ) : ℝ) / (N:ℝ) ≤ (9:ℝ)/100 + 100/(N:ℝ) := by
  have hnat : 100 * (N/100) + N%100 = N := by
    exact Nat.div_add_mod N 100
  have hdecomp : (100:ℝ) * ((N/100:ℕ):ℝ) + ((N%100:ℕ):ℝ) = (N:ℝ) := by exact_mod_cast hnat
  have hrnat : N%100 ≤ 99 := Nat.le_of_lt_succ (Nat.mod_lt N (by norm_num:0<100))
  have hr : ((N%100:ℕ):ℝ) ≤ 99 := by exact_mod_cast hrnat
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hqnon : (0:ℝ) ≤ ((N/100:ℕ):ℝ) := by exact_mod_cast Nat.zero_le (N/100)
  have hrnon : (0:ℝ) ≤ ((N%100:ℕ):ℝ) := by exact_mod_cast Nat.zero_le (N%100)
  field_simp [hNpos.ne']
  push_cast
  ring_nf at hdecomp ⊢
  nlinarith [hdecomp, hr, hqnon, hrnon]
lemma lower_ratio_bound (N : ℕ) (hN : 0 < N) :
    (9:ℝ)/100 - 9/(N:ℝ) ≤ ((9*(N/100) : ℕ) : ℝ) / (N:ℝ) := by
  have hnat : 100 * (N/100) + N%100 = N := by
    exact Nat.div_add_mod N 100
  have hdecomp : (100:ℝ) * ((N/100:ℕ):ℝ) + ((N%100:ℕ):ℝ) = (N:ℝ) := by exact_mod_cast hnat
  have hrnat : N%100 ≤ 99 := Nat.le_of_lt_succ (Nat.mod_lt N (by norm_num:0<100))
  have hr : ((N%100:ℕ):ℝ) ≤ 99 := by exact_mod_cast hrnat
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hqnon : (0:ℝ) ≤ ((N/100:ℕ):ℝ) := by exact_mod_cast Nat.zero_le (N/100)
  have hrnon : (0:ℝ) ≤ ((N%100:ℕ):ℝ) := by exact_mod_cast Nat.zero_le (N%100)
  field_simp [hNpos.ne']
  push_cast
  ring_nf at hdecomp ⊢
  nlinarith [hdecomp, hr, hqnon, hrnon]
open Filter Real
open scoped Topology

lemma count_a_eq_le_N (N m : ℕ) : count_a_eq N m ≤ N := by
  simpa [count_a_eq] using (List.countP_le_length (l := List.range N) (p := fun n => decide (a n = m)))
lemma ratio_nonneg (m N : ℕ) : (0:ℝ) ≤ (count_a_eq N m : ℝ) / N := by positivity
lemma ratio_le_one (m N : ℕ) : (count_a_eq N m : ℝ) / N ≤ 1 := by
  by_cases hN : N = 0
  · simp [hN]
  · have hcnt := count_a_eq_le_N N m
    have hNpos : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    calc
      (count_a_eq N m : ℝ) / N ≤ (N:ℝ) / N := div_le_div_of_nonneg_right (by exact_mod_cast hcnt) (le_of_lt hNpos)
      _ = 1 := by field_simp [hNpos.ne']
lemma limsup_ne8_le (m : ℕ) (hm : m ≠ 8) :
    Filter.limsup (fun N : ℕ => (count_a_eq N m : ℝ) / N) atTop ≤ (9:ℝ)/100 := by
  have hbdd : atTop.IsBoundedUnder (fun x y : ℝ => x ≤ y) (fun N : ℕ => (count_a_eq N m : ℝ) / N) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall (ratio_le_one m))
  have hcob : atTop.IsCoboundedUnder (fun x y : ℝ => x ≤ y) (fun N : ℕ => (count_a_eq N m : ℝ) / N) :=
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall (ratio_nonneg m))).isCoboundedUnder_le
  rw [Filter.limsup_le_iff' hcob hbdd]
  intro y hy
  have hpos : 0 < y - (9:ℝ)/100 := by linarith
  have hsmall : ∀ᶠ N : ℕ in atTop, (100:ℝ)/(N:ℝ) < y - (9:ℝ)/100 := by
    exact (tendsto_const_div_atTop_nhds_zero_nat (100:ℝ)).eventually (eventually_lt_nhds hpos)
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hsmallN hN
  have hNp : 0 < N := by omega
  have hcnt := count_bound_ne8 N m hm
  have hdiv : (count_a_eq N m : ℝ) / (N:ℝ) ≤ ((9*(N/100)+N%100:ℕ):ℝ)/(N:ℝ) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcnt) (by positivity)
  have hup := upper_ratio_bound N hNp
  linarith
lemma le_limsup_8 : (9:ℝ)/100 ≤ Filter.limsup (fun N : ℕ => (count_a_eq N 8 : ℝ) / N) atTop := by
  have hbdd : atTop.IsBoundedUnder (fun x y : ℝ => x ≤ y) (fun N : ℕ => (count_a_eq N 8 : ℝ) / N) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall (ratio_le_one 8))
  have hcob : atTop.IsCoboundedUnder (fun x y : ℝ => x ≤ y) (fun N : ℕ => (count_a_eq N 8 : ℝ) / N) :=
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall (ratio_nonneg 8))).isCoboundedUnder_le
  rw [Filter.le_limsup_iff' hcob hbdd]
  intro y hy
  have hpos : 0 < (9:ℝ)/100 - y := by linarith
  have hsmall : ∀ᶠ N : ℕ in atTop, (9:ℝ)/(N:ℝ) < (9:ℝ)/100 - y := by
    exact (tendsto_const_div_atTop_nhds_zero_nat (9:ℝ)).eventually (eventually_lt_nhds hpos)
  have hev : ∀ᶠ N : ℕ in atTop, y ≤ (count_a_eq N 8 : ℝ) / N := by
    filter_upwards [hsmall, eventually_ge_atTop 1] with N hsmallN hN
    have hNp : 0 < N := by omega
    have hcnt := count_lower_8 N
    have hdiv : ((9*(N/100):ℕ):ℝ)/(N:ℝ) ≤ (count_a_eq N 8 : ℝ) / (N:ℝ) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcnt) (by positivity)
    have hlo := lower_ratio_bound N hNp
    linarith
  exact hev.frequently

theorem oeis_326746_conjecture_0 :
  ∀ m : ℕ,
    Filter.limsup (fun N : ℕ => (count_a_eq N 8 : ℝ) / N) atTop
    ≥
    Filter.limsup (fun N : ℕ => (count_a_eq N m : ℝ) / N) atTop := by
  intro m
  by_cases hm : m = 8
  · subst m; rfl
  · exact (limsup_ne8_le m hm).trans le_limsup_8
