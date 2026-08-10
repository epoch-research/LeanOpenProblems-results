import FormalConjectures.Util.ProblemImports

open Matrix Nat Finset

noncomputable def poch (a : ℚ) : ℕ → ℚ
  | 0 => 1
  | n+1 => poch a n * (a + n)

lemma poch_succ (a : ℚ) (n : ℕ) : poch a (n+1) = poch a n * (a+n) := rfl

lemma poch_succ_left (a : ℚ) (n : ℕ) : poch a (n+1) = a * poch (a+1) n := by
  induction n with
  | zero => simp [poch]
  | succ n ih =>
      rw [poch_succ, ih, poch_succ]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring_nf

lemma poch_two_left (b : ℚ) (n : ℕ) : poch b (n+2) = b * (b+1) * poch (b+2) n := by
  rw [poch_succ_left b (n+1), poch_succ_left (b+1) n]
  ring

lemma poch_ne_zero_of_pos (a : ℚ) (ha : 0 < a) (n : ℕ) : poch a n ≠ 0 := by
  induction n with
  | zero => simp [poch]
  | succ n ih =>
      rw [poch_succ]
      apply mul_ne_zero ih
      have : 0 < a + (n : ℚ) := by positivity
      exact ne_of_gt this

noncomputable def H (n : ℕ) (a b : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => poch a (i.val + j.val) / poch b (i.val + j.val)

lemma entry_id (a b : ℚ) (i j : ℕ)
    (hb0 : b ≠ 0) (hb1 : b + 1 ≠ 0)
    (hbj : b + j ≠ 0)
    (hpbj : poch b j ≠ 0) (hpbj1 : poch b (j+1) ≠ 0)
    (hpbij1 : poch b (i+j+1) ≠ 0) (hpbij2 : poch b (i+j+2) ≠ 0) :
    poch a (i+j+2) / poch b (i+j+2)
      - ((a + j) / (b + j)) * (poch a (i+j+1) / poch b (i+j+1))
    = (i+1 : ℚ) * (b-a) * a / (b*(b+1)*(b+j)) * (poch (a+1) (i+j) / poch (b+2) (i+j)) := by
  have ha1 : poch a (i+j+2) = a * poch (a+1) (i+j+1) := poch_succ_left a (i+j+1)
  have ha2 : poch a (i+j+1) = a * poch (a+1) (i+j) := poch_succ_left a (i+j)
  have hb2 : poch b (i+j+2) = b * (b+1) * poch (b+2) (i+j) := poch_two_left b (i+j)
  have hb3 : poch b (i+j+1) = poch b (i+j) * (b + (i+j : ℕ)) := poch_succ b (i+j)
  have hbp2 : poch (b+2) (i+j) ≠ 0 := by
    intro h
    apply hpbij2
    rw [hb2, h, mul_zero]
  have hden : poch b (i+j) * (b + (i+j : ℕ)) ≠ 0 := by
    rw [← hb3]
    exact hpbij1
  have hb4 : poch b (i+j+2) = poch b (i+j) * (b + (i+j : ℕ)) * (b + (i+j : ℕ) + 1) := by
    rw [show i+j+2 = (i+j+1)+1 by omega, poch_succ, poch_succ]
    ring
  have hrel : poch (b+2) (i+j) = poch b (i+j) * (b + (i+j : ℕ)) * (b + (i+j : ℕ) + 1) / (b*(b+1)) := by
    rw [← hb4, hb2]
    field_simp [hb0, hb1]
  have hden2 : poch b (i+j) * (b + (i+j : ℕ)) * (b + (i+j : ℕ) + 1) ≠ 0 := by
    rw [← hb4]
    exact hpbij2



  rw [ha1, ha2, hb2]
  rw [poch_succ (a+1) (i+j), hrel]
  field_simp [hb0, hb1, hbj, hbp2, hpbij1, hden2]
  rw [hb3]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring_nf
