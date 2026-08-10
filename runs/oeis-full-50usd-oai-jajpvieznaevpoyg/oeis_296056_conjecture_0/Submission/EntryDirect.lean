import FormalConjectures.Util.ProblemImports

noncomputable def poch (a : ℚ) : ℕ → ℚ
  | 0 => 1
  | n+1 => poch a n * (a + n)
lemma poch_succ (a : ℚ) (n : ℕ) : poch a (n+1) = poch a n * (a+n) := rfl
lemma poch_succ_left (a : ℚ) (n : ℕ) : poch a (n+1) = a * poch (a+1) n := by
  induction n with
  | zero => simp [poch]
  | succ n ih => rw [poch_succ, ih, poch_succ]; norm_num [Nat.cast_add, Nat.cast_one]; ring_nf
lemma poch_two_left (b : ℚ) (n : ℕ) : poch b (n+2) = b * (b+1) * poch (b+2) n := by
  rw [poch_succ_left b (n+1), poch_succ_left (b+1) n]; ring

example (a b : ℚ) (i j : ℕ)
    (hb0 : b ≠ 0) (hb1 : b + 1 ≠ 0) (hbj : b + j ≠ 0)
    (h1 : poch b (i+j+1) ≠ 0) (h2 : poch b (i+j+2) ≠ 0)
    (h3 : poch (b+2) (i+j) ≠ 0) :
    poch a (i+j+2) / poch b (i+j+2)
      - ((a + j) / (b + j)) * (poch a (i+j+1) / poch b (i+j+1))
    = (i+1 : ℚ) * (b-a) * a / (b*(b+1)*(b+j)) * (poch (a+1) (i+j) / poch (b+2) (i+j)) := by
  rw [poch_succ_left a (i+j+1), poch_succ_left a (i+j), poch_two_left b (i+j)]
  rw [poch_succ (a+1) (i+j)]
  field_simp [hb0,hb1,hbj,h1,h2,h3]
  have hs : poch b (i+j+1) = poch b (i+j) * (b + (i+j : ℕ)) := by
    rw [poch_succ]
  have hrel : poch (b+2) (i+j) = poch b (i+j) * (b + (i+j : ℕ)) * (b + (i+j : ℕ) + 1) / (b*(b+1)) := by
    have hb4 : poch b (i+j+2) = poch b (i+j) * (b + (i+j : ℕ)) * (b + (i+j : ℕ) + 1) := by
      rw [show i+j+2 = (i+j+1)+1 by omega, poch_succ, poch_succ]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring_nf
      all_goals simp
    have hb5 : poch b (i+j+2) = b*(b+1)*poch (b+2) (i+j) := poch_two_left b (i+j)
    rw [eq_div_iff (mul_ne_zero hb0 hb1)]
    rw [← hb4, hb5]
    ring
  rw [hs, hrel]
  field_simp [hb0,hb1]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring_nf
