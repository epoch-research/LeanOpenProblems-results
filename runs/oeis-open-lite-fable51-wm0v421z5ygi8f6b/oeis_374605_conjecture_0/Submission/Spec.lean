import FormalConjectures.Util.ProblemImports

/--
A374605: The sequence $a(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k} \binom{3n+2k}{n}$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

open Finset

namespace Saal

/-- rising factorial over ℚ -/
def rf (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | m + 1 => rf x m * (x + m)

@[simp] lemma rf_zero (x : ℚ) : rf x 0 = 1 := rfl
lemma rf_succ (x : ℚ) (m : ℕ) : rf x (m + 1) = rf x m * (x + m) := rfl

lemma rf_succ_left (x : ℚ) (m : ℕ) : rf x (m + 1) = x * rf (x + 1) m := by
  induction m with
  | zero => simp [rf_succ]
  | succ m ih =>
    rw [rf_succ, ih, rf_succ]
    push_cast
    ring

lemma rf_one (x : ℚ) : rf x 1 = x := by simp [rf_succ]

lemma rf_add (x : ℚ) (m l : ℕ) : rf x (m + l) = rf x m * rf (x + m) l := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [← add_assoc, rf_succ, ih, rf_succ]
    push_cast
    ring

lemma rf_pos {x : ℚ} (hx : 0 < x) (m : ℕ) : 0 < rf x m := by
  induction m with
  | zero => simp
  | succ m ih => rw [rf_succ]; positivity

lemma rf_ne_zero {x : ℚ} (hx : 0 < x) (m : ℕ) : rf x m ≠ 0 := (rf_pos hx m).ne'

/-- duplication formula -/
lemma rf_two_mul (x y z : ℚ) (m : ℕ) (hy : y = x / 2) (hz : z = (x + 1) / 2) :
    rf x (2 * m) = 4 ^ m * rf y m * rf z m := by
  subst hy hz
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, rf_succ, rf_succ, ih, rf_succ, rf_succ]
    push_cast
    ring

/-- rising factorial at a positive integer -/
lemma rf_natCast_succ (a m : ℕ) : rf ((a : ℚ) + 1) m = ((a + m).factorial : ℚ) / (a.factorial : ℚ) := by
  induction m with
  | zero => simp [ne_of_gt (Nat.factorial_pos a)]
  | succ m ih =>
    rw [rf_succ, ih, show a + (m + 1) = (a + m) + 1 by ring, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- rising factorial at a nonpositive integer -/
lemma rf_neg_natCast (a m : ℕ) : rf (-(a : ℚ)) m = (-1) ^ m * (a.descFactorial m : ℚ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [rf_succ, ih, Nat.descFactorial_succ]
    rcases le_or_gt m a with h | h
    · have : ((a - m : ℕ) : ℚ) = (a : ℚ) - m := by push_cast [h]; ring
      push_cast
      rw [this]
      ring
    · rw [Nat.sub_eq_zero_of_le h.le]
      have : a.descFactorial m = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr h
      simp [this]

lemma rf_neg_natCast_of_le (a m : ℕ) (h : m ≤ a) :
    rf (-(a : ℚ)) m = (-1) ^ m * (a.factorial : ℚ) / ((a - m).factorial : ℚ) := by
  rw [rf_neg_natCast]
  have := Nat.factorial_mul_descFactorial h
  have h2 : ((a - m).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  rw [mul_comm]
  exact_mod_cast this

lemma rf_neg_natCast_of_lt (a m : ℕ) (h : a < m) : rf (-(a : ℚ)) m = 0 := by
  rw [rf_neg_natCast, Nat.descFactorial_eq_zero_iff_lt.mpr h]; simp

/-- the term of the Saalschütz sum -/
def F (A B C : ℚ) (k j : ℕ) : ℚ :=
  (k.choose j : ℚ) * rf A j * rf B j * rf (C + j) (k - j) * rf (C - A - B) (k - j)

/-- the certificate term -/
def G (A B C : ℚ) (k j : ℕ) : ℚ :=
  (k.choose j : ℚ) * rf A (j + 1) * rf B (j + 1) * rf (C + j) (k - j) * rf (C - A - B) (k - j)

lemma F_zero (A B C : ℚ) (k : ℕ) : F A B C k 0 = rf C k * rf (C - A - B) k := by
  simp [F]

lemma G_zero (A B C : ℚ) (k : ℕ) : G A B C k 0 = A * B * rf C k * rf (C - A - B) k := by
  simp [G, rf_one]

lemma F_gt (A B C : ℚ) (k j : ℕ) (h : k < j) : F A B C k j = 0 := by
  simp [F, Nat.choose_eq_zero_of_lt h]

lemma G_gt (A B C : ℚ) (k j : ℕ) (h : k < j) : G A B C k j = 0 := by
  simp [G, Nat.choose_eq_zero_of_lt h]

lemma step_zero (A B C : ℚ) (k : ℕ) :
    F A B C (k + 1) 0 = (C - A + k) * (C - B + k) * F A B C k 0 - G A B C k 0 := by
  rw [F_zero, F_zero, G_zero, rf_succ, rf_succ]
  ring

lemma step_succ (A B C : ℚ) (k j : ℕ) (hj : j ≤ k) :
    F A B C (k + 1) (j + 1) =
      (C - A + k) * (C - B + k) * F A B C k (j + 1) + G A B C k j - G A B C k (j + 1) := by
  rcases Nat.eq_or_lt_of_le hj with rfl | hlt
  · rw [F_gt _ _ _ _ _ (Nat.lt_succ_self _), G_gt _ _ _ _ _ (Nat.lt_succ_self _)]
    simp [F, G]
  · obtain ⟨m, rfl⟩ : ∃ m, k = j + m + 1 := ⟨k - j - 1, by omega⟩
    have h1 : j + m + 1 + 1 - (j + 1) = m + 1 := by omega
    have h2 : j + m + 1 - (j + 1) = m := by omega
    have h3 : j + m + 1 - j = m + 1 := by omega
    simp only [F, G, h1, h2, h3]
    have hc : ((j + m + 1).choose (j + 1) : ℚ) * (j + 1) = (j + m + 1).choose j * (m + 1) := by
      have := Nat.choose_succ_right_eq (j + m + 1) j
      rw [show j + m + 1 - j = m + 1 by omega] at this
      exact_mod_cast this
    have hp : ((j + m + 1 + 1).choose (j + 1) : ℚ) =
        (j + m + 1).choose j + (j + m + 1).choose (j + 1) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    rw [hp]
    push_cast
    rw [rf_succ (C + ((j:ℚ) + 1)) m, rf_succ (C - A - B) m, rf_succ_left (C + (j:ℚ)) m,
      rf_succ A (j + 1), rf_succ B (j + 1), show C + (j:ℚ) + 1 = C + ((j:ℚ) + 1) by ring]
    push_cast
    linear_combination
      (-(rf A (j + 1) * rf B (j + 1) * rf (C + ((j:ℚ) + 1)) m * rf (C - A - B) m * (C - A - B + m))) *
        hc

/-- Pfaff–Saalschütz identity (division-free polynomial form). -/
theorem saalschutz (A B C : ℚ) (k : ℕ) :
    ∑ j ∈ range (k + 1), F A B C k j = rf (C - A) k * rf (C - B) k := by
  induction k with
  | zero => simp [F]
  | succ k ih =>
    rw [Finset.sum_range_succ', step_zero]
    rw [Finset.sum_congr rfl (fun j hj => step_succ A B C k j (by
      simpa [Nat.lt_succ_iff] using hj))]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' (fun j => G A B C k j), Finset.sum_range_succ (fun j => G A B C k (j + 1))]
    rw [← Finset.mul_sum]
    have hS : ∑ j ∈ range (k + 1), F A B C k (j + 1) = ∑ j ∈ range (k + 1), F A B C k j - F A B C k 0 := by
      rw [Finset.sum_range_succ' (fun j => F A B C k j)]
      rw [Finset.sum_range_succ (fun j => F A B C k (j + 1))]
      rw [F_gt _ _ _ _ _ (Nat.lt_succ_self k)]
      ring
    rw [hS, ih, G_gt _ _ _ _ _ (Nat.lt_succ_self k), rf_succ, rf_succ]
    ring

/-- Saalschütz instance 1 -/
lemma expand1 (n k : ℕ) :
    rf (3 * n + 1) (2 * k) = ∑ j ∈ range (k + 1), (k.choose j : ℚ) * rf (-((n:ℚ) + 1)) (2 * j) *
      rf (2 * n + 2 * j + 1) (2 * (k - j)) * rf (2 * n + 1) (k - j) / rf ((n:ℚ) + j + 1) (k - j) := by
  have h := saalschutz (-(n:ℚ)/2) (-((n:ℚ)+1)/2) ((n:ℚ) + 1/2) k
  have e1 : rf ((3:ℚ) * n + 1) (2 * k) =
      4 ^ k * rf ((n:ℚ) + 1/2 - (-(n:ℚ)/2)) k * rf ((n:ℚ) + 1/2 - (-((n:ℚ)+1)/2)) k :=
    rf_two_mul _ _ _ k (by ring) (by ring)
  rw [e1, mul_assoc, ← h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  obtain ⟨m, rfl⟩ : ∃ m, k = j + m := ⟨k - j, by omega⟩
  simp only [F, Nat.add_sub_cancel_left]
  rw [rf_two_mul (-((n:ℚ)+1)) (-((n:ℚ)+1)/2) (-(n:ℚ)/2) j (by ring) (by ring)]
  rw [rf_two_mul (2 * (n:ℚ) + 2 * j + 1) ((n:ℚ) + 1/2 + j) ((n:ℚ) + j + 1) m (by ring) (by ring)]
  rw [show (n:ℚ) + 1/2 - (-(n:ℚ)/2) - (-((n:ℚ)+1)/2) = 2 * n + 1 by ring]
  have hne := rf_ne_zero (show (0:ℚ) < (n:ℚ) + j + 1 by positivity) m
  rw [pow_add]
  field_simp

/-- expansion of the summand of `a n` -/
lemma T_expand (n k : ℕ) :
    ((n.choose k : ℚ))^2 * ((n+k).choose k : ℚ) * ((3*n+2*k).choose n : ℚ) =
      ∑ j ∈ range (k+1), (n.choose k : ℚ)^2 * (k.choose j : ℚ) * rf (-((n:ℚ)+1)) (2*j) *
        ((3*n).factorial : ℚ) * ((2*n+k-j).factorial : ℚ) * ((n+j).factorial : ℚ) /
        (((2*n+2*j).factorial : ℚ) * ((2*n).factorial : ℚ) * ((n.factorial : ℚ))^2 * (k.factorial : ℚ)) := by
  have h := expand1 n k
  have e1 := rf_natCast_succ (3*n) (2*k)
  push_cast at e1
  rw [e1] at h
  have c1 : ((3*n+2*k).choose n : ℚ) = ((3*n+2*k).factorial : ℚ) / ((n.factorial : ℚ) * ((2*n+2*k).factorial : ℚ)) := by
    rw [Nat.cast_choose ℚ (by omega : n ≤ 3*n+2*k), show 3*n+2*k-n = 2*n+2*k by omega]
  have c2 : ((n+k).choose k : ℚ) = ((n+k).factorial : ℚ) / ((k.factorial : ℚ) * (n.factorial : ℚ)) := by
    rw [Nat.cast_choose ℚ (by omega : k ≤ n+k), show n+k-k = n by omega]
  have h3 : ((3*n+2*k).factorial : ℚ) = ((3*n).factorial : ℚ) * (∑ j ∈ range (k + 1), (k.choose j : ℚ) * rf (-((n:ℚ) + 1)) (2 * j) *
      rf (2 * n + 2 * j + 1) (2 * (k - j)) * rf (2 * n + 1) (k - j) / rf ((n:ℚ) + j + 1) (k - j)) := by
    rw [← h]; field_simp
  rw [c1, c2, h3]
  simp only [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  obtain ⟨m, rfl⟩ : ∃ m, k = j + m := ⟨k - j, by omega⟩
  simp only [Nat.add_sub_cancel_left]
  have e2 := rf_natCast_succ (2*n+2*j) (2*m)
  have e3 := rf_natCast_succ (2*n) m
  have e4 := rf_natCast_succ (n+j) m
  push_cast at e2 e3 e4
  rw [e2, e3, e4, show 2*n+2*j+2*m = 2*n+2*(j+m) by ring, show 2*n+(j+m)-j = 2*n+m by omega,
    show n + j + m = n + (j + m) by ring]
  field_simp

/-- Saalschütz instance 2 (the inner sum) -/
lemma inner_sum (j N : ℕ) :
    ∑ m ∈ range (N+1), ((j+N).choose (j+m) : ℚ) * (N.choose m : ℚ) *
        ((2*(j+N)+m).factorial : ℚ) / ((j+m).factorial : ℚ)
      = ((2*(j+N)).factorial : ℚ) * ((j+2*N).factorial : ℚ)^2 /
          ((N.factorial : ℚ) * ((j+N).factorial : ℚ)^3) := by
  have h := saalschutz (-(N:ℚ)) (2*((j:ℚ)+N)+1) ((j:ℚ)+1) N
  have e1 : rf ((j:ℚ)+1 - (-(N:ℚ))) N = ((j+N+N).factorial : ℚ) / ((j+N).factorial : ℚ) := by
    rw [show (j:ℚ)+1 - (-(N:ℚ)) = ((j+N : ℕ) : ℚ) + 1 by push_cast; ring]
    exact rf_natCast_succ _ _
  have e2 : rf ((j:ℚ)+1 - (2*((j:ℚ)+N)+1)) N = (-1)^N * ((j+2*N).factorial : ℚ) / ((j+N).factorial : ℚ) := by
    rw [show (j:ℚ)+1 - (2*((j:ℚ)+N)+1) = -((j+2*N : ℕ) : ℚ) by push_cast; ring,
      rf_neg_natCast_of_le _ _ (by omega), show j+2*N-N = j+N by omega]
  rw [e1, e2] at h
  have key : ∀ m ∈ range (N+1), ((j+N).choose (j+m) : ℚ) * (N.choose m : ℚ) *
        ((2*(j+N)+m).factorial : ℚ) / ((j+m).factorial : ℚ) =
      ((2*(j+N)).factorial : ℚ) / ((N.factorial : ℚ) * ((j+N).factorial : ℚ)) * (-1)^N *
        F (-(N:ℚ)) (2*((j:ℚ)+N)+1) ((j:ℚ)+1) N m := by
    intro m hm
    have hm' : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    obtain ⟨r, rfl⟩ : ∃ r, N = m + r := ⟨N - m, by omega⟩
    simp only [F, Nat.add_sub_cancel_left]
    rw [rf_neg_natCast_of_le _ _ (by omega : m ≤ m + r), show m + r - m = r by omega]
    have e3 := rf_natCast_succ (2*(j+(m+r))) m
    have e4 := rf_natCast_succ (j+m) r
    have e5 := rf_neg_natCast_of_le (j+(m+r)) r (by omega)
    push_cast at e3 e4 e5 ⊢
    rw [e3]
    rw [show (j:ℚ) + 1 + (m:ℚ) = (j:ℚ) + (m:ℚ) + 1 by ring, e4]
    rw [show (j:ℚ) + 1 - -((m:ℚ) + r) - (2 * ((j:ℚ) + ((m:ℚ) + r)) + 1) = -((j:ℚ) + ((m:ℚ) + r)) by ring, e5]
    rw [Nat.cast_choose ℚ (by omega : j + m ≤ j + (m+r)), Nat.cast_choose ℚ (by omega : m ≤ m + r),
      show j + (m+r) - (j+m) = r by omega, show m + r - m = r by omega,
      show j + (m + r) - r = j + m by omega]
    push_cast
    rw [show j + m + r = j + (m + r) by ring, pow_add]
    rcases Nat.even_or_odd m with hm | hm <;> rcases Nat.even_or_odd r with hr | hr <;>
      simp only [hm.neg_one_pow, hr.neg_one_pow] <;> field_simp <;> ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, h]
  rw [show j + N + N = j + 2 * N by ring]
  rcases Nat.even_or_odd N with hN | hN <;> simp only [hN.neg_one_pow] <;> field_simp <;> ring


/-- the summand after expansion -/
def f (n k j : ℕ) : ℚ :=
  (n.choose k : ℚ)^2 * (k.choose j : ℚ) * rf (-((n:ℚ)+1)) (2*j) *
        ((3*n).factorial : ℚ) * ((2*n+k-j).factorial : ℚ) * ((n+j).factorial : ℚ) /
        (((2*n+2*j).factorial : ℚ) * ((2*n).factorial : ℚ) * ((n.factorial : ℚ))^2 * (k.factorial : ℚ))

lemma T_expand' (n k : ℕ) :
    ((n.choose k : ℚ))^2 * ((n+k).choose k : ℚ) * ((3*n+2*k).choose n : ℚ) =
      ∑ j ∈ range (k+1), f n k j := T_expand n k

/-- the inner sum after swapping -/
lemma inner_eval (j N : ℕ) :
    ∑ m ∈ range (N+1), f (j+N) (j+m) j =
      ((j+N).choose j : ℚ) * rf (-(((j+N : ℕ) : ℚ)+1)) (2*j) * ((3*(j+N)).factorial : ℚ) *
        ((j+N+j).factorial : ℚ) /
        (((2*(j+N)+2*j).factorial : ℚ) * ((2*(j+N)).factorial : ℚ) * (((j+N).factorial : ℚ))^2) *
      (((2*(j+N)).factorial : ℚ) * ((j+2*N).factorial : ℚ)^2 /
          ((N.factorial : ℚ) * (((j+N).factorial : ℚ))^3)) := by
  rw [← inner_sum j N, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hc : ((j+N).choose (j+m) : ℚ) * ((j+m).choose j : ℚ) =
      ((j+N).choose j : ℚ) * (N.choose m : ℚ) := by
    have := Nat.choose_mul (n := j+N) (k := j+m) (s := j) (by omega)
    rw [show j + N - j = N by omega, show j + m - j = m by omega] at this
    exact_mod_cast this
  unfold f
  rw [show 2*(j+N)+(j+m)-j = 2*(j+N)+m by omega]
  have hne1 : (((2*(j+N)+2*j).factorial : ℚ)) ≠ 0 := by positivity
  have hne2 : (((2*(j+N)).factorial : ℚ)) ≠ 0 := by positivity
  have hne3 : (((j+N).factorial : ℚ)) ≠ 0 := by positivity
  have hne4 : (((j+m).factorial : ℚ)) ≠ 0 := by positivity
  have hne5 : ((N.factorial : ℚ)) ≠ 0 := by positivity
  rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (((j+N).choose (j+m) : ℚ) * rf (-(((j+N : ℕ) : ℚ)+1)) (2*j) * ((3*(j+N)).factorial : ℚ) *
        ((j+N+j).factorial : ℚ) * ((2*(j+N)+m).factorial : ℚ) *
        (((2*(j+N)+2*j).factorial : ℚ) * ((2*(j+N)).factorial : ℚ) * (((j+N).factorial : ℚ))^2 * ((j+m).factorial : ℚ))) * hc

theorem main_identity (n : ℕ) :
    ((3*n+1 : ℕ) : ℚ) * ∑ k ∈ range (n+1),
        (((n.choose k : ℚ))^2 * ((n+k).choose k : ℚ) * ((3*n+2*k).choose n : ℚ))
    = ((n+1 : ℕ) : ℚ) * ∑ j ∈ range (n+1), (if 2*j ≤ n+1 then
        (((3*n+1).choose (n+1-2*j) : ℚ) * ((2*n-j).choose n : ℚ)^2 * ((n+j).choose j : ℚ)) else 0) := by
  rw [Finset.sum_congr rfl (fun k _ => T_expand' n k)]
  rw [Finset.sum_comm' (t' := range (n+1)) (s' := fun j => Ico j (n+1)) (by
    intro k j; simp only [mem_range, mem_Ico]; omega)]
  simp only [Finset.sum_Ico_eq_sum_range]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  obtain ⟨N, rfl⟩ : ∃ N, n = j + N := ⟨n - j, by omega⟩
  rw [show j + N + 1 - j = N + 1 by omega, inner_eval]
  split_ifs with h2
  · have e := rf_neg_natCast_of_le (j+N+1) (2*j) h2
    rw [show j+N+1-2*j = N+1-j by omega, pow_mul, neg_one_sq, one_pow, one_mul] at e
    push_cast at e ⊢
    rw [e]
    rw [show j+N+1-2*j = N+1-j by omega, show 2*(j+N)-j = j+2*N by omega]
    rw [Nat.cast_choose ℚ (by omega : N+1-j ≤ 3*(j+N)+1), show 3*(j+N)+1-(N+1-j) = 2*(j+N)+2*j by omega,
      Nat.cast_choose ℚ (by omega : j+N ≤ j+2*N), show j+2*N-(j+N) = N by omega,
      Nat.cast_choose ℚ (by omega : j ≤ j+N+j), show j+N+j-j = j+N by omega,
      Nat.cast_choose ℚ (by omega : j ≤ j+N), show j+N-j = N by omega,
      Nat.factorial_succ (3*(j+N)), Nat.factorial_succ (j+N)]
    push_cast
    have h1 : ((N+1-j).factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((2*(j+N)+2*j).factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((j+N).factorial : ℚ) ≠ 0 := by positivity
    have h4 : (N.factorial : ℚ) ≠ 0 := by positivity
    have h5 : (j.factorial : ℚ) ≠ 0 := by positivity
    have h6 : ((2*(j+N)).factorial : ℚ) ≠ 0 := by positivity
    field_simp
  · have e := rf_neg_natCast_of_lt (j+N+1) (2*j) (by omega)
    push_cast at e ⊢
    rw [e]
    simp

lemma term_dvd (p n j : ℕ) (hp : p.Prime) (h3 : 2*p+1 ≤ 3*n) (hn : n ≤ p - 1) (hj : 2*j ≤ n+1) :
    p^3 ∣ (n+1) * ((3*n+1).choose (n+1-2*j) * ((2*n-j).choose n)^2 * (n+j).choose j) := by
  have hp2 : 2 ≤ p := hp.two_le
  have h1 : p ∣ (2*n-j).choose n := by
    have := hp.dvd_choose_add (a := n) (b := n - j) (by omega) (by omega) (by omega)
    rwa [show n + (n - j) = 2*n-j by omega] at this
  have h1' : p^2 ∣ ((2*n-j).choose n)^2 := pow_dvd_pow_of_dvd h1 2
  have key : p ∣ (n+1) * ((3*n+1).choose (n+1-2*j) * (n+j).choose j) := by
    rcases le_or_gt p (n+j) with h | h
    · have h2 : p ∣ (n+j).choose j := by
        have := hp.dvd_choose_add (a := j) (b := n) (by omega) (by omega) (by omega)
        rwa [add_comm] at this
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_left h2 _) _
    · rcases Nat.eq_or_lt_of_le (show n + 1 ≤ p by omega) with h4 | h4
      · rw [h4]; exact Dvd.intro _ rfl
      · have h2 : p ∣ (3*n+1).choose (n+1-2*j) := by
          haveI := Fact.mk hp
          have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat
            (n := 3*n+1) (k := n+1-2*j) (p := p)
          have hm1 : (3*n+1) % p = 3*n+1-2*p := by
            have e : 3*n+1 = (3*n+1-2*p) + p*2 := by omega
            conv_lhs => rw [e, Nat.add_mul_mod_self_left]
            exact Nat.mod_eq_of_lt (by omega)
          have hm2 : (n+1-2*j) % p = n+1-2*j := Nat.mod_eq_of_lt (by omega)
          rw [hm1, hm2, Nat.choose_eq_zero_of_lt (n := 3*n+1-2*p) (k := n+1-2*j) (by omega),
            zero_mul] at hl
          exact (Nat.modEq_zero_iff_dvd).mp hl
        exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h2 _) _
  calc p^3 = p^2 * p := by ring
    _ ∣ ((2*n-j).choose n)^2 * ((n+1) * ((3*n+1).choose (n+1-2*j) * (n+j).choose j)) :=
        mul_dvd_mul h1' key
    _ = _ := by ring

end Saal

lemma main_identity_nat (n : ℕ) :
    (3*n+1) * a n = (n+1) * ∑ j ∈ range (n+1), (if 2*j ≤ n+1 then
        (3*n+1).choose (n+1-2*j) * ((2*n-j).choose n)^2 * (n+j).choose j else 0) := by
  have h := Saal.main_identity n
  unfold a
  exact_mod_cast h

/--
Conjecture: for prime $p \ge 5$, $a(n)$ is divisible by $p^3$ for integer $n$ in the interval $[\lceil\frac{2p + 1}{3}\rceil, p - 1]$.
The lower bound $\lceil\frac{2p + 1}{3}\rceil$ for $p \in \mathbb{N}$ is expressed using natural number division as $(2 * p + 1 + 2) / 3 = (2 * p + 3) / 3$.
-/
theorem oeis_374605_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
  ∀ n : ℕ,
    (2 * p + 3) / 3 ≤ n →
    n ≤ p - 1 →
    (p ^ 3 : ℕ) ∣ a n := by
  intro n h1 h2
  have h3 : 2*p+1 ≤ 3*n := by omega
  have hid := main_identity_nat n
  have hb : p^3 ∣ (n+1) * ∑ j ∈ range (n+1), (if 2*j ≤ n+1 then
        (3*n+1).choose (n+1-2*j) * ((2*n-j).choose n)^2 * (n+j).choose j else 0) := by
    rw [Finset.mul_sum]
    apply Finset.dvd_sum
    intro j hj
    split_ifs with hj2
    · exact Saal.term_dvd p n j hp h3 h2 hj2
    · simp
  rw [← hid] at hb
  have hcop : Nat.Coprime (p^3) (3*n+1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    obtain ⟨c, hc⟩ := hd
    have hc2 : 2 < c := by
      by_contra h; push_neg at h; have := Nat.mul_le_mul_left p h; omega
    have hc3 : c < 3 := by
      by_contra h; push_neg at h; have := Nat.mul_le_mul_left p h; omega
    omega
  exact hcop.dvd_of_dvd_mul_left hb


theorem oeis_374605_conjecture_0.disproof : ¬ (type_of% @oeis_374605_conjecture_0) := sorry
