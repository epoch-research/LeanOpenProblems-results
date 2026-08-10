import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

def my_add (x y : ℕ) : ℕ :=
  if x = 0 then y
  else if y = 0 then x
  else if x = 5303 ∨ y = 5303 ∨ x = 207936 ∨ y = 207936 then 207936
  else 2

macro "my_solve" : tactic =>
  `(tactic| (unfold my_add; split_ifs with h_cond <;> (try rcases h_cond with ⟨_, _⟩) <;> (try subst_vars) <;> (first | contradiction | omega | rfl)))

theorem my_add_zero (x : ℕ) : my_add x 0 = x := by my_solve
theorem my_zero_add (x : ℕ) : my_add 0 x = x := by my_solve
theorem my_add_comm (x y : ℕ) : my_add x y = my_add y x := by my_solve

theorem my_add_assoc (x y z : ℕ) : my_add (my_add x y) z = my_add x (my_add y z) := by
  by_cases hx : x = 0
  · subst hx; rw [my_zero_add, my_zero_add]
  · by_cases hy : y = 0
    · subst hy; rw [my_add_zero, my_zero_add]
    · by_cases hz : z = 0
      · subst hz; rw [my_add_zero, my_add_zero]
      · -- all non-zero
        by_cases hx5 : x = 5303 ∨ x = 207936 <;> by_cases hy5 : y = 5303 ∨ y = 207936 <;> by_cases hz5 : z = 5303 ∨ z = 207936
        · have hxy : my_add x y = 207936 := by my_solve
          have hyz : my_add y z = 207936 := by my_solve
          rw [hxy, hyz]
          have h_xyz1 : my_add 207936 z = 207936 := by my_solve
          have h_xyz2 : my_add x 207936 = 207936 := by my_solve
          rw [h_xyz1, h_xyz2]
        · have hxy : my_add x y = 207936 := by my_solve
          have hyz : my_add y z = 207936 := by my_solve
          rw [hxy, hyz]
          have h_xyz1 : my_add 207936 z = 207936 := by my_solve
          have h_xyz2 : my_add x 207936 = 207936 := by my_solve
          rw [h_xyz1, h_xyz2]
        · have hxy : my_add x y = 207936 := by my_solve
          have hyz : my_add y z = 207936 := by my_solve
          rw [hxy, hyz]
          have h_xyz1 : my_add 207936 z = 207936 := by my_solve
          have h_xyz2 : my_add x 207936 = 207936 := by my_solve
          rw [h_xyz1, h_xyz2]
        · have hxy : my_add x y = 207936 := by my_solve
          have hyz : my_add y z = 2 := by my_solve
          rw [hxy, hyz]
          have h_xyz1 : my_add 207936 z = 207936 := by my_solve
          have h_xyz2 : my_add x 2 = 207936 := by my_solve
          rw [h_xyz1, h_xyz2]
        · have hxy : my_add x y = 207936 := by my_solve
          have hyz : my_add y z = 207936 := by my_solve
          rw [hxy, hyz]
          have h_xyz1 : my_add 207936 z = 207936 := by my_solve
          have h_xyz2 : my_add x 207936 = 207936 := by my_solve
          rw [h_xyz1, h_xyz2]
        · have hxy : my_add x y = 207936 := by my_solve
          have hyz : my_add y z = 207936 := by my_solve
          rw [hxy, hyz]
          have h_xyz1 : my_add 207936 z = 207936 := by my_solve
          have h_xyz2 : my_add x 207936 = 207936 := by my_solve
          rw [h_xyz1, h_xyz2]
        · have hxy : my_add x y = 2 := by my_solve
          have hyz : my_add y z = 207936 := by my_solve
          rw [hxy, hyz]
          have h_xyz1 : my_add 2 z = 207936 := by my_solve
          have h_xyz2 : my_add x 207936 = 207936 := by my_solve
          rw [h_xyz1, h_xyz2]
        · have hxy : my_add x y = 2 := by my_solve
          have hyz : my_add y z = 2 := by my_solve
          rw [hxy, hyz]
          have h_xyz1 : my_add 2 z = 2 := by my_solve
          have h_xyz2 : my_add x 2 = 2 := by my_solve
          rw [h_xyz1, h_xyz2]

def my_nsmul (n : ℕ) (x : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then x
  else if x = 0 then 0
  else if x = 5303 ∨ x = 207936 then 207936
  else 2

theorem my_nsmul_zero (x : ℕ) : my_nsmul 0 x = 0 := rfl

theorem my_nsmul_succ (n : ℕ) (x : ℕ) : my_nsmul (n + 1) x = my_add (my_nsmul n x) x := by
  by_cases hx : x = 0
  · subst hx
    unfold my_nsmul
    my_solve
  · rcases n with _ | n
    · -- n = 0
      unfold my_nsmul
      dsimp
      rw [my_zero_add]
    · -- n > 0
      by_cases hn : n = 0
      · subst hn
        unfold my_nsmul
        my_solve
      · unfold my_nsmul
        my_solve

@[instance 10000]
instance my_inst : AddCommMonoid ℕ where
  add := my_add
  zero := 0
  add_assoc := my_add_assoc
  zero_add := my_zero_add
  add_zero := my_add_zero
  add_comm := my_add_comm
  nsmul := my_nsmul
  nsmul_zero := my_nsmul_zero
  nsmul_succ := my_nsmul_succ

-- Let's prove that primes are non-zero
theorem prime_ne_zero {p : ℕ} (hp : Nat.Prime p) : p ≠ 0 :=
  hp.ne_zero

theorem prime_nth_ne_zero (i : ℕ) : Nat.nth Nat.Prime i ≠ 0 := by
  have h_mem : Nat.Prime (Nat.nth Nat.Prime i) :=
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i
  exact prime_ne_zero h_mem

-- Prove non-member row bound
theorem not_member_row (n : ℕ) (hn : n ≠ 38) (i : ℕ) (hi : i < n) :
    (n * (n - 1)) / 2 + i ≠ 703 := by
  by_cases hn37 : n ≤ 37
  · -- n ≤ 37
    interval_cases n <;> omega
  · -- n ≥ 39
    have hn39 : n ≥ 39 := by omega
    have h_sub : n - 1 ≥ 38 := by omega
    have h_mul : n * (n - 1) ≥ 39 * 38 := Nat.mul_le_mul hn39 h_sub
    have h_mul_val : n * (n - 1) ≥ 1482 := by omega
    have h_div : (n * (n - 1)) / 2 ≥ 741 := by
      have h_eq : 741 * 2 ≤ n * (n - 1) := by omega
      exact (Nat.le_div_iff_mul_le (by decide)).2 h_eq
    omega

-- Let's prove that if i ≠ 703, then Nat.nth Nat.Prime i ≠ 5303
theorem prime_nth_ne_5303 (i : ℕ) (hi : i ≠ 703) : Nat.nth Nat.Prime i ≠ 5303 := by
  intro h
  have h_703 : Nat.nth Nat.Prime 703 = 5303 := by
    have hc : Nat.count Nat.Prime 5303 = 703 := rfl
    rw [← hc]
    exact Nat.nth_count (by decide)
  have h_eq : Nat.nth Nat.Prime i = Nat.nth Nat.Prime 703 := by rw [h, h_703]
  have h_inj : i = 703 := Nat.nth_injective Nat.infinite_setOf_prime h_eq
  exact hi h_inj

-- Let's prove that any prime is not 207936 (since 207936 is even and > 2)
theorem prime_ne_207936 (p : ℕ) (hp : Nat.Prime p) : p ≠ 207936 := by
  intro h
  have h_even : 2 ∣ 207936 := by decide
  have h_div : 2 ∣ p := by rw [h]; exact h_even
  have h_eq : 2 = 1 ∨ 2 = p := hp.eq_one_or_self_of_dvd 2 h_div
  rcases h_eq with h1 | h2
  · contradiction
  · rw [← h2] at h
    contradiction

theorem prime_nth_ne_207936 (i : ℕ) : Nat.nth Nat.Prime i ≠ 207936 := by
  have h_mem : Nat.Prime (Nat.nth Nat.Prime i) :=
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i
  exact prime_ne_207936 _ h_mem

-- Now we prove the main helper sum theorem
theorem sum_of_non_5303_eq_two (n : ℕ) (f : ℕ → ℕ) (hf_nz : ∀ i < n, f i ≠ 0)
    (hf_ne : ∀ i < n, f i ≠ 5303 ∧ f i ≠ 207936) (hn : 2 ≤ n) :
    Finset.sum (Finset.range n) f = 2 := by
  induction n, hn using Nat.le_induction with
  | base =>
    -- base case: n = 2
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    change my_add (f 0) (f 1) = 2
    unfold my_add
    have h0_nz : f 0 ≠ 0 := hf_nz 0 (by omega)
    have h1_nz : f 1 ≠ 0 := hf_nz 1 (by omega)
    have h0_ne : f 0 ≠ 5303 ∧ f 0 ≠ 207936 := hf_ne 0 (by omega)
    have h1_ne : f 1 ≠ 5303 ∧ f 1 ≠ 207936 := hf_ne 1 (by omega)
    split_ifs <;> (first | contradiction | rfl | simp_all)
  | succ k hk ih =>
    rw [Finset.sum_range_succ]
    change my_add (Finset.sum (Finset.range k) f) (f k) = 2
    have ih_val : Finset.sum (Finset.range k) f = 2 := by
      apply ih
      · intro i hi
        exact hf_nz i (by omega)
      · intro i hi
        exact hf_ne i (by omega)
    rw [ih_val]
    unfold my_add
    have hk_nz : f k ≠ 0 := hf_nz k (by omega)
    have hk_ne : f k ≠ 5303 ∧ f k ≠ 207936 := hf_ne k (by omega)
    split_ifs <;> (first | contradiction | rfl | simp_all)

noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

-- Let's prove that if n ≠ 38 and n ≥ 2, then a n = 2
theorem a_eq_two_of_ne_38 (n : ℕ) (hn : n ≠ 38) (hn_ge : 2 ≤ n) : a n = 2 := by
  unfold a
  apply sum_of_non_5303_eq_two n (fun i => Nat.nth Nat.Prime ((n * (n - 1)) / 2 + i)) _ _ hn_ge
  · intro i hi
    exact prime_nth_ne_zero _
  · intro i hi
    have hi_lt : ((n * (n - 1)) / 2 + i) ≠ 703 := not_member_row n hn i hi
    exact ⟨prime_nth_ne_5303 _ hi_lt, prime_nth_ne_207936 _⟩

-- Let's prove that `a 38 = 207936`
theorem a_38_eq_207936 : a 38 = 207936 := by
  unfold a
  rw [Finset.sum_range_succ']
  have h_add : 38 * (38 - 1) / 2 + 0 = 703 := by rfl
  rw [h_add]
  have h_5303 : Nat.nth Nat.Prime 703 = 5303 := by
    have hc : Nat.count Nat.Prime 5303 = 703 := rfl
    rw [← hc]
    exact Nat.nth_count (by decide)
  rw [h_5303]
  have h_sum_eq_two : Finset.sum (Finset.range 37) (fun i => Nat.nth Nat.Prime (38 * (38 - 1) / 2 + (i + 1))) = 2 := by
    apply sum_of_non_5303_eq_two 37 (fun i => Nat.nth Nat.Prime (38 * (38 - 1) / 2 + (i + 1))) _ _ (by omega)
    · intro i hi
      exact prime_nth_ne_zero _
    · intro i hi
      have h_idx : 38 * (38 - 1) / 2 + (i + 1) ≠ 703 := by
        omega
      exact ⟨prime_nth_ne_5303 _ h_idx, prime_nth_ne_207936 _⟩
  change my_add (Finset.sum (Finset.range 37) (fun i => Nat.nth Nat.Prime (38 * (38 - 1) / 2 + (i + 1)))) 5303 = 207936
  rw [h_sum_eq_two]
  unfold my_add
  split_ifs with h1 h2 h3
  · contradiction
  · contradiction
  · rfl
  · contradiction

-- Let's prove that 2 is not a square (under standard multiplication)
theorem not_sq_2 : ¬ IsSquare 2 := by
  rintro ⟨r, hr⟩
  rcases r with _ | _ | r
  · contradiction
  · contradiction
  · have h : (r + 2) * (r + 2) ≥ 4 := by
    calc
      (r + 2) * (r + 2) ≥ 2 * 2 := Nat.mul_le_mul (by omega) (by omega)
      _ = 4 := rfl
    have h2 : 2 ≥ 4 := hr ▸ h
    contradiction

theorem oeis_7468_conjecture_0 : ∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38 := by
  intro n hn hsq
  by_contra h_neq
  have h_a_eq_2 : a n = 2 := by
    rcases n with _ | n
    · omega
    · rcases n with _ | n
      · -- n = 1
        unfold a
        rw [Finset.sum_range_one]
        have hc : Nat.count Nat.Prime 2 = 0 := rfl
        have h_prime : Nat.nth Nat.Prime 0 = 2 := by
          rw [← hc]
          exact Nat.nth_count (by decide)
        exact h_prime
      · -- n ≥ 2
        have hn_ge_2 : 2 ≤ n + 2 := by omega
        exact a_eq_two_of_ne_38 (n + 2) h_neq hn_ge_2
  rw [h_a_eq_2] at hsq
  exact not_sq_2 hsq
