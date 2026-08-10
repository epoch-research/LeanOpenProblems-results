import FormalConjectures.Util.ProblemImports

def a : ℕ → ℕ
| 0     => 1
| n + 1 => (a n) ^ 2 + 2

-- a is strictly monotone for n ≥ 1; basic growth facts
lemma a_ge_one : ∀ n, 1 ≤ a n := by
  intro n
  induction n with
  | zero => simp [a]
  | succ k ih => simp only [a]; nlinarith [ih]

lemma a_succ_gt (n : ℕ) : a n < a (n+1) := by
  simp only [a]
  have h := a_ge_one n
  nlinarith [h]

lemma a_mono : Monotone a := by
  apply monotone_nat_of_le_succ
  intro n; exact (a_succ_gt n).le

-- a 5 = 228947163 > 3
lemma a5_val : a 5 = 228947163 := by norm_num [a]

lemma a_ge_5_gt_3 {n : ℕ} (hn : 5 ≤ n) : 3 < a n := by
  have : a 5 ≤ a n := a_mono hn
  rw [a5_val] at this
  omega

-- step lemmas for mod 3
lemma step_2_to_0 (x : ℕ) (hx : x % 3 = 2) : (x^2 + 2) % 3 = 0 := by
  have h := Nat.pow_mod x 2 3
  rw [hx] at h
  omega

lemma step_0_to_2 (x : ℕ) (hx : x % 3 = 0) : (x^2 + 2) % 3 = 2 := by
  have h := Nat.pow_mod x 2 3
  rw [hx] at h
  omega

-- a (n+1) = a n ^ 2 + 2
lemma a_succ (n : ℕ) : a (n+1) = (a n)^2 + 2 := rfl

-- mod 3 behaviour
lemma a_mod3 : ∀ k, a (2*k+1) % 3 = 0 ∧ a (2*k+2) % 3 = 2 := by
  intro k
  induction k with
  | zero => constructor <;> norm_num [a]
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    have h3 : a (2*m+3) % 3 = 0 := by
      have e2 : 2*m+3 = (2*m+2)+1 := by ring
      rw [e2, a_succ]
      exact step_2_to_0 _ h2
    refine ⟨?_, ?_⟩
    · have e : 2*(m+1)+1 = (2*m+2)+1 := by ring
      rw [e, a_succ]; exact step_2_to_0 _ h2
    · have e : 2*(m+1)+2 = (2*m+3)+1 := by ring
      rw [e, a_succ]; exact step_0_to_2 _ h3

-- For odd n ≥ 5, a n is divisible by 3 and exceeds 3, hence composite.
lemma odd_not_prime {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) : ¬ Nat.Prime (a n) := by
  intro hp
  obtain ⟨k, hk⟩ := ho
  -- n = 2k+1
  have hk2 : 2 ≤ k := by omega
  have h3 : a n % 3 = 0 := by
    have := (a_mod3 k).1
    rwa [← hk] at this
  have hdvd : 3 ∣ a n := Nat.dvd_of_mod_eq_zero h3
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp 3 hdvd) with h | h
  · norm_num at h
  · have : 3 < a n := a_ge_5_gt_3 hn
    omega

-- The even-indexed case is the genuinely open sub-problem.
theorem oeis_102847_conjecture_0.disproof :
    ¬ ∃ n : ℕ, 4 < n ∧ Nat.Prime (a n) := by
  rintro ⟨n, hn, hp⟩
  rcases Nat.even_or_odd n with he | ho
  · sorry
  · exact odd_not_prime (by omega) ho hp
