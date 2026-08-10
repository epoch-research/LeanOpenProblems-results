import FormalConjectures.Util.ProblemImports

open List Finset Nat

/--
A306424: Numbers $k$ such that the base $b$ expansion of $k$ for each $b = 3..k-1$ never contains more than two distinct digits.
-/
def A306424_condition (k : ℕ) : Prop :=
  -- The bases $b$ range over $3 \le b \le k-1$, expressed as $3 \le b$ and $b < k$.
  ∀ b : ℕ, 3 ≤ b ∧ b < k → ((Nat.digits b k).toFinset.card) ≤ 2

/--
The sequence A306424: Numbers $k$ such that the base $b$ expansion of $k$ for each $b = 3..k-1$ never contains more than two distinct digits.
-/
noncomputable def a (n : ℕ) : ℕ := n.nth A306424_condition

/-- If a list `[d, c, a]` has three pairwise distinct entries, its `toFinset` has
more than two elements. -/
theorem card3 (d c a : ℕ) (h1 : d ≠ c) (h2 : d ≠ a) (h3 : c ≠ a) :
    2 < ([d, c, a] : List ℕ).toFinset.card := by
  have e : ([d, c, a] : List ℕ).toFinset = {d, c, a} := by simp
  rw [e]
  have : ({d, c, a} : Finset ℕ).card = 3 := by
    rw [Finset.card_eq_three]; exact ⟨d, c, a, h1, h2, h3, rfl⟩
  omega

/-- The base-`b` expansion of a three-digit number `d + b*c + b*(b*a)`. -/
theorem digits_three (b d c a : ℕ) (hb : 1 < b) (hd : d < b) (hc : c < b)
    (ha0 : 0 < a) (ha : a < b) :
    Nat.digits b (d + b * c + b * (b * a)) = [d, c, a] := by
  have hb0 : 0 < b := by omega
  have hn : 0 < d + b * c + b * (b * a) := by positivity
  rw [Nat.digits_def' hb hn]
  have hmod : (d + b * c + b * (b * a)) % b = d := by
    have h : d + b * c + b * (b * a) = d + b * (c + b * a) := by ring
    rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
  have hdiv : (d + b * c + b * (b * a)) / b = c + b * a := by
    have h : d + b * c + b * (b * a) = d + b * (c + b * a) := by ring
    rw [h, Nat.add_mul_div_left _ _ hb0, Nat.div_eq_of_lt hd]; omega
  rw [hmod, hdiv]
  have hn2 : 0 < c + b * a := by positivity
  rw [Nat.digits_def' hb hn2]
  have hmod2 : (c + b * a) % b = c := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  have hdiv2 : (c + b * a) / b = a := by
    rw [Nat.add_mul_div_left _ _ hb0, Nat.div_eq_of_lt hc]; omega
  rw [hmod2, hdiv2]
  rw [Nat.digits_def' hb ha0, Nat.mod_eq_of_lt ha, Nat.div_eq_of_lt ha, Nat.digits_zero]

/-- A three-digit number `d + b*c + b*b` (leading digit `1`) with `d`, `c` distinct
from each other and from `1` has more than two distinct base-`b` digits. -/
theorem card_three1 (b k d c : ℕ) (hb : 1 < b) (hd : d < b) (hc : c < b)
    (hk : k = d + b * c + b * b) (h1 : d ≠ c) (h2 : d ≠ 1) (h3 : c ≠ 1) :
    2 < (Nat.digits b k).toFinset.card := by
  have hkk : k = d + b * c + b * (b * 1) := by rw [hk]; ring
  rw [hkk, digits_three b d c 1 hb hd hc one_pos hb]
  exact card3 d c 1 h1 h2 h3

/-- Exhibiting one base with more than two distinct digits refutes the condition. -/
theorem not_cond_of_base (k b : ℕ) (h3 : 3 ≤ b) (hbk : b < k)
    (hcard : 2 < (Nat.digits b k).toFinset.card) : ¬ A306424_condition k := by
  intro h
  have := h b ⟨h3, hbk⟩
  omega

/-- The main step: every `k ≥ 289` fails the condition.  Writing `m = ⌊√k⌋` and
`s = k - m²` (so `0 ≤ s ≤ 2m`), we exhibit for each range of `s` an explicit base
(one of `m`, `m-1`, `m-2`, `m-3`) in which `k` is a three-digit number with three
distinct digits. -/
theorem not_cond_big (k : ℕ) (hk289 : 289 ≤ k) : ¬ A306424_condition k := by
  set m := Nat.sqrt k with hmdef
  have hm2 : m * m ≤ k := by have := Nat.sqrt_le' k; simpa [pow_two] using this
  have hk1 : k < (m + 1) * (m + 1) := by
    have := Nat.lt_succ_sqrt' k; simpa [pow_two, Nat.succ_eq_add_one] using this
  have hm17 : 17 ≤ m := by rw [hmdef]; exact Nat.le_sqrt.mpr (by omega)
  clear_value m
  clear hmdef
  obtain ⟨s, hks⟩ : ∃ s, k = m * m + s := ⟨k - m * m, by omega⟩
  have hsq : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
  have hs2m : s ≤ 2 * m := by omega
  have hbklt : m < k := by nlinarith [hm2, hm17]
  have hcov : s = 0 ∨ s = 1 ∨ (2 ≤ s ∧ s + 1 ≤ m) ∨ s = m ∨ s = m + 1 ∨
      (m + 2 ≤ s ∧ s + 4 ≤ 2 * m) ∨ s + 3 = 2 * m ∨ s + 2 = 2 * m ∨ s + 1 = 2 * m ∨
      s = 2 * m := by omega
  rcases hcov with h | h | h | h | h | h | h | h | h | h
  · -- s = 0 : base m-3, digits 9,6,1
    obtain ⟨b, rfl⟩ : ∃ b, m = b + 3 := ⟨m - 3, by omega⟩
    have e : k = b * b + 6 * b + 9 + s := by rw [hks]; ring
    exact not_cond_of_base k b (by omega) (by omega)
      (card_three1 b k 9 6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega))
  · -- s = 1 : base m-2, digits 5,4,1
    obtain ⟨b, rfl⟩ : ∃ b, m = b + 2 := ⟨m - 2, by omega⟩
    have e : k = b * b + 4 * b + 4 + s := by rw [hks]; ring
    exact not_cond_of_base k b (by omega) (by omega)
      (card_three1 b k 5 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega))
  · -- 2 ≤ s ≤ m-1 : base m, digits s,0,1
    exact not_cond_of_base k m (by omega) hbklt
      (card_three1 m k s 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega))
  · -- s = m : base m-1, digits 2,3,1
    obtain ⟨b, rfl⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
    have e : k = b * b + 2 * b + 1 + s := by rw [hks]; ring
    exact not_cond_of_base k b (by omega) (by omega)
      (card_three1 b k 2 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega))
  · -- s = m+1 : base m-2, digits 7,5,1
    obtain ⟨b, rfl⟩ : ∃ b, m = b + 2 := ⟨m - 2, by omega⟩
    have e : k = b * b + 4 * b + 4 + s := by rw [hks]; ring
    exact not_cond_of_base k b (by omega) (by omega)
      (card_three1 b k 7 5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega))
  · -- m+2 ≤ s ≤ 2m-4 : base m-1, digits t+4,3,1
    obtain ⟨b, rfl⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, s = b + 3 + t := ⟨s - (b + 3), by omega⟩
    have e : k = b * b + 2 * b + 1 + (b + 3 + t) := by rw [hks]; ring
    exact not_cond_of_base k b (by omega) (by omega)
      (card_three1 b k (t + 4) 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega))
  · -- s = 2m-3 : base m-1, digits 0,4,1
    obtain ⟨b, rfl⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
    have e : k = b * b + 2 * b + 1 + s := by rw [hks]; ring
    exact not_cond_of_base k b (by omega) (by omega)
      (card_three1 b k 0 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega))
  · -- s = 2m-2 : base m-3, digits 13,8,1
    obtain ⟨b, rfl⟩ : ∃ b, m = b + 3 := ⟨m - 3, by omega⟩
    have e : k = b * b + 6 * b + 9 + s := by rw [hks]; ring
    exact not_cond_of_base k b (by omega) (by omega)
      (card_three1 b k 13 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega))
  · -- s = 2m-1 : base m-1, digits 2,4,1
    obtain ⟨b, rfl⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
    have e : k = b * b + 2 * b + 1 + s := by rw [hks]; ring
    exact not_cond_of_base k b (by omega) (by omega)
      (card_three1 b k 2 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega))
  · -- s = 2m : base m, digits 0,2,1
    exact not_cond_of_base k m (by omega) hbklt
      (card_three1 m k 0 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega))

/-- The small-base search used for the finite range. -/
syntax "finite_search " ident : tactic
macro_rules
  | `(tactic| finite_search $k) =>
    `(tactic|
      interval_cases $k <;>
      first
      | (refine not_cond_of_base _ 3 (by norm_num) (by norm_num) ?_; simp; done)
      | (refine not_cond_of_base _ 4 (by norm_num) (by norm_num) ?_; simp; done)
      | (refine not_cond_of_base _ 5 (by norm_num) (by norm_num) ?_; simp; done)
      | (refine not_cond_of_base _ 6 (by norm_num) (by norm_num) ?_; simp; done)
      | (refine not_cond_of_base _ 7 (by norm_num) (by norm_num) ?_; simp; done)
      | (refine not_cond_of_base _ 8 (by norm_num) (by norm_num) ?_; simp; done)
      | (refine not_cond_of_base _ 9 (by norm_num) (by norm_num) ?_; simp; done))

set_option maxHeartbeats 2000000 in
theorem not_cond_fin1 (k : ℕ) (h1 : 44 ≤ k) (h2 : k ≤ 90) : ¬ A306424_condition k := by
  finite_search k

set_option maxHeartbeats 2000000 in
theorem not_cond_fin2 (k : ℕ) (h1 : 91 ≤ k) (h2 : k ≤ 140) : ¬ A306424_condition k := by
  finite_search k

set_option maxHeartbeats 2000000 in
theorem not_cond_fin3 (k : ℕ) (h1 : 141 ≤ k) (h2 : k ≤ 190) : ¬ A306424_condition k := by
  finite_search k

set_option maxHeartbeats 2000000 in
theorem not_cond_fin4 (k : ℕ) (h1 : 191 ≤ k) (h2 : k ≤ 240) : ¬ A306424_condition k := by
  finite_search k

set_option maxHeartbeats 2000000 in
theorem not_cond_fin5 (k : ℕ) (h1 : 241 ≤ k) (h2 : k ≤ 288) : ¬ A306424_condition k := by
  finite_search k

/--
A306424 Conjecture: The sequence is finite, with 43 being the last term.
-/
theorem oeis_306424_conjecture_0 : A306424_condition 43 ∧ ∀ k : ℕ, 43 < k → ¬ A306424_condition k := by
  refine ⟨?_, ?_⟩
  · -- 43 satisfies the condition: check bases 3..42 directly.
    intro b ⟨h3, h43⟩
    interval_cases b <;> simp
  · -- No k > 43 satisfies the condition.
    intro k hk
    rcases (by omega : k ≤ 90 ∨ (91 ≤ k ∧ k ≤ 140) ∨ (141 ≤ k ∧ k ≤ 190) ∨
        (191 ≤ k ∧ k ≤ 240) ∨ (241 ≤ k ∧ k ≤ 288) ∨ 289 ≤ k) with
        h | h | h | h | h | h
    · exact not_cond_fin1 k (by omega) h
    · exact not_cond_fin2 k h.1 h.2
    · exact not_cond_fin3 k h.1 h.2
    · exact not_cond_fin4 k h.1 h.2
    · exact not_cond_fin5 k h.1 h.2
    · exact not_cond_big k h
