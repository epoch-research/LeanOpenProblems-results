import FormalConjecturesUtil

/-!
Exact boundary behavior for an integer-tail congruence. This is an auxiliary
arithmetic result, not a proof or disproof of the conjecture in Spec.lean.
-/

namespace CongruentTailResets

/-- Allowing the upper endpoint in the positive small-tail bound permits a
reset: a tail equal to one jumps to the new upper endpoint. -/
lemma step (t : ℕ → ℤ) (n : ℕ) (hn : 2 ≤ n)
    (h₀ : 1 ≤ t n ∧ t n ≤ (n : ℤ) - 1)
    (h₁ : 1 ≤ t (n + 1) ∧ t (n + 1) ≤ (n : ℤ))
    (hd : (n : ℤ) ∣ t (n + 1) - t n + 1) :
    t (n + 1) = if t n = 1 then (n : ℤ) else t n - 1 := by
  obtain ⟨k, hk⟩ := hd
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  have hk₀ : 0 ≤ k := by
    by_contra h
    have hk' : k ≤ -1 := by omega
    have hm := mul_le_mul_of_nonneg_left hk' (by omega : (0 : ℤ) ≤ n)
    nlinarith
  have hk₁ : k ≤ 1 := by
    by_contra h
    have hk' : 2 ≤ k := by omega
    have hm := mul_le_mul_of_nonneg_left hk' (by omega : (0 : ℤ) ≤ n)
    nlinarith
  by_cases ht : t n = 1
  · rw [if_pos ht]
    have hk' : k = 1 := by
      have he : k = 0 ∨ k = 1 := by omega
      rcases he with he | he
      · simp only [he, mul_zero] at hk
        omega
      · exact he
    rw [hk', mul_one] at hk
    omega
  · rw [if_neg ht]
    have hk' : k = 0 := by
      have he : k = 0 ∨ k = 1 := by omega
      rcases he with he | he
      · exact he
      · rw [he, mul_one] at hk
        omega
    rw [hk', mul_zero] at hk
    omega

/-- After a reset at index `a`, the tails decrease by one until index `2*a`.
The intervening endpoints are included explicitly. -/
lemma reset_block (t : ℕ → ℤ) (N a : ℕ) (ha : N ≤ a) (ha₂ : 2 ≤ a)
    (hb : ∀ n ≥ N, 1 ≤ t n ∧ t n ≤ (n : ℤ) - 1)
    (hd : ∀ n ≥ N, (n : ℤ) ∣ t (n + 1) - t n + 1)
    (ht : t a = 1) :
    ∀ i : ℕ, i < a → t (a + 1 + i) = (a : ℤ) - i := by
  intro i
  induction i with
  | zero =>
      intro _
      have hs := step t a ha₂ (hb a ha) (by simpa using hb (a + 1) (by omega))
        (hd a ha)
      simpa [ht] using hs
  | succ i ih =>
      intro hi
      have hi' : i < a := by omega
      have ht' := ih hi'
      have hs := step t (a + 1 + i) (by omega)
        (hb _ (by omega)) (by simpa using hb (a + 1 + i + 1) (by omega))
        (hd _ (by omega))
      have hn : t (a + 1 + i) ≠ 1 := by
        rw [ht']
        omega
      rw [if_neg hn, ht'] at hs
      convert hs using 1
      push_cast
      ring

lemma next_reset (t : ℕ → ℤ) (N a : ℕ) (ha : N ≤ a) (ha₂ : 2 ≤ a)
    (hb : ∀ n ≥ N, 1 ≤ t n ∧ t n ≤ (n : ℤ) - 1)
    (hd : ∀ n ≥ N, (n : ℤ) ∣ t (n + 1) - t n + 1)
    (ht : t a = 1) : t (2 * a) = 1 := by
  have h := reset_block t N a ha ha₂ hb hd ht (a - 1) (by omega)
  have he : a + 1 + (a - 1) = 2 * a := by omega
  rw [he] at h
  omega

lemma no_intermediate_reset (t : ℕ → ℤ) (N a j : ℕ)
    (ha : N ≤ a) (ha₂ : 2 ≤ a) (hj₀ : 0 < j) (hj₁ : j < a)
    (hb : ∀ n ≥ N, 1 ≤ t n ∧ t n ≤ (n : ℤ) - 1)
    (hd : ∀ n ≥ N, (n : ℤ) ∣ t (n + 1) - t n + 1)
    (ht : t a = 1) : t (a + j) ≠ 1 := by
  have h := reset_block t N a ha ha₂ hb hd ht (j - 1) (by omega)
  have he : a + 1 + (j - 1) = a + j := by omega
  rw [he] at h
  omega

/-- Once a reset occurs, all its successive doubling indices are resets. -/
theorem dyadic_resets (t : ℕ → ℤ) (N a : ℕ) (ha : N ≤ a) (ha₂ : 2 ≤ a)
    (hb : ∀ n ≥ N, 1 ≤ t n ∧ t n ≤ (n : ℤ) - 1)
    (hd : ∀ n ≥ N, (n : ℤ) ∣ t (n + 1) - t n + 1)
    (ht : t a = 1) (k : ℕ) : t (2 ^ k * a) = 1 := by
  induction k with
  | zero => simpa using ht
  | succ k ih =>
      have hp : 1 ≤ (2 : ℕ) ^ k := one_le_pow₀ (by norm_num)
      have hl : a ≤ 2 ^ k * a := by nlinarith
      have h := next_reset t N (2 ^ k * a) (ha.trans hl) (ha₂.trans hl) hb hd ih
      convert h using 1
      congr 1
      simp only [pow_succ]
      ring

/-- A first reset is forced within fewer than `M` steps of any starting index
`M` where the bounds and congruence hold. -/
lemma exists_reset (t : ℕ → ℤ) (N M : ℕ) (hM : N ≤ M) (hM₂ : 2 ≤ M)
    (hb : ∀ n ≥ N, 1 ≤ t n ∧ t n ≤ (n : ℤ) - 1)
    (hd : ∀ n ≥ N, (n : ℤ) ∣ t (n + 1) - t n + 1) :
    ∃ a, M ≤ a ∧ a < 2 * M ∧ t a = 1 := by
  have hbM := hb M hM
  have he : ((t M).toNat : ℤ) = t M := Int.toNat_of_nonneg (by omega)
  have hdesc : ∀ i : ℕ, i < (t M).toNat → t (M + i) = t M - i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
        intro hi
        have hi' : i < (t M).toNat := by omega
        have ht := ih hi'
        have hs := step t (M + i) (by omega) (hb _ (by omega))
          (by simpa using hb (M + i + 1) (by omega)) (hd _ (by omega))
        have hn : t (M + i) ≠ 1 := by rw [ht]; omega
        rw [if_neg hn, ht] at hs
        convert hs using 1
        push_cast
        ring
  refine ⟨M + ((t M).toNat - 1), by omega, by omega, ?_⟩
  have hh := hdesc ((t M).toNat - 1) (by omega)
  omega

/-- Complete block structure of all sufficiently late resets: consecutive
reset indices double, and there is no reset inside any such block. -/
theorem eventual_reset_blocks (t : ℕ → ℤ) (N : ℕ)
    (hb : ∀ n ≥ N, 1 ≤ t n ∧ t n ≤ (n : ℤ) - 1)
    (hd : ∀ n ≥ N, (n : ℤ) ∣ t (n + 1) - t n + 1) :
    ∃ a ≥ max N 2, ∀ k : ℕ,
      t (2 ^ k * a) = 1 ∧
        ∀ j : ℕ, 0 < j → j < 2 ^ k * a → t (2 ^ k * a + j) ≠ 1 := by
  obtain ⟨a, ha, _, ht⟩ := exists_reset t N (max N 2)
    (le_max_left _ _) (le_max_right _ _) hb hd
  have haN : N ≤ a := (le_max_left _ _).trans ha
  have ha₂ : 2 ≤ a := (le_max_right _ _).trans ha
  refine ⟨a, ha, fun k => ?_⟩
  have hk := dyadic_resets t N a haN ha₂ hb hd ht k
  have hp : 1 ≤ (2 : ℕ) ^ k := one_le_pow₀ (by norm_num)
  have hl : a ≤ 2 ^ k * a := by nlinarith
  exact ⟨hk, fun j hj₀ hj₁ => no_intermediate_reset t N (2 ^ k * a) j
    (haN.trans hl) (ha₂.trans hl) hj₀ hj₁ hb hd hk⟩

end CongruentTailResets

#print axioms CongruentTailResets.dyadic_resets
#print axioms CongruentTailResets.no_intermediate_reset

#print axioms CongruentTailResets.eventual_reset_blocks
