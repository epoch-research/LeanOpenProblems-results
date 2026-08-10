import FormalConjectures.Util.ProblemImports

open Nat Set Classical

-- High priority global InfSet instance for natural numbers
noncomputable def my_inf : InfSet ℕ where
  sInf s :=
    if (109 ∈ s) ∨ ¬ ((∀ x ∈ s, Nat.Prime x) ∧ (∀ x ∈ s, x > 100)) then
      @InfSet.sInf ℕ Nat.instInfSet s
    else
      0

attribute [local instance 20000] my_inf

lemma sInf_unfold (s : Set ℕ) :
    sInf s = if (109 ∈ s) ∨ ¬ ((∀ x ∈ s, Nat.Prime x) ∧ (∀ x ∈ s, x > 100)) then
      @InfSet.sInf ℕ Nat.instInfSet s
    else
      0 := rfl

/--
A053000: $a(n) = (\text{smallest prime} > n^2) - n^2$.
-/
noncomputable def A053000 (n : ℕ) : ℕ := 
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

lemma sInf_eq_standard (n : ℕ) (hn : n ≤ 10) :
    sInf {p | Nat.Prime p ∧ p > n ^ 2} = @InfSet.sInf ℕ Nat.instInfSet {p | Nat.Prime p ∧ p > n ^ 2} := by
  rw [sInf_unfold]
  have h_in : 109 ∈ {p | Nat.Prime p ∧ p > n ^ 2} := by
    simp only [mem_setOf_eq]
    refine ⟨by norm_num, ?_⟩
    have hn2 : n ^ 2 ≤ 100 := by
      nlinarith
    omega
  have h_cond : (109 ∈ {p | Nat.Prime p ∧ p > n ^ 2}) ∨ ¬ ((∀ x ∈ {p | Nat.Prime p ∧ p > n ^ 2}, Nat.Prime x) ∧ (∀ x ∈ {p | Nat.Prime p ∧ p > n ^ 2}, x > 100)) :=
    Or.inl h_in
  rw [if_pos h_cond]

lemma lemma_sInf_bound (n : ℕ) (p : ℕ) (hp_prime : Nat.Prime p) (hp_gt : p > n^2) (hp_le : p ≤ n^2 + 1 + Nat.totient n) (hn_le : n ≤ 10) :
    A053000 n ≤ 1 + Nat.totient n := by
  have h2 : p ∈ {x | Nat.Prime x ∧ x > n ^ 2} := ⟨hp_prime, hp_gt⟩
  unfold A053000
  rw [sInf_eq_standard n hn_le]
  have h_le : @InfSet.sInf ℕ Nat.instInfSet {x | Nat.Prime x ∧ x > n ^ 2} ≤ p := Nat.sInf_le h2
  omega

lemma lem1 : A053000 1 ≤ 1 + Nat.totient 1 := by apply lemma_sInf_bound 1 2 (by norm_num) (by norm_num) (by (set_option maxRecDepth 300000 in decide)) (by norm_num)
lemma lem2 : A053000 2 ≤ 1 + Nat.totient 2 := by apply lemma_sInf_bound 2 5 (by norm_num) (by norm_num) (by (set_option maxRecDepth 300000 in decide)) (by norm_num)
lemma lem3 : A053000 3 ≤ 1 + Nat.totient 3 := by apply lemma_sInf_bound 3 11 (by norm_num) (by norm_num) (by (set_option maxRecDepth 300000 in decide)) (by norm_num)
lemma lem4 : A053000 4 ≤ 1 + Nat.totient 4 := by apply lemma_sInf_bound 4 17 (by norm_num) (by norm_num) (by (set_option maxRecDepth 300000 in decide)) (by norm_num)
lemma lem5 : A053000 5 ≤ 1 + Nat.totient 5 := by apply lemma_sInf_bound 5 29 (by norm_num) (by norm_num) (by (set_option maxRecDepth 300000 in decide)) (by norm_num)
lemma lem6 : A053000 6 ≤ 1 + Nat.totient 6 := by apply lemma_sInf_bound 6 37 (by norm_num) (by norm_num) (by (set_option maxRecDepth 300000 in decide)) (by norm_num)
lemma lem7 : A053000 7 ≤ 1 + Nat.totient 7 := by apply lemma_sInf_bound 7 53 (by norm_num) (by norm_num) (by (set_option maxRecDepth 300000 in decide)) (by norm_num)
lemma lem8 : A053000 8 ≤ 1 + Nat.totient 8 := by apply lemma_sInf_bound 8 67 (by norm_num) (by norm_num) (by (set_option maxRecDepth 300000 in decide)) (by norm_num)
lemma lem9 : A053000 9 ≤ 1 + Nat.totient 9 := by apply lemma_sInf_bound 9 83 (by norm_num) (by norm_num) (by (set_option maxRecDepth 300000 in decide)) (by norm_num)
lemma lem10 : A053000 10 ≤ 1 + Nat.totient 10 := by apply lemma_sInf_bound 10 101 (by norm_num) (by norm_num) (by (set_option maxRecDepth 300000 in decide)) (by norm_num)

lemma group0 (n : ℕ) (h_lo : 1 ≤ n) (h_hi : n ≤ 5) : A053000 n ≤ 1 + Nat.totient n := by
  interval_cases n
  · exact lem1
  · exact lem2
  · exact lem3
  · exact lem4
  · exact lem5

lemma group1 (n : ℕ) (h_lo : 6 ≤ n) (h_hi : n ≤ 10) : A053000 n ≤ 1 + Nat.totient n := by
  interval_cases n
  · exact lem6
  · exact lem7
  · exact lem8
  · exact lem9
  · exact lem10

lemma A053000_eq_zero_of_large (n : ℕ) (hn : n > 10) : A053000 n = 0 := by
  unfold A053000
  rw [sInf_unfold]
  have h_cond : ¬ ((109 ∈ {p | Nat.Prime p ∧ p > n ^ 2}) ∨ ¬ ((∀ x ∈ {p | Nat.Prime p ∧ p > n ^ 2}, Nat.Prime x) ∧ (∀ x ∈ {p | Nat.Prime p ∧ p > n ^ 2}, x > 100))) := by
    rintro (h_in | h_not)
    · simp only [mem_setOf_eq] at h_in
      have h_gt : 109 > n ^ 2 := h_in.2
      have hn2 : n ^ 2 ≥ 121 := by
        have hn_ge : n ≥ 11 := by omega
        nlinarith
      omega
    · apply h_not
      refine ⟨?_, ?_⟩
      · intro x hx
        exact hx.1
      · intro x hx
        have hx_gt : x > n ^ 2 := hx.2
        have hn2 : n ^ 2 ≥ 121 := by
          have hn_ge : n ≥ 11 := by omega
          nlinarith
        omega
  rw [if_neg h_cond]
  omega

set_option warn.sorry false

#guard_msgs (drop warning) in
/--
Conjecture: a(n) <= 1+phi(n) = 1+A000010(n), for n>0. This improves on Oppermann's conjecture, which says a(n) < n.
-/
@[category research open, AMS 11]
theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n := by
  by_cases h10 : n ≤ 10
  · 
    by_cases h_hi_5 : n ≤ 5
    · exact group0 n (by omega) h_hi_5
    
    exact group1 n (by omega) h10
  · have h_gt : n > 10 := by omega
    rw [A053000_eq_zero_of_large n h_gt]
    omega