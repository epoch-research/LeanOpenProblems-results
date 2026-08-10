import FormalConjectures.Util.ProblemImports

open Finset Nat Set Classical

set_option maxRecDepth 200000
set_option maxHeartbeats 0

/--
The number of partitions of $m$ into $n$ distinct primes.
This is defined by counting subsets of primes $S$ such that $|S|=n$ and $\sum_{p \in S} p = m$.
The set of candidate primes must include primes up to $m$.
-/
def count_distinct_prime_partitions (m n : ℕ) : ℕ :=
  let all_primes_le_m : Finset ℕ := Nat.primesBelow (m + 1)
  (all_primes_le_m.powerset.filter (fun S => S.card = n ∧ S.sum id = m)).card

/--
A344989: Smallest number whose number of partitions into $n$ distinct primes is $n$, or zero if there are no such partitions.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- S is the set of natural numbers m satisfying the condition.
    let S : Set ℕ := {m : ℕ | count_distinct_prime_partitions m n = n}
    -- sInf S computes the smallest element of S. If S is empty, sInf S = 0 for Nat.
    sInf S

def count_fast (m n : ℕ) : ℕ :=
  let all_primes_le_m : Finset ℕ := Nat.primesBelow (m + 1)
  (all_primes_le_m.powersetCard n |>.filter (fun S => S.sum id = m)).card

theorem count_eq_count_fast (m n : ℕ) : count_distinct_prime_partitions m n = count_fast m n := by
  unfold count_distinct_prime_partitions count_fast
  refine congrArg card ?_
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
  tauto

def count_bounded (m n max_p : ℕ) : ℕ :=
  let primes : Finset ℕ := Nat.primesBelow max_p
  (primes.powersetCard n |>.filter (fun S => S.sum id = m)).card

theorem count_fast_eq_count_bounded (m n max_p : ℕ) (h : m + 1 ≤ max_p) :
    count_fast m n = count_bounded m n max_p := by
  unfold count_fast count_bounded
  refine congrArg card ?_
  ext S
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  have h_subset : (m + 1).primesBelow ⊆ max_p.primesBelow := by
    intro x hx
    rw [Nat.mem_primesBelow] at hx ⊢
    exact ⟨by omega, hx.2⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, h1.2⟩, h2⟩
    exact Trans.trans h1.1 h_subset
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, h1.2⟩, h2⟩
    intro x hx
    rw [Nat.mem_primesBelow]
    have h_prime : x.Prime := by
      have hx' := h1.1 hx
      rw [Nat.mem_primesBelow] at hx'
      exact hx'.2
    refine ⟨?_, h_prime⟩
    have h_le : x ≤ S.sum id := single_le_sum (fun y _ => Nat.zero_le y) hx
    rw [h2] at h_le
    omega


lemma count_lt_two_n (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : m < 2 * n) :
    count_distinct_prime_partitions m n = 0 := by
  unfold count_distinct_prime_partitions
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro S hS
  rintro ⟨h_card, h_sum⟩
  have h_sum_ge : S.card * 2 ≤ S.sum id := by
    have h1 : S.sum (fun _ => 2) ≤ S.sum id := by
      apply Finset.sum_le_sum
      intro x hx
      rw [Finset.mem_powerset] at hS
      have hx_mem := hS hx
      rw [Nat.mem_primesBelow] at hx_mem
      have h_prime := hx_mem.2
      exact Nat.Prime.two_le h_prime
    have h2 : S.sum (fun _ => 2) = S.card * 2 := by
      simp
    omega
  rw [h_card] at h_sum_ge
  rw [h_sum] at h_sum_ge
  omega

lemma k_lt_Cn (n k Cn : ℕ) (hCn_pos : 0 < Cn) (hCn_eq : count_distinct_prime_partitions Cn n = n)
    (h_cond2 : ∀ m', m' ≤ k → m' = 0 ∨ count_distinct_prime_partitions m' n ≠ n) : k < Cn := by
  by_contra h_le
  push_neg at h_le
  have h_or := h_cond2 Cn h_le
  rcases h_or with h1 | h2
  · omega
  · exact h2 hCn_eq

def check_no_k (n Cn : ℕ) : Bool :=
  List.all (List.range Cn) (fun k =>
    List.any (List.range (2 * n)) (fun d =>
      count_fast (k + 1 + d) n ≤ n
    )
  )

theorem check_no_k_spec (n Cn k : ℕ) (h_check : check_no_k n Cn = true) (hk : k < Cn) :
    ∃ m, k < m ∧ m ≤ k + 2 * n ∧ count_distinct_prime_partitions m n ≤ n := by
  have h_mem : k ∈ List.range Cn := List.mem_range.mpr hk
  unfold check_no_k at h_check
  rw [List.all_eq_true] at h_check
  have h_any := h_check k h_mem
  rw [List.any_eq_true] at h_any
  rcases h_any with ⟨d, hd_mem, hd_cond⟩
  rw [List.mem_range] at hd_mem
  use k + 1 + d
  refine ⟨by omega, by omega, ?_⟩
  rw [count_eq_count_fast]
  exact of_decide_eq_true hd_cond

theorem check_no_k_1_true : check_no_k 1 2 = true := by decide
theorem check_no_k_2_true : check_no_k 2 16 = true := by decide
theorem check_no_k_3_true : check_no_k 3 26 = true := by decide
theorem check_no_k_4_true : check_no_k 4 33 = true := by decide

def violating_m_5 (k : ℕ) : ℕ :=
  if k = 45 then 47
  else if k = 47 then 49
  else if k = 49 then 51
  else if k = 51 then 53
  else if k = 53 then 55
  else k + 1

def check_no_k_5_bounded (max_p : ℕ) : Bool :=
  let primes : Finset ℕ := Nat.primesBelow max_p
  let subsets := primes.powersetCard 5
  List.all (List.range 55) (fun k =>
    let m := violating_m_5 k
    (subsets.filter (fun S => S.sum id = m)).card ≤ 5
  )

theorem check_no_k_5_bounded_true : check_no_k_5_bounded 56 = true := by decide

theorem check_no_k_5_bounded_spec (k : ℕ) (hk : k < 55) :
    ∃ m, k < m ∧ m ≤ k + 10 ∧ count_distinct_prime_partitions m 5 ≤ 5 := by
  have h_check := check_no_k_5_bounded_true
  unfold check_no_k_5_bounded at h_check
  rw [List.all_eq_true] at h_check
  have h_mem : k ∈ List.range 55 := List.mem_range.mpr hk
  have h_any := h_check k h_mem
  use violating_m_5 k
  have h_bounds : k < violating_m_5 k ∧ violating_m_5 k ≤ k + 10 := by
    unfold violating_m_5
    split_ifs <;> omega
  refine ⟨h_bounds.1, h_bounds.2, ?_⟩
  rw [count_eq_count_fast, count_fast_eq_count_bounded (violating_m_5 k) 5 56 (by
    unfold violating_m_5
    split_ifs <;> omega)]
  exact of_decide_eq_true h_any

def check_no_k_6_bounded (max_p : ℕ) : Bool :=
  let primes : Finset ℕ := Nat.primesBelow max_p
  let subsets := primes.powersetCard 6
  List.all (List.range' 40 19) (fun k =>
    (subsets.filter (fun S => S.sum id = k + 1)).card ≤ 6
  )

theorem check_no_k_6_bounded_true : check_no_k_6_bounded 60 = true := by decide

def check_no_k_6_bounded_small (max_p : ℕ) : Bool :=
  let primes : Finset ℕ := Nat.primesBelow max_p
  let subsets := primes.powersetCard 6
  List.all (List.range 40) (fun k =>
    (subsets.filter (fun S => S.sum id = k + 1)).card ≤ 6
  )

theorem check_no_k_6_bounded_small_true : check_no_k_6_bounded_small 41 = true := by decide

theorem check_no_k_6_bounded_spec (k : ℕ) (hk : k < 59) :
    ∃ m, k < m ∧ m ≤ k + 12 ∧ count_distinct_prime_partitions m 6 ≤ 6 := by
  rcases lt_or_ge k 40 with hk_small | hk_large
  · have h_check := check_no_k_6_bounded_small_true
    unfold check_no_k_6_bounded_small at h_check
    rw [List.all_eq_true] at h_check
    have h_mem : k ∈ List.range 40 := List.mem_range.mpr hk_small
    have h_any := h_check k h_mem
    use k + 1
    refine ⟨by omega, by omega, ?_⟩
    rw [count_eq_count_fast, count_fast_eq_count_bounded (k + 1) 6 41 (by omega)]
    exact of_decide_eq_true h_any
  · have h_check := check_no_k_6_bounded_true
    unfold check_no_k_6_bounded at h_check
    rw [List.all_eq_true] at h_check
    have h_mem : k ∈ List.range' 40 19 1 := by
      rw [List.mem_range']
      use k - 40
      refine ⟨by omega, by omega⟩
    have h_any := h_check k h_mem
    use k + 1
    refine ⟨by omega, by omega, ?_⟩
    rw [count_eq_count_fast, count_fast_eq_count_bounded (k + 1) 6 60 (by omega)]
    exact of_decide_eq_true h_any

/--
Conjecture based on OEIS A344989 commentary by David A. Corneth:
$a(n) = 0$ if $2n$ consecutive integers can be written in strictly more than $n$ ways
as a sum of $n$ distinct primes and up to that point no positive integer has exactly $n$ such ways.
-/
theorem A344989_conjecture_heuristic_zero (n : ℕ) (hn : 0 < n):
  (∃ k : ℕ,
      -- Condition 1: 2n consecutive integers m > k have strictly more than n partitions.
      (∀ m : ℕ, k < m ∧ m ≤ k + 2 * n → count_distinct_prime_partitions m n > n)
      ∧
      -- Condition 2: No integer m' up to k (with m' > 0) has exactly n partitions.
      (∀ m' : ℕ, m' ≤ k → m' = 0 ∨ count_distinct_prime_partitions m' n ≠ n)
  ) → a n = 0 := by
  intro h
  rcases h with ⟨k, hk1, hk2⟩
  unfold a
  split_ifs with hn0
  · rfl
  · by_contra ha
    have hS : {m : ℕ | count_distinct_prime_partitions m n = n}.Nonempty := by
      by_contra h_empty
      have h_empty' : {m : ℕ | count_distinct_prime_partitions m n = n} = ∅ := Set.not_nonempty_iff_eq_empty.mp h_empty
      rw [h_empty'] at ha
      exact ha Nat.sInf_empty
    have h_mem := Nat.sInf_mem hS
    have hM_pos : 0 < sInf {m : ℕ | count_distinct_prime_partitions m n = n} := Nat.pos_of_ne_zero ha
    have hM_gt_k : k < sInf {m : ℕ | count_distinct_prime_partitions m n = n} := by
      by_contra h_le
      push_neg at h_le
      have h_or := hk2 (sInf {m : ℕ | count_distinct_prime_partitions m n = n}) h_le
      rcases h_or with h1 | h2
      · exact ha h1
      · exact h2 h_mem
    have h_gt : k + 2 * n < sInf {m : ℕ | count_distinct_prime_partitions m n = n} := by
      by_contra h_le
      push_neg at h_le
      have h_cond : k < sInf {m : ℕ | count_distinct_prime_partitions m n = n} ∧ sInf {m : ℕ | count_distinct_prime_partitions m n = n} ≤ k + 2 * n := ⟨hM_gt_k, h_le⟩
      have h_gt_n := hk1 (sInf {m : ℕ | count_distinct_prime_partitions m n = n}) h_cond
      rw [h_mem] at h_gt_n
      exact lt_irrefl n h_gt_n
    
    rcases n with _ | n'
    · omega
    · rcases n' with _ | n''
      · -- n = 1
        have hCn : count_distinct_prime_partitions 2 1 = 1 := by
          rw [count_eq_count_fast, count_fast_eq_count_bounded 2 1 3 (by omega)]
          decide
        have hk_lt := k_lt_Cn 1 k 2 (by omega) hCn hk2
        have h_m := check_no_k_spec 1 2 k check_no_k_1_true hk_lt
        rcases h_m with ⟨m, hm1, hm2, hm3⟩
        have h_gt_m : k < m ∧ m ≤ k + 2 * 1 := ⟨hm1, hm2⟩
        have h_gt_m' := hk1 m h_gt_m
        change count_distinct_prime_partitions m 1 > 1 at h_gt_m'
        omega
      · rcases n'' with _ | n'''
        · -- n = 2
          have hCn : count_distinct_prime_partitions 16 2 = 2 := by
            rw [count_eq_count_fast, count_fast_eq_count_bounded 16 2 17 (by omega)]
            decide
          have hk_lt := k_lt_Cn 2 k 16 (by omega) hCn hk2
          have h_m := check_no_k_spec 2 16 k check_no_k_2_true hk_lt
          rcases h_m with ⟨m, hm1, hm2, hm3⟩
          have h_gt_m : k < m ∧ m ≤ k + 2 * 2 := ⟨hm1, hm2⟩
          have h_gt_m' := hk1 m h_gt_m
          change count_distinct_prime_partitions m 2 > 2 at h_gt_m'
          omega
        · rcases n''' with _ | n''''
          · -- n = 3
            have hCn : count_distinct_prime_partitions 26 3 = 3 := by
              rw [count_eq_count_fast, count_fast_eq_count_bounded 26 3 27 (by omega)]
              decide
            have hk_lt := k_lt_Cn 3 k 26 (by omega) hCn hk2
            have h_m := check_no_k_spec 3 26 k check_no_k_3_true hk_lt
            rcases h_m with ⟨m, hm1, hm2, hm3⟩
            have h_gt_m : k < m ∧ m ≤ k + 2 * 3 := ⟨hm1, hm2⟩
            have h_gt_m' := hk1 m h_gt_m
            change count_distinct_prime_partitions m 3 > 3 at h_gt_m'
            omega
          · rcases n'''' with _ | n'''''
            · -- n = 4
              have hCn : count_distinct_prime_partitions 33 4 = 4 := by
                rw [count_eq_count_fast, count_fast_eq_count_bounded 33 4 34 (by omega)]
                decide
              have hk_lt := k_lt_Cn 4 k 33 (by omega) hCn hk2
              have h_m := check_no_k_spec 4 33 k check_no_k_4_true hk_lt
              rcases h_m with ⟨m, hm1, hm2, hm3⟩
              have h_gt_m : k < m ∧ m ≤ k + 2 * 4 := ⟨hm1, hm2⟩
              have h_gt_m' := hk1 m h_gt_m
              change count_distinct_prime_partitions m 4 > 4 at h_gt_m'
              omega
            · rcases n''''' with _ | n''''''
              · -- n = 5
                have hCn : count_distinct_prime_partitions 55 5 = 5 := by
                  rw [count_eq_count_fast, count_fast_eq_count_bounded 55 5 56 (by omega)]
                  decide
                have hk_lt := k_lt_Cn 5 k 55 (by omega) hCn hk2
                have h_m := check_no_k_5_bounded_spec k hk_lt
                rcases h_m with ⟨m, hm1, hm2, hm3⟩
                have h_gt_m : k < m ∧ m ≤ k + 10 := ⟨hm1, hm2⟩
                have h_gt_m' := hk1 m h_gt_m
                change count_distinct_prime_partitions m 5 > 5 at h_gt_m'
                omega
              · rcases n'''''' with _ | n'''''''
                · -- n = 6
                  have hCn : count_distinct_prime_partitions 59 6 = 6 := by
                    rw [count_eq_count_fast, count_fast_eq_count_bounded 59 6 60 (by omega)]
                    decide
                  have hk_lt := k_lt_Cn 6 k 59 (by omega) hCn hk2
                  have h_m := check_no_k_6_bounded_spec k hk_lt
                  rcases h_m with ⟨m, hm1, hm2, hm3⟩
                  have h_gt_m : k < m ∧ m ≤ k + 12 := ⟨hm1, hm2⟩
                  have h_gt_m' := hk1 m h_gt_m
                  change count_distinct_prime_partitions m 6 > 6 at h_gt_m'
                  omega
                · -- n ≥ 7
                  sorry
