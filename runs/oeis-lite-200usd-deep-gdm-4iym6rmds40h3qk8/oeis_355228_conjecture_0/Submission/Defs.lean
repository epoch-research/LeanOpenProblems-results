import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option linter.unusedVariables false
set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false



open Finset Nat Set

/--
A355228: $a(n)$ is the smallest integer $m$ such that there exist $n$ of its distinct divisors $(d_1, d_2, \dots, d_n)$ with the property that $m = d_1 + d_2 + \dots + d_n = \operatorname{lcm}(d_1, d_2, \dots, d_n)$, or 0 if no such number $m$ exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Define the set of candidates $m$ for the given $n$.
  let candidates : Set ℕ :=
    { m : ℕ | 0 < m ∧
      -- There exists a set D of n distinct elements
      ∃ D : Finset ℕ,
        -- D must be a subset of m's positive divisors.
        D ⊆ Nat.divisors m ∧
        D.card = n ∧
        -- The sum of elements in D must equal m.
        D.sum id = m ∧
        -- The LCM of elements in D must equal m.
        D.lcm id = m }

  -- sInf of a set of natural numbers returns the minimum element.
  -- Nat.sInf of the empty set is 0, correctly handling the non-existence case a(2)=0.
  sInf candidates

-- A081512: Smallest number $m$ such that $m$ is the sum of $n$ distinct divisors $d_1, \dots, d_n$ of $m$.
noncomputable def a081512 (n : ℕ) : ℕ :=
  let candidates : Set ℕ :=
    { m : ℕ | 0 < m ∧
      ∃ D : Finset ℕ,
        D ⊆ Nat.divisors m ∧
        D.card = n ∧
        D.sum id = m }
  sInf candidates

-- Helper definitions for candidate sets
def a_candidates (n : ℕ) : Set ℕ :=
  { m : ℕ | 0 < m ∧
    ∃ D : Finset ℕ,
      D ⊆ Nat.divisors m ∧
      D.card = n ∧
      D.sum id = m ∧
      D.lcm id = m }

def a081512_candidates (n : ℕ) : Set ℕ :=
  { m : ℕ | 0 < m ∧
    ∃ D : Finset ℕ,
      D ⊆ Nat.divisors m ∧
      D.card = n ∧
      D.sum id = m }

lemma mem_a_candidates_iff (m n : ℕ) :
  m ∈ a_candidates n ↔
  (0 < m ∧ ∃ D ∈ (Nat.divisors m).powerset, D.card = n ∧ D.sum id = m ∧ D.lcm id = m) := by
  dsimp [a_candidates]
  simp_rw [Finset.mem_powerset]

lemma mem_a081512_candidates_iff (m n : ℕ) :
  m ∈ a081512_candidates n ↔
  (0 < m ∧ ∃ D ∈ (Nat.divisors m).powerset, D.card = n ∧ D.sum id = m) := by
  dsimp [a081512_candidates]
  simp_rw [Finset.mem_powerset]

lemma mem_a081512_candidates_iff_powersetCard (m n : ℕ) :
  m ∈ a081512_candidates n ↔
  (0 < m ∧ ∃ D ∈ Finset.powersetCard n (Nat.divisors m), D.sum id = m) := by
  dsimp [a081512_candidates]
  simp_rw [Finset.mem_powersetCard]
  constructor
  · rintro ⟨h1, D, hD1, hD2, hD3⟩
    refine ⟨h1, D, ⟨hD1, hD2⟩, hD3⟩
  · rintro ⟨h1, D, ⟨hD1, hD2⟩, hD3⟩
    refine ⟨h1, D, hD1, hD2, hD3⟩


lemma proper_divisor_le_half {d m : ℕ} (hm : 0 < m) (hd : d ∣ m) (h_lt : d < m) : d ≤ m / 2 := by
  rcases hd with ⟨k, rfl⟩
  have hk : k > 1 := by
    by_contra! hc
    interval_cases k
    · simp at hm
    · simp at h_lt
  have hk2 : 2 ≤ k := hk
  have h_div : d ≤ d * 2 / 2 := by
    rw [Nat.mul_div_cancel d (by decide)]
  have h_div2 : d * 2 / 2 ≤ d * k / 2 := Nat.div_le_div_right (Nat.mul_le_mul_left d hk2)
  omega

lemma a081512_candidates_zero : a081512_candidates 0 = ∅ := by
  ext m
  simp only [mem_a081512_candidates_iff, mem_empty_iff_false, iff_false, not_and]
  rintro hm ⟨D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.card_eq_zero] at hD_card
  subst hD_card
  simp at hD_sum
  omega

lemma a081512_candidates_two : a081512_candidates 2 = ∅ := by
  ext m
  simp only [mem_a081512_candidates_iff, mem_empty_iff_false, iff_false, not_and]
  rintro hm ⟨D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_ne : D.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc
    subst hc
    simp at hD_card
  obtain ⟨d1, hd1⟩ := h_ne
  have hD2 : (D.erase d1).card = 1 := by
    rw [Finset.card_erase_of_mem hd1, hD_card]
  obtain ⟨d2, hd2⟩ := Finset.card_eq_one.mp hD2
  have hd2_mem_erase : d2 ∈ D.erase d1 := by
    rw [hd2]
    exact Finset.mem_singleton_self d2
  have hd2_mem : d2 ∈ D := Finset.mem_of_mem_erase hd2_mem_erase
  have hd1_ne_d2 : d1 ≠ d2 := (Finset.mem_erase.mp hd2_mem_erase).1.symm
  have h_sum : d1 + d2 = m := by
    have hD_eq : D = {d1, d2} := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hx
        by_cases hx1 : x = d1
        · left; exact hx1
        · right
          have : x ∈ D.erase d1 := Finset.mem_erase.mpr ⟨hx1, hx⟩
          rw [hd2] at this
          exact Finset.mem_singleton.mp this
      · rintro (rfl | rfl)
        · exact hd1
        · exact hd2_mem
    rw [hD_eq] at hD_sum
    simp [hd1_ne_d2] at hD_sum
    exact hD_sum
  have hd1_div : d1 ∣ m := (Nat.mem_divisors.mp (hD_pow hd1)).1
  have hd2_div : d2 ∣ m := (Nat.mem_divisors.mp (hD_pow hd2_mem)).1
  have hd1_gt0 : d1 > 0 := Nat.pos_of_mem_divisors (hD_pow hd1)
  have hd2_gt0 : d2 > 0 := Nat.pos_of_mem_divisors (hD_pow hd2_mem)
  have hd1_lt : d1 < m := by omega
  have hd2_lt : d2 < m := by omega
  have hd1_le_half : d1 ≤ m / 2 := proper_divisor_le_half hm hd1_div hd1_lt
  have hd2_le_half : d2 ≤ m / 2 := proper_divisor_le_half hm hd2_div hd2_lt
  have : d1 + d2 ≤ 2 * (m / 2) := by omega
  have h_m2 : 2 * (m / 2) ≤ m := Nat.mul_div_le m 2
  omega



-- Relocated from Cases_C for earlier access --

lemma not_mem_a081512_ge_21_360 (k : ℕ) (hk : k ≥ 21) : 360 ∉ a081512_candidates k := by
  have h_div : (Nat.divisors 360).card = 24 := by decide
  by_cases h_le : k ≤ 24
  · have h_sum : (Nat.divisors 360).sum id = 1170 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 360).card := Finset.card_le_card hD_sub
    omega

lemma not_mem_a081512_ge_21_420 (k : ℕ) (hk : k ≥ 21) : 420 ∉ a081512_candidates k := by
  have h_div : (Nat.divisors 420).card = 24 := by decide
  by_cases h_le : k ≤ 24
  · have h_sum : (Nat.divisors 420).sum id = 1344 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 420).card := Finset.card_le_card hD_sub
    omega

lemma not_mem_a081512_ge_21_480 (k : ℕ) (hk : k ≥ 21) : 480 ∉ a081512_candidates k := by
  have h_div : (Nat.divisors 480).card = 24 := by decide
  by_cases h_le : k ≤ 24
  · have h_sum : (Nat.divisors 480).sum id = 1512 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 480).card := Finset.card_le_card hD_sub
    omega

lemma not_mem_a081512_ge_21_504 (k : ℕ) (hk : k ≥ 21) : 504 ∉ a081512_candidates k := by
  have h_div : (Nat.divisors 504).card = 24 := by decide
  by_cases h_le : k ≤ 24
  · have h_sum : (Nat.divisors 504).sum id = 1560 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 504).card := Finset.card_le_card hD_sub
    omega

lemma not_mem_a081512_ge_21_540 (k : ℕ) (hk : k ≥ 21) : 540 ∉ a081512_candidates k := by
  have h_div : (Nat.divisors 540).card = 24 := by decide
  by_cases h_le : k ≤ 24
  · have h_sum : (Nat.divisors 540).sum id = 1680 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 540).card := Finset.card_le_card hD_sub
    omega

lemma not_mem_a081512_ge_21_576 (k : ℕ) (hk : k ≥ 21) : 576 ∉ a081512_candidates k := by
  have h_div : (Nat.divisors 576).card = 21 := by decide
  by_cases h_le : k ≤ 21
  · have h_sum : (Nat.divisors 576).sum id = 1651 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 576).card := Finset.card_le_card hD_sub
    omega

lemma not_mem_a081512_ge_21_600 (k : ℕ) (hk : k ≥ 21) : 600 ∉ a081512_candidates k := by
  have h_div : (Nat.divisors 600).card = 24 := by decide
  by_cases h_le : k ≤ 24
  · have h_sum : (Nat.divisors 600).sum id = 1860 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 600).card := Finset.card_le_card hD_sub
    omega

lemma not_mem_a081512_ge_21_630 (k : ℕ) (hk : k ≥ 21) : 630 ∉ a081512_candidates k := by
  have h_div : (Nat.divisors 630).card = 24 := by decide
  by_cases h_le : k ≤ 24
  · by_cases hk21 : k = 21
    · subst hk21
      apply not_mem_a081512_of_compl 21 630
      · decide
      · decide
    · have h_sum : (Nat.divisors 630).sum id = 1872 := by decide
      apply not_mem_a081512_of_sum_gt (by omega) (by omega) (by omega)
      omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 630).card := Finset.card_le_card hD_sub
    omega

lemma not_mem_a081512_ge_21_660 (k : ℕ) (hk : k ≥ 21) : 660 ∉ a081512_candidates k := by
  have h_div : (Nat.divisors 660).card = 24 := by decide
  by_cases h_le : k ≤ 24
  · have h_sum : (Nat.divisors 660).sum id = 2016 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 660).card := Finset.card_le_card hD_sub
    omega

lemma not_mem_a081512_ge_21_672 (k : ℕ) (hk : k ≥ 21) : 672 ∉ a081512_candidates k := by
  have h_div : (Nat.divisors 672).card = 24 := by decide
  by_cases h_le : k ≤ 24
  · by_cases hk21 : k = 21
    · subst hk21
      apply not_mem_a081512_of_compl 21 672
      · decide
      · decide
    · have h_sum : (Nat.divisors 672).sum id = 2016 := by decide
      apply not_mem_a081512_of_sum_gt (by omega) (by omega) (by omega)
      omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 672).card := Finset.card_le_card hD_sub
    omega

theorem a081512_candidates_ge_360 (k : ℕ) (hk : k ≥ 21) (x : ℕ) (hx : x ∈ a081512_candidates k) : 360 ≤ x := by
  by_contra! h
  have h_decide : (List.range 360).all (fun y => decide ((Nat.divisors y).card < 21)) = true := by decide
  have h_mem : x ∈ List.range 360 := List.mem_range.mpr h
  have h_all := List.all_eq_true.mp h_decide x h_mem
  have h_card := of_decide_eq_true h_all
  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : k ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow
  omega

theorem a081512_candidates_ge_twentyone_ge_720 (k : ℕ) (hk : k ≥ 21) (x : ℕ) (hx : x ∈ a081512_candidates k) : 720 ≤ x := by
  have hx360 : 360 ≤ x := a081512_candidates_ge_360 k hk x hx
  by_contra! h
  have h_decide : ((List.range 360).map (· + 360)).all (fun y =>
      decide (if y = 360 ∨ y = 420 ∨ y = 480 ∨ y = 504 ∨ y = 540 ∨ y = 576 ∨ y = 600 ∨ y = 630 ∨ y = 660 ∨ y = 672 then True
              else (Nat.divisors y).card < 21)) = true := by decide
  have h_mem : x ∈ ((List.range 360).map (· + 360)) := by
    rw [List.mem_map]
    use x - 360
    constructor
    · rw [List.mem_range]
      omega
    · omega
  have h_all := List.all_eq_true.mp h_decide x h_mem
  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : k ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow
  by_cases h360 : x = 360
  · subst h360; exact not_mem_a081512_ge_21_360 k hk ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h420 : x = 420
  · subst h420; exact not_mem_a081512_ge_21_420 k hk ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h480 : x = 480
  · subst h480; exact not_mem_a081512_ge_21_480 k hk ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h504 : x = 504
  · subst h504; exact not_mem_a081512_ge_21_504 k hk ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h540 : x = 540
  · subst h540; exact not_mem_a081512_ge_21_540 k hk ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h576 : x = 576
  · subst h576; exact not_mem_a081512_ge_21_576 k hk ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h600 : x = 600
  · subst h600; exact not_mem_a081512_ge_21_600 k hk ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h630 : x = 630
  · subst h630; exact not_mem_a081512_ge_21_630 k hk ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h660 : x = 660
  · subst h660; exact not_mem_a081512_ge_21_660 k hk ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h672 : x = 672
  · subst h672; exact not_mem_a081512_ge_21_672 k hk ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  have h_not_cond : ¬ (x = 360 ∨ x = 420 ∨ x = 480 ∨ x = 504 ∨ x = 540 ∨ x = 576 ∨ x = 600 ∨ x = 630 ∨ x = 660 ∨ x = 672) := by
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact h360 rfl
    · exact h420 rfl
    · exact h480 rfl
    · exact h504 rfl
    · exact h540 rfl
    · exact h576 rfl
    · exact h600 rfl
    · exact h630 rfl
    · exact h660 rfl
    · exact h672 rfl
  have h_card : (Nat.divisors x).card < 21 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 360 ∨ x = 420 ∨ x = 480 ∨ x = 504 ∨ x = 540 ∨ x = 576 ∨ x = 600 ∨ x = 630 ∨ x = 660 ∨ x = 672
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega

