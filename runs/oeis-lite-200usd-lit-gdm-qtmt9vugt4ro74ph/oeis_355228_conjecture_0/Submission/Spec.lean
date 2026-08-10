import FormalConjectures.Util.ProblemImports

-- A small test comment.
set_option maxHeartbeats 0
set_option maxRecDepth 15000

open Finset Nat Set

instance decidableLoHiAnd (lo hi : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Decidable (∀ m, lo ≤ m ∧ m < hi → P m) :=
  decidable_of_iff (∀ m, lo ≤ m → m < hi → P m) <| by
    simp only [and_imp]


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

lemma sInf_eq_of_mem_and_lt_not_mem {s : Set ℕ} {x : ℕ} (h_mem : x ∈ s) (h_lt : ∀ y < x, y ∉ s) : sInf s = x := by
  have h_le : ∀ y ∈ s, x ≤ y := by
    intro y hy
    by_contra h_contr
    have h_lt' : y < x := by omega
    exact h_lt y h_lt' hy
  have h1 : sInf s ≤ x := Nat.sInf_le h_mem
  have h_nonempty : s.Nonempty := ⟨x, h_mem⟩
  have h_sInf_mem : sInf s ∈ s := Nat.sInf_mem h_nonempty
  have h2 : x ≤ sInf s := h_le (sInf s) h_sInf_mem
  exact le_antisymm h1 h2

def candidates_a08 (n : ℕ) : Set ℕ :=
  { m : ℕ | 0 < m ∧
    ∃ D : Finset ℕ,
      D ⊆ Nat.divisors m ∧
      D.card = n ∧
      D.sum id = m }

def candidates_a (n : ℕ) : Set ℕ :=
  { m : ℕ | 0 < m ∧
    ∃ D : Finset ℕ,
      D ⊆ Nat.divisors m ∧
      D.card = n ∧
      D.sum id = m ∧
      D.lcm id = m }

lemma candidates_a08_zero_eq_empty : candidates_a08 0 = ∅ := by
  ext m
  simp only [candidates_a08, mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨h0, D, _, h_card, h_sum⟩
  have h_empty : D = ∅ := card_eq_zero.mp h_card
  rw [h_empty, sum_empty] at h_sum
  omega

lemma candidates_a_zero_eq_empty : candidates_a 0 = ∅ := by
  ext m
  simp only [candidates_a, mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨h0, D, _, h_card, h_sum, _⟩
  have h_empty : D = ∅ := card_eq_zero.mp h_card
  rw [h_empty, sum_empty] at h_sum
  omega

lemma div_le_of_dvd_of_lt {d m : ℕ} (h_dvd : d ∣ m) (h_lt : d < m) : d ≤ m / 2 := by
  rcases h_dvd with ⟨k, rfl⟩
  have h_k : 2 ≤ k := by
    by_contra h_contr
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · simp at h_lt
    · simp at h_lt
  have : 2 * d ≤ d * k := by
    rw [mul_comm d k]
    exact Nat.mul_le_mul_right d h_k
  omega

lemma candidates_a08_two_eq_empty : candidates_a08 2 = ∅ := by
  ext m
  simp only [candidates_a08, mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨h0, D, h_div, h_card, h_sum⟩
  rcases card_eq_two.mp h_card with ⟨x, y, hxy, rfl⟩
  have h_sum' : x + y = m := by
    rw [sum_insert (by simp [hxy]), sum_singleton] at h_sum
    exact h_sum
  have h_x_div : x ∈ Nat.divisors m := h_div (by simp)
  have h_y_div : y ∈ Nat.divisors m := h_div (by simp [hxy])
  have h_x_dvd : x ∣ m := Nat.mem_divisors.mp h_x_div |>.1
  have h_y_dvd : y ∣ m := Nat.mem_divisors.mp h_y_div |>.1
  have h_x_pos : 0 < x := Nat.pos_of_mem_divisors h_x_div
  have h_y_pos : 0 < y := Nat.pos_of_mem_divisors h_y_div
  have h_x_lt : x < m := by omega
  have h_y_lt : y < m := by omega
  have h_x_le : x ≤ m / 2 := div_le_of_dvd_of_lt h_x_dvd h_x_lt
  have h_y_le : y ≤ m / 2 := div_le_of_dvd_of_lt h_y_dvd h_y_lt
  omega

lemma candidates_a_two_eq_empty : candidates_a 2 = ∅ := by
  ext m
  simp only [candidates_a, mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨h0, D, h_div, h_card, h_sum, _⟩
  rcases card_eq_two.mp h_card with ⟨x, y, hxy, rfl⟩
  have h_sum' : x + y = m := by
    rw [sum_insert (by simp [hxy]), sum_singleton] at h_sum
    exact h_sum
  have h_x_div : x ∈ Nat.divisors m := h_div (by simp)
  have h_y_div : y ∈ Nat.divisors m := h_div (by simp [hxy])
  have h_x_dvd : x ∣ m := Nat.mem_divisors.mp h_x_div |>.1
  have h_y_dvd : y ∣ m := Nat.mem_divisors.mp h_y_div |>.1
  have h_x_pos : 0 < x := Nat.pos_of_mem_divisors h_x_div
  have h_y_pos : 0 < y := Nat.pos_of_mem_divisors h_y_div
  have h_x_lt : x < m := by omega
  have h_y_lt : y < m := by omega
  have h_x_le : x ≤ m / 2 := div_le_of_dvd_of_lt h_x_dvd h_x_lt
  have h_y_le : y ≤ m / 2 := div_le_of_dvd_of_lt h_y_dvd h_y_lt
  omega

lemma mem_candidates_a08_iff_powerset (n m : ℕ) :
  m ∈ candidates_a08 n ↔ 0 < m ∧ ∃ D ∈ (Nat.divisors m).powerset, D.card = n ∧ D.sum id = m := by
  simp [candidates_a08, Finset.mem_powerset]

lemma mem_candidates_a_iff_powerset (n m : ℕ) :
  m ∈ candidates_a n ↔ 0 < m ∧ ∃ D ∈ (Nat.divisors m).powerset, D.card = n ∧ D.sum id = m ∧ D.lcm id = m := by
  simp [candidates_a, Finset.mem_powerset]

instance (n m : ℕ) : Decidable (m ∈ candidates_a08 n) :=
  decidable_of_iff _ (mem_candidates_a08_iff_powerset n m).symm


instance (n m : ℕ) : Decidable (m ∈ candidates_a n) :=
  decidable_of_iff _ (mem_candidates_a_iff_powerset n m).symm



lemma candidates_a_sub_candidates_a08 (n : ℕ) : candidates_a n ⊆ candidates_a08 n := by
  intro x hx
  rw [candidates_a, mem_setOf_eq] at hx
  rw [candidates_a08, mem_setOf_eq]
  rcases hx with ⟨h1, D, hD, h_card, h_sum, _⟩
  exact ⟨h1, D, hD, h_card, h_sum⟩

lemma not_mem_candidates_a08_of_card_lt {n m : ℕ} (h : (Nat.divisors m).card < n) : m ∉ candidates_a08 n := by
  rw [mem_candidates_a08_iff_powerset]
  rintro ⟨-, D, hD_pow, h_card, _⟩
  rw [Finset.mem_powerset] at hD_pow
  have : D.card ≤ (Nat.divisors m).card := Finset.card_le_card hD_pow
  omega


lemma sum_eq_sum_divisors_sub {m : ℕ} {D : Finset ℕ} (hD : D ⊆ Nat.divisors m)
    (h_card : D.card + 1 = (Nat.divisors m).card) :
    ∃ d ∈ Nat.divisors m, D.sum id + d = (Nat.divisors m).sum id := by
  have h_sdiff : (Nat.divisors m \ D).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hD]
    omega
  rcases Finset.card_eq_one.mp h_sdiff with ⟨d, hd⟩
  use d
  have hd_mem : d ∈ Nat.divisors m \ D := hd ▸ Finset.mem_singleton_self d
  rw [Finset.mem_sdiff] at hd_mem
  refine ⟨hd_mem.1, ?_⟩
  have h_union : D ∪ (Nat.divisors m \ D) = Nat.divisors m := Finset.union_sdiff_of_subset hD
  have h_disj : Disjoint D (Nat.divisors m \ D) := Finset.disjoint_sdiff
  have h_sum : (D ∪ (Nat.divisors m \ D)).sum id = D.sum id + (Nat.divisors m \ D).sum id := Finset.sum_union h_disj
  rw [h_union, hd] at h_sum
  simp only [Finset.sum_singleton, id_eq] at h_sum
  exact h_sum.symm


lemma not_mem_candidates_a08_of_no_sub_div_sum {m n k target : ℕ} (hc : (Nat.divisors m).card = n + k)
    (ht : (Nat.divisors m).sum id - m = target)
    (h_no : ∀ Y ⊆ Nat.divisors m, Y.card = k → Y.sum id ≠ target) : m ∉ candidates_a08 n := by
  intro h
  rw [mem_candidates_a08_iff_powerset] at h
  rcases h with ⟨-, D, hD_pow, h_card, h_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_card_eq : (Nat.divisors m \ D).card = k := by
    rw [Finset.card_sdiff_of_subset hD_pow, h_card, hc]
    omega
  have h_sum_eq : (Nat.divisors m \ D).sum id = target := by
    have h_sum_sdiff : (Nat.divisors m \ D).sum id + D.sum id = (Nat.divisors m).sum id := Finset.sum_sdiff hD_pow
    omega
  have h_sub : (Nat.divisors m \ D) ⊆ Nat.divisors m := Finset.sdiff_subset
  exact h_no (Nat.divisors m \ D) h_sub h_card_eq h_sum_eq


lemma not_mem_candidates_a08_eq_of_sum_divisors_ne_m {m n : ℕ} (hm : (Nat.divisors m).card = n)
    (h_sum : (Nat.divisors m).sum id ≠ m) : m ∉ candidates_a08 n := by
  intro h
  rw [mem_candidates_a08_iff_powerset] at h
  rcases h with ⟨hm0, D, hD_pow, h_card, h_sum_D⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_eq : D = Nat.divisors m := by
    apply Finset.eq_of_subset_of_card_le hD_pow
    omega
  rw [h_eq] at h_sum_D
  exact h_sum h_sum_D


lemma not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m {m n : ℕ} (hm : (Nat.divisors m).card = n + 1)
    (h_sum : (Nat.divisors m).sum id > 2 * m) : m ∉ candidates_a08 n := by
  intro h
  rw [mem_candidates_a08_iff_powerset] at h
  rcases h with ⟨hm0, D, hD_pow, h_card, h_sum_D⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_card_eq : D.card + 1 = (Nat.divisors m).card := by omega
  rcases sum_eq_sum_divisors_sub hD_pow h_card_eq with ⟨d, hd_mem, hd_sum⟩
  have hd_dvd : d ∣ m := Nat.mem_divisors.mp hd_mem |>.1
  have hd_le : d ≤ m := Nat.le_of_dvd hm0 hd_dvd
  omega










lemma no_sum_1 {m target : ℕ} (h_all : ∀ a ∈ Nat.divisors m, a ≠ target) :
    ∀ Y ⊆ Nat.divisors m, Y.card = 1 → Y.sum id ≠ target := by
  intro Y hY hk h_sum
  rcases Finset.card_eq_one.mp hk with ⟨a, rfl⟩
  rw [Finset.sum_singleton] at h_sum
  dsimp [id] at h_sum
  have ha : a ∈ Nat.divisors m := hY (by simp)
  exact h_all a ha h_sum

lemma no_sum_2 {m target : ℕ} (h_all : ∀ a ∈ Nat.divisors m, ∀ b ∈ Nat.divisors m,
    a ≠ b → a + b ≠ target) :
    ∀ Y ⊆ Nat.divisors m, Y.card = 2 → Y.sum id ≠ target := by
  intro Y hY hk h_sum
  rcases Finset.card_eq_two.mp hk with ⟨a, b, hab, rfl⟩
  rw [Finset.sum_insert (by simp [hab]), Finset.sum_singleton] at h_sum
  dsimp [id] at h_sum
  have ha : a ∈ Nat.divisors m := hY (by simp)
  have hb : b ∈ Nat.divisors m := hY (by simp [hab])
  exact h_all a ha b hb hab h_sum

lemma no_sum_3 {m target : ℕ} (h_all : ∀ a ∈ Nat.divisors m, ∀ b ∈ Nat.divisors m, ∀ c ∈ Nat.divisors m,
    a ≠ b ∧ a ≠ c ∧ b ≠ c → a + (b + c) ≠ target) :
    ∀ Y ⊆ Nat.divisors m, Y.card = 3 → Y.sum id ≠ target := by
  intro Y hY hk h_sum
  rcases Finset.card_eq_three.mp hk with ⟨a, b, c, hab, hac, hbc, rfl⟩
  rw [Finset.sum_insert (by simp [hab, hac, hbc]), Finset.sum_insert (by simp [hab, hac, hbc]), Finset.sum_singleton] at h_sum
  dsimp [id] at h_sum
  have ha : a ∈ Nat.divisors m := hY (by simp)
  have hb : b ∈ Nat.divisors m := hY (by simp [hab, hac, hbc])
  have hc : c ∈ Nat.divisors m := hY (by simp [hab, hac, hbc])
  exact h_all a ha b hb c hc ⟨hab, hac, hbc⟩ h_sum

lemma no_sum_4 {m target : ℕ} (h_all : ∀ a ∈ Nat.divisors m, ∀ b ∈ Nat.divisors m, ∀ c ∈ Nat.divisors m, ∀ d ∈ Nat.divisors m,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d → a + (b + (c + d)) ≠ target) :
    ∀ Y ⊆ Nat.divisors m, Y.card = 4 → Y.sum id ≠ target := by
  intro Y hY hk h_sum
  rcases Finset.card_eq_four.mp hk with ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton] at h_sum
  · dsimp [id] at h_sum
    have ha : a ∈ Nat.divisors m := hY (by simp)
    have hb : b ∈ Nat.divisors m := hY (by simp [hab, hac, had, hbc, hbd, hcd])
    have hc : c ∈ Nat.divisors m := hY (by simp [hab, hac, had, hbc, hbd, hcd])
    have hd : d ∈ Nat.divisors m := hY (by simp [hab, hac, had, hbc, hbd, hcd])
    exact h_all a ha b hb c hc d hd ⟨hab, hac, had, hbc, hbd, hcd⟩ h_sum
  · simp [hab, hac, had, hbc, hbd, hcd]
  · simp [hab, hac, had, hbc, hbd, hcd]
  · simp [hab, hac, had, hbc, hbd, hcd]


lemma a_eq_sInf_candidates_a (n : ℕ) : a n = sInf (candidates_a n) := rfl
lemma a081512_eq_sInf_candidates_a08 (n : ℕ) : a081512 n = sInf (candidates_a08 n) := rfl

lemma sInf_eq_zero_of_empty {s : Set ℕ} (h_empty : s = ∅) : sInf s = 0 := by
  rw [h_empty]
  exact Nat.sInf_empty

lemma a08_zero : a081512 0 = 0 := by
  rw [a081512_eq_sInf_candidates_a08, sInf_eq_zero_of_empty candidates_a08_zero_eq_empty]

lemma a_zero : a 0 = 0 := by
  rw [a_eq_sInf_candidates_a, sInf_eq_zero_of_empty candidates_a_zero_eq_empty]

lemma a08_two : a081512 2 = 0 := by
  rw [a081512_eq_sInf_candidates_a08, sInf_eq_zero_of_empty candidates_a08_two_eq_empty]

lemma a_two : a 2 = 0 := by
  rw [a_eq_sInf_candidates_a, sInf_eq_zero_of_empty candidates_a_two_eq_empty]

set_option maxRecDepth 10000 in
lemma a08_one : a081512 1 = 1 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a08_iff_powerset]; decide
  · intro y hy
    interval_cases y
    rw [mem_candidates_a08_iff_powerset]
    decide

set_option maxRecDepth 10000 in
lemma a_one : a 1 = 1 := by
  rw [a_eq_sInf_candidates_a]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a_iff_powerset]; decide
  · intro y hy
    interval_cases y
    rw [mem_candidates_a_iff_powerset]
    decide

set_option maxRecDepth 10000 in
lemma a08_three : a081512 3 = 6 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a08_iff_powerset]; decide
  · intro y hy
    interval_cases y
    all_goals (rw [mem_candidates_a08_iff_powerset]; decide)

set_option maxRecDepth 10000 in
lemma a_three : a 3 = 6 := by
  rw [a_eq_sInf_candidates_a]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a_iff_powerset]; decide
  · intro y hy
    interval_cases y
    all_goals (rw [mem_candidates_a_iff_powerset]; decide)

set_option maxRecDepth 10000 in
lemma a08_four : a081512 4 = 12 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a08_iff_powerset]; decide
  · intro y hy
    interval_cases y
    all_goals (rw [mem_candidates_a08_iff_powerset]; decide)

set_option maxRecDepth 10000 in
lemma a_four : a 4 = 18 := by
  rw [a_eq_sInf_candidates_a]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a_iff_powerset]; decide
  · intro y hy
    interval_cases y
    all_goals (rw [mem_candidates_a_iff_powerset]; decide)

set_option maxRecDepth 10000 in
lemma a08_five : a081512 5 = 24 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a08_iff_powerset]; decide
  · intro y hy
    interval_cases y
    all_goals (rw [mem_candidates_a08_iff_powerset]; decide)

set_option maxRecDepth 10000 in
lemma a_five : a 5 = 28 := by
  rw [a_eq_sInf_candidates_a]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a_iff_powerset]; decide
  · intro y hy
    interval_cases y
    all_goals (rw [mem_candidates_a_iff_powerset]; decide)


set_option maxRecDepth 10000 in
lemma L_ge_12_of_card_divisors_ge_6 {L : ℕ} (h : 6 ≤ (Nat.divisors L).card) : 12 ≤ L := by
  by_contra h_lt
  have : L < 12 := by omega
  interval_cases L <;> revert h <;> decide

set_option maxRecDepth 10000 in
lemma m_ge_24_of_mem_candidates_a08 {n m : ℕ} (hn : 6 ≤ n) (hm : m ∈ candidates_a08 n) : 24 ≤ m := by
  have h_div_card : n ≤ (Nat.divisors m).card := by
    rcases hm with ⟨_, D, hD_div, hD_card, _⟩
    rw [← hD_card]
    exact Finset.card_le_card hD_div
  have h_div_card6 : 6 ≤ (Nat.divisors m).card := by omega
  have h_ge12 : 12 ≤ m := L_ge_12_of_card_divisors_ge_6 h_div_card6
  by_contra h_lt
  have h_lt24 : m < 24 := by omega
  interval_cases m
  · -- m = 12
    have h_card : (Nat.divisors 12).card = 6 := by decide
    have : n = 6 := by omega
    subst this
    have : 12 ∉ candidates_a08 6 := by rw [mem_candidates_a08_iff_powerset]; decide
    exact this hm
  · -- m = 13
    have h_card : (Nat.divisors 13).card = 2 := by decide
    omega
  · -- m = 14
    have h_card : (Nat.divisors 14).card = 4 := by decide
    omega
  · -- m = 15
    have h_card : (Nat.divisors 15).card = 4 := by decide
    omega
  · -- m = 16
    have h_card : (Nat.divisors 16).card = 5 := by decide
    omega
  · -- m = 17
    have h_card : (Nat.divisors 17).card = 2 := by decide
    omega
  · -- m = 18
    have h_card : (Nat.divisors 18).card = 6 := by decide
    have : n = 6 := by omega
    subst this
    have : 18 ∉ candidates_a08 6 := by rw [mem_candidates_a08_iff_powerset]; decide
    exact this hm
  · -- m = 19
    have h_card : (Nat.divisors 19).card = 2 := by decide
    omega
  · -- m = 20
    have h_card : (Nat.divisors 20).card = 6 := by decide
    have : n = 6 := by omega
    subst this
    have : 20 ∉ candidates_a08 6 := by rw [mem_candidates_a08_iff_powerset]; decide
    exact this hm
  · -- m = 21
    have h_card : (Nat.divisors 21).card = 4 := by decide
    omega
  · -- m = 22
    have h_card : (Nat.divisors 22).card = 4 := by decide
    omega
  · -- m = 23
    have h_card : (Nat.divisors 23).card = 2 := by decide
    omega


def D_witness_ge_6 : ℕ → Finset ℕ
  | 0 => {1, 2, 3, 4, 6, 8}
  | n + 1 =>
    let D := D_witness_ge_6 n
    (D.image (fun x => 2 * x)).erase 4 ∪ {1, 3}

set_option maxRecDepth 10000 in
lemma mem_one_D_witness_ge_6 (n : ℕ) : 1 ∈ D_witness_ge_6 n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [D_witness_ge_6]
    apply Finset.mem_union_right
    decide

set_option maxRecDepth 10000 in
lemma mem_two_D_witness_ge_6 (n : ℕ) : 2 ∈ D_witness_ge_6 n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [D_witness_ge_6]
    apply Finset.mem_union_left
    rw [Finset.mem_erase]
    refine ⟨by decide, ?_⟩
    rw [Finset.mem_image]
    use 1
    refine ⟨mem_one_D_witness_ge_6 n, by decide⟩

lemma disjoint_image_erase_odd (D : Finset ℕ) : Disjoint ((D.image (fun x => 2 * x)).erase 4) {1, 3} := by
  rw [Finset.disjoint_iff_ne]
  intro x hx y hy
  simp only [Finset.mem_erase, Finset.mem_image] at hx
  rcases hx.2 with ⟨a, _, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl
  · omega
  · omega

set_option maxRecDepth 10000 in
lemma card_D_witness_ge_6 (n : ℕ) : (D_witness_ge_6 n).card = n + 6 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [D_witness_ge_6]
    rw [Finset.card_union_of_disjoint (disjoint_image_erase_odd (D_witness_ge_6 n))]
    have h_four : 4 ∈ (D_witness_ge_6 n).image (fun x => 2 * x) := by
      rw [Finset.mem_image]
      use 2
      exact ⟨mem_two_D_witness_ge_6 n, rfl⟩
    rw [Finset.card_erase_of_mem h_four]
    have h_inj : Function.Injective (fun x : ℕ => 2 * x) := by
      intro a b hab; dsimp at hab; omega
    rw [Finset.card_image_of_injective _ h_inj]
    rw [ih]
    have h_card : ({1, 3} : Finset ℕ).card = 2 := by decide
    rw [h_card]
    omega

set_option maxRecDepth 10000 in
lemma sum_D_witness_ge_6 (n : ℕ) : (D_witness_ge_6 n).sum id = 24 * 2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [D_witness_ge_6]
    rw [Finset.sum_union (disjoint_image_erase_odd (D_witness_ge_6 n))]
    have h_four : 4 ∈ (D_witness_ge_6 n).image (fun x => 2 * x) := by
      rw [Finset.mem_image]
      use 2
      exact ⟨mem_two_D_witness_ge_6 n, rfl⟩
    have h_sum_erase := Finset.sum_erase_add ((D_witness_ge_6 n).image (fun x => 2 * x)) id h_four
    have h_sum_13 : ({1, 3} : Finset ℕ).sum id = 4 := by decide
    rw [h_sum_13]
    have h_inj : Function.Injective (fun x : ℕ => 2 * x) := by
      intro a b hab; dsimp at hab; omega
    have h_sum_image : ((D_witness_ge_6 n).image (fun x => 2 * x)).sum id = (D_witness_ge_6 n).sum (fun x => 2 * x) := Finset.sum_image h_inj.injOn
    have h_factor : (D_witness_ge_6 n).sum (fun x => 2 * x) = 2 * (D_witness_ge_6 n).sum id := by
      rw [← Finset.mul_sum]
      rfl
    rw [h_sum_image] at h_sum_erase
    rw [h_factor] at h_sum_erase
    rw [ih] at h_sum_erase
    have : 2 * (24 * 2^n) = 24 * 2^(n+1) := by omega
    rw [this] at h_sum_erase
    exact h_sum_erase

set_option maxRecDepth 10000 in
lemma divisors_D_witness_ge_6 (n : ℕ) : ∀ x ∈ D_witness_ge_6 n, x ∣ 24 * 2^n := by
  induction n with
  | zero =>
    intro x hx
    revert hx x
    decide
  | succ n ih =>
    intro x hx
    simp only [D_witness_ge_6] at hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · rw [Finset.mem_erase] at hx
      rcases hx with ⟨_, h_mem⟩
      rw [Finset.mem_image] at h_mem
      rcases h_mem with ⟨a, ha_mem, rfl⟩
      have ha_dvd := ih a ha_mem
      have : 2 * a ∣ 2 * (24 * 2^n) := mul_dvd_mul_left 2 ha_dvd
      have h_eq : 2 * (24 * 2^n) = 24 * 2^(n+1) := by omega
      rw [h_eq] at this
      exact this
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact one_dvd (24 * 2^(n+1))
      · have h3 : 3 ∣ 24 := by decide
        have h4 : 24 ∣ 24 * 2^(n+1) := dvd_mul_right 24 (2^(n+1))
        exact dvd_trans h3 h4

set_option maxRecDepth 10000 in
lemma mem_three_D_witness_ge_6 (n : ℕ) : 3 ∈ D_witness_ge_6 n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [D_witness_ge_6]
    apply Finset.mem_union_right
    decide

set_option maxRecDepth 10000 in
lemma mem_eight_mul_two_pow_D_witness_ge_6 (n : ℕ) : 8 * 2^n ∈ D_witness_ge_6 n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [D_witness_ge_6]
    apply Finset.mem_union_left
    rw [Finset.mem_erase]
    refine ⟨by omega, ?_⟩
    rw [Finset.mem_image]
    use 8 * 2^n
    refine ⟨ih, by omega⟩

set_option maxRecDepth 10000 in
lemma coprime_three_eight_mul_two_pow (n : ℕ) : Nat.Coprime 3 (8 * 2^n) := by
  apply Nat.Coprime.mul_right
  · decide
  · apply Nat.Coprime.pow_right
    decide

lemma lcm_D_witness_ge_6 (n : ℕ) : (D_witness_ge_6 n).lcm id = 24 * 2^n := by
  have h3_dvd : 3 ∣ (D_witness_ge_6 n).lcm id := Finset.dvd_lcm (mem_three_D_witness_ge_6 n)
  have h8_dvd : 8 * 2^n ∣ (D_witness_ge_6 n).lcm id := Finset.dvd_lcm (mem_eight_mul_two_pow_D_witness_ge_6 n)
  have h24_dvd : 24 * 2^n ∣ (D_witness_ge_6 n).lcm id := by
    have h_coprime := coprime_three_eight_mul_two_pow n
    have h_mul := Nat.Coprime.mul_dvd_of_dvd_of_dvd h_coprime h3_dvd h8_dvd
    have h_eq : 3 * (8 * 2^n) = 24 * 2^n := by omega
    rwa [h_eq] at h_mul
  have h_lcm_dvd : (D_witness_ge_6 n).lcm id ∣ 24 * 2^n := by
    apply Finset.lcm_dvd
    intro x hx
    exact divisors_D_witness_ge_6 n x hx
  exact Nat.dvd_antisymm h_lcm_dvd h24_dvd

set_option maxRecDepth 10000 in
lemma a_seven_le_48 : a 7 ≤ 48 := by
  rw [a_eq_sInf_candidates_a]
  apply Nat.sInf_le
  rw [mem_candidates_a_iff_powerset]
  decide

set_option maxRecDepth 10000 in
lemma a08_seven_eq_48 : a081512 7 = 48 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a08_iff_powerset]; decide
  · intro y hy
    interval_cases y
    all_goals (rw [mem_candidates_a08_iff_powerset]; decide)

set_option maxRecDepth 10000 in
lemma a08_six_eq_24 : a081512 6 = 24 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a08_iff_powerset]; decide
  · intro y hy
    by_cases h_card : (Nat.divisors y).card < 6
    · exact not_mem_candidates_a08_of_card_lt h_card
    · have h_all : ∀ y < 24, ¬ (Nat.divisors y).card < 6 → y = 12 ∨ y = 18 ∨ y = 20 := by decide
      have h_y := h_all y hy h_card
      rcases h_y with rfl | rfl | rfl
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 12 6 (by decide) (by decide)
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 18 6 (by decide) (by decide)
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 20 6 (by decide) (by decide)

set_option maxRecDepth 10000 in
lemma a08_eight_eq_60 : a081512 8 = 60 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a08_iff_powerset]; decide
  · intro y hy
    by_cases h_card : (Nat.divisors y).card < 8
    · exact not_mem_candidates_a08_of_card_lt h_card
    · have h_all : ∀ y < 60, ¬ (Nat.divisors y).card < 8 → y = 24 ∨ y = 30 ∨ y = 36 ∨ y = 40 ∨ y = 42 ∨ y = 48 ∨ y = 54 ∨ y = 56 := by decide
      have h_y := h_all y hy h_card
      rcases h_y with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 24 8 (by decide) (by decide)
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 30 8 (by decide) (by decide)
      · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 36 8 (by decide) (by decide)
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 40 8 (by decide) (by decide)
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 42 8 (by decide) (by decide)
      · refine @not_mem_candidates_a08_of_no_sub_div_sum 48 8 2 76 (by decide) (by decide) (no_sum_2 (by decide))
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 54 8 (by decide) (by decide)
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 56 8 (by decide) (by decide)

set_option maxRecDepth 10000 in
lemma a08_nine_eq_84 : a081512 9 = 84 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a08_iff_powerset]
    have h_84 : 0 < 84 := by decide
    refine ⟨h_84, ?_⟩
    let D : Finset ℕ := {1, 2, 3, 4, 6, 7, 12, 21, 28}
    use D
    have h_prop : D ⊆ (Nat.divisors 84) ∧ D.card = 9 ∧ D.sum id = 84 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · intro y hy
    by_cases h_card : (Nat.divisors y).card < 9
    · exact not_mem_candidates_a08_of_card_lt h_card
    · have h_all : ∀ y < 84, ¬ (Nat.divisors y).card < 9 → y = 36 ∨ y = 48 ∨ y = 60 ∨ y = 72 ∨ y = 80 := by decide
      have h_y := h_all y hy h_card
      rcases h_y with rfl | rfl | rfl | rfl | rfl
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 36 9 (by decide) (by decide)
      · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 48 9 (by decide) (by decide)
      · refine @not_mem_candidates_a08_of_no_sub_div_sum 60 9 3 108 (by decide) (by decide) (no_sum_3 (by decide))
      · refine @not_mem_candidates_a08_of_no_sub_div_sum 72 9 3 123 (by decide) (by decide) (no_sum_3 (by decide))
      · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 80 9 (by decide) (by decide)

set_option maxRecDepth 10000 in
lemma a08_ten_eq_120 : a081512 10 = 120 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a08_iff_powerset]
    have h_120 : 0 < 120 := by decide
    refine ⟨h_120, ?_⟩
    let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 15, 20, 24, 40}
    use D
    have h_prop : D ⊆ (Nat.divisors 120) ∧ D.card = 10 ∧ D.sum id = 120 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · intro y hy
    by_cases h_card : (Nat.divisors y).card < 10
    · exact not_mem_candidates_a08_of_card_lt h_card
    · have h_all : ∀ y < 120, ¬ (Nat.divisors y).card < 10 → y = 48 ∨ y = 60 ∨ y = 72 ∨ y = 80 ∨ y = 84 ∨ y = 90 ∨ y = 96 ∨ y = 108 ∨ y = 112 := by decide
      have h_y := h_all y hy h_card
      rcases h_y with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 48 10 (by decide) (by decide)
      · refine @not_mem_candidates_a08_of_no_sub_div_sum 60 10 2 108 (by decide) (by decide) (no_sum_2 (by decide))
      · refine @not_mem_candidates_a08_of_no_sub_div_sum 72 10 2 123 (by decide) (by decide) (no_sum_2 (by decide))
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 80 10 (by decide) (by decide)
      · refine @not_mem_candidates_a08_of_no_sub_div_sum 84 10 2 140 (by decide) (by decide) (no_sum_2 (by decide))
      · refine @not_mem_candidates_a08_of_no_sub_div_sum 90 10 2 144 (by decide) (by decide) (no_sum_2 (by decide))
      · refine @not_mem_candidates_a08_of_no_sub_div_sum 96 10 2 156 (by decide) (by decide) (no_sum_2 (by decide))
      · refine @not_mem_candidates_a08_of_no_sub_div_sum 108 10 2 172 (by decide) (by decide) (no_sum_2 (by decide))
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 112 10 (by decide) (by decide)

set_option maxRecDepth 10000 in
lemma a08_eleven_eq_120 : a081512 11 = 120 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a08_iff_powerset]
    have h_120 : 0 < 120 := by decide
    refine ⟨h_120, ?_⟩
    let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 12, 15, 24, 40}
    use D
    have h_prop : D ⊆ (Nat.divisors 120) ∧ D.card = 11 ∧ D.sum id = 120 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · intro y hy
    by_cases h_card : (Nat.divisors y).card < 11
    · exact not_mem_candidates_a08_of_card_lt h_card
    · have h_all : ∀ y < 120, ¬ (Nat.divisors y).card < 11 → y = 60 ∨ y = 72 ∨ y = 84 ∨ y = 90 ∨ y = 96 ∨ y = 108 := by decide
      have h_y := h_all y hy h_card
      rcases h_y with rfl | rfl | rfl | rfl | rfl | rfl
      · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 60 11 (by decide) (by decide)
      · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 72 11 (by decide) (by decide)
      · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 84 11 (by decide) (by decide)
      · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 90 11 (by decide) (by decide)
      · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 96 11 (by decide) (by decide)
      · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 108 11 (by decide) (by decide)

set_option maxRecDepth 10000 in
lemma a08_twelve_eq_120 : a081512 12 = 120 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a08_iff_powerset]
    have h_120 : 0 < 120 := by decide
    refine ⟨h_120, ?_⟩
    let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 24, 30}
    use D
    have h_prop : D ⊆ (Nat.divisors 120) ∧ D.card = 12 ∧ D.sum id = 120 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · intro y hy
    by_cases h_card : (Nat.divisors y).card < 12
    · exact not_mem_candidates_a08_of_card_lt h_card
    · have h_all : ∀ y < 120, ¬ (Nat.divisors y).card < 12 → y = 60 ∨ y = 72 ∨ y = 84 ∨ y = 90 ∨ y = 96 ∨ y = 108 := by decide
      have h_y := h_all y hy h_card
      rcases h_y with rfl | rfl | rfl | rfl | rfl | rfl
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 60 12 (by decide) (by decide)
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 72 12 (by decide) (by decide)
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 84 12 (by decide) (by decide)
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 90 12 (by decide) (by decide)
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 96 12 (by decide) (by decide)
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 108 12 (by decide) (by decide)

set_option maxRecDepth 10000 in
lemma a08_thirteen_eq_180 : a081512 13 = 180 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a08_iff_powerset]
    have h_180 : 0 < 180 := by decide
    refine ⟨h_180, ?_⟩
    let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 9, 10, 12, 18, 20, 30, 60}
    use D
    have h_prop : D ⊆ (Nat.divisors 180) ∧ D.card = 13 ∧ D.sum id = 180 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · intro y hy
    by_cases h_card : (Nat.divisors y).card < 13
    · exact not_mem_candidates_a08_of_card_lt h_card
    · have h_all : ∀ y < 180, ¬ (Nat.divisors y).card < 13 → y = 120 ∨ y = 144 ∨ y = 168 := by decide
      have h_y := h_all y hy h_card
      rcases h_y with rfl | rfl | rfl
      · refine @not_mem_candidates_a08_of_no_sub_div_sum 120 13 3 240 (by decide) (by decide) (no_sum_3 (by decide))
      · refine @not_mem_candidates_a08_of_no_sub_div_sum 144 13 2 259 (by decide) (by decide) (no_sum_2 (by decide))
      · refine @not_mem_candidates_a08_of_no_sub_div_sum 168 13 3 312 (by decide) (by decide) (no_sum_3 (by decide))

set_option maxRecDepth 10000 in
lemma a08_fourteen_eq_180 : a081512 14 = 180 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a08_iff_powerset]
    have h_180 : 0 < 180 := by decide
    refine ⟨h_180, ?_⟩
    let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 45}
    use D
    have h_prop : D ⊆ (Nat.divisors 180) ∧ D.card = 14 ∧ D.sum id = 180 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · intro y hy
    by_cases h_card : (Nat.divisors y).card < 14
    · exact not_mem_candidates_a08_of_card_lt h_card
    · have h_all : ∀ y < 180, ¬ (Nat.divisors y).card < 14 → y = 120 ∨ y = 144 ∨ y = 168 := by decide
      have h_y := h_all y hy h_card
      rcases h_y with rfl | rfl | rfl
      · refine @not_mem_candidates_a08_of_no_sub_div_sum 120 14 2 240 (by decide) (by decide) (no_sum_2 (by decide))
      · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 144 14 (by decide) (by decide)
      · refine @not_mem_candidates_a08_of_no_sub_div_sum 168 14 2 312 (by decide) (by decide) (no_sum_2 (by decide))

set_option maxRecDepth 10000 in
lemma a08_fifteen_eq_240 : a081512 15 = 240 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a08_iff_powerset]
    have h_240 : 0 < 240 := by decide
    refine ⟨h_240, ?_⟩
    let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 16, 20, 30, 48, 60}
    use D
    have h_prop : D ⊆ (Nat.divisors 240) ∧ D.card = 15 ∧ D.sum id = 240 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · intro y hy
    by_cases h_card : (Nat.divisors y).card < 15
    · exact not_mem_candidates_a08_of_card_lt h_card
    · have h_all : ∀ y < 240, ¬ (Nat.divisors y).card < 15 → y = 120 ∨ y = 144 ∨ y = 168 ∨ y = 180 ∨ y = 210 ∨ y = 216 := by decide
      have h_y := h_all y hy h_card
      rcases h_y with rfl | rfl | rfl | rfl | rfl | rfl
      · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 120 15 (by decide) (by decide)
      · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 144 15 (by decide) (by decide)
      · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 168 15 (by decide) (by decide)
      · refine @not_mem_candidates_a08_of_no_sub_div_sum 180 15 3 366 (by decide) (by decide) (no_sum_3 (by decide))
      · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 210 15 (by decide) (by decide)
      · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 216 15 (by decide) (by decide)

set_option maxRecDepth 10000 in
lemma a08_sixteen_eq_360 : a081512 16 = 360 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a08_iff_powerset]
    have h_360 : 0 < 360 := by decide
    refine ⟨h_360, ?_⟩
    let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 30, 45, 72, 120}
    use D
    have h_prop : D ⊆ (Nat.divisors 360) ∧ D.card = 16 ∧ D.sum id = 360 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · intro y hy
    by_cases h_card : (Nat.divisors y).card < 16
    · exact not_mem_candidates_a08_of_card_lt h_card
    · by_cases hy_180 : y < 180
      · have h_all1 : ∀ y < 180, ¬ (Nat.divisors y).card < 16 → y = 120 ∨ y = 168 := by decide
        have h_y := h_all1 y hy_180 h_card
        rcases h_y with rfl | rfl
        · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 120 16 (by decide) (by decide)
        · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 168 16 (by decide) (by decide)
      · have hy_ge : 180 ≤ y := by omega
        have h_all2 : ∀ y, 180 ≤ y ∧ y < 360 → ¬ (Nat.divisors y).card < 16 → y = 180 ∨ y = 210 ∨ y = 216 ∨ y = 240 ∨ y = 252 ∨ y = 264 ∨ y = 270 ∨ y = 280 ∨ y = 288 ∨ y = 300 ∨ y = 312 ∨ y = 330 ∨ y = 336 := by decide
        have h_y := h_all2 y ⟨hy_ge, hy⟩ h_card
        rcases h_y with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · refine @not_mem_candidates_a08_of_no_sub_div_sum 180 16 2 366 (by decide) (by decide) (no_sum_2 (by decide))
        · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 210 16 (by decide) (by decide)
        · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 216 16 (by decide) (by decide)
        · refine @not_mem_candidates_a08_of_no_sub_div_sum 240 16 4 504 (by decide) (by decide) (no_sum_4 (by decide))
        · refine @not_mem_candidates_a08_of_no_sub_div_sum 252 16 2 476 (by decide) (by decide) (no_sum_2 (by decide))
        · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 264 16 (by decide) (by decide)
        · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 270 16 (by decide) (by decide)
        · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 280 16 (by decide) (by decide)
        · refine @not_mem_candidates_a08_of_no_sub_div_sum 288 16 2 531 (by decide) (by decide) (no_sum_2 (by decide))
        · refine @not_mem_candidates_a08_of_no_sub_div_sum 300 16 2 568 (by decide) (by decide) (no_sum_2 (by decide))
        · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 312 16 (by decide) (by decide)
        · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 330 16 (by decide) (by decide)
        · refine @not_mem_candidates_a08_of_no_sub_div_sum 336 16 4 656 (by decide) (by decide) (no_sum_4 (by decide))

set_option maxRecDepth 10000 in
lemma a08_seventeen_eq_360 : a081512 17 = 360 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a08_iff_powerset]
    have h_360 : 0 < 360 := by decide
    refine ⟨h_360, ?_⟩
    let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 40, 45, 72, 90}
    use D
    have h_prop : D ⊆ (Nat.divisors 360) ∧ D.card = 17 ∧ D.sum id = 360 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · intro y hy
    by_cases h_card : (Nat.divisors y).card < 17
    · exact not_mem_candidates_a08_of_card_lt h_card
    · by_cases hy_180 : y < 180
      · have h_all1 : ∀ y < 180, ¬ (Nat.divisors y).card < 17 → False := by decide
        exact False.elim (h_all1 y hy_180 h_card)
      · have hy_ge : 180 ≤ y := by omega
        have h_all2 : ∀ y, 180 ≤ y ∧ y < 360 → ¬ (Nat.divisors y).card < 17 → y = 180 ∨ y = 240 ∨ y = 252 ∨ y = 288 ∨ y = 300 ∨ y = 336 := by decide
        have h_y := h_all2 y ⟨hy_ge, hy⟩ h_card
        rcases h_y with rfl | rfl | rfl | rfl | rfl | rfl
        · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 180 17 (by decide) (by decide)
        · refine @not_mem_candidates_a08_of_no_sub_div_sum 240 17 3 504 (by decide) (by decide) (no_sum_3 (by decide))
        · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 252 17 (by decide) (by decide)
        · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 288 17 (by decide) (by decide)
        · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 300 17 (by decide) (by decide)
        · refine @not_mem_candidates_a08_of_no_sub_div_sum 336 17 3 656 (by decide) (by decide) (no_sum_3 (by decide))

set_option maxRecDepth 10000 in
lemma a08_eighteen_eq_360 : a081512 18 = 360 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a08_iff_powerset]
    have h_360 : 0 < 360 := by decide
    refine ⟨h_360, ?_⟩
    let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 30, 40, 45, 60, 72}
    use D
    have h_prop : D ⊆ (Nat.divisors 360) ∧ D.card = 18 ∧ D.sum id = 360 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · intro y hy
    by_cases h_card : (Nat.divisors y).card < 18
    · exact not_mem_candidates_a08_of_card_lt h_card
    · by_cases hy_180 : y < 180
      · have h_all1 : ∀ y < 180, ¬ (Nat.divisors y).card < 18 → False := by decide
        exact False.elim (h_all1 y hy_180 h_card)
      · have hy_ge : 180 ≤ y := by omega
        have h_all2 : ∀ y, 180 ≤ y ∧ y < 360 → ¬ (Nat.divisors y).card < 18 → y = 180 ∨ y = 240 ∨ y = 252 ∨ y = 288 ∨ y = 300 ∨ y = 336 := by decide
        have h_y := h_all2 y ⟨hy_ge, hy⟩ h_card
        rcases h_y with rfl | rfl | rfl | rfl | rfl | rfl
        · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 180 18 (by decide) (by decide)
        · refine @not_mem_candidates_a08_of_no_sub_div_sum 240 18 2 504 (by decide) (by decide) (no_sum_2 (by decide))
        · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 252 18 (by decide) (by decide)
        · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 288 18 (by decide) (by decide)
        · refine @not_mem_candidates_a08_eq_of_sum_divisors_ne_m 300 18 (by decide) (by decide)
        · refine @not_mem_candidates_a08_of_no_sub_div_sum 336 18 2 656 (by decide) (by decide) (no_sum_2 (by decide))

set_option maxRecDepth 10000 in
lemma a08_nineteen_eq_360 : a081512 19 = 360 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · rw [mem_candidates_a08_iff_powerset]
    have h_360 : 0 < 360 := by decide
    refine ⟨h_360, ?_⟩
    let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 30, 36, 40, 45, 72}
    use D
    have h_prop : D ⊆ (Nat.divisors 360) ∧ D.card = 19 ∧ D.sum id = 360 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · intro y hy
    by_cases h_card : (Nat.divisors y).card < 19
    · exact not_mem_candidates_a08_of_card_lt h_card
    · by_cases hy_180 : y < 180
      · have h_all1 : ∀ y < 180, ¬ (Nat.divisors y).card < 19 → False := by decide
        exact False.elim (h_all1 y hy_180 h_card)
      · have hy_ge : 180 ≤ y := by omega
        have h_all2 : ∀ y, 180 ≤ y ∧ y < 360 → ¬ (Nat.divisors y).card < 19 → y = 240 ∨ y = 336 := by decide
        have h_y := h_all2 y ⟨hy_ge, hy⟩ h_card
        rcases h_y with rfl | rfl
        · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 240 19 (by decide) (by decide)
        · refine @not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m 336 19 (by decide) (by decide)


lemma mem_candidates_a_of_mem_candidates_a08' {n m : ℕ} (hm : m ∈ candidates_a08 n)
    (h_L : ∀ L : ℕ, L ∣ m → L ≤ m / 2 → n ≤ (Nat.divisors L).card → ∀ D ⊆ L.divisors, D.card = n → D.sum id ≠ m) :
    m ∈ candidates_a n := by
  rw [mem_candidates_a_iff_powerset]
  rw [mem_candidates_a08_iff_powerset] at hm
  rcases hm with ⟨hm0, D, hD_pow, h_card, h_sum⟩
  refine ⟨hm0, D, hD_pow, h_card, h_sum, ?_⟩
  let L := D.lcm id
  have h_L_dvd : L ∣ m := by
    apply Finset.lcm_dvd
    intro x hx
    rw [Finset.mem_powerset] at hD_pow
    have h_div := hD_pow hx
    rw [Nat.mem_divisors] at h_div
    exact h_div.1
  by_contra h_ne
  have h_lt : L < m := by
    have : L ≤ m := Nat.le_of_dvd hm0 h_L_dvd
    omega
  have h_div2 : L ≤ m / 2 := div_le_of_dvd_of_lt h_L_dvd h_lt
  have h_L_nz : L ≠ 0 := by
    intro h_eq
    have : 0 ∣ m := h_eq ▸ h_L_dvd
    have : m = 0 := Nat.eq_zero_of_zero_dvd this
    omega
  have h_D_sub_L : D ⊆ L.divisors := by
    intro x hx
    rw [Nat.mem_divisors]
    refine ⟨Finset.dvd_lcm hx, h_L_nz⟩
  have h_card_le : n ≤ L.divisors.card := by
    rw [← h_card]
    exact Finset.card_le_card h_D_sub_L
  have h_sum_ne : D.sum id ≠ m := h_L L h_L_dvd h_div2 h_card_le D h_D_sub_L h_card
  exact h_sum_ne h_sum


lemma mem_candidates_a_of_mem_candidates_a08 {n m : ℕ} (hm : m ∈ candidates_a08 n)
    (h_L : ∀ L : ℕ, n ≤ (Nat.divisors L).card → 2 * L > m) :
    m ∈ candidates_a n := by
  rw [mem_candidates_a_iff_powerset]
  rw [mem_candidates_a08_iff_powerset] at hm
  rcases hm with ⟨hm0, D, hD_pow, h_card, h_sum⟩
  refine ⟨hm0, D, hD_pow, h_card, h_sum, ?_⟩
  let L := D.lcm id
  have h_L_dvd : L ∣ m := by
    apply Finset.lcm_dvd
    intro x hx
    rw [Finset.mem_powerset] at hD_pow
    have h_div := hD_pow hx
    rw [Nat.mem_divisors] at h_div
    exact h_div.1
  have h_L_nz : L ≠ 0 := by
    intro h_eq
    have : 0 ∣ m := h_eq ▸ h_L_dvd
    have : m = 0 := Nat.eq_zero_of_zero_dvd this
    omega
  have h_D_sub_L : D ⊆ L.divisors := by
    intro x hx
    rw [Nat.mem_divisors]
    refine ⟨Finset.dvd_lcm hx, h_L_nz⟩
  have h_card_le : n ≤ L.divisors.card := by
    rw [← h_card]
    exact Finset.card_le_card h_D_sub_L
  have h_2L_gt : 2 * L > m := h_L L h_card_le
  by_contra h_ne
  have h_lt : L < m := by
    have : L ≤ m := Nat.le_of_dvd hm0 h_L_dvd
    omega
  have h_div2 : L ≤ m / 2 := div_le_of_dvd_of_lt h_L_dvd h_lt
  omega



set_option maxRecDepth 10000 in
lemma a_witness_6 : a 6 ≤ 24 := by
  rw [a_eq_sInf_candidates_a]
  apply Nat.sInf_le
  rw [candidates_a, mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := {1, 2, 3, 4, 6, 8}
  use D
  refine ⟨by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 10000 in
lemma a_witness_8 : a 8 ≤ 60 := by
  rw [a_eq_sInf_candidates_a]
  apply Nat.sInf_le
  rw [candidates_a, mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := {1, 2, 3, 4, 5, 10, 15, 20}
  use D
  refine ⟨by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 10000 in
lemma a_witness_9 : a 9 ≤ 84 := by
  rw [a_eq_sInf_candidates_a]
  apply Nat.sInf_le
  rw [candidates_a, mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := {1, 2, 3, 4, 6, 7, 12, 21, 28}
  use D
  refine ⟨by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 10000 in
lemma a_witness_10 : a 10 ≤ 120 := by
  rw [a_eq_sInf_candidates_a]
  apply Nat.sInf_le
  rw [candidates_a, mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 15, 20, 24, 40}
  use D
  refine ⟨by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 10000 in
lemma a_witness_11 : a 11 ≤ 120 := by
  rw [a_eq_sInf_candidates_a]
  apply Nat.sInf_le
  rw [candidates_a, mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 12, 15, 24, 40}
  use D
  refine ⟨by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 10000 in
lemma a_witness_12 : a 12 ≤ 120 := by
  rw [a_eq_sInf_candidates_a]
  apply Nat.sInf_le
  rw [candidates_a, mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 24, 30}
  use D
  refine ⟨by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 10000 in
lemma a_witness_13 : a 13 ≤ 180 := by
  rw [a_eq_sInf_candidates_a]
  apply Nat.sInf_le
  rw [candidates_a, mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 9, 10, 12, 18, 20, 30, 60}
  use D
  refine ⟨by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 10000 in
lemma a_witness_14 : a 14 ≤ 180 := by
  rw [a_eq_sInf_candidates_a]
  apply Nat.sInf_le
  rw [candidates_a, mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 45}
  use D
  refine ⟨by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 10000 in
lemma a_witness_15 : a 15 ≤ 240 := by
  rw [a_eq_sInf_candidates_a]
  apply Nat.sInf_le
  rw [candidates_a, mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 16, 20, 30, 48, 60}
  use D
  refine ⟨by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 10000 in
lemma a_witness_16 : a 16 ≤ 360 := by
  rw [a_eq_sInf_candidates_a]
  apply Nat.sInf_le
  rw [candidates_a, mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 30, 45, 72, 120}
  use D
  refine ⟨by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 10000 in
lemma a_witness_17 : a 17 ≤ 360 := by
  rw [a_eq_sInf_candidates_a]
  apply Nat.sInf_le
  rw [candidates_a, mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 40, 45, 72, 90}
  use D
  refine ⟨by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 10000 in
lemma a_witness_18 : a 18 ≤ 360 := by
  rw [a_eq_sInf_candidates_a]
  apply Nat.sInf_le
  rw [candidates_a, mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 30, 40, 45, 60, 72}
  use D
  refine ⟨by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 10000 in
lemma a_witness_19 : a 19 ≤ 360 := by
  rw [a_eq_sInf_candidates_a]
  apply Nat.sInf_le
  rw [candidates_a, mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 30, 36, 40, 45, 72}
  use D
  refine ⟨by decide, by decide, by decide, by decide⟩

lemma not_mem_candidates_a08_23_of_sum_divisors_gt_2m {m : ℕ} (hm : (Nat.divisors m).card = 24)
    (h_sum : (Nat.divisors m).sum id > 2 * m) : m ∉ candidates_a08 23 := by
  intro h
  rw [mem_candidates_a08_iff_powerset] at h
  rcases h with ⟨hm0, D, hD_pow, h_card, h_sum_D⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_card_eq : D.card + 1 = (Nat.divisors m).card := by omega
  rcases sum_eq_sum_divisors_sub hD_pow h_card_eq with ⟨d, hd_mem, hd_sum⟩
  have hd_dvd : d ∣ m := Nat.mem_divisors.mp hd_mem |>.1
  have hd_le : d ≤ m := Nat.le_of_dvd hm0 hd_dvd
  omega

lemma not_mem_candidates_a08_24_of_sum_divisors_ne_m {m : ℕ} (hm : (Nat.divisors m).card = 24)
    (h_sum : (Nat.divisors m).sum id ≠ m) : m ∉ candidates_a08 24 := by
  intro h
  rw [mem_candidates_a08_iff_powerset] at h
  rcases h with ⟨hm0, D, hD_pow, h_card, h_sum_D⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_eq : D = Nat.divisors m := by
    apply Finset.eq_of_subset_of_card_le hD_pow
    omega
  rw [h_eq] at h_sum_D
  exact h_sum h_sum_D




set_option maxRecDepth 10000 in
lemma card_divisors_lt_20_chunk0 : ∀ m, m < 100 → (Nat.divisors m).card < 20 := by decide
set_option maxRecDepth 10000 in
lemma card_divisors_lt_20_chunk1 : ∀ m, 100 ≤ m ∧ m < 200 → (Nat.divisors m).card < 20 := by decide
set_option maxRecDepth 10000 in
lemma card_divisors_lt_20_chunk2 : ∀ m, 200 ≤ m ∧ m < 300 → m ≠ 240 → (Nat.divisors m).card < 20 := by decide
set_option maxRecDepth 10000 in
lemma card_divisors_lt_20_chunk3 : ∀ m, 300 ≤ m ∧ m < 400 → m ≠ 336 ∧ m ≠ 360 → (Nat.divisors m).card < 20 := by decide
set_option maxRecDepth 10000 in
lemma card_divisors_lt_20_chunk4 : ∀ m, 400 ≤ m ∧ m < 500 → m ≠ 420 ∧ m ≠ 432 ∧ m ≠ 480 → (Nat.divisors m).card < 20 := by decide
set_option maxRecDepth 10000 in
lemma card_divisors_lt_20_chunk5 : ∀ m, 500 ≤ m ∧ m < 600 → m ≠ 504 ∧ m ≠ 528 ∧ m ≠ 540 ∧ m ≠ 560 ∧ m ≠ 576 → (Nat.divisors m).card < 20 := by decide
set_option maxRecDepth 10000 in
lemma card_divisors_lt_20_chunk6 : ∀ m, 600 ≤ m ∧ m < 672 → m ≠ 600 ∧ m ≠ 624 ∧ m ≠ 630 ∧ m ≠ 648 ∧ m ≠ 660 → (Nat.divisors m).card < 20 := by decide

lemma card_divisors_lt_21_chunk1 : ∀ m, 100 ≤ m ∧ m < 200 → (Nat.divisors m).card < 21 := by
  intro m hm
  have := card_divisors_lt_20_chunk1 m hm
  omega

lemma card_divisors_lt_21_chunk2 : ∀ m, 200 ≤ m ∧ m < 300 → (Nat.divisors m).card < 21 := by
  intro m hm
  by_cases h : m = 240
  · subst h; decide
  · have := card_divisors_lt_20_chunk2 m hm h
    omega

lemma card_divisors_lt_21_chunk3 : ∀ m, 300 ≤ m ∧ m < 400 → m ≠ 360 → (Nat.divisors m).card < 21 := by
  intro m hm h360
  by_cases h : m = 336
  · subst h; decide
  · have := card_divisors_lt_20_chunk3 m hm ⟨h, h360⟩
    omega

lemma card_divisors_lt_21_chunk4 : ∀ m, 400 ≤ m ∧ m < 500 → m ≠ 420 ∧ m ≠ 480 → (Nat.divisors m).card < 21 := by
  intro m hm ⟨h420, h480⟩
  by_cases h : m = 432
  · subst h; decide
  · have := card_divisors_lt_20_chunk4 m hm ⟨h420, ⟨h, h480⟩⟩
    omega

lemma card_divisors_lt_21_chunk5 : ∀ m, 500 ≤ m ∧ m < 600 → m ≠ 504 ∧ m ≠ 540 ∧ m ≠ 576 → (Nat.divisors m).card < 21 := by
  intro m hm ⟨h504, ⟨h540, h576⟩⟩
  by_cases h1 : m = 528
  · subst h1; decide
  by_cases h2 : m = 560
  · subst h2; decide
  · have := card_divisors_lt_20_chunk5 m hm ⟨h504, ⟨h1, ⟨h540, ⟨h2, h576⟩⟩⟩⟩
    omega

lemma card_divisors_lt_21_chunk6 : ∀ m, 600 ≤ m ∧ m < 700 → m ≠ 600 ∧ m ≠ 630 ∧ m ≠ 660 ∧ m ≠ 672 → (Nat.divisors m).card < 21 := by
  intro m hm h
  by_cases h2 : m < 672
  · rcases h with ⟨h600, h630, h660, h672⟩
    by_cases h1 : m = 624
    · subst h1; decide
    by_cases h3 : m = 648
    · subst h3; decide
    · have := card_divisors_lt_20_chunk6 m ⟨hm.1, h2⟩ ⟨h600, ⟨h1, ⟨h630, ⟨h3, h660⟩⟩⟩⟩
      omega
  · have h_all : ∀ y, 672 ≤ y ∧ y < 700 → (Nat.divisors y).card < 21 := by decide
    exact h_all m ⟨by omega, by omega⟩

set_option maxRecDepth 30000 in
lemma card_divisors_lt_21_chunk7 : ∀ m, 700 ≤ m ∧ m < 720 → (Nat.divisors m).card < 21 := by decide

lemma card_divisors_lt_22_chunk1 : ∀ m, 100 ≤ m ∧ m < 200 → (Nat.divisors m).card < 22 := by
  intro m hm
  have := card_divisors_lt_21_chunk1 m hm
  omega

lemma card_divisors_lt_22_chunk2 : ∀ m, 200 ≤ m ∧ m < 300 → (Nat.divisors m).card < 22 := by
  intro m hm
  have := card_divisors_lt_21_chunk2 m hm
  omega

lemma card_divisors_lt_22_chunk3 : ∀ m, 300 ≤ m ∧ m < 400 → m ≠ 360 → (Nat.divisors m).card < 22 := by
  intro m hm h
  have := card_divisors_lt_21_chunk3 m hm h
  omega

lemma card_divisors_lt_22_chunk4 : ∀ m, 400 ≤ m ∧ m < 500 → m ≠ 420 ∧ m ≠ 480 → (Nat.divisors m).card < 22 := by
  intro m hm h
  have := card_divisors_lt_21_chunk4 m hm h
  omega

lemma card_divisors_lt_22_chunk5 : ∀ m, 500 ≤ m ∧ m < 600 → m ≠ 504 ∧ m ≠ 540 → (Nat.divisors m).card < 22 := by
  intro m hm ⟨h504, h540⟩
  by_cases h : m = 576
  · subst h; decide
  · have := card_divisors_lt_21_chunk5 m hm ⟨h504, ⟨h540, h⟩⟩
    omega

lemma card_divisors_lt_22_chunk6 : ∀ m, 600 ≤ m ∧ m < 700 → m ≠ 600 ∧ m ≠ 630 ∧ m ≠ 660 ∧ m ≠ 672 → (Nat.divisors m).card < 22 := by
  intro m hm h
  have := card_divisors_lt_21_chunk6 m hm h
  omega

lemma card_divisors_lt_22_chunk7 : ∀ m, 700 ≤ m ∧ m < 720 → (Nat.divisors m).card < 22 := by
  intro m hm
  have := card_divisors_lt_21_chunk7 m hm
  omega

lemma card_divisors_lt_23_chunk1 : ∀ m, 100 ≤ m ∧ m < 200 → (Nat.divisors m).card < 23 := by
  intro m hm
  have := card_divisors_lt_22_chunk1 m hm
  omega

lemma card_divisors_lt_23_chunk2 : ∀ m, 200 ≤ m ∧ m < 300 → (Nat.divisors m).card < 23 := by
  intro m hm
  have := card_divisors_lt_22_chunk2 m hm
  omega

lemma card_divisors_lt_23_chunk3 : ∀ m, 300 ≤ m ∧ m < 400 → m ≠ 360 → (Nat.divisors m).card < 23 := by
  intro m hm h
  have := card_divisors_lt_22_chunk3 m hm h
  omega

lemma card_divisors_lt_23_chunk4 : ∀ m, 400 ≤ m ∧ m < 500 → m ≠ 420 ∧ m ≠ 480 → (Nat.divisors m).card < 23 := by
  intro m hm h
  have := card_divisors_lt_22_chunk4 m hm h
  omega

lemma card_divisors_lt_23_chunk5 : ∀ m, 500 ≤ m ∧ m < 600 → m ≠ 504 ∧ m ≠ 540 → (Nat.divisors m).card < 23 := by
  intro m hm h
  have := card_divisors_lt_22_chunk5 m hm h
  omega

lemma card_divisors_lt_23_chunk6 : ∀ m, 600 ≤ m ∧ m < 700 → m ≠ 600 ∧ m ≠ 630 ∧ m ≠ 660 ∧ m ≠ 672 → (Nat.divisors m).card < 23 := by
  intro m hm h
  have := card_divisors_lt_22_chunk6 m hm h
  omega

lemma card_divisors_lt_23_chunk7 : ∀ m, 700 ≤ m ∧ m < 720 → (Nat.divisors m).card < 23 := by
  intro m hm
  have := card_divisors_lt_22_chunk7 m hm
  omega

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma L_ge_360_of_card_divisors_ge_23 {L : ℕ} (h : 23 ≤ (Nat.divisors L).card) : 360 ≤ L := by
  by_contra h_lt
  have h_lt360 : L < 360 := by omega
  have h_dec : ∀ m, m < 360 → 23 ≤ (Nat.divisors m).card → 360 ≤ m := by decide
  have := h_dec L h_lt360 h
  omega

lemma card_divisors_lt_23_of_mem_range : ∀ m, m < 720 →
    (m ≠ 360 ∧ m ≠ 420 ∧ m ≠ 480 ∧ m ≠ 504 ∧ m ≠ 540 ∧ m ≠ 600 ∧ m ≠ 630 ∧ m ≠ 660 ∧ m ≠ 672) →
    (Nat.divisors m).card < 23 := by
  intro m hm h_not
  rcases h_not with ⟨h360, h420, h480, h504, h540, h600, h630, h660, h672⟩
  by_cases h0 : m < 100
  · have := card_divisors_lt_20_chunk0 m h0
    omega
  by_cases h1 : m < 200
  · exact card_divisors_lt_23_chunk1 m ⟨by omega, h1⟩
  by_cases h2 : m < 300
  · exact card_divisors_lt_23_chunk2 m ⟨by omega, h2⟩
  by_cases h3 : m < 400
  · exact card_divisors_lt_23_chunk3 m ⟨by omega, h3⟩ h360
  by_cases h4 : m < 500
  · exact card_divisors_lt_23_chunk4 m ⟨by omega, h4⟩ ⟨h420, h480⟩
  by_cases h5 : m < 600
  · exact card_divisors_lt_23_chunk5 m ⟨by omega, h5⟩ ⟨h504, h540⟩
  by_cases h6 : m < 700
  · exact card_divisors_lt_23_chunk6 m ⟨by omega, h6⟩ ⟨h600, ⟨h630, ⟨h660, h672⟩⟩⟩
  · exact card_divisors_lt_23_chunk7 m ⟨by omega, hm⟩

set_option maxRecDepth 10000 in
lemma m_ge_720_of_mem_candidates_a08 {n m : ℕ} (hn : 23 ≤ n) (hm : m ∈ candidates_a08 n) : 720 ≤ m := by
  have h_div_card : n ≤ (Nat.divisors m).card := by
    rcases hm with ⟨_, D, hD_div, hD_card, _⟩
    rw [← hD_card]
    exact Finset.card_le_card hD_div
  have h_div_card23 : 23 ≤ (Nat.divisors m).card := by omega
  have h_ge360 : 360 ≤ m := L_ge_360_of_card_divisors_ge_23 h_div_card23
  by_contra h_lt
  have h_lt720 : m < 720 := by omega
  by_cases h_special : m = 360 ∨ m = 420 ∨ m = 480 ∨ m = 504 ∨ m = 540 ∨ m = 600 ∨ m = 630 ∨ m = 660 ∨ m = 672
  · rcases h_special with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hn_le24 : n ≤ 24 := by
        have : (Nat.divisors 360).card = 24 := by decide
        omega
      interval_cases n
      · exact not_mem_candidates_a08_23_of_sum_divisors_gt_2m (by decide) (by decide) hm
      · exact not_mem_candidates_a08_24_of_sum_divisors_ne_m (by decide) (by decide) hm
    · have hn_le24 : n ≤ 24 := by
        have : (Nat.divisors 420).card = 24 := by decide
        omega
      interval_cases n
      · exact not_mem_candidates_a08_23_of_sum_divisors_gt_2m (by decide) (by decide) hm
      · exact not_mem_candidates_a08_24_of_sum_divisors_ne_m (by decide) (by decide) hm
    · have hn_le24 : n ≤ 24 := by
        have : (Nat.divisors 480).card = 24 := by decide
        omega
      interval_cases n
      · exact not_mem_candidates_a08_23_of_sum_divisors_gt_2m (by decide) (by decide) hm
      · exact not_mem_candidates_a08_24_of_sum_divisors_ne_m (by decide) (by decide) hm
    · have hn_le24 : n ≤ 24 := by
        have : (Nat.divisors 504).card = 24 := by decide
        omega
      interval_cases n
      · exact not_mem_candidates_a08_23_of_sum_divisors_gt_2m (by decide) (by decide) hm
      · exact not_mem_candidates_a08_24_of_sum_divisors_ne_m (by decide) (by decide) hm
    · have hn_le24 : n ≤ 24 := by
        have : (Nat.divisors 540).card = 24 := by decide
        omega
      interval_cases n
      · exact not_mem_candidates_a08_23_of_sum_divisors_gt_2m (by decide) (by decide) hm
      · exact not_mem_candidates_a08_24_of_sum_divisors_ne_m (by decide) (by decide) hm
    · have hn_le24 : n ≤ 24 := by
        have : (Nat.divisors 600).card = 24 := by decide
        omega
      interval_cases n
      · exact not_mem_candidates_a08_23_of_sum_divisors_gt_2m (by decide) (by decide) hm
      · exact not_mem_candidates_a08_24_of_sum_divisors_ne_m (by decide) (by decide) hm
    · have hn_le24 : n ≤ 24 := by
        have : (Nat.divisors 630).card = 24 := by decide
        omega
      interval_cases n
      · exact not_mem_candidates_a08_23_of_sum_divisors_gt_2m (by decide) (by decide) hm
      · exact not_mem_candidates_a08_24_of_sum_divisors_ne_m (by decide) (by decide) hm
    · have hn_le24 : n ≤ 24 := by
        have : (Nat.divisors 660).card = 24 := by decide
        omega
      interval_cases n
      · exact not_mem_candidates_a08_23_of_sum_divisors_gt_2m (by decide) (by decide) hm
      · exact not_mem_candidates_a08_24_of_sum_divisors_ne_m (by decide) (by decide) hm
    · have hn_le24 : n ≤ 24 := by
        have : (Nat.divisors 672).card = 24 := by decide
        omega
      interval_cases n
      · exact not_mem_candidates_a08_23_of_sum_divisors_gt_2m (by decide) (by decide) hm
      · exact not_mem_candidates_a08_24_of_sum_divisors_ne_m (by decide) (by decide) hm
  · have h_not : m ≠ 360 ∧ m ≠ 420 ∧ m ≠ 480 ∧ m ≠ 504 ∧ m ≠ 540 ∧ m ≠ 600 ∧ m ≠ 630 ∧ m ≠ 660 ∧ m ≠ 672 := by tauto
    have h_card : (Nat.divisors m).card < 23 := card_divisors_lt_23_of_mem_range m h_lt720 h_not
    omega

lemma witness_mem_candidates_a08 (n : ℕ) (hn : 6 ≤ n) : 24 * 2^(n-6) ∈ candidates_a08 n := by
  rw [mem_candidates_a08_iff_powerset]
  refine ⟨by positivity, D_witness_ge_6 (n-6), ?_, ?_, ?_⟩
  · rw [Finset.mem_powerset]
    intro x hx
    rw [Nat.mem_divisors]
    refine ⟨divisors_D_witness_ge_6 (n-6) x hx, by positivity⟩
  · have h_card := card_D_witness_ge_6 (n-6)
    omega
  · have h_sum := sum_D_witness_ge_6 (n-6)
    exact h_sum

lemma a08_mem (n : ℕ) (hn : 6 ≤ n) : a081512 n ∈ candidates_a08 n := by
  rw [a081512_eq_sInf_candidates_a08]
  apply Nat.sInf_mem
  use 24 * 2^(n-6)
  exact witness_mem_candidates_a08 n hn


lemma mul_two_le_of_dvd_of_lt {d m : ℕ} (hm0 : 0 < m) (h_dvd : d ∣ m) (h_lt : d < m) : 2 * d ≤ m := by
  rcases h_dvd with ⟨k, rfl⟩
  have h_k : 2 ≤ k := by
    by_contra h_contr
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · simp at hm0
    · simp at h_lt
  rw [mul_comm d k]
  exact Nat.mul_le_mul_right d h_k

lemma mul_three_le_of_dvd_of_lt {d m : ℕ} (hm0 : 0 < m) (h_dvd : d ∣ m) (h_lt1 : d < m) (h_lt2 : 2 * d < m) : 3 * d ≤ m := by
  rcases h_dvd with ⟨k, rfl⟩
  have h_k : 3 ≤ k := by
    by_contra h_contr
    have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl | rfl
    · simp at hm0
    · simp at h_lt1
    · rw [mul_comm] at h_lt2; simp at h_lt2
  rw [mul_comm d k]
  exact Nat.mul_le_mul_right d h_k

lemma mul_four_le_of_dvd_of_lt {d m : ℕ} (hm0 : 0 < m) (h_dvd : d ∣ m) (h_lt1 : d < m) (h_lt2 : 2 * d < m) (h_lt3 : 3 * d < m) : 4 * d ≤ m := by
  rcases h_dvd with ⟨k, rfl⟩
  have h_k : 4 ≤ k := by
    by_contra h_contr
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · simp at hm0
    · simp at h_lt1
    · rw [mul_comm] at h_lt2; simp at h_lt2
    · rw [mul_comm] at h_lt3; simp at h_lt3
  rw [mul_comm d k]
  exact Nat.mul_le_mul_right d h_k

lemma sum_two_distinct_divisors_bounds_sorted {m x y : ℕ} (hm : 0 < m) (hx : x ∈ Nat.divisors m) (hy : y ∈ Nat.divisors m)
    (h_xy : x < y) :
    x + y ≤ m + m / 2 := by
  have hx_dvd : x ∣ m := (Nat.mem_divisors.mp hx).1
  have hy_dvd : y ∣ m := (Nat.mem_divisors.mp hy).1
  have hy_le : y ≤ m := Nat.le_of_dvd hm hy_dvd
  have hx_lt : x < m := by omega
  have hx_le2 := div_le_of_dvd_of_lt hx_dvd hx_lt
  omega

lemma sum_two_distinct_divisors_bounds {m x y : ℕ} (hm : 0 < m) (hx : x ∈ Nat.divisors m) (hy : y ∈ Nat.divisors m)
    (hxy : x ≠ y) :
    x + y ≤ m + m / 2 := by
  rcases lt_or_gt_of_ne hxy with h_xy_lt | h_xy_gt
  · exact sum_two_distinct_divisors_bounds_sorted hm hx hy h_xy_lt
  · rw [add_comm]
    exact sum_two_distinct_divisors_bounds_sorted hm hy hx h_xy_gt

lemma sum_three_distinct_divisors_bounds_sorted {m x y z : ℕ} (hm : 0 < m) (hx : x ∈ Nat.divisors m) (hy : y ∈ Nat.divisors m) (hz : z ∈ Nat.divisors m)
    (h_xy : x < y) (h_yz : y < z) :
    x + y + z ≤ m + m / 2 + m / 3 := by
  have hx_dvd : x ∣ m := (Nat.mem_divisors.mp hx).1
  have hy_dvd : y ∣ m := (Nat.mem_divisors.mp hy).1
  have hz_dvd : z ∣ m := (Nat.mem_divisors.mp hz).1
  have hz_le : z ≤ m := Nat.le_of_dvd hm hz_dvd
  have hy_lt : y < m := by omega
  have hy_le2 := mul_two_le_of_dvd_of_lt hm hy_dvd hy_lt
  have hx_lt1 : x < m := by omega
  have hx_lt2 : 2 * x < m := by omega
  have hx_le3 := mul_three_le_of_dvd_of_lt hm hx_dvd hx_lt1 hx_lt2
  have hy_le_half : y ≤ m / 2 := by omega
  have hx_le_third : x ≤ m / 3 := by omega
  omega

lemma sum_three_distinct_divisors_bounds {m x y z : ℕ} (hm : 0 < m) (hx : x ∈ Nat.divisors m) (hy : y ∈ Nat.divisors m) (hz : z ∈ Nat.divisors m)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    x + y + z ≤ m + m / 2 + m / 3 := by
  rcases lt_or_gt_of_ne hxy with h_xy_lt | h_xy_gt
  · rcases lt_or_gt_of_ne hxz with h_xz_lt | h_xz_gt
    · rcases lt_or_gt_of_ne hyz with h_yz_lt | h_yz_gt
      · exact sum_three_distinct_divisors_bounds_sorted hm hx hy hz h_xy_lt h_yz_lt
      · have h1 : x + y + z = x + z + y := by omega
        rw [h1]
        exact sum_three_distinct_divisors_bounds_sorted hm hx hz hy h_xz_lt h_yz_gt
    · have h1 : x + y + z = z + x + y := by omega
      rw [h1]
      have h_zx : z < x := by omega
      exact sum_three_distinct_divisors_bounds_sorted hm hz hx hy h_zx h_xy_lt
  · rcases lt_or_gt_of_ne hxz with h_xz_lt | h_xz_gt
    · have h1 : x + y + z = y + x + z := by omega
      rw [h1]
      have h_yx : y < x := by omega
      exact sum_three_distinct_divisors_bounds_sorted hm hy hx hz h_yx h_xz_lt
    · rcases lt_or_gt_of_ne hyz with h_yz_lt | h_yz_gt
      · have h1 : x + y + z = y + z + x := by omega
        rw [h1]
        have h_zx : z < x := by omega
        exact sum_three_distinct_divisors_bounds_sorted hm hy hz hx h_yz_lt h_zx
      · have h1 : x + y + z = z + y + x := by omega
        rw [h1]
        have h_zy : z < y := by omega
        have h_yx : y < x := by omega
        exact sum_three_distinct_divisors_bounds_sorted hm hz hy hx h_zy h_yx

set_option maxRecDepth 10000 in
lemma le_70_of_mem_div_630_and_not_mem {w : ℕ} (hw : w ∈ Nat.divisors 630) (hn : w ∉ ({90, 105, 126, 210, 315, 630} : Finset ℕ)) : w ≤ 70 := by
  revert w hw hn; decide

set_option maxRecDepth 10000 in
lemma le_110_of_mem_div_660_and_not_mem {w : ℕ} (hw : w ∈ Nat.divisors 660) (hn : w ∉ ({132, 165, 220, 330, 660} : Finset ℕ)) : w ≤ 110 := by
  revert w hw hn; decide

set_option maxRecDepth 10000 in
lemma sum_four_distinct_divisors_bounds_w_le_70 {w x y z : ℕ} (hw : w ∈ Nat.divisors 630) (hx : x ∈ Nat.divisors 630) (hy : y ∈ Nat.divisors 630) (hz : z ∈ Nat.divisors 630)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hw_le : w ≤ 70) :
    w + x + y + z < 1242 := by
  have h_sum3 := sum_three_distinct_divisors_bounds (by decide) hx hy hz hxy hxz hyz
  omega

set_option maxRecDepth 10000 in
lemma sum_four_distinct_divisors_bounds_w_le_110 {w x y z : ℕ} (hw : w ∈ Nat.divisors 660) (hx : x ∈ Nat.divisors 660) (hy : y ∈ Nat.divisors 660) (hz : z ∈ Nat.divisors 660)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hw_le : w ≤ 110) :
    w + x + y + z < 1356 := by
  have h_sum3 := sum_three_distinct_divisors_bounds (by decide) hx hy hz hxy hxz hyz
  omega

lemma le_div4_of_mem_divisors_and_not_mem {m d : ℕ} (hm : 0 < m) (hd : d ∈ Nat.divisors m) (hn : d ∉ ({m, m / 2, m / 3} : Finset ℕ)) : d ≤ m / 4 := by
  have hd_dvd : d ∣ m := (Nat.mem_divisors.mp hd).1
  have hd_lt1 : d < m := by
    by_contra h_contr
    have : d = m := by
      have := Nat.le_of_dvd hm hd_dvd
      omega
    simp [this] at hn
  have hd_lt2 : 2 * d < m := by
    by_contra h_contr
    have : 2 * d ≤ m := mul_two_le_of_dvd_of_lt hm hd_dvd hd_lt1
    have : 2 * d = m := by omega
    have : d = m / 2 := by omega
    simp [this] at hn
  have hd_lt3 : 3 * d < m := by
    by_contra h_contr
    have : 3 * d ≤ m := mul_three_le_of_dvd_of_lt hm hd_dvd hd_lt1 hd_lt2
    have : 3 * d = m := by omega
    have : d = m / 3 := by omega
    simp [this] at hn
  have : 4 * d ≤ m := mul_four_le_of_dvd_of_lt hm hd_dvd hd_lt1 hd_lt2 hd_lt3
  omega

lemma exists_le_div4_of_four_distinct {m w x y z : ℕ} (hm : 0 < m) (hw : w ∈ Nat.divisors m) (hx : x ∈ Nat.divisors m) (hy : y ∈ Nat.divisors m) (hz : z ∈ Nat.divisors m)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    w ≤ m / 4 ∨ x ≤ m / 4 ∨ y ≤ m / 4 ∨ z ≤ m / 4 := by
  by_cases hw_mem : w ∈ ({m, m / 2, m / 3} : Finset ℕ)
  · by_cases hx_mem : x ∈ ({m, m / 2, m / 3} : Finset ℕ)
    · by_cases hy_mem : y ∈ ({m, m / 2, m / 3} : Finset ℕ)
      · by_cases hz_mem : z ∈ ({m, m / 2, m / 3} : Finset ℕ)
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hw_mem hx_mem hy_mem hz_mem
          rcases hw_mem with rfl | rfl | rfl <;>
          rcases hx_mem with rfl | rfl | rfl <;>
          rcases hy_mem with rfl | rfl | rfl <;>
          rcases hz_mem with rfl | rfl | rfl <;>
          omega
        · right; right; right
          exact le_div4_of_mem_divisors_and_not_mem hm hz hz_mem
      · right; right; left
        exact le_div4_of_mem_divisors_and_not_mem hm hy hy_mem
    · right; left
      exact le_div4_of_mem_divisors_and_not_mem hm hx hx_mem
  · left
    exact le_div4_of_mem_divisors_and_not_mem hm hw hw_mem


set_option maxRecDepth 10000 in
lemma no_four_divisors_360 : ∀ D ⊆ Nat.divisors 360, D.card = 4 → D.sum id ≠ 810 := by
  intro D hD h_card
  rcases card_eq_four.mp h_card with ⟨w, x, y, z, hwx, hwy, hwz, hxy, hxz, hyz, rfl⟩
  have hw : w ∈ Nat.divisors 360 := hD (by simp)
  have hx : x ∈ Nat.divisors 360 := hD (by simp)
  have hy : y ∈ Nat.divisors 360 := hD (by simp)
  have hz : z ∈ Nat.divisors 360 := hD (by simp)
  have h_sum : ({w, x, y, z} : Finset ℕ).sum id = w + x + y + z := by
    rw [sum_insert, sum_insert, sum_insert, sum_singleton]
    · dsimp [id]; omega
    · rwa [Finset.mem_singleton]
    · simp [hxy, hxz]
    · simp [hwx, hwy, hwz]
  rw [h_sum]
  have h_cases := exists_le_div4_of_four_distinct (by decide) hw hx hy hz hwx hwy hwz hxy hxz hyz
  have h_sum3_w := sum_three_distinct_divisors_bounds (by decide) hx hy hz hxy hxz hyz
  have h_sum3_x := sum_three_distinct_divisors_bounds (by decide) hw hy hz hwy hwz hyz
  have h_sum3_y := sum_three_distinct_divisors_bounds (by decide) hw hx hz hwx hwz hxz
  have h_sum3_z := sum_three_distinct_divisors_bounds (by decide) hw hx hy hwx hwy hxy
  rcases h_cases with hw_le | hx_le | hy_le | hz_le <;> omega

set_option maxRecDepth 10000 in
lemma no_four_divisors_420 : ∀ D ⊆ Nat.divisors 420, D.card = 4 → D.sum id ≠ 924 := by
  intro D hD h_card
  rcases card_eq_four.mp h_card with ⟨w, x, y, z, hwx, hwy, hwz, hxy, hxz, hyz, rfl⟩
  have hw : w ∈ Nat.divisors 420 := hD (by simp)
  have hx : x ∈ Nat.divisors 420 := hD (by simp)
  have hy : y ∈ Nat.divisors 420 := hD (by simp)
  have hz : z ∈ Nat.divisors 420 := hD (by simp)
  have h_sum : ({w, x, y, z} : Finset ℕ).sum id = w + x + y + z := by
    rw [sum_insert, sum_insert, sum_insert, sum_singleton]
    · dsimp [id]; omega
    · rwa [Finset.mem_singleton]
    · simp [hxy, hxz]
    · simp [hwx, hwy, hwz]
  rw [h_sum]
  have h_cases := exists_le_div4_of_four_distinct (by decide) hw hx hy hz hwx hwy hwz hxy hxz hyz
  have h_sum3_w := sum_three_distinct_divisors_bounds (by decide) hx hy hz hxy hxz hyz
  have h_sum3_x := sum_three_distinct_divisors_bounds (by decide) hw hy hz hwy hwz hyz
  have h_sum3_y := sum_three_distinct_divisors_bounds (by decide) hw hx hz hwx hwz hxz
  have h_sum3_z := sum_three_distinct_divisors_bounds (by decide) hw hx hy hwx hwy hxy
  rcases h_cases with hw_le | hx_le | hy_le | hz_le <;> omega

set_option maxRecDepth 10000 in
lemma no_four_divisors_480 : ∀ D ⊆ Nat.divisors 480, D.card = 4 → D.sum id ≠ 1032 := by
  intro D hD h_card
  rcases card_eq_four.mp h_card with ⟨w, x, y, z, hwx, hwy, hwz, hxy, hxz, hyz, rfl⟩
  have hw : w ∈ Nat.divisors 480 := hD (by simp)
  have hx : x ∈ Nat.divisors 480 := hD (by simp)
  have hy : y ∈ Nat.divisors 480 := hD (by simp)
  have hz : z ∈ Nat.divisors 480 := hD (by simp)
  have h_sum : ({w, x, y, z} : Finset ℕ).sum id = w + x + y + z := by
    rw [sum_insert, sum_insert, sum_insert, sum_singleton]
    · dsimp [id]; omega
    · rwa [Finset.mem_singleton]
    · simp [hxy, hxz]
    · simp [hwx, hwy, hwz]
  rw [h_sum]
  have h_cases := exists_le_div4_of_four_distinct (by decide) hw hx hy hz hwx hwy hwz hxy hxz hyz
  have h_sum3_w := sum_three_distinct_divisors_bounds (by decide) hx hy hz hxy hxz hyz
  have h_sum3_x := sum_three_distinct_divisors_bounds (by decide) hw hy hz hwy hwz hyz
  have h_sum3_y := sum_three_distinct_divisors_bounds (by decide) hw hx hz hwx hwz hxz
  have h_sum3_z := sum_three_distinct_divisors_bounds (by decide) hw hx hy hwx hwy hxy
  rcases h_cases with hw_le | hx_le | hy_le | hz_le <;> omega

set_option maxRecDepth 10000 in
lemma no_four_divisors_504 : ∀ D ⊆ Nat.divisors 504, D.card = 4 → D.sum id ≠ 1056 := by
  intro D hD h_card
  rcases card_eq_four.mp h_card with ⟨w, x, y, z, hwx, hwy, hwz, hxy, hxz, hyz, rfl⟩
  have hw : w ∈ Nat.divisors 504 := hD (by simp)
  have hx : x ∈ Nat.divisors 504 := hD (by simp)
  have hy : y ∈ Nat.divisors 504 := hD (by simp)
  have hz : z ∈ Nat.divisors 504 := hD (by simp)
  have h_sum : ({w, x, y, z} : Finset ℕ).sum id = w + x + y + z := by
    rw [sum_insert, sum_insert, sum_insert, sum_singleton]
    · dsimp [id]; omega
    · rwa [Finset.mem_singleton]
    · simp [hxy, hxz]
    · simp [hwx, hwy, hwz]
  rw [h_sum]
  have h_cases := exists_le_div4_of_four_distinct (by decide) hw hx hy hz hwx hwy hwz hxy hxz hyz
  have h_sum3_w := sum_three_distinct_divisors_bounds (by decide) hx hy hz hxy hxz hyz
  have h_sum3_x := sum_three_distinct_divisors_bounds (by decide) hw hy hz hwy hwz hyz
  have h_sum3_y := sum_three_distinct_divisors_bounds (by decide) hw hx hz hwx hwz hxz
  have h_sum3_z := sum_three_distinct_divisors_bounds (by decide) hw hx hy hwx hwy hxy
  rcases h_cases with hw_le | hx_le | hy_le | hz_le <;> omega

set_option maxRecDepth 10000 in
lemma no_four_divisors_540 : ∀ D ⊆ Nat.divisors 540, D.card = 4 → D.sum id ≠ 1140 := by
  intro D hD h_card
  rcases card_eq_four.mp h_card with ⟨w, x, y, z, hwx, hwy, hwz, hxy, hxz, hyz, rfl⟩
  have hw : w ∈ Nat.divisors 540 := hD (by simp)
  have hx : x ∈ Nat.divisors 540 := hD (by simp)
  have hy : y ∈ Nat.divisors 540 := hD (by simp)
  have hz : z ∈ Nat.divisors 540 := hD (by simp)
  have h_sum : ({w, x, y, z} : Finset ℕ).sum id = w + x + y + z := by
    rw [sum_insert, sum_insert, sum_insert, sum_singleton]
    · dsimp [id]; omega
    · rwa [Finset.mem_singleton]
    · simp [hxy, hxz]
    · simp [hwx, hwy, hwz]
  rw [h_sum]
  have h_cases := exists_le_div4_of_four_distinct (by decide) hw hx hy hz hwx hwy hwz hxy hxz hyz
  have h_sum3_w := sum_three_distinct_divisors_bounds (by decide) hx hy hz hxy hxz hyz
  have h_sum3_x := sum_three_distinct_divisors_bounds (by decide) hw hy hz hwy hwz hyz
  have h_sum3_y := sum_three_distinct_divisors_bounds (by decide) hw hx hz hwx hwz hxz
  have h_sum3_z := sum_three_distinct_divisors_bounds (by decide) hw hx hy hwx hwy hxy
  rcases h_cases with hw_le | hx_le | hy_le | hz_le <;> omega

set_option maxRecDepth 10000 in
lemma no_four_divisors_600 : ∀ D ⊆ Nat.divisors 600, D.card = 4 → D.sum id ≠ 1260 := by
  intro D hD h_card
  rcases card_eq_four.mp h_card with ⟨w, x, y, z, hwx, hwy, hwz, hxy, hxz, hyz, rfl⟩
  have hw : w ∈ Nat.divisors 600 := hD (by simp)
  have hx : x ∈ Nat.divisors 600 := hD (by simp)
  have hy : y ∈ Nat.divisors 600 := hD (by simp)
  have hz : z ∈ Nat.divisors 600 := hD (by simp)
  have h_sum : ({w, x, y, z} : Finset ℕ).sum id = w + x + y + z := by
    rw [sum_insert, sum_insert, sum_insert, sum_singleton]
    · dsimp [id]; omega
    · rwa [Finset.mem_singleton]
    · simp [hxy, hxz]
    · simp [hwx, hwy, hwz]
  rw [h_sum]
  have h_cases := exists_le_div4_of_four_distinct (by decide) hw hx hy hz hwx hwy hwz hxy hxz hyz
  have h_sum3_w := sum_three_distinct_divisors_bounds (by decide) hx hy hz hxy hxz hyz
  have h_sum3_x := sum_three_distinct_divisors_bounds (by decide) hw hy hz hwy hwz hyz
  have h_sum3_y := sum_three_distinct_divisors_bounds (by decide) hw hx hz hwx hwz hxz
  have h_sum3_z := sum_three_distinct_divisors_bounds (by decide) hw hx hy hwx hwy hxy
  rcases h_cases with hw_le | hx_le | hy_le | hz_le <;> omega

set_option maxRecDepth 10000 in
lemma no_four_divisors_630 : ∀ D ⊆ Nat.divisors 630, D.card = 4 → D.sum id ≠ 1242 := by
  intro D hD h_card
  rcases card_eq_four.mp h_card with ⟨w, x, y, z, hwx, hwy, hwz, hxy, hxz, hyz, rfl⟩
  have hw : w ∈ Nat.divisors 630 := hD (by simp)
  have hx : x ∈ Nat.divisors 630 := hD (by simp)
  have hy : y ∈ Nat.divisors 630 := hD (by simp)
  have hz : z ∈ Nat.divisors 630 := hD (by simp)
  have h_sum : ({w, x, y, z} : Finset ℕ).sum id = w + x + y + z := by
    rw [sum_insert, sum_insert, sum_insert, sum_singleton]
    · dsimp [id]; omega
    · rwa [Finset.mem_singleton]
    · simp [hxy, hxz]
    · simp [hwx, hwy, hwz]
  rw [h_sum]
  by_cases h_w : w ∈ ({90, 105, 126, 210, 315, 630} : Finset ℕ)
  · by_cases h_x : x ∈ ({90, 105, 126, 210, 315, 630} : Finset ℕ)
    · by_cases h_y : y ∈ ({90, 105, 126, 210, 315, 630} : Finset ℕ)
      · by_cases h_z : z ∈ ({90, 105, 126, 210, 315, 630} : Finset ℕ)
        · have h_dec : ∀ w ∈ ({90, 105, 126, 210, 315, 630} : Finset ℕ), ∀ x ∈ ({90, 105, 126, 210, 315, 630} : Finset ℕ), ∀ y ∈ ({90, 105, 126, 210, 315, 630} : Finset ℕ), ∀ z ∈ ({90, 105, 126, 210, 315, 630} : Finset ℕ), w ≠ x → w ≠ y → w ≠ z → x ≠ y → x ≠ z → y ≠ z → w + x + y + z ≠ 1242 := by decide
          exact h_dec w h_w x h_x y h_y z h_z hwx hwy hwz hxy hxz hyz
        · have hz_le : z ≤ 70 := le_70_of_mem_div_630_and_not_mem hz h_z
          have h_le := sum_four_distinct_divisors_bounds_w_le_70 hz hw hx hy hwz.symm hxz.symm hyz.symm hwx hwy hxy hz_le
          omega
      · have hy_le : y ≤ 70 := le_70_of_mem_div_630_and_not_mem hy h_y
        have h_le := sum_four_distinct_divisors_bounds_w_le_70 hy hw hx hz hwy.symm hxy.symm hyz hwx hwz hxz hy_le
        omega
    · have hx_le : x ≤ 70 := le_70_of_mem_div_630_and_not_mem hx h_x
      have h_le := sum_four_distinct_divisors_bounds_w_le_70 hx hw hy hz hwx.symm hxy hxz hwy hwz hyz hx_le
      omega
  · have hw_le : w ≤ 70 := le_70_of_mem_div_630_and_not_mem hw h_w
    have h_le := sum_four_distinct_divisors_bounds_w_le_70 hw hx hy hz hwx hwy hwz hxy hxz hyz hw_le
    omega

set_option maxRecDepth 10000 in
lemma no_four_divisors_660 : ∀ D ⊆ Nat.divisors 660, D.card = 4 → D.sum id ≠ 1356 := by
  intro D hD h_card
  rcases card_eq_four.mp h_card with ⟨w, x, y, z, hwx, hwy, hwz, hxy, hxz, hyz, rfl⟩
  have hw : w ∈ Nat.divisors 660 := hD (by simp)
  have hx : x ∈ Nat.divisors 660 := hD (by simp)
  have hy : y ∈ Nat.divisors 660 := hD (by simp)
  have hz : z ∈ Nat.divisors 660 := hD (by simp)
  have h_sum : ({w, x, y, z} : Finset ℕ).sum id = w + x + y + z := by
    rw [sum_insert, sum_insert, sum_insert, sum_singleton]
    · dsimp [id]; omega
    · rwa [Finset.mem_singleton]
    · simp [hxy, hxz]
    · simp [hwx, hwy, hwz]
  rw [h_sum]
  by_cases h_w : w ∈ ({132, 165, 220, 330, 660} : Finset ℕ)
  · by_cases h_x : x ∈ ({132, 165, 220, 330, 660} : Finset ℕ)
    · by_cases h_y : y ∈ ({132, 165, 220, 330, 660} : Finset ℕ)
      · by_cases h_z : z ∈ ({132, 165, 220, 330, 660} : Finset ℕ)
        · have h_dec : ∀ w ∈ ({132, 165, 220, 330, 660} : Finset ℕ), ∀ x ∈ ({132, 165, 220, 330, 660} : Finset ℕ), ∀ y ∈ ({132, 165, 220, 330, 660} : Finset ℕ), ∀ z ∈ ({132, 165, 220, 330, 660} : Finset ℕ), w ≠ x → w ≠ y → w ≠ z → x ≠ y → x ≠ z → y ≠ z → w + x + y + z ≠ 1356 := by decide
          exact h_dec w h_w x h_x y h_y z h_z hwx hwy hwz hxy hxz hyz
        · have hz_le : z ≤ 110 := le_110_of_mem_div_660_and_not_mem hz h_z
          have h_le := sum_four_distinct_divisors_bounds_w_le_110 hz hw hx hy hwz.symm hxz.symm hyz.symm hwx hwy hxy hz_le
          omega
      · have hy_le : y ≤ 110 := le_110_of_mem_div_660_and_not_mem hy h_y
        have h_le := sum_four_distinct_divisors_bounds_w_le_110 hy hw hx hz hwy.symm hxy.symm hyz hwx hwz hxz hy_le
        omega
    · have hx_le : x ≤ 110 := le_110_of_mem_div_660_and_not_mem hx h_x
      have h_le := sum_four_distinct_divisors_bounds_w_le_110 hx hw hy hz hwx.symm hxy hxz hwy hwz hyz hx_le
      omega
  · have hw_le : w ≤ 110 := le_110_of_mem_div_660_and_not_mem hw h_w
    have h_le := sum_four_distinct_divisors_bounds_w_le_110 hw hx hy hz hwx hwy hwz hxy hxz hyz hw_le
    omega

set_option maxRecDepth 10000 in
lemma no_three_divisors_360 : ∀ D ⊆ Nat.divisors 360, D.card = 3 → D.sum id ≠ 810 := by
  intro D hD h_card
  rcases card_eq_three.mp h_card with ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hx : x ∈ Nat.divisors 360 := hD (by simp)
  have hy : y ∈ Nat.divisors 360 := hD (by simp)
  have hz : z ∈ Nat.divisors 360 := hD (by simp)
  have h_sum : ({x, y, z} : Finset ℕ).sum id = x + y + z := by
    rw [sum_insert, sum_insert, sum_singleton]
    · dsimp [id]; omega
    · rwa [Finset.mem_singleton]
    · simp [hxy, hxz]
  rw [h_sum]
  have h_bound := sum_three_distinct_divisors_bounds (by decide) hx hy hz hxy hxz hyz
  omega

set_option maxRecDepth 10000 in
lemma no_three_divisors_420 : ∀ D ⊆ Nat.divisors 420, D.card = 3 → D.sum id ≠ 924 := by
  intro D hD h_card
  rcases card_eq_three.mp h_card with ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hx : x ∈ Nat.divisors 420 := hD (by simp)
  have hy : y ∈ Nat.divisors 420 := hD (by simp)
  have hz : z ∈ Nat.divisors 420 := hD (by simp)
  have h_sum : ({x, y, z} : Finset ℕ).sum id = x + y + z := by
    rw [sum_insert, sum_insert, sum_singleton]
    · dsimp [id]; omega
    · rwa [Finset.mem_singleton]
    · simp [hxy, hxz]
  rw [h_sum]
  have h_bound := sum_three_distinct_divisors_bounds (by decide) hx hy hz hxy hxz hyz
  omega

set_option maxRecDepth 10000 in
lemma no_three_divisors_480 : ∀ D ⊆ Nat.divisors 480, D.card = 3 → D.sum id ≠ 1032 := by
  intro D hD h_card
  rcases card_eq_three.mp h_card with ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hx : x ∈ Nat.divisors 480 := hD (by simp)
  have hy : y ∈ Nat.divisors 480 := hD (by simp)
  have hz : z ∈ Nat.divisors 480 := hD (by simp)
  have h_sum : ({x, y, z} : Finset ℕ).sum id = x + y + z := by
    rw [sum_insert, sum_insert, sum_singleton]
    · dsimp [id]; omega
    · rwa [Finset.mem_singleton]
    · simp [hxy, hxz]
  rw [h_sum]
  have h_bound := sum_three_distinct_divisors_bounds (by decide) hx hy hz hxy hxz hyz
  omega

set_option maxRecDepth 10000 in
lemma no_three_divisors_504 : ∀ D ⊆ Nat.divisors 504, D.card = 3 → D.sum id ≠ 1056 := by
  intro D hD h_card
  rcases card_eq_three.mp h_card with ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hx : x ∈ Nat.divisors 504 := hD (by simp)
  have hy : y ∈ Nat.divisors 504 := hD (by simp)
  have hz : z ∈ Nat.divisors 504 := hD (by simp)
  have h_sum : ({x, y, z} : Finset ℕ).sum id = x + y + z := by
    rw [sum_insert, sum_insert, sum_singleton]
    · dsimp [id]; omega
    · rwa [Finset.mem_singleton]
    · simp [hxy, hxz]
  rw [h_sum]
  have h_bound := sum_three_distinct_divisors_bounds (by decide) hx hy hz hxy hxz hyz
  omega

set_option maxRecDepth 10000 in
lemma no_three_divisors_540 : ∀ D ⊆ Nat.divisors 540, D.card = 3 → D.sum id ≠ 1140 := by
  intro D hD h_card
  rcases card_eq_three.mp h_card with ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hx : x ∈ Nat.divisors 540 := hD (by simp)
  have hy : y ∈ Nat.divisors 540 := hD (by simp)
  have hz : z ∈ Nat.divisors 540 := hD (by simp)
  have h_sum : ({x, y, z} : Finset ℕ).sum id = x + y + z := by
    rw [sum_insert, sum_insert, sum_singleton]
    · dsimp [id]; omega
    · rwa [Finset.mem_singleton]
    · simp [hxy, hxz]
  rw [h_sum]
  have h_bound := sum_three_distinct_divisors_bounds (by decide) hx hy hz hxy hxz hyz
  omega

set_option maxRecDepth 10000 in
lemma no_three_divisors_600 : ∀ D ⊆ Nat.divisors 600, D.card = 3 → D.sum id ≠ 1260 := by
  intro D hD h_card
  rcases card_eq_three.mp h_card with ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hx : x ∈ Nat.divisors 600 := hD (by simp)
  have hy : y ∈ Nat.divisors 600 := hD (by simp)
  have hz : z ∈ Nat.divisors 600 := hD (by simp)
  have h_sum : ({x, y, z} : Finset ℕ).sum id = x + y + z := by
    rw [sum_insert, sum_insert, sum_singleton]
    · dsimp [id]; omega
    · rwa [Finset.mem_singleton]
    · simp [hxy, hxz]
  rw [h_sum]
  have h_bound := sum_three_distinct_divisors_bounds (by decide) hx hy hz hxy hxz hyz
  omega

set_option maxRecDepth 10000 in
lemma no_three_divisors_630 : ∀ D ⊆ Nat.divisors 630, D.card = 3 → D.sum id ≠ 1242 := by
  intro D hD h_card
  rcases card_eq_three.mp h_card with ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hx : x ∈ Nat.divisors 630 := hD (by simp)
  have hy : y ∈ Nat.divisors 630 := hD (by simp)
  have hz : z ∈ Nat.divisors 630 := hD (by simp)
  have h_sum : ({x, y, z} : Finset ℕ).sum id = x + y + z := by
    rw [sum_insert, sum_insert, sum_singleton]
    · dsimp [id]; omega
    · rwa [Finset.mem_singleton]
    · simp [hxy, hxz]
  rw [h_sum]
  have h_bound := sum_three_distinct_divisors_bounds (by decide) hx hy hz hxy hxz hyz
  omega

set_option maxRecDepth 10000 in
lemma no_three_divisors_660 : ∀ D ⊆ Nat.divisors 660, D.card = 3 → D.sum id ≠ 1356 := by
  intro D hD h_card
  rcases card_eq_three.mp h_card with ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hx : x ∈ Nat.divisors 660 := hD (by simp)
  have hy : y ∈ Nat.divisors 660 := hD (by simp)
  have hz : z ∈ Nat.divisors 660 := hD (by simp)
  have h_sum : ({x, y, z} : Finset ℕ).sum id = x + y + z := by
    rw [sum_insert, sum_insert, sum_singleton]
    · dsimp [id]; omega
    · rwa [Finset.mem_singleton]
    · simp [hxy, hxz]
  rw [h_sum]
  have h_bound := sum_three_distinct_divisors_bounds (by decide) hx hy hz hxy hxz hyz
  omega

set_option maxRecDepth 10000 in
lemma no_three_divisors_672 : ∀ D ⊆ Nat.divisors 672, D.card = 3 → D.sum id ≠ 1344 := by
  intro D hD h_card
  rcases card_eq_three.mp h_card with ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hx : x ∈ Nat.divisors 672 := hD (by simp)
  have hy : y ∈ Nat.divisors 672 := hD (by simp)
  have hz : z ∈ Nat.divisors 672 := hD (by simp)
  have h_sum : ({x, y, z} : Finset ℕ).sum id = x + y + z := by
    rw [sum_insert, sum_insert, sum_singleton]
    · dsimp [id]; omega
    · rwa [Finset.mem_singleton]
    · simp [hxy, hxz]
  rw [h_sum]
  have h_bound := sum_three_distinct_divisors_bounds (by decide) hx hy hz hxy hxz hyz
  omega

set_option maxRecDepth 10000 in
lemma no_two_divisors_360 : ∀ D ⊆ Nat.divisors 360, D.card = 2 → D.sum id ≠ 810 := by
  intro D hD h_card
  rcases card_eq_two.mp h_card with ⟨x, y, hxy, rfl⟩
  have hx : x ∈ Nat.divisors 360 := hD (by simp)
  have hy : y ∈ Nat.divisors 360 := hD (by simp)
  have h_sum : ({x, y} : Finset ℕ).sum id = x + y := by
    simp [hxy]
  rw [h_sum]
  have h_bound := sum_two_distinct_divisors_bounds (by decide) hx hy hxy
  omega

set_option maxRecDepth 10000 in
lemma no_two_divisors_420 : ∀ D ⊆ Nat.divisors 420, D.card = 2 → D.sum id ≠ 924 := by
  intro D hD h_card
  rcases card_eq_two.mp h_card with ⟨x, y, hxy, rfl⟩
  have hx : x ∈ Nat.divisors 420 := hD (by simp)
  have hy : y ∈ Nat.divisors 420 := hD (by simp)
  have h_sum : ({x, y} : Finset ℕ).sum id = x + y := by
    simp [hxy]
  rw [h_sum]
  have h_bound := sum_two_distinct_divisors_bounds (by decide) hx hy hxy
  omega

set_option maxRecDepth 10000 in
lemma no_two_divisors_480 : ∀ D ⊆ Nat.divisors 480, D.card = 2 → D.sum id ≠ 1032 := by
  intro D hD h_card
  rcases card_eq_two.mp h_card with ⟨x, y, hxy, rfl⟩
  have hx : x ∈ Nat.divisors 480 := hD (by simp)
  have hy : y ∈ Nat.divisors 480 := hD (by simp)
  have h_sum : ({x, y} : Finset ℕ).sum id = x + y := by
    simp [hxy]
  rw [h_sum]
  have h_bound := sum_two_distinct_divisors_bounds (by decide) hx hy hxy
  omega

set_option maxRecDepth 10000 in
lemma no_two_divisors_504 : ∀ D ⊆ Nat.divisors 504, D.card = 2 → D.sum id ≠ 1056 := by
  intro D hD h_card
  rcases card_eq_two.mp h_card with ⟨x, y, hxy, rfl⟩
  have hx : x ∈ Nat.divisors 504 := hD (by simp)
  have hy : y ∈ Nat.divisors 504 := hD (by simp)
  have h_sum : ({x, y} : Finset ℕ).sum id = x + y := by
    simp [hxy]
  rw [h_sum]
  have h_bound := sum_two_distinct_divisors_bounds (by decide) hx hy hxy
  omega

set_option maxRecDepth 10000 in
lemma no_two_divisors_540 : ∀ D ⊆ Nat.divisors 540, D.card = 2 → D.sum id ≠ 1140 := by
  intro D hD h_card
  rcases card_eq_two.mp h_card with ⟨x, y, hxy, rfl⟩
  have hx : x ∈ Nat.divisors 540 := hD (by simp)
  have hy : y ∈ Nat.divisors 540 := hD (by simp)
  have h_sum : ({x, y} : Finset ℕ).sum id = x + y := by
    simp [hxy]
  rw [h_sum]
  have h_bound := sum_two_distinct_divisors_bounds (by decide) hx hy hxy
  omega

set_option maxRecDepth 10000 in
lemma no_two_divisors_600 : ∀ D ⊆ Nat.divisors 600, D.card = 2 → D.sum id ≠ 1260 := by
  intro D hD h_card
  rcases card_eq_two.mp h_card with ⟨x, y, hxy, rfl⟩
  have hx : x ∈ Nat.divisors 600 := hD (by simp)
  have hy : y ∈ Nat.divisors 600 := hD (by simp)
  have h_sum : ({x, y} : Finset ℕ).sum id = x + y := by
    simp [hxy]
  rw [h_sum]
  have h_bound := sum_two_distinct_divisors_bounds (by decide) hx hy hxy
  omega

set_option maxRecDepth 10000 in
lemma no_two_divisors_630 : ∀ D ⊆ Nat.divisors 630, D.card = 2 → D.sum id ≠ 1242 := by
  intro D hD h_card
  rcases card_eq_two.mp h_card with ⟨x, y, hxy, rfl⟩
  have hx : x ∈ Nat.divisors 630 := hD (by simp)
  have hy : y ∈ Nat.divisors 630 := hD (by simp)
  have h_sum : ({x, y} : Finset ℕ).sum id = x + y := by
    simp [hxy]
  rw [h_sum]
  have h_bound := sum_two_distinct_divisors_bounds (by decide) hx hy hxy
  omega

set_option maxRecDepth 10000 in
lemma no_two_divisors_660 : ∀ D ⊆ Nat.divisors 660, D.card = 2 → D.sum id ≠ 1356 := by
  intro D hD h_card
  rcases card_eq_two.mp h_card with ⟨x, y, hxy, rfl⟩
  have hx : x ∈ Nat.divisors 660 := hD (by simp)
  have hy : y ∈ Nat.divisors 660 := hD (by simp)
  have h_sum : ({x, y} : Finset ℕ).sum id = x + y := by
    simp [hxy]
  rw [h_sum]
  have h_bound := sum_two_distinct_divisors_bounds (by decide) hx hy hxy
  omega

set_option maxRecDepth 10000 in
lemma no_two_divisors_672 : ∀ D ⊆ Nat.divisors 672, D.card = 2 → D.sum id ≠ 1344 := by
  intro D hD h_card
  rcases card_eq_two.mp h_card with ⟨x, y, hxy, rfl⟩
  have hx : x ∈ Nat.divisors 672 := hD (by simp)
  have hy : y ∈ Nat.divisors 672 := hD (by simp)
  have h_sum : ({x, y} : Finset ℕ).sum id = x + y := by
    simp [hxy]
  rw [h_sum]
  have h_bound := sum_two_distinct_divisors_bounds (by decide) hx hy hxy
  omega

lemma card_divisors_lt_20_of_mem_range : ∀ m, m < 672 →
    (m ≠ 240 ∧ m ≠ 336 ∧ m ≠ 360 ∧ m ≠ 420 ∧ m ≠ 432 ∧ m ≠ 480 ∧ m ≠ 504 ∧ m ≠ 528 ∧ m ≠ 540 ∧ m ≠ 560 ∧ m ≠ 576 ∧ m ≠ 600 ∧ m ≠ 624 ∧ m ≠ 630 ∧ m ≠ 648 ∧ m ≠ 660) →
    (Nat.divisors m).card < 20 := by
  intro m hm h_not
  rcases h_not with ⟨h240, h336, h360, h420, h432, h480, h504, h528, h540, h560, h576, h600, h624, h630, h648, h660⟩
  by_cases h0 : m < 100
  · exact card_divisors_lt_20_chunk0 m h0
  by_cases h1 : m < 200
  · exact card_divisors_lt_20_chunk1 m ⟨by omega, h1⟩
  by_cases h2 : m < 300
  · exact card_divisors_lt_20_chunk2 m ⟨by omega, h2⟩ h240
  by_cases h3 : m < 400
  · exact card_divisors_lt_20_chunk3 m ⟨by omega, h3⟩ ⟨h336, h360⟩
  by_cases h4 : m < 500
  · exact card_divisors_lt_20_chunk4 m ⟨by omega, h4⟩ ⟨h420, ⟨h432, h480⟩⟩
  by_cases h5 : m < 600
  · exact card_divisors_lt_20_chunk5 m ⟨by omega, h5⟩ ⟨h504, ⟨h528, ⟨h540, ⟨h560, h576⟩⟩⟩⟩
  · exact card_divisors_lt_20_chunk6 m ⟨by omega, hm⟩ ⟨h600, ⟨h624, ⟨h630, ⟨h648, h660⟩⟩⟩⟩

lemma card_divisors_lt_21_of_mem_range : ∀ m, m < 720 →
    (m ≠ 360 ∧ m ≠ 420 ∧ m ≠ 480 ∧ m ≠ 504 ∧ m ≠ 540 ∧ m ≠ 576 ∧ m ≠ 600 ∧ m ≠ 630 ∧ m ≠ 660 ∧ m ≠ 672) →
    (Nat.divisors m).card < 21 := by
  intro m hm h_not
  rcases h_not with ⟨h360, h420, h480, h504, h540, h576, h600, h630, h660, h672⟩
  by_cases h0 : m < 100
  · have := card_divisors_lt_20_chunk0 m h0
    omega
  by_cases h1 : m < 200
  · exact card_divisors_lt_21_chunk1 m ⟨by omega, h1⟩
  by_cases h2 : m < 300
  · exact card_divisors_lt_21_chunk2 m ⟨by omega, h2⟩
  by_cases h3 : m < 400
  · exact card_divisors_lt_21_chunk3 m ⟨by omega, h3⟩ h360
  by_cases h4 : m < 500
  · exact card_divisors_lt_21_chunk4 m ⟨by omega, h4⟩ ⟨h420, h480⟩
  by_cases h5 : m < 600
  · exact card_divisors_lt_21_chunk5 m ⟨by omega, h5⟩ ⟨h504, ⟨h540, h576⟩⟩
  by_cases h6 : m < 700
  · exact card_divisors_lt_21_chunk6 m ⟨by omega, h6⟩ ⟨h600, ⟨h630, ⟨h660, h672⟩⟩⟩
  · exact card_divisors_lt_21_chunk7 m ⟨by omega, hm⟩

lemma card_divisors_lt_22_of_mem_range : ∀ m, m < 720 →
    (m ≠ 360 ∧ m ≠ 420 ∧ m ≠ 480 ∧ m ≠ 504 ∧ m ≠ 540 ∧ m ≠ 600 ∧ m ≠ 630 ∧ m ≠ 660 ∧ m ≠ 672) →
    (Nat.divisors m).card < 22 := by
  intro m hm h_not
  rcases h_not with ⟨h360, h420, h480, h504, h540, h600, h630, h660, h672⟩
  by_cases h0 : m < 100
  · have := card_divisors_lt_20_chunk0 m h0
    omega
  by_cases h1 : m < 200
  · exact card_divisors_lt_22_chunk1 m ⟨by omega, h1⟩
  by_cases h2 : m < 300
  · exact card_divisors_lt_22_chunk2 m ⟨by omega, h2⟩
  by_cases h3 : m < 400
  · exact card_divisors_lt_22_chunk3 m ⟨by omega, h3⟩ h360
  by_cases h4 : m < 500
  · exact card_divisors_lt_22_chunk4 m ⟨by omega, h4⟩ ⟨h420, h480⟩
  by_cases h5 : m < 600
  · exact card_divisors_lt_22_chunk5 m ⟨by omega, h5⟩ ⟨h504, h540⟩
  by_cases h6 : m < 700
  · exact card_divisors_lt_22_chunk6 m ⟨by omega, h6⟩ ⟨h600, ⟨h630, ⟨h660, h672⟩⟩⟩
  · exact card_divisors_lt_22_chunk7 m ⟨by omega, hm⟩

set_option maxRecDepth 30000 in
lemma a08_20_eq_672 : a081512 20 = 672 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · have h : 672 ∈ candidates_a 20 := by
      rw [candidates_a, mem_setOf_eq]
      refine ⟨by decide, ?_⟩
      let D : Finset ℕ := [1, 2, 3, 4, 6, 7, 8, 12, 14, 16, 21, 24, 28, 32, 42, 48, 56, 84, 96, 168].toFinset
      use D
      refine ⟨by decide, by decide, by decide, by decide⟩
    exact candidates_a_sub_candidates_a08 20 h
  · intro y hy
    by_cases h_special : y = 240 ∨ y = 336 ∨ y = 360 ∨ y = 420 ∨ y = 432 ∨ y = 480 ∨ y = 504 ∨ y = 528 ∨ y = 540 ∨ y = 560 ∨ y = 576 ∨ y = 600 ∨ y = 624 ∨ y = 630 ∨ y = 648 ∨ y = 660
    · rcases h_special with rfl | h_next
      · exact not_mem_candidates_a08_eq_of_sum_divisors_ne_m (by decide) (by decide)
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_eq_of_sum_divisors_ne_m (by decide) (by decide)
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_four_divisors_360
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_four_divisors_420
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_eq_of_sum_divisors_ne_m (by decide) (by decide)
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_four_divisors_480
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_four_divisors_504
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_eq_of_sum_divisors_ne_m (by decide) (by decide)
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_four_divisors_540
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_eq_of_sum_divisors_ne_m (by decide) (by decide)
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_sub_one_of_sum_divisors_gt_2m (by decide) (by decide)
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_four_divisors_600
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_eq_of_sum_divisors_ne_m (by decide) (by decide)
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_four_divisors_630
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_eq_of_sum_divisors_ne_m (by decide) (by decide)
      subst h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_four_divisors_660
    · have h_not : y ≠ 240 ∧ y ≠ 336 ∧ y ≠ 360 ∧ y ≠ 420 ∧ y ≠ 432 ∧ y ≠ 480 ∧ y ≠ 504 ∧ y ≠ 528 ∧ y ≠ 540 ∧ y ≠ 560 ∧ y ≠ 576 ∧ y ≠ 600 ∧ y ≠ 624 ∧ y ≠ 630 ∧ y ≠ 648 ∧ y ≠ 660 := by tauto
      have h_card : (Nat.divisors y).card < 20 := card_divisors_lt_20_of_mem_range y hy h_not
      exact not_mem_candidates_a08_of_card_lt h_card

set_option maxRecDepth 30000 in
lemma a08_21_eq_720 : a081512 21 = 720 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · have h : 720 ∈ candidates_a 21 := by
      rw [candidates_a, mem_setOf_eq]
      refine ⟨by decide, ?_⟩
      let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 30, 36, 45, 72, 144, 240].toFinset
      use D
      refine ⟨by decide, by decide, by decide, by decide⟩
    exact candidates_a_sub_candidates_a08 21 h
  · intro y hy
    by_cases h_special : y = 360 ∨ y = 420 ∨ y = 480 ∨ y = 504 ∨ y = 540 ∨ y = 576 ∨ y = 600 ∨ y = 630 ∨ y = 660 ∨ y = 672
    · rcases h_special with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_three_divisors_360
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_three_divisors_420
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_three_divisors_480
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_three_divisors_504
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_three_divisors_540
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_eq_of_sum_divisors_ne_m (by decide) (by decide)
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_three_divisors_600
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_three_divisors_630
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_three_divisors_660
      subst h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_three_divisors_672
    · have h_not : y ≠ 360 ∧ y ≠ 420 ∧ y ≠ 480 ∧ y ≠ 504 ∧ y ≠ 540 ∧ y ≠ 576 ∧ y ≠ 600 ∧ y ≠ 630 ∧ y ≠ 660 ∧ y ≠ 672 := by tauto
      have h_card : (Nat.divisors y).card < 21 := card_divisors_lt_21_of_mem_range y hy h_not
      exact not_mem_candidates_a08_of_card_lt h_card

set_option maxRecDepth 30000 in
lemma a08_22_eq_720 : a081512 22 = 720 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply sInf_eq_of_mem_and_lt_not_mem
  · have h : 720 ∈ candidates_a 22 := by
      rw [candidates_a, mem_setOf_eq]
      refine ⟨by decide, ?_⟩
      let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 30, 36, 45, 60, 72, 144, 180].toFinset
      use D
      refine ⟨by decide, by decide, by decide, by decide⟩
    exact candidates_a_sub_candidates_a08 22 h
  · intro y hy
    by_cases h_special : y = 360 ∨ y = 420 ∨ y = 480 ∨ y = 504 ∨ y = 540 ∨ y = 600 ∨ y = 630 ∨ y = 660 ∨ y = 672
    · rcases h_special with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_two_divisors_360
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_two_divisors_420
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_two_divisors_480
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_two_divisors_504
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_two_divisors_540
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_two_divisors_600
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_two_divisors_630
      rcases h_next with rfl | h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_two_divisors_660
      subst h_next
      · exact not_mem_candidates_a08_of_no_sub_div_sum (by decide) (by decide) no_two_divisors_672
    · have h_not : y ≠ 360 ∧ y ≠ 420 ∧ y ≠ 480 ∧ y ≠ 504 ∧ y ≠ 540 ∧ y ≠ 600 ∧ y ≠ 630 ∧ y ≠ 660 ∧ y ≠ 672 := by tauto
      have h_card : (Nat.divisors y).card < 22 := card_divisors_lt_22_of_mem_range y hy h_not
      exact not_mem_candidates_a08_of_card_lt h_card

set_option maxRecDepth 30000 in
lemma a_witness_20 : a 20 ≤ 672 := by
  rw [a_eq_sInf_candidates_a]
  apply Nat.sInf_le
  rw [candidates_a, mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := [1, 2, 3, 4, 6, 7, 8, 12, 14, 16, 21, 24, 28, 32, 42, 48, 56, 84, 96, 168].toFinset
  use D
  refine ⟨by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 30000 in
lemma a_witness_21 : a 21 ≤ 720 := by
  rw [a_eq_sInf_candidates_a]
  apply Nat.sInf_le
  rw [candidates_a, mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 30, 36, 45, 72, 144, 240].toFinset
  use D
  refine ⟨by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 30000 in
lemma a_witness_22 : a 22 ≤ 720 := by
  rw [a_eq_sInf_candidates_a]
  apply Nat.sInf_le
  rw [candidates_a, mem_setOf_eq]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 30, 36, 45, 60, 72, 144, 180].toFinset
  use D
  refine ⟨by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma a081512_23_le_720 : a081512 23 ≤ 720 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply Nat.sInf_le
  rw [mem_candidates_a08_iff_powerset]
  have h_720 : 0 < 720 := by decide
  refine ⟨h_720, ?_⟩
  let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 30, 36, 40, 45, 72, 80, 120, 144].toFinset
  use D
  have h_prop : D ⊆ (Nat.divisors 720) ∧ D.card = 23 ∧ D.sum id = 720 := by decide
  exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma a081512_24_le_840 : a081512 24 ≤ 840 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply Nat.sInf_le
  rw [mem_candidates_a08_iff_powerset]
  have h_840 : 0 < 840 := by decide
  refine ⟨h_840, ?_⟩
  let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 20, 21, 24, 28, 30, 35, 42, 56, 84, 105, 140, 168].toFinset
  use D
  have h_prop : D ⊆ (Nat.divisors 840) ∧ D.card = 24 ∧ D.sum id = 840 := by decide
  exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma L_eq_360_or_420_of_le_420_and_card_ge_24 {L : ℕ} (hL : L ≤ 420) (h_card : 24 ≤ (Nat.divisors L).card) : L = 360 ∨ L = 420 :=
  have h : ∀ m, m ≤ 420 → 24 ≤ (Nat.divisors m).card → m = 360 ∨ m = 420 := by decide
  h L hL h_card

set_option maxRecDepth 30000 in
lemma L_ge_720_of_card_divisors_ge_25 {L : ℕ} (h : 25 ≤ (Nat.divisors L).card) : 720 ≤ L := by
  by_contra h_lt
  have h_lt720 : L < 720 := by omega
  by_cases h_special : L = 360 ∨ L = 420 ∨ L = 480 ∨ L = 504 ∨ L = 540 ∨ L = 600 ∨ L = 630 ∨ L = 660 ∨ L = 672
  · rcases h_special with rfl | h_next
    · have : (Nat.divisors 360).card = 24 := by decide
      omega
    rcases h_next with rfl | h_next
    · have : (Nat.divisors 420).card = 24 := by decide
      omega
    rcases h_next with rfl | h_next
    · have : (Nat.divisors 480).card = 24 := by decide
      omega
    rcases h_next with rfl | h_next
    · have : (Nat.divisors 504).card = 24 := by decide
      omega
    rcases h_next with rfl | h_next
    · have : (Nat.divisors 540).card = 24 := by decide
      omega
    rcases h_next with rfl | h_next
    · have : (Nat.divisors 600).card = 24 := by decide
      omega
    rcases h_next with rfl | h_next
    · have : (Nat.divisors 630).card = 24 := by decide
      omega
    rcases h_next with rfl | h_next
    · have : (Nat.divisors 660).card = 24 := by decide
      omega
    subst h_next
    · have : (Nat.divisors 672).card = 24 := by decide
      omega
  · have h_not : L ≠ 360 ∧ L ≠ 420 ∧ L ≠ 480 ∧ L ≠ 504 ∧ L ≠ 540 ∧ L ≠ 600 ∧ L ≠ 630 ∧ L ≠ 660 ∧ L ≠ 672 := by tauto
    have h_card := card_divisors_lt_23_of_mem_range L h_lt720 h_not
    omega

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma a081512_le_1260_of_le_29 {n : ℕ} (h25 : 25 ≤ n) (h29 : n ≤ 29) : a081512 n ≤ 1260 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply Nat.sInf_le
  rw [mem_candidates_a08_iff_powerset]
  have h_1260 : 0 < 1260 := by decide
  refine ⟨h_1260, ?_⟩
  interval_cases n
  · let D : Finset ℕ := [4, 6, 7, 9, 12, 14, 15, 18, 20, 21, 28, 30, 35, 36, 42, 45, 60, 63, 70, 84, 90, 105, 126, 140, 180].toFinset
    use D
    have h_prop : D ⊆ (Nat.divisors 1260) ∧ D.card = 25 ∧ D.sum id = 1260 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · let D : Finset ℕ := [4, 5, 6, 7, 9, 10, 12, 14, 18, 20, 21, 28, 30, 35, 36, 42, 45, 60, 63, 70, 84, 90, 105, 126, 140, 180].toFinset
    use D
    have h_prop : D ⊆ (Nat.divisors 1260) ∧ D.card = 26 ∧ D.sum id = 1260 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · let D : Finset ℕ := [3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 20, 21, 28, 30, 35, 36, 42, 45, 60, 63, 70, 84, 90, 105, 126, 140, 180].toFinset
    use D
    have h_prop : D ⊆ (Nat.divisors 1260) ∧ D.card = 27 ∧ D.sum id = 1260 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · let D : Finset ℕ := [2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 18, 21, 28, 30, 35, 36, 42, 45, 60, 63, 70, 84, 90, 105, 126, 140, 180].toFinset
    use D
    have h_prop : D ⊆ (Nat.divisors 1260) ∧ D.card = 28 ∧ D.sum id = 1260 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 18, 20, 28, 30, 35, 36, 42, 45, 60, 63, 70, 84, 90, 105, 126, 140, 180].toFinset
    use D
    have h_prop : D ⊆ (Nat.divisors 1260) ∧ D.card = 29 ∧ D.sum id = 1260 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩

set_option maxRecDepth 30000 in
lemma a_witness_23 : a 23 ≤ 720 := by
  rw [a_eq_sInf_candidates_a]
  apply Nat.sInf_le
  rw [mem_candidates_a_iff_powerset]
  have h_720 : 0 < 720 := by decide
  refine ⟨h_720, ?_⟩
  let D : Finset ℕ := [1, 2, 3, 4, 5, 8, 9, 10, 12, 15, 16, 18, 20, 24, 30, 36, 40, 45, 60, 72, 80, 90, 120].toFinset
  use D
  have h_prop : D ⊆ (Nat.divisors 720) ∧ D.card = 23 ∧ D.sum id = 720 ∧ D.lcm id = 720 := by decide
  exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2.1, h_prop.2.2.2⟩

set_option maxRecDepth 30000 in
lemma a081512_le_1680_of_le_32 {n : ℕ} (h30 : 30 ≤ n) (h32 : n ≤ 32) : a081512 n ≤ 1680 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply Nat.sInf_le
  rw [mem_candidates_a08_iff_powerset]
  have h_1680 : 0 < 1680 := by decide
  refine ⟨h_1680, ?_⟩
  interval_cases n
  · let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 16, 20, 21, 24, 28, 30, 35, 40, 42, 48, 56, 60, 80, 105, 112, 120, 336, 420].toFinset
    use D
    have h_prop : D ⊆ (Nat.divisors 1680) ∧ D.card = 30 ∧ D.sum id = 1680 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 16, 20, 21, 24, 28, 30, 35, 40, 42, 48, 56, 60, 70, 80, 105, 120, 168, 210, 420].toFinset
    use D
    have h_prop : D ⊆ (Nat.divisors 1680) ∧ D.card = 31 ∧ D.sum id = 1680 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 16, 20, 21, 24, 28, 30, 35, 40, 42, 48, 56, 60, 70, 80, 84, 105, 120, 168, 210, 336].toFinset
    use D
    have h_prop : D ⊆ (Nat.divisors 1680) ∧ D.card = 32 ∧ D.sum id = 1680 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma a081512_le_2520_of_le_36 {n : ℕ} (h33 : 33 ≤ n) (h36 : n ≤ 36) : a081512 n ≤ 2520 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply Nat.sInf_le
  rw [mem_candidates_a08_iff_powerset]
  have h_2520 : 0 < 2520 := by decide
  refine ⟨h_2520, ?_⟩
  interval_cases n
  · let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 21, 24, 28, 30, 35, 36, 40, 42, 45, 56, 60, 63, 70, 72, 84, 105, 315, 1260].toFinset
    use D
    have h_prop : D ⊆ (Nat.divisors 2520) ∧ D.card = 33 ∧ D.sum id = 2520 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 21, 24, 28, 30, 35, 36, 40, 42, 45, 56, 60, 63, 70, 72, 84, 90, 120, 210, 1260].toFinset
    use D
    have h_prop : D ⊆ (Nat.divisors 2520) ∧ D.card = 34 ∧ D.sum id = 2520 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 21, 24, 28, 30, 35, 36, 40, 42, 45, 56, 60, 63, 70, 72, 84, 90, 120, 126, 504, 840].toFinset
    use D
    have h_prop : D ⊆ (Nat.divisors 2520) ∧ D.card = 35 ∧ D.sum id = 2520 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 21, 24, 28, 30, 35, 36, 40, 42, 45, 56, 60, 63, 70, 72, 84, 90, 105, 120, 210, 315, 840].toFinset
    use D
    have h_prop : D ⊆ (Nat.divisors 2520) ∧ D.card = 36 ∧ D.sum id = 2520 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma a081512_le_2520_of_le_39 {n : ℕ} (h37 : 37 ≤ n) (h39 : n ≤ 39) : a081512 n ≤ 2520 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply Nat.sInf_le
  rw [mem_candidates_a08_iff_powerset]
  have h_2520 : 0 < 2520 := by decide
  refine ⟨h_2520, ?_⟩
  interval_cases n
  · let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 21, 24, 28, 30, 35, 36, 40, 42, 45, 56, 60, 63, 70, 72, 84, 90, 105, 120, 126, 315, 420, 504].toFinset
    use D
    have h_prop : D ⊆ (Nat.divisors 2520) ∧ D.card = 37 ∧ D.sum id = 2520 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 21, 24, 28, 30, 35, 36, 40, 42, 45, 56, 60, 63, 70, 72, 84, 90, 105, 120, 126, 140, 280, 315, 504].toFinset
    use D
    have h_prop : D ⊆ (Nat.divisors 2520) ∧ D.card = 38 ∧ D.sum id = 2520 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩
  · let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 21, 24, 28, 30, 35, 36, 40, 42, 45, 56, 60, 63, 70, 72, 84, 90, 105, 120, 140, 168, 210, 252, 280, 315].toFinset
    use D
    have h_prop : D ⊆ (Nat.divisors 2520) ∧ D.card = 39 ∧ D.sum id = 2520 := by decide
    exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩

set_option maxRecDepth 30000 in
lemma not_mem_1620_candidates_a08 : 1620 ∉ candidates_a08 30 := by
  exact not_mem_candidates_a08_eq_of_sum_divisors_ne_m (by decide) (by decide)

set_option maxRecDepth 30000 in
lemma divisors_840_pairs : ∀ x ∈ Nat.divisors 840, ∀ y ∈ Nat.divisors 840, x ≠ y → x + y = 1260 ∨ x + y ≤ 1120 := by decide

set_option maxRecDepth 30000 in
lemma no_sum_840_30 : ∀ D ⊆ (Nat.divisors 840), D.card = 30 → D.sum id = 1620 ∨ 1760 ≤ D.sum id := by
  intro D hD h_card
  have hS_card : (Nat.divisors 840).card = 32 := by decide
  have h_sdiff : (Nat.divisors 840 \ D).card = 2 := by
    rw [Finset.card_sdiff_of_subset hD, h_card, hS_card]
  rcases card_eq_two.mp h_sdiff with ⟨x, y, hxy, hxy_eq⟩
  have hx : x ∈ Nat.divisors 840 := by
    have : x ∈ Nat.divisors 840 \ D := by rw [hxy_eq]; simp
    exact Finset.sdiff_subset this
  have hy : y ∈ Nat.divisors 840 := by
    have : y ∈ Nat.divisors 840 \ D := by rw [hxy_eq]; simp
    exact Finset.sdiff_subset this
  have hxy_ne : x ≠ y := hxy
  have h_sum : (Nat.divisors 840 \ D).sum id = x + y := by
    simp [hxy_eq, hxy]
  have h_sum_sdiff : (Nat.divisors 840 \ D).sum id = (Nat.divisors 840).sum id - D.sum id := by
    have h_sum_sdiff : (Nat.divisors 840 \ D).sum id + D.sum id = (Nat.divisors 840).sum id := Finset.sum_sdiff hD
    omega
  have h_840_sum : (Nat.divisors 840).sum id = 2880 := by decide
  have h_pairs := divisors_840_pairs x hx y hy hxy_ne
  omega

set_option maxRecDepth 30000 in
lemma min_sum_1260_35_ge_3108 : ∀ D ⊆ (Nat.divisors 1260), D.card ≥ 35 → 3108 ≤ D.sum id := by
  intro D hD h_card
  have hS_card : (Nat.divisors 1260).card = 36 := by decide
  have hS_sum : (Nat.divisors 1260).sum id = 4368 := by decide
  have h_card_le : D.card ≤ 36 := by
    have := Finset.card_le_card hD
    omega
  have h_card_cases : D.card = 35 ∨ D.card = 36 := by omega
  rcases h_card_cases with h35 | h36
  · have h_sdiff : (Nat.divisors 1260 \ D).card = 1 := by
      rw [Finset.card_sdiff_of_subset hD, h35, hS_card]
    rcases Finset.card_eq_one.mp h_sdiff with ⟨x, hx_eq⟩
    have hx : x ∈ Nat.divisors 1260 := by
      have : x ∈ Nat.divisors 1260 \ D := by rw [hx_eq]; simp
      exact Finset.sdiff_subset this
    have hx_le : x ≤ 1260 := Nat.le_of_dvd (by decide) (Nat.mem_divisors.mp hx).1
    have h_sum : (Nat.divisors 1260 \ D).sum id = x := by
      rw [hx_eq, sum_singleton]; rfl
    have h_sum_sdiff : (Nat.divisors 1260 \ D).sum id = (Nat.divisors 1260).sum id - D.sum id := by
      have h_sum_sdiff : (Nat.divisors 1260 \ D).sum id + D.sum id = (Nat.divisors 1260).sum id := Finset.sum_sdiff hD
      omega
    omega
  · have h_eq : D = Nat.divisors 1260 := by
      apply Finset.eq_of_subset_of_card_le hD
      rw [hS_card, h36]
    rw [h_eq, hS_sum]; decide

set_option maxRecDepth 30000 in
lemma divisors_1260_pairs : ∀ x ∈ Nat.divisors 1260, ∀ y ∈ Nat.divisors 1260, x ≠ y → x + y = 1890 ∨ x + y ≤ 1830 := by decide

set_option maxRecDepth 30000 in
lemma no_sum_1260_34 : ∀ D ⊆ (Nat.divisors 1260), D.card = 34 → D.sum id = 2478 ∨ 2538 ≤ D.sum id := by
  intro D hD h_card
  have hS_card : (Nat.divisors 1260).card = 36 := by decide
  have h_sdiff : (Nat.divisors 1260 \ D).card = 2 := by
    rw [Finset.card_sdiff_of_subset hD, h_card, hS_card]
  rcases card_eq_two.mp h_sdiff with ⟨x, y, hxy, hxy_eq⟩
  have hx : x ∈ Nat.divisors 1260 := by
    have : x ∈ Nat.divisors 1260 \ D := by rw [hxy_eq]; simp
    exact Finset.sdiff_subset this
  have hy : y ∈ Nat.divisors 1260 := by
    have : y ∈ Nat.divisors 1260 \ D := by rw [hxy_eq]; simp
    exact Finset.sdiff_subset this
  have hxy_ne : x ≠ y := hxy
  have h_sum : (Nat.divisors 1260 \ D).sum id = x + y := by
    simp [hxy_eq, hxy]
  have h_sum_sdiff : (Nat.divisors 1260 \ D).sum id = (Nat.divisors 1260).sum id - D.sum id := by
    have h_sum_sdiff : (Nat.divisors 1260 \ D).sum id + D.sum id = (Nat.divisors 1260).sum id := Finset.sum_sdiff hD
    omega
  have h_1260_sum : (Nat.divisors 1260).sum id = 4368 := by decide
  have h_pairs := divisors_1260_pairs x hx y hy hxy_ne
  omega

set_option maxRecDepth 30000 in
lemma not_mem_2478_candidates_a08 : 2478 ∉ candidates_a08 34 := by
  rw [mem_candidates_a08_iff_powerset]
  rintro ⟨-, D, hD, h_card, -⟩
  rw [Finset.mem_powerset] at hD
  have h_le := Finset.card_le_card hD
  have h_card_lt : (Nat.divisors 2478).card < 34 := by decide
  omega

set_option maxRecDepth 30000 in
lemma a081512_33_le_2160 : a081512 33 ≤ 2160 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply Nat.sInf_le
  rw [mem_candidates_a08_iff_powerset]
  have h_2160 : 0 < 2160 := by decide
  refine ⟨h_2160, ?_⟩
  let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 27, 30, 36, 40, 45, 48, 54, 60, 72, 80, 90, 120, 135, 144, 180, 216, 270, 360].toFinset
  use D
  have h_prop : D ⊆ (Nat.divisors 2160) ∧ D.card = 33 ∧ D.sum id = 2160 := by decide
  exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩

set_option maxRecDepth 30000 in
lemma divisors_1260_triples : ∀ x ∈ Nat.divisors 1260, ∀ y ∈ Nat.divisors 1260, ∀ z ∈ Nat.divisors 1260,
  x ≠ y → x ≠ z → y ≠ z → x + y + z = 2310 ∨ x + y + z ≤ 2205 := by decide

set_option maxRecDepth 30000 in
lemma no_sum_1260_33 : ∀ D ⊆ (Nat.divisors 1260), D.card = 33 → D.sum id ≠ a081512 33 := by
  intro D hD h_card h_eq
  have hS_card : (Nat.divisors 1260).card = 36 := by decide
  have h_sdiff : (Nat.divisors 1260 \ D).card = 3 := by
    rw [Finset.card_sdiff_of_subset hD, h_card, hS_card]
  rcases card_eq_three.mp h_sdiff with ⟨x, y, z, hxy, hxz, hyz, hxyz_eq⟩
  have hx : x ∈ Nat.divisors 1260 := by
    have : x ∈ Nat.divisors 1260 \ D := by rw [hxyz_eq]; simp
    exact Finset.sdiff_subset this
  have hy : y ∈ Nat.divisors 1260 := by
    have : y ∈ Nat.divisors 1260 \ D := by rw [hxyz_eq]; simp
    exact Finset.sdiff_subset this
  have hz : z ∈ Nat.divisors 1260 := by
    have : z ∈ Nat.divisors 1260 \ D := by rw [hxyz_eq]; simp
    exact Finset.sdiff_subset this
  have h_sum : (Nat.divisors 1260 \ D).sum id = x + y + z := by
    simp [hxyz_eq, hxy, hxz, hyz]; omega
  have h_sum_sdiff : (Nat.divisors 1260 \ D).sum id = (Nat.divisors 1260).sum id - D.sum id := by
    have h_sum_sdiff : (Nat.divisors 1260 \ D).sum id + D.sum id = (Nat.divisors 1260).sum id := Finset.sum_sdiff hD
    omega
  have hS_sum : (Nat.divisors 1260).sum id = 4368 := by decide
  have h_triples := divisors_1260_triples x hx y hy z hz hxy hxz hyz
  have hm_mem : a081512 33 ∈ candidates_a08 33 := a08_mem 33 (by omega)
  rcases h_triples with h1 | h2
  · have h_D_sum : D.sum id = 2058 := by omega
    rw [← h_eq, h_D_sum] at hm_mem
    rw [mem_candidates_a08_iff_powerset] at hm_mem
    rcases hm_mem with ⟨-, D_witness, hD_witness, h_card_witness, h_sum_witness⟩
    rw [Finset.mem_powerset] at hD_witness
    have h_card_2058 : (Nat.divisors 2058).card = 16 := by decide
    have : D_witness.card ≤ 16 := by
      have : D_witness ⊆ Nat.divisors 2058 := hD_witness
      have := Finset.card_le_card this
      omega
    omega
  · have h_D_sum : 2163 ≤ D.sum id := by omega
    have h_le33 : a081512 33 ≤ 2160 := a081512_33_le_2160
    omega

set_option maxRecDepth 30000 in
lemma min_sum_840_31 : ∀ D ⊆ (Nat.divisors 840), D.card = 31 → 2040 ≤ D.sum id := by
  intro D hD h_card
  have hS_card : (Nat.divisors 840).card = 32 := by decide
  have h_sdiff : (Nat.divisors 840 \ D).card = 1 := by
    rw [Finset.card_sdiff_of_subset hD, h_card, hS_card]
  rcases Finset.card_eq_one.mp h_sdiff with ⟨x, hx_eq⟩
  have hx : x ∈ Nat.divisors 840 := by
    have : x ∈ Nat.divisors 840 \ D := by rw [hx_eq]; simp
    exact Finset.sdiff_subset this
  have hx_le : x ≤ 840 := Nat.le_of_dvd (by decide) (Nat.mem_divisors.mp hx).1
  have h_sum_sdiff : (Nat.divisors 840 \ D).sum id = (Nat.divisors 840).sum id - D.sum id := by
    have h_sum_sdiff : (Nat.divisors 840 \ D).sum id + D.sum id = (Nat.divisors 840).sum id := Finset.sum_sdiff hD
    omega
  have h_sum : (Nat.divisors 840 \ D).sum id = x := by
    rw [hx_eq, sum_singleton]; rfl
  have hS_sum : (Nat.divisors 840).sum id = 2880 := by decide
  omega

set_option maxRecDepth 30000 in
lemma min_sum_840_32 : ∀ D ⊆ (Nat.divisors 840), D.card = 32 → 2880 ≤ D.sum id := by
  intro D hD h_card
  have hS_card : (Nat.divisors 840).card = 32 := by decide
  have h_eq : D = Nat.divisors 840 := by
    apply Finset.eq_of_subset_of_card_le hD
    rw [hS_card, h_card]
  have hS_sum : (Nat.divisors 840).sum id = 2880 := by decide
  rw [h_eq, hS_sum]

set_option maxRecDepth 30000 in
lemma card_divisors_lt_30_chunk0 : ∀ m, m < 300 → (Nat.divisors m).card < 30 := by decide
set_option maxRecDepth 30000 in
lemma card_divisors_lt_30_chunk1 : ∀ m, 300 ≤ m ∧ m < 600 → (Nat.divisors m).card < 30 := by decide
set_option maxRecDepth 30000 in
lemma card_divisors_lt_30_chunk2 : ∀ m, 600 ≤ m ∧ m < 840 → m ≠ 720 → (Nat.divisors m).card < 30 := by decide

lemma card_divisors_lt_30_of_le_840 {L : ℕ} (hL : L ≤ 840) (h720 : L ≠ 720) (h840 : L ≠ 840) : (Nat.divisors L).card < 30 := by
  by_cases h0 : L < 300
  · exact card_divisors_lt_30_chunk0 L h0
  · by_cases h1 : L < 600
    · exact card_divisors_lt_30_chunk1 L ⟨by omega, h1⟩
    · have : L < 840 := by omega
      exact card_divisors_lt_30_chunk2 L ⟨by omega, this⟩ h720

lemma card_divisors_lt_33_chunk0 : ∀ m, m < 400 → (Nat.divisors m).card < 33 := by
  intro m hm
  by_cases h : m < 300
  · have := card_divisors_lt_30_chunk0 m h
    omega
  · have h2 : 300 ≤ m ∧ m < 600 := by omega
    have := card_divisors_lt_30_chunk1 m h2
    omega

lemma card_divisors_lt_33_chunk1 : ∀ m, 400 ≤ m ∧ m < 800 → (Nat.divisors m).card < 33 := by
  intro m hm
  by_cases h1 : m < 600
  · have h2 : 300 ≤ m ∧ m < 600 := by omega
    have := card_divisors_lt_30_chunk1 m h2
    omega
  · by_cases h2 : m = 720
    · subst h2; decide
    · have h3 : 600 ≤ m ∧ m < 840 := by omega
      have := card_divisors_lt_30_chunk2 m h3 h2
      omega

set_option maxRecDepth 30000 in
lemma card_divisors_lt_33_chunk2_a : ∀ m, 800 ≤ m ∧ m < 950 → (Nat.divisors m).card < 33 := by decide
set_option maxRecDepth 30000 in
lemma card_divisors_lt_33_chunk2_b : ∀ m, 950 ≤ m ∧ m < 1100 → (Nat.divisors m).card < 33 := by decide
set_option maxRecDepth 30000 in
lemma card_divisors_lt_33_chunk2_c : ∀ m, 1100 ≤ m ∧ m < 1260 → (Nat.divisors m).card < 33 := by decide

lemma card_divisors_lt_33_chunk2 : ∀ m, 800 ≤ m ∧ m < 1260 → (Nat.divisors m).card < 33 := by
  intro m hm
  by_cases h1 : m < 950
  · exact card_divisors_lt_33_chunk2_a m ⟨hm.1, h1⟩
  · by_cases h2 : m < 1100
    · exact card_divisors_lt_33_chunk2_b m ⟨by omega, h2⟩
    · exact card_divisors_lt_33_chunk2_c m ⟨by omega, hm.2⟩

lemma card_divisors_lt_33_of_le_1260 {L : ℕ} (hL : L ≤ 1260) (h1260 : L ≠ 1260) : (Nat.divisors L).card < 33 := by
  by_cases h0 : L < 400
  · exact card_divisors_lt_33_chunk0 L h0
  · by_cases h1 : L < 800
    · exact card_divisors_lt_33_chunk1 L ⟨by omega, h1⟩
    · have : L < 1260 := by omega
      exact card_divisors_lt_33_chunk2 L ⟨by omega, this⟩

lemma card_divisors_lt_37_chunk0 : ∀ m, m < 400 → (Nat.divisors m).card < 37 := by
  intro m hm
  have := card_divisors_lt_33_chunk0 m hm
  omega

lemma card_divisors_lt_37_chunk1 : ∀ m, 400 ≤ m ∧ m < 800 → (Nat.divisors m).card < 37 := by
  intro m hm
  have := card_divisors_lt_33_chunk1 m hm
  omega

set_option maxRecDepth 30000 in
lemma card_divisors_lt_37_chunk2 : ∀ m, 800 ≤ m ∧ m < 1261 → (Nat.divisors m).card < 37 := by
  intro m hm
  by_cases h : m = 1260
  · subst h; decide
  · have h2 : 800 ≤ m ∧ m < 1260 := by omega
    have := card_divisors_lt_33_chunk2 m h2
    omega

lemma card_divisors_lt_37_of_le_1260 {L : ℕ} (hL : L ≤ 1260) : (Nat.divisors L).card < 37 := by
  by_cases h0 : L < 400
  · exact card_divisors_lt_37_chunk0 L h0
  · by_cases h1 : L < 800
    · exact card_divisors_lt_37_chunk1 L ⟨by omega, h1⟩
    · have : L < 1261 := by omega
      exact card_divisors_lt_37_chunk2 L ⟨by omega, this⟩

lemma card_divisors_lt_40_chunk0 : ∀ m, m < 300 → (Nat.divisors m).card < 40 := by
  intro m hm
  have h2 : m < 400 := by omega
  have := card_divisors_lt_37_chunk0 m h2
  omega

lemma card_divisors_lt_40_chunk1 : ∀ m, 300 ≤ m ∧ m < 600 → (Nat.divisors m).card < 40 := by
  intro m hm
  by_cases h : m < 400
  · have := card_divisors_lt_37_chunk0 m h
    omega
  · have h2 : 400 ≤ m ∧ m < 800 := by omega
    have := card_divisors_lt_37_chunk1 m h2
    omega

lemma card_divisors_lt_40_chunk2 : ∀ m, 600 ≤ m ∧ m < 900 → (Nat.divisors m).card < 40 := by
  intro m hm
  by_cases h : m < 800
  · have h2 : 400 ≤ m ∧ m < 800 := by omega
    have := card_divisors_lt_37_chunk1 m h2
    omega
  · have h2 : 800 ≤ m ∧ m < 1261 := by omega
    have := card_divisors_lt_37_chunk2 m h2
    omega

lemma card_divisors_lt_40_chunk3 : ∀ m, 900 ≤ m ∧ m < 1200 → (Nat.divisors m).card < 40 := by
  intro m hm
  have h2 : 800 ≤ m ∧ m < 1261 := by omega
  have := card_divisors_lt_37_chunk2 m h2
  omega

set_option maxRecDepth 30000 in
lemma card_divisors_lt_40_chunk4_a : ∀ m, 1200 ≤ m ∧ m < 1350 → (Nat.divisors m).card < 40 := by decide
set_option maxRecDepth 30000 in
lemma card_divisors_lt_40_chunk4_b : ∀ m, 1350 ≤ m ∧ m < 1500 → (Nat.divisors m).card < 40 := by decide
set_option maxRecDepth 30000 in
lemma card_divisors_lt_40_chunk5_a : ∀ m, 1500 ≤ m ∧ m < 1600 → (Nat.divisors m).card < 40 := by decide
set_option maxRecDepth 30000 in
lemma card_divisors_lt_40_chunk5_b : ∀ m, 1600 ≤ m ∧ m < 1680 → (Nat.divisors m).card < 40 := by decide

lemma card_divisors_lt_40_chunk4 : ∀ m, 1200 ≤ m ∧ m < 1500 → (Nat.divisors m).card < 40 := by
  intro m hm
  by_cases h : m < 1350
  · exact card_divisors_lt_40_chunk4_a m ⟨hm.1, h⟩
  · exact card_divisors_lt_40_chunk4_b m ⟨by omega, hm.2⟩

lemma card_divisors_lt_40_chunk5 : ∀ m, 1500 ≤ m ∧ m < 1680 → (Nat.divisors m).card < 40 := by
  intro m hm
  by_cases h : m < 1600
  · exact card_divisors_lt_40_chunk5_a m ⟨hm.1, h⟩
  · exact card_divisors_lt_40_chunk5_b m ⟨by omega, hm.2⟩

lemma card_divisors_lt_40_of_lt_1680 {L : ℕ} (hL : L < 1680) : (Nat.divisors L).card < 40 := by
  by_cases h0 : L < 300
  · exact card_divisors_lt_40_chunk0 L h0
  · by_cases h1 : L < 600
    · exact card_divisors_lt_40_chunk1 L ⟨by omega, h1⟩
    · by_cases h2 : L < 900
      · exact card_divisors_lt_40_chunk2 L ⟨by omega, h2⟩
      · by_cases h3 : L < 1200
        · exact card_divisors_lt_40_chunk3 L ⟨by omega, h3⟩
        · by_cases h4 : L < 1500
          · exact card_divisors_lt_40_chunk4 L ⟨by omega, h4⟩
          · exact card_divisors_lt_40_chunk5 L ⟨by omega, hL⟩
lemma L_ge_1680_of_card_divisors_ge_40 {L : ℕ} (h : 40 ≤ (Nat.divisors L).card) : 1680 ≤ L := by
  by_contra! hc
  have := card_divisors_lt_40_of_lt_1680 hc
  omega

lemma witness_mem_candidates_a (n : ℕ) (hn : 6 ≤ n) : 24 * 2^(n-6) ∈ candidates_a n := by
  rw [mem_candidates_a_iff_powerset]
  refine ⟨by positivity, D_witness_ge_6 (n-6), ?_, ?_, ?_, ?_⟩
  · rw [Finset.mem_powerset]
    intro x hx
    rw [Nat.mem_divisors]
    refine ⟨divisors_D_witness_ge_6 (n-6) x hx, by positivity⟩
  · have h_card := card_D_witness_ge_6 (n-6)
    omega
  · exact sum_D_witness_ge_6 (n-6)
  · exact lcm_D_witness_ge_6 (n-6)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma a081512_40_le_3360 : a081512 40 ≤ 3360 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply Nat.sInf_le
  rw [mem_candidates_a08_iff_powerset]
  have h_3360 : 0 < 3360 := by decide
  refine ⟨h_3360, ?_⟩
  let D : Finset ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 16, 20, 21, 28, 30, 32, 35, 40, 42, 48, 56, 60, 70, 80, 84, 96, 105, 112, 120, 140, 160, 168, 210, 224, 240, 280, 336, 420].toFinset
  use D
  have h_prop : D ⊆ (Nat.divisors 3360) ∧ D.card = 40 ∧ D.sum id = 3360 := by decide
  exact ⟨Finset.mem_powerset.mpr h_prop.1, h_prop.2.1, h_prop.2.2⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma a081512_24_mem_candidates_a : a081512 24 ∈ candidates_a 24 := by
  apply mem_candidates_a_of_mem_candidates_a08' (a08_mem 24 (by omega))
  intro L hdvd hL h_card D hD h_card_D
  have h_m_le : a081512 24 ≤ 840 := a081512_24_le_840
  have hL_le : L ≤ 420 := by omega
  have h_cases : L = 360 ∨ L = 420 := L_eq_360_or_420_of_le_420_and_card_ge_24 hL_le h_card
  rcases h_cases with rfl | rfl
  · have h_D_eq : D = Nat.divisors 360 := by
      apply Finset.eq_of_subset_of_card_le hD
      have : (Nat.divisors 360).card = 24 := by decide
      omega
    rw [h_D_eq]
    have : (Nat.divisors 360).sum id = 1170 := by decide
    omega
  · have h_D_eq : D = Nat.divisors 420 := by
      apply Finset.eq_of_subset_of_card_le hD
      have : (Nat.divisors 420).card = 24 := by decide
      omega
    rw [h_D_eq]
    have : (Nat.divisors 420).sum id = 1344 := by decide
    omega

set_option maxRecDepth 30000 in
lemma a081512_41_le_4320 : a081512 41 ≤ 4320 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply Nat.sInf_le
  rw [mem_candidates_a08_iff_powerset]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 27, 30, 32, 36, 40, 45, 48, 54, 60, 72, 80, 90, 96, 108, 120, 135, 144, 160, 180, 240, 270, 288, 360, 432, 480, 540}
  use D
  refine ⟨by decide, by decide, by decide⟩

lemma card_divisors_lt_41_chunk0 : ∀ m, 1680 ≤ m ∧ m < 1710 → (Nat.divisors m).card < 41 := by decide
lemma card_divisors_lt_41_chunk1 : ∀ m, 1710 ≤ m ∧ m < 1740 → (Nat.divisors m).card < 41 := by decide
lemma card_divisors_lt_41_chunk2 : ∀ m, 1740 ≤ m ∧ m < 1770 → (Nat.divisors m).card < 41 := by decide
lemma card_divisors_lt_41_chunk3 : ∀ m, 1770 ≤ m ∧ m < 1800 → (Nat.divisors m).card < 41 := by decide
lemma card_divisors_lt_41_chunk4 : ∀ m, 1800 ≤ m ∧ m < 1830 → (Nat.divisors m).card < 41 := by decide
lemma card_divisors_lt_41_chunk5 : ∀ m, 1830 ≤ m ∧ m < 1860 → (Nat.divisors m).card < 41 := by decide
lemma card_divisors_lt_41_chunk6 : ∀ m, 1860 ≤ m ∧ m < 1890 → (Nat.divisors m).card < 41 := by decide
lemma card_divisors_lt_41_chunk7 : ∀ m, 1890 ≤ m ∧ m < 1920 → (Nat.divisors m).card < 41 := by decide
lemma card_divisors_lt_41_chunk8 : ∀ m, 1920 ≤ m ∧ m < 1950 → (Nat.divisors m).card < 41 := by decide
lemma card_divisors_lt_41_chunk9 : ∀ m, 1950 ≤ m ∧ m < 1980 → (Nat.divisors m).card < 41 := by decide
lemma card_divisors_lt_41_chunk10 : ∀ m, 1980 ≤ m ∧ m < 2010 → (Nat.divisors m).card < 41 := by decide
lemma card_divisors_lt_41_chunk11 : ∀ m, 2010 ≤ m ∧ m < 2040 → (Nat.divisors m).card < 41 := by decide
lemma card_divisors_lt_41_chunk12 : ∀ m, 2040 ≤ m ∧ m < 2070 → (Nat.divisors m).card < 41 := by decide
lemma card_divisors_lt_41_chunk13 : ∀ m, 2070 ≤ m ∧ m < 2100 → (Nat.divisors m).card < 41 := by decide
lemma card_divisors_lt_41_chunk14 : ∀ m, 2100 ≤ m ∧ m < 2130 → (Nat.divisors m).card < 41 := by decide
lemma card_divisors_lt_41_chunk15 : ∀ m, 2130 ≤ m ∧ m < 2160 → (Nat.divisors m).card < 41 := by decide

lemma card_divisors_lt_45_chunk0 : ∀ m, 2160 ≤ m ∧ m < 2190 → (Nat.divisors m).card < 45 := by decide
lemma card_divisors_lt_45_chunk1 : ∀ m, 2190 ≤ m ∧ m < 2220 → (Nat.divisors m).card < 45 := by decide
lemma card_divisors_lt_45_chunk2 : ∀ m, 2220 ≤ m ∧ m < 2250 → (Nat.divisors m).card < 45 := by decide
lemma card_divisors_lt_45_chunk3 : ∀ m, 2250 ≤ m ∧ m < 2280 → (Nat.divisors m).card < 45 := by decide
lemma card_divisors_lt_45_chunk4 : ∀ m, 2280 ≤ m ∧ m < 2310 → (Nat.divisors m).card < 45 := by decide
lemma card_divisors_lt_45_chunk5 : ∀ m, 2310 ≤ m ∧ m < 2340 → (Nat.divisors m).card < 45 := by decide
lemma card_divisors_lt_45_chunk6 : ∀ m, 2340 ≤ m ∧ m < 2370 → (Nat.divisors m).card < 45 := by decide
lemma card_divisors_lt_45_chunk7 : ∀ m, 2370 ≤ m ∧ m < 2400 → (Nat.divisors m).card < 45 := by decide
lemma card_divisors_lt_45_chunk8 : ∀ m, 2400 ≤ m ∧ m < 2430 → (Nat.divisors m).card < 45 := by decide
lemma card_divisors_lt_45_chunk9 : ∀ m, 2430 ≤ m ∧ m < 2460 → (Nat.divisors m).card < 45 := by decide
lemma card_divisors_lt_45_chunk10 : ∀ m, 2460 ≤ m ∧ m < 2490 → (Nat.divisors m).card < 45 := by decide
lemma card_divisors_lt_45_chunk11 : ∀ m, 2490 ≤ m ∧ m < 2520 → (Nat.divisors m).card < 45 := by decide

lemma div_le_third_of_dvd_of_lt {d m : ℕ} (h_dvd : d ∣ m) (h_lt : d < m / 2) : d ≤ m / 3 := by
  rcases h_dvd with ⟨k, rfl⟩
  have h_k : 3 ≤ k := by
    by_contra h_contr
    have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl | rfl
    · simp at h_lt
    · have : d / 2 ≤ d := Nat.div_le_self d 2
      omega
    · have h_eq : d * 2 / 2 = d := Nat.mul_div_cancel d (by decide)
      rw [h_eq] at h_lt
      omega
  have : 3 * d ≤ d * k := by
    rw [mul_comm d k]
    exact Nat.mul_le_mul_right d h_k
  omega

lemma div_le_1260_of_mem_and_ne {x : ℕ} (hx : x ∈ Nat.divisors 2520) (hx_ne : x ≠ 2520) : x ≤ 1260 := by
  have h_dvd : x ∣ 2520 := Nat.mem_divisors.mp hx |>.1
  have h_lt : x < 2520 := by
    have : x ≤ 2520 := Nat.le_of_dvd (by decide) h_dvd
    omega
  exact div_le_of_dvd_of_lt h_dvd h_lt

lemma div_le_840_of_mem_and_ne {x : ℕ} (hx : x ∈ Nat.divisors 2520) (hx_ne1 : x ≠ 2520) (hx_ne2 : x ≠ 1260) : x ≤ 840 := by
  have h_dvd : x ∣ 2520 := Nat.mem_divisors.mp hx |>.1
  have h_lt1 : x < 2520 := by
    have : x ≤ 2520 := Nat.le_of_dvd (by decide) h_dvd
    omega
  have h_le1260 := div_le_of_dvd_of_lt h_dvd h_lt1
  have h_lt2 : x < 1260 := by omega
  have : 1260 = 2520 / 2 := by decide
  rw [this] at h_lt2
  exact div_le_third_of_dvd_of_lt h_dvd h_lt2

lemma divisors_2520_singles_7560 : ∀ x ∈ Nat.divisors 2520, id x ≠ 1800 := by decide

lemma divisors_2520_pairs_7560 : ∀ x ∈ Nat.divisors 2520, ∀ y ∈ Nat.divisors 2520,
    x ≠ y → id x + id y ≠ 1800 := by decide

lemma divisors_2520_triples_proof (x : ℕ) (hx : x ∈ Nat.divisors 2520) (y : ℕ) (hy : y ∈ Nat.divisors 2520) (z : ℕ) (hz : z ∈ Nat.divisors 2520)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : id x + id y + id z ≠ 4320 := by
  by_cases hx_2520 : x = 2520
  · subst hx_2520
    intro h_sum
    dsimp [id] at *
    have h_pair : y + z = 1800 := by omega
    exact divisors_2520_pairs_7560 y hy z hz hyz h_pair
  · by_cases hy_2520 : y = 2520
    · subst hy_2520
      intro h_sum
      dsimp [id] at *
      have hxy_ne : x ≠ z := hxz
      have h_pair : x + z = 1800 := by omega
      exact divisors_2520_pairs_7560 x hx z hz hxy_ne h_pair
    · by_cases hz_2520 : z = 2520
      · subst hz_2520
        intro h_sum
        dsimp [id] at *
        have h_pair : x + y = 1800 := by omega
        exact divisors_2520_pairs_7560 x hx y hy hxy h_pair
      · by_cases hx_1260 : x = 1260
        · subst hx_1260
          intro h_sum
          dsimp [id] at *
          have hy_le : y ≤ 1260 := div_le_1260_of_mem_and_ne hy hy_2520
          have hz_le : z ≤ 1260 := div_le_1260_of_mem_and_ne hz hz_2520
          have hy_ne1260 : y ≠ 1260 := Ne.symm hxy
          have hz_ne1260 : z ≠ 1260 := Ne.symm hxz
          have hy_le840 : y ≤ 840 := div_le_840_of_mem_and_ne hy hy_2520 hy_ne1260
          have hz_le840 : z ≤ 840 := div_le_840_of_mem_and_ne hz hz_2520 hz_ne1260
          omega
        · by_cases hy_1260 : y = 1260
          · subst hy_1260
            intro h_sum
            dsimp [id] at *
            have hx_le : x ≤ 1260 := div_le_1260_of_mem_and_ne hx hx_2520
            have hz_le : z ≤ 1260 := div_le_1260_of_mem_and_ne hz hz_2520
            have hx_ne1260 : x ≠ 1260 := hx_1260
            have hz_ne1260 : z ≠ 1260 := Ne.symm hyz
            have hx_le840 : x ≤ 840 := div_le_840_of_mem_and_ne hx hx_2520 hx_ne1260
            have hz_le840 : z ≤ 840 := div_le_840_of_mem_and_ne hz hz_2520 hz_ne1260
            omega
          · by_cases hz_1260 : z = 1260
            · subst hz_1260
              intro h_sum
              dsimp [id] at *
              have hx_le : x ≤ 1260 := div_le_1260_of_mem_and_ne hx hx_2520
              have hy_le : y ≤ 1260 := div_le_1260_of_mem_and_ne hy hy_2520
              have hx_ne1260 : x ≠ 1260 := hx_1260
              have hy_ne1260 : y ≠ 1260 := hy_1260
              have hx_le840 : x ≤ 840 := div_le_840_of_mem_and_ne hx hx_2520 hx_ne1260
              have hy_le840 : y ≤ 840 := div_le_840_of_mem_and_ne hy hy_2520 hy_ne1260
              omega
            · dsimp [id] at *
              have hx_le840 : x ≤ 840 := div_le_840_of_mem_and_ne hx hx_2520 hx_1260
              have hy_le840 : y ≤ 840 := div_le_840_of_mem_and_ne hy hy_2520 hy_1260
              have hz_le840 : z ≤ 840 := div_le_840_of_mem_and_ne hz hz_2520 hz_1260
              omega

lemma divisors_2520_singles : ∀ x ∈ Nat.divisors 2520, id x ≠ 4320 := by decide

lemma divisors_2520_pairs : ∀ x ∈ Nat.divisors 2520, ∀ y ∈ Nat.divisors 2520,
    x ≠ y → id x + id y ≠ 4320 := by decide

lemma no_sum_2520_45_5040 (D : Finset ℕ) (hD : D ⊆ Nat.divisors 2520) (h_card : D.card ≥ 45) : ∑ x ∈ D, id x ≠ 5040 := by
  have hS_card : (Nat.divisors 2520).card = 48 := by decide
  have hS_sum : ∑ x ∈ Nat.divisors 2520, id x = 9360 := by decide
  have h_card_le : D.card ≤ 48 := by
    have := Finset.card_le_card hD
    omega
  have h_card_cases : D.card = 45 ∨ D.card = 46 ∨ D.card = 47 ∨ D.card = 48 := by omega
  have h_sum_sdiff : ∑ x ∈ Nat.divisors 2520 \ D, id x = (∑ x ∈ Nat.divisors 2520, id x) - ∑ x ∈ D, id x := by
    have := Finset.sum_sdiff (f := id) hD
    omega
  rcases h_card_cases with h45 | h46 | h47 | h48
  · have h_sdiff : (Nat.divisors 2520 \ D).card = 3 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hD, h45, hS_card]
    rcases card_eq_three.mp h_sdiff with ⟨x, y, z, hxy, hxz, hyz, h_sdiff_eq⟩
    have hx : x ∈ Nat.divisors 2520 := (Finset.mem_sdiff.mp (by rw [h_sdiff_eq]; simp)).1
    have hy : y ∈ Nat.divisors 2520 := (Finset.mem_sdiff.mp (by rw [h_sdiff_eq]; simp)).1
    have hz : z ∈ Nat.divisors 2520 := (Finset.mem_sdiff.mp (by rw [h_sdiff_eq]; simp)).1
    have h_sum_c : ∑ a ∈ Nat.divisors 2520 \ D, id a = id x + id y + id z := by
      rw [h_sdiff_eq]
      rw [sum_insert (by simp [hxy, hxz]), sum_insert (by simp [hyz]), sum_singleton]
      omega
    intro h_sum
    have h_c_sum : ∑ a ∈ Nat.divisors 2520 \ D, id a = 4320 := by omega
    have := divisors_2520_triples_proof x hx y hy z hz hxy hxz hyz
    omega
  · have h_sdiff : (Nat.divisors 2520 \ D).card = 2 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hD, h46, hS_card]
    rcases card_eq_two.mp h_sdiff with ⟨x, y, hxy, h_sdiff_eq⟩
    have hx : x ∈ Nat.divisors 2520 := (Finset.mem_sdiff.mp (by rw [h_sdiff_eq]; simp)).1
    have hy : y ∈ Nat.divisors 2520 := (Finset.mem_sdiff.mp (by rw [h_sdiff_eq]; simp [hxy])).1
    have h_sum_c : ∑ a ∈ Nat.divisors 2520 \ D, id a = id x + id y := by
      rw [h_sdiff_eq]
      rw [sum_insert (by simp [hxy]), sum_singleton]
    intro h_sum
    have h_c_sum : ∑ a ∈ Nat.divisors 2520 \ D, id a = 4320 := by omega
    have := divisors_2520_pairs x hx y hy hxy
    omega
  · have h_sdiff : (Nat.divisors 2520 \ D).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hD, h47, hS_card]
    rcases card_eq_one.mp h_sdiff with ⟨x, h_sdiff_eq⟩
    have hx : x ∈ Nat.divisors 2520 := (Finset.mem_sdiff.mp (by rw [h_sdiff_eq]; simp)).1
    have h_sum_c : ∑ a ∈ Nat.divisors 2520 \ D, id a = id x := by
      rw [h_sdiff_eq, sum_singleton]
    intro h_sum
    have h_c_sum : ∑ a ∈ Nat.divisors 2520 \ D, id a = 4320 := by omega
    have := divisors_2520_singles x hx
    omega
  · have h_eq : D = Nat.divisors 2520 := by
      apply Finset.eq_of_subset_of_card_le hD
      rw [hS_card, h48]
    intro h_sum
    rw [h_eq, hS_sum] at h_sum
    omega

lemma no_sum_2520_46_7560 (D : Finset ℕ) (hD : D ⊆ Nat.divisors 2520) (h_card : D.card ≥ 46) : ∑ x ∈ D, id x ≠ 7560 := by
  have hS_card : (Nat.divisors 2520).card = 48 := by decide
  have hS_sum : ∑ x ∈ Nat.divisors 2520, id x = 9360 := by decide
  have h_card_le : D.card ≤ 48 := by
    have := Finset.card_le_card hD
    omega
  have h_card_cases : D.card = 46 ∨ D.card = 47 ∨ D.card = 48 := by omega
  have h_sum_sdiff : ∑ x ∈ Nat.divisors 2520 \ D, id x = (∑ x ∈ Nat.divisors 2520, id x) - ∑ x ∈ D, id x := by
    have := Finset.sum_sdiff (f := id) hD
    omega
  rcases h_card_cases with h46 | h47 | h48
  · have h_sdiff : (Nat.divisors 2520 \ D).card = 2 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hD, h46, hS_card]
    rcases card_eq_two.mp h_sdiff with ⟨x, y, hxy, h_sdiff_eq⟩
    have hx : x ∈ Nat.divisors 2520 := (Finset.mem_sdiff.mp (by rw [h_sdiff_eq]; simp)).1
    have hy : y ∈ Nat.divisors 2520 := (Finset.mem_sdiff.mp (by rw [h_sdiff_eq]; simp [hxy])).1
    have h_sum_c : ∑ a ∈ Nat.divisors 2520 \ D, id a = id x + id y := by
      rw [h_sdiff_eq]
      rw [sum_insert (by simp [hxy]), sum_singleton]
    intro h_sum
    have h_c_sum : ∑ a ∈ Nat.divisors 2520 \ D, id a = 1800 := by omega
    have := divisors_2520_pairs_7560 x hx y hy hxy
    omega
  · have h_sdiff : (Nat.divisors 2520 \ D).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hD, h47, hS_card]
    rcases card_eq_one.mp h_sdiff with ⟨x, h_sdiff_eq⟩
    have hx : x ∈ Nat.divisors 2520 := (Finset.mem_sdiff.mp (by rw [h_sdiff_eq]; simp)).1
    have h_sum_c : ∑ a ∈ Nat.divisors 2520 \ D, id a = id x := by
      rw [h_sdiff_eq, sum_singleton]
    intro h_sum
    have h_c_sum : ∑ a ∈ Nat.divisors 2520 \ D, id a = 1800 := by omega
    have := divisors_2520_singles_7560 x hx
    omega
  · have h_eq : D = Nat.divisors 2520 := by
      apply Finset.eq_of_subset_of_card_le hD
      rw [hS_card, h48]
    intro h_sum
    rw [h_eq, hS_sum] at h_sum
    omega

lemma a081512_42_le_2520 : a081512 42 ≤ 2520 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply Nat.sInf_le
  rw [mem_candidates_a08_iff_powerset]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 28, 30, 35, 36, 40, 42, 45, 48, 56, 60, 63, 70, 72, 80, 84, 90, 105, 112, 126, 140, 144, 315, 504, 2520}
  use D
  refine ⟨by decide, by decide, by decide⟩

lemma a081512_43_le_2520 : a081512 43 ≤ 2520 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply Nat.sInf_le
  rw [mem_candidates_a08_iff_powerset]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 28, 30, 35, 36, 40, 42, 45, 48, 56, 60, 63, 70, 72, 80, 84, 90, 105, 112, 120, 126, 140, 168, 315, 360, 2520}
  use D
  refine ⟨by decide, by decide, by decide⟩

lemma a081512_44_le_2520 : a081512 44 ≤ 2520 := by
  rw [a081512_eq_sInf_candidates_a08]
  apply Nat.sInf_le
  rw [mem_candidates_a08_iff_powerset]
  refine ⟨by decide, ?_⟩
  let D : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 28, 30, 35, 36, 40, 42, 45, 48, 56, 60, 63, 70, 72, 80, 84, 90, 105, 112, 120, 126, 140, 144, 315, 504, 720, 1680}
  use D
  refine ⟨by decide, by decide, by decide⟩

lemma test_hn40 (n : ℕ) (hn40 : 40 ≤ n) : a n ≤ a081512 n := by
  by_cases hn41 : n < 41
  · have h_n40 : n = 40 := by omega
    subst h_n40
    rw [a_eq_sInf_candidates_a]
    apply Nat.sInf_le
    apply mem_candidates_a_of_mem_candidates_a08' (a08_mem 40 (by omega))
    intro L hdvd hL h_card D hD h_card_D
    have h_m_le : a081512 40 ≤ 3360 := a081512_40_le_3360
    have h_L_le : L ≤ 1680 := by omega
    have h_L_ge : 1680 ≤ L := L_ge_1680_of_card_divisors_ge_40 h_card
    have h_L_eq : L = 1680 := by omega
    subst h_L_eq
    have h_D_eq : D = Nat.divisors 1680 := by
      apply Finset.eq_of_subset_of_card_le hD
      have : (Nat.divisors 1680).card = 40 := by decide
      omega
    rw [h_D_eq]
    have : (Nat.divisors 1680).sum id = 5952 := by decide
    omega
  · by_cases hn42 : n < 42
    · have h_n41 : n = 41 := by omega
      subst h_n41
      rw [a_eq_sInf_candidates_a]
      apply Nat.sInf_le
      apply mem_candidates_a_of_mem_candidates_a08' (a08_mem 41 (by omega))
      intro L hdvd hL h_card D hD h_card_D
      have h_m_le : a081512 41 ≤ 4320 := a081512_41_le_4320
      have h_L_le : L ≤ 2160 := by omega
      have h_card_lt : (Nat.divisors L).card < 41 := by
        by_cases h_lt_1680 : L < 1680
        · have := card_divisors_lt_40_of_lt_1680 h_lt_1680
          omega
        · by_cases h_lt_1710 : L < 1710
          · exact card_divisors_lt_41_chunk0 L ⟨by omega, h_lt_1710⟩
          · by_cases h_lt_1740 : L < 1740
            · exact card_divisors_lt_41_chunk1 L ⟨by omega, h_lt_1740⟩
            · by_cases h_lt_1770 : L < 1770
              · exact card_divisors_lt_41_chunk2 L ⟨by omega, h_lt_1770⟩
              · by_cases h_lt_1800 : L < 1800
                · exact card_divisors_lt_41_chunk3 L ⟨by omega, h_lt_1800⟩
                · by_cases h_lt_1830 : L < 1830
                  · exact card_divisors_lt_41_chunk4 L ⟨by omega, h_lt_1830⟩
                  · by_cases h_lt_1860 : L < 1860
                    · exact card_divisors_lt_41_chunk5 L ⟨by omega, h_lt_1860⟩
                    · by_cases h_lt_1890 : L < 1890
                      · exact card_divisors_lt_41_chunk6 L ⟨by omega, h_lt_1890⟩
                      · by_cases h_lt_1920 : L < 1920
                        · exact card_divisors_lt_41_chunk7 L ⟨by omega, h_lt_1920⟩
                        · by_cases h_lt_1950 : L < 1950
                          · exact card_divisors_lt_41_chunk8 L ⟨by omega, h_lt_1950⟩
                          · by_cases h_lt_1980 : L < 1980
                            · exact card_divisors_lt_41_chunk9 L ⟨by omega, h_lt_1980⟩
                            · by_cases h_lt_2010 : L < 2010
                              · exact card_divisors_lt_41_chunk10 L ⟨by omega, h_lt_2010⟩
                              · by_cases h_lt_2040 : L < 2040
                                · exact card_divisors_lt_41_chunk11 L ⟨by omega, h_lt_2040⟩
                                · by_cases h_lt_2070 : L < 2070
                                  · exact card_divisors_lt_41_chunk12 L ⟨by omega, h_lt_2070⟩
                                  · by_cases h_lt_2100 : L < 2100
                                    · exact card_divisors_lt_41_chunk13 L ⟨by omega, h_lt_2100⟩
                                    · by_cases h_lt_2130 : L < 2130
                                      · exact card_divisors_lt_41_chunk14 L ⟨by omega, h_lt_2130⟩
                                      · by_cases h_lt_2160 : L < 2160
                                        · exact card_divisors_lt_41_chunk15 L ⟨by omega, h_lt_2160⟩
                                        · have : L = 2160 := by omega
                                          subst this
                                          decide
      omega
    · by_cases hn45 : n < 45
      · interval_cases n
        · -- n = 42
          rw [a_eq_sInf_candidates_a]
          apply Nat.sInf_le
          apply mem_candidates_a_of_mem_candidates_a08' (a08_mem 42 (by omega))
          intro L hdvd hL h_card D hD h_card_D
          have h_m_le : a081512 42 ≤ 2520 := a081512_42_le_2520
          have h1 : L ≤ 1260 := by omega
          have h2 : (Nat.divisors L).card < 37 := card_divisors_lt_37_of_le_1260 h1
          omega
        · -- n = 43
          rw [a_eq_sInf_candidates_a]
          apply Nat.sInf_le
          apply mem_candidates_a_of_mem_candidates_a08' (a08_mem 43 (by omega))
          intro L hdvd hL h_card D hD h_card_D
          have h_m_le : a081512 43 ≤ 2520 := a081512_43_le_2520
          have h1 : L ≤ 1260 := by omega
          have h2 : (Nat.divisors L).card < 37 := card_divisors_lt_37_of_le_1260 h1
          omega
        · -- n = 44
          rw [a_eq_sInf_candidates_a]
          apply Nat.sInf_le
          apply mem_candidates_a_of_mem_candidates_a08' (a08_mem 44 (by omega))
          intro L hdvd hL h_card D hD h_card_D
          have h_m_le : a081512 44 ≤ 2520 := a081512_44_le_2520
          have h1 : L ≤ 1260 := by omega
          have h2 : (Nat.divisors L).card < 37 := card_divisors_lt_37_of_le_1260 h1
          omega
      · -- n >= 45
        rw [a_eq_sInf_candidates_a]
        apply Nat.sInf_le
        apply mem_candidates_a_of_mem_candidates_a08' (a08_mem n (by omega))
        intro L hdvd hL h_card D hD h_card_D h_sum_D
        have hL_ge : 2520 ≤ L := by
          by_contra! hc_L
          have h_card_lt : (Nat.divisors L).card < 45 := by
            by_cases h_lt_1680 : L < 1680
            · have := card_divisors_lt_40_of_lt_1680 h_lt_1680
              omega
            · by_cases h_lt_1710 : L < 1710
              · have := card_divisors_lt_41_chunk0 L ⟨by omega, h_lt_1710⟩; omega
              · by_cases h_lt_1740 : L < 1740
                · have := card_divisors_lt_41_chunk1 L ⟨by omega, h_lt_1740⟩; omega
                · by_cases h_lt_1770 : L < 1770
                  · have := card_divisors_lt_41_chunk2 L ⟨by omega, h_lt_1770⟩; omega
                  · by_cases h_lt_1800 : L < 1800
                    · have := card_divisors_lt_41_chunk3 L ⟨by omega, h_lt_1800⟩; omega
                    · by_cases h_lt_1830 : L < 1830
                      · have := card_divisors_lt_41_chunk4 L ⟨by omega, h_lt_1830⟩; omega
                      · by_cases h_lt_1860 : L < 1860
                        · have := card_divisors_lt_41_chunk5 L ⟨by omega, h_lt_1860⟩; omega
                        · by_cases h_lt_1890 : L < 1890
                          · have := card_divisors_lt_41_chunk6 L ⟨by omega, h_lt_1890⟩; omega
                          · by_cases h_lt_1920 : L < 1920
                            · have := card_divisors_lt_41_chunk7 L ⟨by omega, h_lt_1920⟩; omega
                            · by_cases h_lt_1950 : L < 1950
                              · have := card_divisors_lt_41_chunk8 L ⟨by omega, h_lt_1950⟩; omega
                              · by_cases h_lt_1980 : L < 1980
                                · have := card_divisors_lt_41_chunk9 L ⟨by omega, h_lt_1980⟩; omega
                                · by_cases h_lt_2010 : L < 2010
                                  · have := card_divisors_lt_41_chunk10 L ⟨by omega, h_lt_2010⟩; omega
                                  · by_cases h_lt_2040 : L < 2040
                                    · have := card_divisors_lt_41_chunk11 L ⟨by omega, h_lt_2040⟩; omega
                                    · by_cases h_lt_2070 : L < 2070
                                      · have := card_divisors_lt_41_chunk12 L ⟨by omega, h_lt_2070⟩; omega
                                      · by_cases h_lt_2100 : L < 2100
                                        · have := card_divisors_lt_41_chunk13 L ⟨by omega, h_lt_2100⟩; omega
                                        · by_cases h_lt_2130 : L < 2130
                                          · have := card_divisors_lt_41_chunk14 L ⟨by omega, h_lt_2130⟩; omega
                                          · by_cases h_lt_2160 : L < 2160
                                            · have := card_divisors_lt_41_chunk15 L ⟨by omega, h_lt_2160⟩; omega
                                            · by_cases h_lt_2190 : L < 2190
                                              · exact card_divisors_lt_45_chunk0 L ⟨by omega, h_lt_2190⟩
                                              · by_cases h_lt_2220 : L < 2220
                                                · exact card_divisors_lt_45_chunk1 L ⟨by omega, h_lt_2220⟩
                                                · by_cases h_lt_2250 : L < 2250
                                                  · exact card_divisors_lt_45_chunk2 L ⟨by omega, h_lt_2250⟩
                                                  · by_cases h_lt_2280 : L < 2280
                                                    · exact card_divisors_lt_45_chunk3 L ⟨by omega, h_lt_2280⟩
                                                    · by_cases h_lt_2310 : L < 2310
                                                      · exact card_divisors_lt_45_chunk4 L ⟨by omega, h_lt_2310⟩
                                                      · by_cases h_lt_2340 : L < 2340
                                                        · exact card_divisors_lt_45_chunk5 L ⟨by omega, h_lt_2340⟩
                                                        · by_cases h_lt_2370 : L < 2370
                                                          · exact card_divisors_lt_45_chunk6 L ⟨by omega, h_lt_2370⟩
                                                          · by_cases h_lt_2400 : L < 2400
                                                            · exact card_divisors_lt_45_chunk7 L ⟨by omega, h_lt_2400⟩
                                                            · by_cases h_lt_2430 : L < 2430
                                                              · exact card_divisors_lt_45_chunk8 L ⟨by omega, h_lt_2430⟩
                                                              · by_cases h_lt_2460 : L < 2460
                                                                · exact card_divisors_lt_45_chunk9 L ⟨by omega, h_lt_2460⟩
                                                                · by_cases h_lt_2490 : L < 2490
                                                                  · exact card_divisors_lt_45_chunk10 L ⟨by omega, h_lt_2490⟩
                                                                  · exact card_divisors_lt_45_chunk11 L ⟨by omega, hc_L⟩
          omega
        by_cases hL_2520 : L = 2520
        · subst hL_2520
          have h_m_cases : a081512 n = 5040 ∨ a081512 n = 7560 ∨ (a081512 n ≠ 5040 ∧ a081512 n ≠ 7560) := by omega
          rcases h_m_cases with h5040 | h7560 | h_others
          · rw [h5040] at h_sum_D
            exact no_sum_2520_45_5040 D hD (by omega) h_sum_D
          · rw [h7560] at h_sum_D
            have hn46 : 46 ≤ n := by
              by_contra! hc_n
              have h_n45 : n = 45 := by omega
              subst h_n45
              have h_le5040 : a081512 45 ≤ 5040 := by
                rw [a081512_eq_sInf_candidates_a08]
                apply Nat.sInf_le
                rw [mem_candidates_a08_iff_powerset]
                refine ⟨by decide, ?_⟩
                let D_witness : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 28, 30, 35, 36, 40, 42, 45, 48, 56, 60, 63, 70, 72, 80, 84, 90, 105, 112, 120, 126, 140, 144, 168, 315, 336, 720, 1680}
                use D_witness
                refine ⟨by decide, by decide, by decide⟩
              omega
            exact no_sum_2520_46_7560 D hD (by omega) h_sum_D
          · have h_le_9360 : a081512 n ≤ 9360 := by
              have h_dvd : ∑ x ∈ D, id x = a081512 n := h_sum_D
              have h_sum_le_all : ∑ x ∈ D, id x ≤ ∑ x ∈ Nat.divisors 2520, id x := Finset.sum_le_sum_of_subset hD
              have : ∑ x ∈ Nat.divisors 2520, id x = 9360 := by decide
              omega
            have h_dvd_m : 2520 ∣ a081512 n := hdvd
            have h_cases : a081512 n = 2520 ∨ a081512 n = 5040 ∨ a081512 n = 7560 := by
              rcases h_dvd_m with ⟨k, hk⟩
              have hk_pos : 0 < k := by
                by_contra! hc_k
                have : k = 0 := by omega
                subst this
                have : a081512 n = 0 := by omega
                have : a081512 n > 0 := Nat.pos_of_mem_divisors (a08_mem n (by omega))
                omega
              have hk_le : k ≤ 3 := by
                have : 2520 * k ≤ 9360 := by omega
                omega
              interval_cases k
              · left; omega
              · right; left; omega
              · right; right; omega
            omega
        · have : 2 * L ≤ a081512 n := by omega
          omega


lemma a_le_a081512_of_ge_23 {n : ℕ} (hn : 23 ≤ n) : a n ≤ a081512 n := by
  by_cases hn25 : n < 25
  · interval_cases n
    · have h1 : a 23 ≤ 720 := a_witness_23
      have h2 : 720 ≤ a081512 23 := by
        apply m_ge_720_of_mem_candidates_a08 (by omega) (a08_mem 23 (by omega))
      omega
    · rw [a_eq_sInf_candidates_a]
      apply Nat.sInf_le
      exact a081512_24_mem_candidates_a
  · have hn25' : 25 ≤ n := by omega
    by_cases hn30 : n < 30
    · have h_le29 : n ≤ 29 := by omega
      have h_m_le : a081512 n ≤ 1260 := a081512_le_1260_of_le_29 hn25' h_le29
      rw [a_eq_sInf_candidates_a]
      apply Nat.sInf_le
      apply mem_candidates_a_of_mem_candidates_a08 (a08_mem n (by omega))
      intro L h_card
      have hL_ge : 720 ≤ L := L_ge_720_of_card_divisors_ge_25 (by omega)
      omega
    · by_cases hn33 : n < 33
      · have h_le32 : n ≤ 32 := by omega
        have h_m_le : a081512 n ≤ 1680 := a081512_le_1680_of_le_32 hn30 h_le32
        rw [a_eq_sInf_candidates_a]
        apply Nat.sInf_le
        apply mem_candidates_a_of_mem_candidates_a08' (a08_mem n (by omega))
        intro L hdvd hL h_card D hD h_card_D
        have h_L_cases : L = 720 ∨ L = 840 := by
          by_contra! hc
          have h1 : L ≤ 840 := hL.trans (by omega)
          have h2 : (Nat.divisors L).card < 30 := card_divisors_lt_30_of_le_840 h1 hc.1 hc.2
          omega
        rcases h_L_cases with rfl | rfl
        · have h_n30 : n = 30 := by
            have : (Nat.divisors 720).card = 30 := by decide
            have : D.card ≤ 30 := Finset.card_le_card hD
            omega
          have h_D_eq : D = Nat.divisors 720 := by
            apply Finset.eq_of_subset_of_card_le hD
            have : (Nat.divisors 720).card = 30 := by decide
            omega
          rw [h_D_eq]
          have : (Nat.divisors 720).sum id = 2418 := by decide
          omega
        · interval_cases n
          · rcases no_sum_840_30 D hD h_card_D with h_sum1 | h_sum2
            · intro h_eq
              have hm_eq : a081512 30 = 1620 := h_eq ▸ h_sum1
              have hm_mem : a081512 30 ∈ candidates_a08 30 := a08_mem 30 (by omega)
              rw [hm_eq] at hm_mem
              exact not_mem_1620_candidates_a08 hm_mem
            · omega
          · have := min_sum_840_31 D hD h_card_D
            omega
          · have := min_sum_840_32 D hD h_card_D
            omega
      · by_cases hn37 : n < 37
        · have h_le36 : n ≤ 36 := by omega
          have h_m_le : a081512 n ≤ 2520 := a081512_le_2520_of_le_36 hn33 h_le36
          rw [a_eq_sInf_candidates_a]
          apply Nat.sInf_le
          apply mem_candidates_a_of_mem_candidates_a08' (a08_mem n (by omega))
          intro L hdvd hL h_card D hD h_card_D
          have h_L_cases : L = 1260 := by
            by_contra! hc
            have h1 : L ≤ 1260 := hL.trans (by omega)
            have h2 : (Nat.divisors L).card < 33 := card_divisors_lt_33_of_le_1260 h1 hc
            omega
          subst h_L_cases
          interval_cases n
          · intro h_sum
            have := no_sum_1260_33 D hD h_card_D
            exact this h_sum.symm
          · rcases no_sum_1260_34 D hD h_card_D with h_sum1 | h_sum2
            · intro h_eq
              have hm_eq : a081512 34 = 2478 := h_eq ▸ h_sum1
              have hm_mem : a081512 34 ∈ candidates_a08 34 := a08_mem 34 (by omega)
              rw [hm_eq] at hm_mem
              exact not_mem_2478_candidates_a08 hm_mem
            · omega
          · have : 3108 ≤ D.sum id := min_sum_1260_35_ge_3108 D hD (by omega)
            omega
          · have : 3108 ≤ D.sum id := min_sum_1260_35_ge_3108 D hD (by omega)
            omega
        · by_cases hn40 : n < 40
          · have h_le39 : n ≤ 39 := by omega
            have h_m_le : a081512 n ≤ 2520 := a081512_le_2520_of_le_39 hn37 h_le39
            rw [a_eq_sInf_candidates_a]
            apply Nat.sInf_le
            apply mem_candidates_a_of_mem_candidates_a08' (a08_mem n (by omega))
            intro L hdvd hL h_card D hD h_card_D
            have h1 : L ≤ 1260 := hL.trans (by omega)
            have h2 : (Nat.divisors L).card < 37 := card_divisors_lt_37_of_le_1260 h1
            omega
          · exact test_hn40 n (by omega)

lemma a_le_a081512_of_ge_20 {n : ℕ} (hn : 20 ≤ n) : a n ≤ a081512 n := by
  by_cases hn23 : n ≤ 22
  · interval_cases n
    · rw [a08_20_eq_672]; exact a_witness_20
    · rw [a08_21_eq_720]; exact a_witness_21
    · rw [a08_22_eq_720]; exact a_witness_22
  · have hn23' : 23 ≤ n := by omega
    exact a_le_a081512_of_ge_23 hn23'
lemma a_le_a081512_of_ge_6 (n : ℕ) (hn : 6 ≤ n) : a n ≤ a081512 n := by
  by_cases hn20 : n ≤ 19
  · interval_cases n
    · rw [a08_six_eq_24]; exact a_witness_6
    · rw [a08_seven_eq_48]; exact a_seven_le_48
    · rw [a08_eight_eq_60]; exact a_witness_8
    · rw [a08_nine_eq_84]; exact a_witness_9
    · rw [a08_ten_eq_120]; exact a_witness_10
    · rw [a08_eleven_eq_120]; exact a_witness_11
    · rw [a08_twelve_eq_120]; exact a_witness_12
    · rw [a08_thirteen_eq_180]; exact a_witness_13
    · rw [a08_fourteen_eq_180]; exact a_witness_14
    · rw [a08_fifteen_eq_240]; exact a_witness_15
    · rw [a08_sixteen_eq_360]; exact a_witness_16
    · rw [a08_seventeen_eq_360]; exact a_witness_17
    · rw [a08_eighteen_eq_360]; exact a_witness_18
    · rw [a08_nineteen_eq_360]; exact a_witness_19
  · exact a_le_a081512_of_ge_20 (by omega)
