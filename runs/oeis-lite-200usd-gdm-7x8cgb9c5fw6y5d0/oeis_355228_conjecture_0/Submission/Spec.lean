import FormalConjectures.Util.ProblemImports

open Finset Nat Set

noncomputable def a (n : ℕ) : ℕ :=
  let candidates : Set ℕ :=
    { m : ℕ | 0 < m ∧
      ∃ D : Finset ℕ,
        D ⊆ Nat.divisors m ∧
        D.card = n ∧
        D.sum id = m ∧
        D.lcm id = m }
  sInf candidates

noncomputable def a081512 (n : ℕ) : ℕ :=
  let candidates : Set ℕ :=
    { m : ℕ | 0 < m ∧
      ∃ D : Finset ℕ,
        D ⊆ Nat.divisors m ∧
        D.card = n ∧
        D.sum id = m }
  sInf candidates

set_option maxRecDepth 1000000

def P_a08 (n m : ℕ) : Prop :=
  0 < m ∧ ∃ D ∈ (Nat.divisors m).powerset, D.card = n ∧ D.sum id = m

lemma P_a08_eq (n m : ℕ) :
  (0 < m ∧ ∃ D : Finset ℕ, D ⊆ Nat.divisors m ∧ D.card = n ∧ D.sum id = m) ↔ P_a08 n m := by
  unfold P_a08
  simp only [Finset.mem_powerset]

instance (n m : ℕ) : Decidable (P_a08 n m) := by
  unfold P_a08
  infer_instance

lemma a081512_def_eq (n : ℕ) :
  a081512 n = sInf { m : ℕ | P_a08 n m } := by
  unfold a081512
  simp_rw [P_a08_eq]

def P_a (n m : ℕ) : Prop :=
  0 < m ∧ ∃ D ∈ (Nat.divisors m).powerset, D.card = n ∧ D.sum id = m ∧ D.lcm id = m

lemma P_a_eq (n m : ℕ) :
  (0 < m ∧ ∃ D : Finset ℕ, D ⊆ Nat.divisors m ∧ D.card = n ∧ D.sum id = m ∧ D.lcm id = m) ↔ P_a n m := by
  unfold P_a
  simp only [Finset.mem_powerset]

instance (n m : ℕ) : Decidable (P_a n m) := by
  unfold P_a
  infer_instance

lemma a_def_eq (n : ℕ) :
  a n = sInf { m : ℕ | P_a n m } := by
  unfold a
  simp_rw [P_a_eq]

lemma a081512_zero : a081512 0 = 0 := by
  rw [a081512_def_eq]
  have h : { m : ℕ | P_a08 0 m } = ∅ := by
    ext m
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    rintro ⟨h1, D, hD, hcard, hsum⟩
    rw [Finset.mem_powerset] at hD
    rw [Finset.card_eq_zero] at hcard
    subst hcard
    simp only [sum_empty, id_eq] at hsum
    omega
  rw [h]
  exact Nat.sInf_empty

lemma a_zero : a 0 = 0 := by
  rw [a_def_eq]
  have h : { m : ℕ | P_a 0 m } = ∅ := by
    ext m
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    rintro ⟨h1, D, hD, hcard, hsum, _⟩
    rw [Finset.mem_powerset] at hD
    rw [Finset.card_eq_zero] at hcard
    subst hcard
    simp only [sum_empty, id_eq] at hsum
    omega
  rw [h]
  exact Nat.sInf_empty

lemma a081512_one : a081512 1 = 1 := by
  rw [a081512_def_eq]
  have h1 : sInf { m : ℕ | P_a08 1 m } ≤ 1 := by
    apply Nat.sInf_le
    simp only [mem_setOf_eq]
    decide
  have h2 : 1 ≤ sInf { m : ℕ | P_a08 1 m } := by
    by_contra! h
    have h_nonempty : { m : ℕ | P_a08 1 m }.Nonempty := by
      use 1
      simp only [mem_setOf_eq]
      decide
    have h_mem := Nat.sInf_mem h_nonempty
    simp only [mem_setOf_eq] at h_mem
    have h_all : ∀ k ∈ Finset.range 1, ¬ P_a08 1 k := by
      decide
    have h_in_range : sInf { m : ℕ | P_a08 1 m } ∈ Finset.range 1 := by
      rw [Finset.mem_range]
      exact h
    exact h_all (sInf { m : ℕ | P_a08 1 m }) h_in_range h_mem
  omega

lemma a_one : a 1 = 1 := by
  rw [a_def_eq]
  have h1 : sInf { m : ℕ | P_a 1 m } ≤ 1 := by
    apply Nat.sInf_le
    simp only [mem_setOf_eq]
    decide
  have h2 : 1 ≤ sInf { m : ℕ | P_a 1 m } := by
    by_contra! h
    have h_nonempty : { m : ℕ | P_a 1 m }.Nonempty := by
      use 1
      simp only [mem_setOf_eq]
      decide
    have h_mem := Nat.sInf_mem h_nonempty
    simp only [mem_setOf_eq] at h_mem
    have h_all : ∀ k ∈ Finset.range 1, ¬ P_a 1 k := by
      decide
    have h_in_range : sInf { m : ℕ | P_a 1 m } ∈ Finset.range 1 := by
      rw [Finset.mem_range]
      exact h
    exact h_all (sInf { m : ℕ | P_a 1 m }) h_in_range h_mem
  omega

lemma mul_two_le_of_dvd_and_lt {x m : ℕ} (hdiv : x ∣ m) (hlt : x < m) : 2 * x ≤ m := by
  rcases hdiv with ⟨c, rfl⟩
  have hc : 2 ≤ c := by
    by_contra! h
    interval_cases c
    · simp at hlt
    · simp at hlt
  rw [mul_comm]
  exact Nat.mul_le_mul_left x hc

lemma a081512_two : a081512 2 = 0 := by
  rw [a081512_def_eq]
  have h : { m : ℕ | P_a08 2 m } = ∅ := by
    ext m
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    rintro ⟨_, D, hD, hcard, hsum⟩
    rw [Finset.mem_powerset] at hD
    rw [Finset.card_eq_two] at hcard
    rcases hcard with ⟨x, y, hxy, rfl⟩
    rw [Finset.sum_pair hxy] at hsum
    simp only [id_eq] at hsum
    have hx_div : x ∈ divisors m := by
      apply hD
      simp
    have hy_div : y ∈ divisors m := by
      apply hD
      simp
    have hx_pos : 0 < x := Nat.pos_of_mem_divisors hx_div
    have hy_pos : 0 < y := Nat.pos_of_mem_divisors hy_div
    have hx_dvd : x ∣ m := Nat.dvd_of_mem_divisors hx_div
    have hy_dvd : y ∣ m := Nat.dvd_of_mem_divisors hy_div
    have hx_lt : x < m := by omega
    have hy_lt : y < m := by omega
    have hx_le := mul_two_le_of_dvd_and_lt hx_dvd hx_lt
    have hy_le := mul_two_le_of_dvd_and_lt hy_dvd hy_lt
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · have h2x : 2 * x < m := by omega
      omega
    · have h2y : 2 * y < m := by omega
      omega
  rw [h]
  exact Nat.sInf_empty

lemma a_two : a 2 = 0 := by
  rw [a_def_eq]
  have h : { m : ℕ | P_a 2 m } = ∅ := by
    ext m
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    rintro ⟨_, D, hD, hcard, hsum, hlcm⟩
    rw [Finset.mem_powerset] at hD
    rw [Finset.card_eq_two] at hcard
    rcases hcard with ⟨x, y, hxy, rfl⟩
    rw [Finset.sum_pair hxy] at hsum
    simp only [id_eq] at hsum
    have hx_div : x ∈ divisors m := by
      apply hD
      simp
    have hy_div : y ∈ divisors m := by
      apply hD
      simp
    have hx_pos : 0 < x := Nat.pos_of_mem_divisors hx_div
    have hy_pos : 0 < y := Nat.pos_of_mem_divisors hy_div
    have hx_dvd : x ∣ m := Nat.dvd_of_mem_divisors hx_div
    have hy_dvd : y ∣ m := Nat.dvd_of_mem_divisors hy_div
    have hx_lt : x < m := by omega
    have hy_lt : y < m := by omega
    have hx_le := mul_two_le_of_dvd_and_lt hx_dvd hx_lt
    have hy_le := mul_two_le_of_dvd_and_lt hy_dvd hy_lt
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · have h2x : 2 * x < m := by omega
      omega
    · have h2y : 2 * y < m := by omega
      omega
  rw [h]
  exact Nat.sInf_empty

lemma a081512_three : a081512 3 = 6 := by
  have h1 : a081512 3 ≤ 6 := by
    rw [a081512_def_eq]
    apply Nat.sInf_le
    simp only [mem_setOf_eq]
    decide
  have h2 : 6 ≤ a081512 3 := by
    rw [a081512_def_eq]
    by_contra! h
    have h_nonempty : { m : ℕ | P_a08 3 m }.Nonempty := by
      use 6
      simp only [mem_setOf_eq]
      decide
    have h_mem := Nat.sInf_mem h_nonempty
    simp only [mem_setOf_eq] at h_mem
    have h_all : ∀ k ∈ Finset.range 6, ¬ P_a08 3 k := by
      decide
    have h_in_range : sInf { m : ℕ | P_a08 3 m } ∈ Finset.range 6 := by
      rw [Finset.mem_range]
      exact h
    exact h_all (sInf { m : ℕ | P_a08 3 m }) h_in_range h_mem
  omega

lemma a_three : a 3 = 6 := by
  have h1 : a 3 ≤ 6 := by
    rw [a_def_eq]
    apply Nat.sInf_le
    simp only [mem_setOf_eq]
    decide
  have h2 : 6 ≤ a 3 := by
    rw [a_def_eq]
    by_contra! h
    have h_nonempty : { m : ℕ | P_a 3 m }.Nonempty := by
      use 6
      simp only [mem_setOf_eq]
      decide
    have h_mem := Nat.sInf_mem h_nonempty
    simp only [mem_setOf_eq] at h_mem
    have h_all : ∀ k ∈ Finset.range 6, ¬ P_a 3 k := by
      decide
    have h_in_range : sInf { m : ℕ | P_a 3 m } ∈ Finset.range 6 := by
      rw [Finset.mem_range]
      exact h
    exact h_all (sInf { m : ℕ | P_a 3 m }) h_in_range h_mem
  omega

lemma a081512_four : a081512 4 = 12 := by
  have h1 : a081512 4 ≤ 12 := by
    rw [a081512_def_eq]
    apply Nat.sInf_le
    simp only [mem_setOf_eq]
    decide
  have h2 : 12 ≤ a081512 4 := by
    rw [a081512_def_eq]
    by_contra! h
    have h_nonempty : { m : ℕ | P_a08 4 m }.Nonempty := by
      use 12
      simp only [mem_setOf_eq]
      decide
    have h_mem := Nat.sInf_mem h_nonempty
    simp only [mem_setOf_eq] at h_mem
    have h_all : ∀ k ∈ Finset.range 12, ¬ P_a08 4 k := by
      decide
    have h_in_range : sInf { m : ℕ | P_a08 4 m } ∈ Finset.range 12 := by
      rw [Finset.mem_range]
      exact h
    exact h_all (sInf { m : ℕ | P_a08 4 m }) h_in_range h_mem
  omega

lemma a081512_five : a081512 5 = 24 := by
  have h1 : a081512 5 ≤ 24 := by
    rw [a081512_def_eq]
    apply Nat.sInf_le
    simp only [mem_setOf_eq]
    decide
  have h2 : 24 ≤ a081512 5 := by
    rw [a081512_def_eq]
    by_contra! h
    have h_nonempty : { m : ℕ | P_a08 5 m }.Nonempty := by
      use 24
      simp only [mem_setOf_eq]
      decide
    have h_mem := Nat.sInf_mem h_nonempty
    simp only [mem_setOf_eq] at h_mem
    have h_all : ∀ k ∈ Finset.range 24, ¬ P_a08 5 k := by
      decide
    have h_in_range : sInf { m : ℕ | P_a08 5 m } ∈ Finset.range 24 := by
      rw [Finset.mem_range]
      exact h
    exact h_all (sInf { m : ℕ | P_a08 5 m }) h_in_range h_mem
  omega

lemma a_four : a 4 = 18 := by
  have h1 : a 4 ≤ 18 := by
    rw [a_def_eq]
    apply Nat.sInf_le
    simp only [mem_setOf_eq]
    decide
  have h2 : 18 ≤ a 4 := by
    rw [a_def_eq]
    by_contra! h
    have h_nonempty : { m : ℕ | P_a 4 m }.Nonempty := by
      use 18
      simp only [mem_setOf_eq]
      decide
    have h_mem := Nat.sInf_mem h_nonempty
    simp only [mem_setOf_eq] at h_mem
    have h_all : ∀ k ∈ Finset.range 18, ¬ P_a 4 k := by
      decide
    have h_in_range : sInf { m : ℕ | P_a 4 m } ∈ Finset.range 18 := by
      rw [Finset.mem_range]
      exact h
    exact h_all (sInf { m : ℕ | P_a 4 m }) h_in_range h_mem
  omega

lemma a_five : a 5 = 28 := by
  have h1 : a 5 ≤ 28 := by
    rw [a_def_eq]
    apply Nat.sInf_le
    simp only [mem_setOf_eq]
    decide
  have h2 : 28 ≤ a 5 := by
    rw [a_def_eq]
    by_contra! h
    have h_nonempty : { m : ℕ | P_a 5 m }.Nonempty := by
      use 28
      simp only [mem_setOf_eq]
      decide
    have h_mem := Nat.sInf_mem h_nonempty
    simp only [mem_setOf_eq] at h_mem
    have h_all : ∀ k ∈ Finset.range 28, ¬ P_a 5 k := by
      decide
    have h_in_range : sInf { m : ℕ | P_a 5 m } ∈ Finset.range 28 := by
      rw [Finset.mem_range]
      exact h
    exact h_all (sInf { m : ℕ | P_a 5 m }) h_in_range h_mem
  omega

lemma a_le_a081512_of_lemma {k : ℕ} (h_lem : ∀ m, P_a08 k m → ∃ m' ≤ m, P_a k m') : a k ≤ a081512 k := by
  rw [a081512_def_eq, a_def_eq]
  by_cases h_empty : { m : ℕ | P_a08 k m } = ∅
  · rw [h_empty]
    have h_sub : { m : ℕ | P_a k m } ⊆ { m : ℕ | P_a08 k m } := by
      intro x hx
      simp only [mem_setOf_eq] at hx ⊢
      rcases hx with ⟨hx1, D, hD, hcard, hsum, hlcm⟩
      refine ⟨hx1, D, hD, hcard, hsum⟩
    have h_empty_a : { m : ℕ | P_a k m } = ∅ := by
      rw [h_empty] at h_sub
      exact Set.subset_empty_iff.mp h_sub
    rw [h_empty_a]
  · have h_nonempty : { m : ℕ | P_a08 k m }.Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty
    have h_mem := Nat.sInf_mem h_nonempty
    simp only [mem_setOf_eq] at h_mem
    rcases h_lem (sInf { m : ℕ | P_a08 k m }) h_mem with ⟨m', hm'_le, hm'_Pa⟩
    have h_mem_a : m' ∈ { x : ℕ | P_a k x } := by
      simp only [mem_setOf_eq]
      exact hm'_Pa
    have h_le := Nat.sInf_le h_mem_a
    exact le_trans h_le hm'_le

lemma lcm_dvd_of_subset_divisors {D : Finset ℕ} {m : ℕ} (hD : D ⊆ divisors m) :
    D.lcm id ∣ m := by
  apply Finset.lcm_dvd
  intro b hb
  have h_b_div := hD hb
  exact Nat.dvd_of_mem_divisors h_b_div

lemma helper (k : ℕ) (hk : 6 ≤ k) (m : ℕ) : P_a08 k m → ∃ m' ≤ m, P_a k m' := by
  induction' m using Nat.strong_induction_on with m ih
  intro hm
  by_cases h_exists : ∃ m' < m, P_a08 k m'
  · rcases h_exists with ⟨m', hm'_lt, hm'_Pa08⟩
    rcases ih m' hm'_lt hm'_Pa08 with ⟨m'', hm''_le, hm''_Pa⟩
    use m''
    refine ⟨by omega, hm''_Pa⟩
  · have hm_copy := hm
    rcases hm with ⟨h_pos, D, hD, hcard, hsum⟩
    rw [Finset.mem_powerset] at hD
    let L := D.lcm id
    have hL_dvd : L ∣ m := lcm_dvd_of_subset_divisors hD
    have hL_le : L ≤ m := Nat.le_of_dvd h_pos hL_dvd
    by_cases hL : L = m
    · use m
      refine ⟨le_rfl, ?_⟩
      rw [← P_a_eq]
      exact ⟨h_pos, D, hD, hcard, hsum, hL⟩
    · have hL_lt : L < m := lt_of_le_of_ne hL_le hL
      rcases k with _ | _ | _ | _ | _ | _ | k
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      rcases k with _ | k
      · -- k = 6: m = 24.
        have h_ge : 24 ≤ m := by
          by_contra! h_lt
          have h_all : ∀ x ∈ Finset.range 24, ¬ P_a08 6 x := by decide
          have h_in_range : m ∈ Finset.range 24 := Finset.mem_range.mpr h_lt
          exact h_all m h_in_range hm_copy
        have h_le : m ≤ 24 := by
          by_contra! h_gt
          have h24_lt : 24 < m := h_gt
          have h24_P : P_a08 6 24 := by decide
          exact h_exists ⟨24, h24_lt, h24_P⟩
        have hm_eq : m = 24 := by omega
        subst hm_eq
        use 24
        refine ⟨le_rfl, ?_⟩
        rw [← P_a_eq]
        decide
      · -- k ≥ 7
        by_cases hk7 : k = 0
        · subst hk7  -- k = 7
          have h_ge : 48 ≤ m := by
            by_contra! h_lt
            have h_all : ∀ x ∈ Finset.range 48, ¬ P_a08 7 x := by decide
            have h_in_range : m ∈ Finset.range 48 := Finset.mem_range.mpr h_lt
            exact h_all m h_in_range hm_copy
          have h_le : m ≤ 48 := by
            by_contra! h_gt
            have h48_lt : 48 < m := h_gt
            have h48_P : P_a08 7 48 := by decide
            exact h_exists ⟨48, h48_lt, h48_P⟩
          have hm_eq : m = 48 := by omega
          subst hm_eq
          use 48
          refine ⟨le_rfl, ?_⟩
          rw [← P_a_eq]
          decide
        · -- k ≥ 8
          sorry

lemma a_le_a081512_of_helper {k : ℕ} (hk : 6 ≤ k) : a k ≤ a081512 k := by
  apply a_le_a081512_of_lemma
  intro m hm
  exact helper k hk m hm

theorem oeis_355228_conjecture_0 (n : ℕ) :
  (a n > a081512 n) ↔ (n = 4 ∨ n = 5) := by
  rcases n with _ | _ | _ | _ | _ | _ | n
  · rw [a_zero, a081512_zero]
    simp
  · rw [a_one, a081512_one]
    simp
  · rw [a_two, a081512_two]
    simp
  · rw [a_three, a081512_three]
    simp
  · rw [a_four, a081512_four]
    simp
  · rw [a_five, a081512_five]
    simp
  · have h_rhs : ¬ (n + 6 = 4 ∨ n + 6 = 5) := by omega
    simp only [h_rhs, iff_false, not_lt]
    exact a_le_a081512_of_helper (by omega)
