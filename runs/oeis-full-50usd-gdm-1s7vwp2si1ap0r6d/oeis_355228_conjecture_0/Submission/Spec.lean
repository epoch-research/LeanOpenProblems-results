import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
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

def S_a08 (n : ℕ) : Set ℕ :=
  { m : ℕ | 0 < m ∧
    ∃ D : Finset ℕ,
      D ⊆ Nat.divisors m ∧
      D.card = n ∧
      D.sum id = m }

def S_a (n : ℕ) : Set ℕ :=
  { m : ℕ | 0 < m ∧
    ∃ D : Finset ℕ,
      D ⊆ Nat.divisors m ∧
      D.card = n ∧
      D.sum id = m ∧
      D.lcm id = m }

lemma divisors_subset_sum_sub {n : ℕ} {D : Finset ℕ} {L : ℕ} (hD : D ⊆ Nat.divisors L) (hsum : D.sum id = 2 * L) (hL : L ∈ D) (hcard : D.card = n + 6) :
  ∃ D' : Finset ℕ, D' ⊆ Nat.divisors L ∧ D'.card = n + 5 ∧ D'.sum id = L := by
  use D.erase L
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    apply hD
    exact Finset.mem_of_mem_erase hx
  · rw [Finset.card_erase_of_mem hL, hcard]
    rfl
  · rw [← Finset.sum_erase_add D id hL] at hsum
    change (D.erase L).sum id + L = 2 * L at hsum
    omega

lemma a081512_eq_sInf_S_a08 (n : ℕ) : a081512 n = sInf (S_a08 n) := rfl
lemma a_eq_sInf_S_a (n : ℕ) : a n = sInf (S_a n) := rfl

abbrev is_candidate_dec (n m : ℕ) : Prop :=
  m ≠ 0 ∧ ((Nat.divisors m).powerset.filter (fun D => D.card = n ∧ D.sum id = m)) ≠ ∅

lemma is_candidate_dec_iff (n m : ℕ) : is_candidate_dec n m ↔ m ∈ S_a08 n := by
  dsimp [is_candidate_dec, S_a08]
  constructor
  · rintro ⟨hm0, hD⟩
    refine ⟨Nat.pos_of_ne_zero hm0, ?_⟩
    rcases Finset.nonempty_iff_ne_empty.mpr hD with ⟨D, hDmem⟩
    simp only [Finset.mem_filter, Finset.mem_powerset] at hDmem
    exact ⟨D, hDmem.1, hDmem.2.1, hDmem.2.2⟩
  · rintro ⟨hm0, D, hD, hcard, hsum⟩
    refine ⟨hm0.ne', ?_⟩
    apply Finset.nonempty_iff_ne_empty.mp
    use D
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hD, hcard, hsum⟩

abbrev is_a_candidate_dec (n m : ℕ) : Prop :=
  m ≠ 0 ∧ ((Nat.divisors m).powerset.filter (fun D => D.card = n ∧ D.sum id = m ∧ D.lcm id = m)) ≠ ∅

lemma is_a_candidate_dec_iff (n m : ℕ) : is_a_candidate_dec n m ↔ m ∈ S_a n := by
  dsimp [is_a_candidate_dec, S_a]
  constructor
  · rintro ⟨hm0, hD⟩
    refine ⟨Nat.pos_of_ne_zero hm0, ?_⟩
    rcases Finset.nonempty_iff_ne_empty.mpr hD with ⟨D, hDmem⟩
    simp only [Finset.mem_filter, Finset.mem_powerset] at hDmem
    exact ⟨D, hDmem.1, hDmem.2.1, hDmem.2.2.1, hDmem.2.2.2⟩
  · rintro ⟨hm0, D, hD, hcard, hsum, hlcm⟩
    refine ⟨hm0.ne', ?_⟩
    apply Finset.nonempty_iff_ne_empty.mp
    use D
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hD, hcard, hsum, hlcm⟩

lemma no_candidate_two_helper (m x y : ℕ) (_hx : x ∣ m) (hy : y ∣ m) (hx_pos : 0 < x) (_hy_pos : 0 < y) (hxy : x < y) (hsum : x + y = m) : False := by
  have hk : ∃ k, m = y * k := hy
  rcases hk with ⟨k, hk_eq⟩
  have hk_gt : 1 < k := by
    by_contra hc
    have hc' : k ≤ 1 := Nat.le_of_not_lt hc
    interval_cases k
    · rw [hk_eq] at hsum
      simp at hsum
      omega
    · rw [hk_eq] at hsum
      simp at hsum
      omega
  have hk_ge : 2 ≤ k := hk_gt
  have h_y_le : y * 2 ≤ m := by
    rw [hk_eq]
    apply Nat.mul_le_mul_left
    exact hk_ge
  have h_x_le : x * 2 < y * 2 := by omega
  omega

lemma no_candidate_two_helper_symm (m x y : ℕ) (hx : x ∣ m) (hy : y ∣ m) (hx_pos : 0 < x) (hy_pos : 0 < y) (hxy : x ≠ y) (hsum : x + y = m) : False := by
  rcases lt_trichotomy x y with hlt | rfl | hgt
  · exact no_candidate_two_helper m x y hx hy hx_pos hy_pos hlt hsum
  · contradiction
  · have hsum' : y + x = m := by omega
    exact no_candidate_two_helper m y x hy hx hy_pos hx_pos hgt hsum'

lemma S_a08_two_empty : S_a08 2 = ∅ := by
  apply Set.ext
  intro m
  simp only [S_a08, mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨hm0, D, hD, hcard, hsum⟩
  rcases card_eq_two.mp hcard with ⟨x, y, hxy, hD_eq⟩
  have hx : x ∈ Nat.divisors m := by
    apply hD
    rw [hD_eq]
    simp
  have hy : y ∈ Nat.divisors m := by
    apply hD
    rw [hD_eq]
    simp
  have hx_div : x ∣ m := Nat.dvd_of_mem_divisors hx
  have hy_div : y ∣ m := Nat.dvd_of_mem_divisors hy
  have hx_pos : 0 < x := Nat.pos_of_mem_divisors hx
  have hy_pos : 0 < y := Nat.pos_of_mem_divisors hy
  have hsum' : x + y = m := by
    rw [hD_eq] at hsum
    simp [hxy] at hsum
    exact hsum
  exact no_candidate_two_helper_symm m x y hx_div hy_div hx_pos hy_pos hxy hsum'

lemma S_a_subset_S_a08 (n : ℕ) : S_a n ⊆ S_a08 n := by
  intro m hm
  rcases hm with ⟨hm0, D, hD, hcard, hsum, hlcm⟩
  exact ⟨hm0, D, hD, hcard, hsum⟩

lemma S_a_two_empty : S_a 2 = ∅ := by
  have h_sub := S_a_subset_S_a08 2
  rw [S_a08_two_empty] at h_sub
  exact Set.subset_empty_iff.mp h_sub

lemma a081512_two : a081512 2 = 0 := by
  rw [a081512_eq_sInf_S_a08, S_a08_two_empty]
  simp

lemma a_two : a 2 = 0 := by
  rw [a_eq_sInf_S_a, S_a_two_empty]
  simp

lemma S_a08_zero_empty : S_a08 0 = ∅ := by
  apply Set.ext
  intro m
  simp only [S_a08, mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨hm0, D, hD, hcard, hsum⟩
  have hD_empty : D = ∅ := card_eq_zero.mp hcard
  rw [hD_empty] at hsum
  simp [id] at hsum
  omega

lemma a081512_zero : a081512 0 = 0 := by
  rw [a081512_eq_sInf_S_a08, S_a08_zero_empty]
  simp

lemma S_a_zero_empty : S_a 0 = ∅ := by
  have h_sub := S_a_subset_S_a08 0
  rw [S_a08_zero_empty] at h_sub
  exact Set.subset_empty_iff.mp h_sub

lemma a_zero : a 0 = 0 := by
  rw [a_eq_sInf_S_a, S_a_zero_empty]
  simp

lemma no_smaller_candidate_one : ∀ m < 1, m ∉ S_a08 1 := by
  intro m hm h_mem
  rcases h_mem with ⟨hm0, -⟩
  omega

lemma a081512_one : a081512 1 = 1 := by
  rw [a081512_eq_sInf_S_a08]
  have h1 : 1 ∈ S_a08 1 := by
    rw [← is_candidate_dec_iff]
    decide
  have h_le : sInf (S_a08 1) ≤ 1 := Nat.sInf_le h1
  have h_ge : 1 ≤ sInf (S_a08 1) := by
    have h_nonempty : (S_a08 1).Nonempty := ⟨1, h1⟩
    have h_mem : sInf (S_a08 1) ∈ S_a08 1 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a08 1) < 1 := by
      intro hc
      exact no_smaller_candidate_one _ hc h_mem
    omega
  omega

lemma no_smaller_candidate_a_one : ∀ m < 1, m ∉ S_a 1 := by
  intro m hm h_mem
  rcases h_mem with ⟨hm0, -⟩
  omega

lemma a_one : a 1 = 1 := by
  rw [a_eq_sInf_S_a]
  have h1 : 1 ∈ S_a 1 := by
    rw [← is_a_candidate_dec_iff]
    decide
  have h_le : sInf (S_a 1) ≤ 1 := Nat.sInf_le h1
  have h_ge : 1 ≤ sInf (S_a 1) := by
    have h_nonempty : (S_a 1).Nonempty := ⟨1, h1⟩
    have h_mem : sInf (S_a 1) ∈ S_a 1 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a 1) < 1 := by
      intro hc
      exact no_smaller_candidate_a_one _ hc h_mem
    omega
  omega

lemma no_smaller_candidate_three : ∀ m < 6, m ∉ S_a08 3 := by
  intro m hm
  rw [← is_candidate_dec_iff]
  interval_cases m <;> decide

lemma a081512_three : a081512 3 = 6 := by
  rw [a081512_eq_sInf_S_a08]
  have h6 : 6 ∈ S_a08 3 := by
    rw [← is_candidate_dec_iff]
    decide
  have h_le : sInf (S_a08 3) ≤ 6 := Nat.sInf_le h6
  have h_ge : 6 ≤ sInf (S_a08 3) := by
    have h_nonempty : (S_a08 3).Nonempty := ⟨6, h6⟩
    have h_mem : sInf (S_a08 3) ∈ S_a08 3 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a08 3) < 6 := by
      intro hc
      exact no_smaller_candidate_three _ hc h_mem
    omega
  omega

lemma no_smaller_candidate_a_three : ∀ m < 6, m ∉ S_a 3 := by
  intro m hm
  rw [← is_a_candidate_dec_iff]
  interval_cases m <;> decide

lemma a_three : a 3 = 6 := by
  rw [a_eq_sInf_S_a]
  have h6 : 6 ∈ S_a 3 := by
    rw [← is_a_candidate_dec_iff]
    decide
  have h_le : sInf (S_a 3) ≤ 6 := Nat.sInf_le h6
  have h_ge : 6 ≤ sInf (S_a 3) := by
    have h_nonempty : (S_a 3).Nonempty := ⟨6, h6⟩
    have h_mem : sInf (S_a 3) ∈ S_a 3 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a 3) < 6 := by
      intro hc
      exact no_smaller_candidate_a_three _ hc h_mem
    omega
  omega

lemma no_smaller_candidate_four : ∀ m < 12, m ∉ S_a08 4 := by
  intro m hm
  rw [← is_candidate_dec_iff]
  interval_cases m <;> decide

lemma a081512_four : a081512 4 = 12 := by
  rw [a081512_eq_sInf_S_a08]
  have h12 : 12 ∈ S_a08 4 := by
    rw [← is_candidate_dec_iff]
    decide
  have h_le : sInf (S_a08 4) ≤ 12 := Nat.sInf_le h12
  have h_ge : 12 ≤ sInf (S_a08 4) := by
    have h_nonempty : (S_a08 4).Nonempty := ⟨12, h12⟩
    have h_mem : sInf (S_a08 4) ∈ S_a08 4 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a08 4) < 12 := by
      intro hc
      exact no_smaller_candidate_four _ hc h_mem
    omega
  omega

lemma no_smaller_candidate_a_four : ∀ m < 18, m ∉ S_a 4 := by
  intro m hm
  rw [← is_a_candidate_dec_iff]
  interval_cases m <;> decide

lemma a_four : a 4 = 18 := by
  rw [a_eq_sInf_S_a]
  have h18 : 18 ∈ S_a 4 := by
    rw [← is_a_candidate_dec_iff]
    decide
  have h_le : sInf (S_a 4) ≤ 18 := Nat.sInf_le h18
  have h_ge : 18 ≤ sInf (S_a 4) := by
    have h_nonempty : (S_a 4).Nonempty := ⟨18, h18⟩
    have h_mem : sInf (S_a 4) ∈ S_a 4 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a 4) < 18 := by
      intro hc
      exact no_smaller_candidate_a_four _ hc h_mem
    omega
  omega

lemma no_smaller_candidate_a08_five : ∀ m < 24, m ∉ S_a08 5 := by
  intro m hm
  rw [← is_candidate_dec_iff]
  interval_cases m <;> decide

lemma a081512_five : a081512 5 = 24 := by
  rw [a081512_eq_sInf_S_a08]
  have h24 : 24 ∈ S_a08 5 := by
    rw [← is_candidate_dec_iff]
    decide
  have h_le : sInf (S_a08 5) ≤ 24 := Nat.sInf_le h24
  have h_ge : 24 ≤ sInf (S_a08 5) := by
    have h_nonempty : (S_a08 5).Nonempty := ⟨24, h24⟩
    have h_mem : sInf (S_a08 5) ∈ S_a08 5 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a08 5) < 24 := by
      intro hc
      exact no_smaller_candidate_a08_five _ hc h_mem
    omega
  omega

lemma no_smaller_candidate_a_five : ∀ m < 28, m ∉ S_a 5 := by
  intro m hm
  rw [← is_a_candidate_dec_iff]
  interval_cases m <;> decide

lemma a_five : a 5 = 28 := by
  rw [a_eq_sInf_S_a]
  have h28 : 28 ∈ S_a 5 := by
    rw [← is_a_candidate_dec_iff]
    decide
  have h_le : sInf (S_a 5) ≤ 28 := Nat.sInf_le h28
  have h_ge : 28 ≤ sInf (S_a 5) := by
    have h_nonempty : (S_a 5).Nonempty := ⟨28, h28⟩
    have h_mem : sInf (S_a 5) ∈ S_a 5 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a 5) < 28 := by
      intro hc
      exact no_smaller_candidate_a_five _ hc h_mem
    omega
  omega

lemma no_smaller_candidate_a08_six : ∀ m < 24, m ∉ S_a08 6 := by
  intro m hm
  rw [← is_candidate_dec_iff]
  interval_cases m <;> decide

lemma a081512_six : a081512 6 = 24 := by
  rw [a081512_eq_sInf_S_a08]
  have h24 : 24 ∈ S_a08 6 := by
    rw [← is_candidate_dec_iff]
    decide
  have h_le : sInf (S_a08 6) ≤ 24 := Nat.sInf_le h24
  have h_ge : 24 ≤ sInf (S_a08 6) := by
    have h_nonempty : (S_a08 6).Nonempty := ⟨24, h24⟩
    have h_mem : sInf (S_a08 6) ∈ S_a08 6 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a08 6) < 24 := by
      intro hc
      exact no_smaller_candidate_a08_six _ hc h_mem
    omega
  omega

lemma no_smaller_candidate_a_six : ∀ m < 24, m ∉ S_a 6 := by
  intro m hm
  rw [← is_a_candidate_dec_iff]
  interval_cases m <;> decide

lemma a_six : a 6 = 24 := by
  rw [a_eq_sInf_S_a]
  have h24 : 24 ∈ S_a 6 := by
    rw [← is_a_candidate_dec_iff]
    decide
  have h_le : sInf (S_a 6) ≤ 24 := Nat.sInf_le h24
  have h_ge : 24 ≤ sInf (S_a 6) := by
    have h_nonempty : (S_a 6).Nonempty := ⟨24, h24⟩
    have h_mem : sInf (S_a 6) ∈ S_a 6 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a 6) < 24 := by
      intro hc
      exact no_smaller_candidate_a_six _ hc h_mem
    omega
  omega

lemma no_smaller_candidate_a08_seven : ∀ m < 48, m ∉ S_a08 7 := by
  intro m hm
  rw [← is_candidate_dec_iff]
  interval_cases m <;> decide

lemma a081512_seven : a081512 7 = 48 := by
  rw [a081512_eq_sInf_S_a08]
  have h48 : 48 ∈ S_a08 7 := by
    rw [← is_candidate_dec_iff]
    decide
  have h_le : sInf (S_a08 7) ≤ 48 := Nat.sInf_le h48
  have h_ge : 48 ≤ sInf (S_a08 7) := by
    have h_nonempty : (S_a08 7).Nonempty := ⟨48, h48⟩
    have h_mem : sInf (S_a08 7) ∈ S_a08 7 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a08 7) < 48 := by
      intro hc
      exact no_smaller_candidate_a08_seven _ hc h_mem
    omega
  omega

lemma no_smaller_candidate_a_seven : ∀ m < 48, m ∉ S_a 7 := by
  intro m hm
  rw [← is_a_candidate_dec_iff]
  interval_cases m <;> decide

lemma a_seven : a 7 = 48 := by
  rw [a_eq_sInf_S_a]
  have h48 : 48 ∈ S_a 7 := by
    rw [← is_a_candidate_dec_iff]
    decide
  have h_le : sInf (S_a 7) ≤ 48 := Nat.sInf_le h48
  have h_ge : 48 ≤ sInf (S_a 7) := by
    have h_nonempty : (S_a 7).Nonempty := ⟨48, h48⟩
    have h_mem : sInf (S_a 7) ∈ S_a 7 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a 7) < 48 := by
      intro hc
      exact no_smaller_candidate_a_seven _ hc h_mem
    omega
  omega

lemma mem_S_a08_imp_abundant {n m : ℕ} (hn : 2 ≤ n) (hm : m ∈ S_a08 n) :
  2 * m ≤ (Nat.divisors m).sum id := by
  rcases hm with ⟨hm0, D, hD, hcard, hsum⟩
  have hm_notin : m ∉ D := by
    intro hmem
    have h_sum_eq : D.sum id = (D.erase m).sum id + m := by
      rw [← Finset.sum_erase_add D id hmem]
      rfl
    have h_card_erase : (D.erase m).card = n - 1 := by
      rw [Finset.card_erase_of_mem hmem, hcard]
    have h_erase_nonempty : (D.erase m).Nonempty := by
      apply Finset.card_pos.mp
      omega
    rcases h_erase_nonempty with ⟨x, hx⟩
    have hx_pos : 0 < x := by
      have hx_div : x ∈ Nat.divisors m := by
        apply hD
        exact Finset.mem_of_mem_erase hx
      exact Nat.pos_of_mem_divisors hx_div
    have h_sum_erase_ge : id x ≤ (D.erase m).sum id := Finset.single_le_sum (fun a _ => Nat.zero_le a) hx
    change x ≤ (D.erase m).sum id at h_sum_erase_ge
    omega
  have h_sub : D ⊆ (Nat.divisors m).erase m := by
    intro x hx
    rw [Finset.mem_erase]
    refine ⟨?_, hD hx⟩
    rintro rfl
    exact hm_notin hx
  have h_sum_le : D.sum id ≤ ((Nat.divisors m).erase m).sum id := Finset.sum_le_sum_of_subset h_sub
  have h_sum_divisors : (Nat.divisors m).sum id = ((Nat.divisors m).erase m).sum id + m := by
    rw [← Finset.sum_erase_add (Nat.divisors m) id (Nat.mem_divisors_self m hm0.ne')]
    rfl
  omega

lemma mem_S_a08_imp_card_divisors {n m : ℕ} (hn : 2 ≤ n) (hm : m ∈ S_a08 n) :
  n < (Nat.divisors m).card := by
  rcases hm with ⟨hm0, D, hD, hcard, hsum⟩
  have hm_notin : m ∉ D := by
    intro hmem
    have h_sum_eq : D.sum id = (D.erase m).sum id + m := by
      rw [← Finset.sum_erase_add D id hmem]
      rfl
    have h_card_erase : (D.erase m).card = n - 1 := by
      rw [Finset.card_erase_of_mem hmem, hcard]
    have h_erase_nonempty : (D.erase m).Nonempty := by
      apply Finset.card_pos.mp
      omega
    rcases h_erase_nonempty with ⟨x, hx⟩
    have hx_pos : 0 < x := by
      have hx_div : x ∈ Nat.divisors m := by
        apply hD
        exact Finset.mem_of_mem_erase hx
      exact Nat.pos_of_mem_divisors hx_div
    have h_sum_erase_ge : id x ≤ (D.erase m).sum id := Finset.single_le_sum (fun a _ => Nat.zero_le a) hx
    change x ≤ (D.erase m).sum id at h_sum_erase_ge
    omega
  have h_sub : D ⊆ (Nat.divisors m).erase m := by
    intro x hx
    rw [Finset.mem_erase]
    refine ⟨?_, hD hx⟩
    rintro rfl
    exact hm_notin hx
  have h_card_le : D.card ≤ ((Nat.divisors m).erase m).card := Finset.card_le_card h_sub
  have h_card_erase_div : ((Nat.divisors m).erase m).card = (Nat.divisors m).card - 1 := by
    rw [Finset.card_erase_of_mem (Nat.mem_divisors_self m hm0.ne')]
  omega

lemma no_smaller_candidate_a_from_a08 {n : ℕ} {C : ℕ} (h08 : ∀ x < C, x ∉ S_a08 n) :
  ∀ x < C, x ∉ S_a n := by
  intro x hx h_mem
  exact h08 x hx (S_a_subset_S_a08 n h_mem)

lemma no_smaller_candidate_a08_8 : ∀ m < 60, m ∉ S_a08 8 := by
  intro m hm h_mem
  have h_ab : 2 * m ≤ (Nat.divisors m).sum id := mem_S_a08_imp_abundant (by decide) h_mem
  have h_cd : 8 < (Nat.divisors m).card := mem_S_a08_imp_card_divisors (by decide) h_mem
  have h_poss : m = 36 ∨ m = 48 := by
    have h_dec : ∀ x < 60, 2 * x ≤ (Nat.divisors x).sum id ∧ 8 < (Nat.divisors x).card → x = 36 ∨ x = 48 := by decide
    exact h_dec m hm ⟨h_ab, h_cd⟩
  rcases h_poss with rfl | rfl
  · have h_dec : ¬ is_candidate_dec 8 36 := by decide
    rw [is_candidate_dec_iff] at h_dec
    exact h_dec h_mem
  · have h_dec : ¬ is_candidate_dec 8 48 := by decide
    rw [is_candidate_dec_iff] at h_dec
    exact h_dec h_mem

lemma no_smaller_candidate_a_8 : ∀ m < 60, m ∉ S_a 8 :=
  no_smaller_candidate_a_from_a08 no_smaller_candidate_a08_8

lemma a081512_8 : a081512 8 = 60 := by
  rw [a081512_eq_sInf_S_a08]
  have h60 : 60 ∈ S_a08 8 := by
    dsimp [S_a08]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 10, 15, 20}
    refine ⟨?_, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h_le : sInf (S_a08 8) ≤ 60 := Nat.sInf_le h60
  have h_ge : 60 ≤ sInf (S_a08 8) := by
    have h_nonempty : (S_a08 8).Nonempty := ⟨60, h60⟩
    have h_mem : sInf (S_a08 8) ∈ S_a08 8 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a08 8) < 60 := by
      intro hc
      exact no_smaller_candidate_a08_8 _ hc h_mem
    omega
  omega

lemma a_8 : a 8 = 60 := by
  rw [a_eq_sInf_S_a]
  have h60 : 60 ∈ S_a 8 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 10, 15, 20}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h_le : sInf (S_a 8) ≤ 60 := Nat.sInf_le h60
  have h_ge : 60 ≤ sInf (S_a 8) := by
    have h_nonempty : (S_a 8).Nonempty := ⟨60, h60⟩
    have h_mem : sInf (S_a 8) ∈ S_a 8 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a 8) < 60 := by
      intro hc
      exact no_smaller_candidate_a_8 _ hc h_mem
    omega
  omega

lemma no_smaller_candidate_a08_9 : ∀ m < 84, m ∉ S_a08 9 := by
  intro m hm h_mem
  have h_ab : 2 * m ≤ (Nat.divisors m).sum id := mem_S_a08_imp_abundant (by decide) h_mem
  have h_cd : 9 < (Nat.divisors m).card := mem_S_a08_imp_card_divisors (by decide) h_mem
  have h_poss : m = 48 ∨ m = 60 ∨ m = 72 ∨ m = 80 := by
    have h_dec : ∀ x < 84, 2 * x ≤ (Nat.divisors x).sum id ∧ 9 < (Nat.divisors x).card → x = 48 ∨ x = 60 ∨ x = 72 ∨ x = 80 := by decide
    exact h_dec m hm ⟨h_ab, h_cd⟩
  rcases h_poss with rfl | rfl | rfl | rfl
  · have h_dec : ¬ is_candidate_dec 9 48 := by decide
    rw [is_candidate_dec_iff] at h_dec
    exact h_dec h_mem
  · have h_dec : ¬ is_candidate_dec 9 60 := by decide
    rw [is_candidate_dec_iff] at h_dec
    exact h_dec h_mem
  · have h_dec : ¬ is_candidate_dec 9 72 := by decide
    rw [is_candidate_dec_iff] at h_dec
    exact h_dec h_mem
  · have h_dec : ¬ is_candidate_dec 9 80 := by decide
    rw [is_candidate_dec_iff] at h_dec
    exact h_dec h_mem

lemma no_smaller_candidate_a_9 : ∀ m < 84, m ∉ S_a 9 :=
  no_smaller_candidate_a_from_a08 no_smaller_candidate_a08_9

lemma a081512_9 : a081512 9 = 84 := by
  rw [a081512_eq_sInf_S_a08]
  have h84 : 84 ∈ S_a08 9 := by
    dsimp [S_a08]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 6, 7, 12, 21, 28}
    refine ⟨?_, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h_le : sInf (S_a08 9) ≤ 84 := Nat.sInf_le h84
  have h_ge : 84 ≤ sInf (S_a08 9) := by
    have h_nonempty : (S_a08 9).Nonempty := ⟨84, h84⟩
    have h_mem : sInf (S_a08 9) ∈ S_a08 9 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a08 9) < 84 := by
      intro hc
      exact no_smaller_candidate_a08_9 _ hc h_mem
    omega
  omega

lemma a_9 : a 9 = 84 := by
  rw [a_eq_sInf_S_a]
  have h84 : 84 ∈ S_a 9 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 6, 7, 12, 21, 28}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h_le : sInf (S_a 9) ≤ 84 := Nat.sInf_le h84
  have h_ge : 84 ≤ sInf (S_a 9) := by
    have h_nonempty : (S_a 9).Nonempty := ⟨84, h84⟩
    have h_mem : sInf (S_a 9) ∈ S_a 9 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a 9) < 84 := by
      intro hc
      exact no_smaller_candidate_a_9 _ hc h_mem
    omega
  omega

lemma no_smaller_candidate_a08_10 : ∀ m < 120, m ∉ S_a08 10 := by
  intro m hm h_mem
  have h_ab : 2 * m ≤ (Nat.divisors m).sum id := mem_S_a08_imp_abundant (by decide) h_mem
  have h_cd : 10 < (Nat.divisors m).card := mem_S_a08_imp_card_divisors (by decide) h_mem
  have h_poss : m = 60 ∨ m = 72 ∨ m = 84 ∨ m = 90 ∨ m = 96 ∨ m = 108 := by
    have h_dec : ∀ x < 120, 2 * x ≤ (Nat.divisors x).sum id ∧ 10 < (Nat.divisors x).card → x = 60 ∨ x = 72 ∨ x = 84 ∨ x = 90 ∨ x = 96 ∨ x = 108 := by decide
    exact h_dec m hm ⟨h_ab, h_cd⟩
  rcases h_poss with rfl | rfl | rfl | rfl | rfl | rfl
  · have h_dec : ¬ is_candidate_dec 10 60 := by decide
    rw [is_candidate_dec_iff] at h_dec
    exact h_dec h_mem
  · have h_dec : ¬ is_candidate_dec 10 72 := by decide
    rw [is_candidate_dec_iff] at h_dec
    exact h_dec h_mem
  · have h_dec : ¬ is_candidate_dec 10 84 := by decide
    rw [is_candidate_dec_iff] at h_dec
    exact h_dec h_mem
  · have h_dec : ¬ is_candidate_dec 10 90 := by decide
    rw [is_candidate_dec_iff] at h_dec
    exact h_dec h_mem
  · have h_dec : ¬ is_candidate_dec 10 96 := by decide
    rw [is_candidate_dec_iff] at h_dec
    exact h_dec h_mem
  · have h_dec : ¬ is_candidate_dec 10 108 := by decide
    rw [is_candidate_dec_iff] at h_dec
    exact h_dec h_mem

lemma no_smaller_candidate_a_10 : ∀ m < 120, m ∉ S_a 10 :=
  no_smaller_candidate_a_from_a08 no_smaller_candidate_a08_10

lemma a081512_10 : a081512 10 = 120 := by
  rw [a081512_eq_sInf_S_a08]
  have h120 : 120 ∈ S_a08 10 := by
    dsimp [S_a08]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 15, 20, 24, 40}
    refine ⟨?_, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h_le : sInf (S_a08 10) ≤ 120 := Nat.sInf_le h120
  have h_ge : 120 ≤ sInf (S_a08 10) := by
    have h_nonempty : (S_a08 10).Nonempty := ⟨120, h120⟩
    have h_mem : sInf (S_a08 10) ∈ S_a08 10 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a08 10) < 120 := by
      intro hc
      exact no_smaller_candidate_a08_10 _ hc h_mem
    omega
  omega

lemma a_10 : a 10 = 120 := by
  rw [a_eq_sInf_S_a]
  have h120 : 120 ∈ S_a 10 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 15, 20, 24, 40}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h_le : sInf (S_a 10) ≤ 120 := Nat.sInf_le h120
  have h_ge : 120 ≤ sInf (S_a 10) := by
    have h_nonempty : (S_a 10).Nonempty := ⟨120, h120⟩
    have h_mem : sInf (S_a 10) ∈ S_a 10 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a 10) < 120 := by
      intro hc
      exact no_smaller_candidate_a_10 _ hc h_mem
    omega
  omega

lemma no_smaller_candidate_a08_11 : ∀ m < 120, m ∉ S_a08 11 := by
  intro m hm h_mem
  have h_ab : 2 * m ≤ (Nat.divisors m).sum id := mem_S_a08_imp_abundant (by decide) h_mem
  have h_cd : 11 < (Nat.divisors m).card := mem_S_a08_imp_card_divisors (by decide) h_mem
  have h_poss : m = 60 ∨ m = 72 ∨ m = 84 ∨ m = 90 ∨ m = 96 ∨ m = 108 := by
    have h_dec : ∀ x < 120, 2 * x ≤ (Nat.divisors x).sum id ∧ 11 < (Nat.divisors x).card → x = 60 ∨ x = 72 ∨ x = 84 ∨ x = 90 ∨ x = 96 ∨ x = 108 := by decide
    exact h_dec m hm ⟨h_ab, h_cd⟩
  rcases h_poss with rfl | rfl | rfl | rfl | rfl | rfl
  · have h_dec : ¬ is_candidate_dec 11 60 := by decide
    rw [is_candidate_dec_iff] at h_dec
    exact h_dec h_mem
  · have h_dec : ¬ is_candidate_dec 11 72 := by decide
    rw [is_candidate_dec_iff] at h_dec
    exact h_dec h_mem
  · have h_dec : ¬ is_candidate_dec 11 84 := by decide
    rw [is_candidate_dec_iff] at h_dec
    exact h_dec h_mem
  · have h_dec : ¬ is_candidate_dec 11 90 := by decide
    rw [is_candidate_dec_iff] at h_dec
    exact h_dec h_mem
  · have h_dec : ¬ is_candidate_dec 11 96 := by decide
    rw [is_candidate_dec_iff] at h_dec
    exact h_dec h_mem
  · have h_dec : ¬ is_candidate_dec 11 108 := by decide
    rw [is_candidate_dec_iff] at h_dec
    exact h_dec h_mem

lemma no_smaller_candidate_a_11 : ∀ m < 120, m ∉ S_a 11 :=
  no_smaller_candidate_a_from_a08 no_smaller_candidate_a08_11

lemma a081512_11 : a081512 11 = 120 := by
  rw [a081512_eq_sInf_S_a08]
  have h120 : 120 ∈ S_a08 11 := by
    dsimp [S_a08]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 8, 12, 15, 24, 40}
    refine ⟨?_, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h_le : sInf (S_a08 11) ≤ 120 := Nat.sInf_le h120
  have h_ge : 120 ≤ sInf (S_a08 11) := by
    have h_nonempty : (S_a08 11).Nonempty := ⟨120, h120⟩
    have h_mem : sInf (S_a08 11) ∈ S_a08 11 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a08 11) < 120 := by
      intro hc
      exact no_smaller_candidate_a08_11 _ hc h_mem
    omega
  omega

lemma a_11 : a 11 = 120 := by
  rw [a_eq_sInf_S_a]
  have h120 : 120 ∈ S_a 11 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 8, 12, 15, 24, 40}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h_le : sInf (S_a 11) ≤ 120 := Nat.sInf_le h120
  have h_ge : 120 ≤ sInf (S_a 11) := by
    have h_nonempty : (S_a 11).Nonempty := ⟨120, h120⟩
    have h_mem : sInf (S_a 11) ∈ S_a 11 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a 11) < 120 := by
      intro hc
      exact no_smaller_candidate_a_11 _ hc h_mem
    omega
  omega

lemma no_smaller_candidate_a08_12 : ∀ m < 120, m ∉ S_a08 12 := by
  intro m hm h_mem
  have h_ab : 2 * m ≤ (Nat.divisors m).sum id := mem_S_a08_imp_abundant (by decide) h_mem
  have h_cd : 12 < (Nat.divisors m).card := mem_S_a08_imp_card_divisors (by decide) h_mem
  have h_poss : False := by
    have h_dec : ∀ x < 120, ¬ (2 * x ≤ (Nat.divisors x).sum id ∧ 12 < (Nat.divisors x).card) := by decide
    exact h_dec m hm ⟨h_ab, h_cd⟩
  contradiction

lemma no_smaller_candidate_a_12 : ∀ m < 120, m ∉ S_a 12 :=
  no_smaller_candidate_a_from_a08 no_smaller_candidate_a08_12

lemma a081512_12 : a081512 12 = 120 := by
  rw [a081512_eq_sInf_S_a08]
  have h120 : 120 ∈ S_a08 12 := by
    dsimp [S_a08]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 24, 30}
    refine ⟨?_, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h_le : sInf (S_a08 12) ≤ 120 := Nat.sInf_le h120
  have h_ge : 120 ≤ sInf (S_a08 12) := by
    have h_nonempty : (S_a08 12).Nonempty := ⟨120, h120⟩
    have h_mem : sInf (S_a08 12) ∈ S_a08 12 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a08 12) < 120 := by
      intro hc
      exact no_smaller_candidate_a08_12 _ hc h_mem
    omega
  omega

lemma a_12 : a 12 = 120 := by
  rw [a_eq_sInf_S_a]
  have h120 : 120 ∈ S_a 12 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 24, 30}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h_le : sInf (S_a 12) ≤ 120 := Nat.sInf_le h120
  have h_ge : 120 ≤ sInf (S_a 12) := by
    have h_nonempty : (S_a 12).Nonempty := ⟨120, h120⟩
    have h_mem : sInf (S_a 12) ∈ S_a 12 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a 12) < 120 := by
      intro hc
      exact no_smaller_candidate_a_12 _ hc h_mem
    omega
  omega

theorem oeis_355228_conjecture_0 (n : ℕ) :
  (a n > a081512 n) ↔ (n = 4 ∨ n = 5) := by
  constructor
  · intro h
    by_contra hc
    have hn4 : n ≠ 4 := by omega
    have hn5 : n ≠ 5 := by omega
    rcases n with _ | _ | _ | _ | _ | _ | n
    · rw [a_zero, a081512_zero] at h
      omega
    · rw [a_one, a081512_one] at h
      omega
    · rw [a_two, a081512_two] at h
      omega
    · rw [a_three, a081512_three] at h
      omega
    · contradiction
    · contradiction
    · -- n ≥ 6 case
      rcases n with _ | _ | n
      · -- n + 6 = 6 case
        change a 6 > a081512 6 at h
        have h_le : a 6 ≤ a081512 6 := by
          rw [a_six, a081512_six]
        omega
      · -- n + 6 = 7 case
        change a 7 > a081512 7 at h
        have h_le : a 7 ≤ a081512 7 := by
          rw [a_seven, a081512_seven]
        omega
      · -- n + 6 ≥ 8 case
        rcases n with _ | _ | _ | _ | _ | n
        · -- n+8 = 8
          rw [a_8, a081512_8] at h
          omega
        · -- n+8 = 9
          rw [a_9, a081512_9] at h
          omega
        · -- n+8 = 10
          rw [a_10, a081512_10] at h
          omega
        · -- n+8 = 11
          rw [a_11, a081512_11] at h
          omega
        · -- n+8 = 12
          rw [a_12, a081512_12] at h
          omega
        · -- n+8 ≥ 13 case
          have h_goal : False := by
            sorry
  · intro h
    rcases h with rfl | rfl
    · rw [a081512_four, a_four]
      decide
    · rw [a081512_five, a_five]
      decide
