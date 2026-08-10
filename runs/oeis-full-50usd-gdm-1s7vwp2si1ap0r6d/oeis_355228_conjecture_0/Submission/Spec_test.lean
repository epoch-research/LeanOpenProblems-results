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


open Finset Nat Set

-- ==================== 120 ====================

lemma divisors_120_eq : (Nat.divisors 120) = ({1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120} : Finset ℕ) := by decide

def S_120_small : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24}
def S_120_big : Finset ℕ := {30, 40, 60, 120}

lemma S_120_small_sum : S_120_small.sum id = 110 := by decide

lemma mem_small_elements_120 (x : ℕ) (hx : x ∈ Nat.divisors 120) (h_not_big : x ∉ S_120_big) : x ∈ S_120_small := by
  have h_dec : ∀ y ∈ Nat.divisors 120, y ∉ ({30, 40, 60, 120} : Finset ℕ) → y ∈ ({1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24} : Finset ℕ) := by decide
  exact h_dec x hx h_not_big

lemma S_120_small_card : S_120_small.card = 12 := by rfl

lemma test_120_cases : ∀ B ⊆ S_120_big, B ≠ ∅ →
  13 - B.card ≤ 12 ∧
  (13 - B.card = 12 → B.sum id + 110 > 120) ∧
  (13 - B.card = 11 → B.sum id + 86 > 120) ∧
  (13 - B.card = 10 → B.sum id + 66 > 120) ∧
  (13 - B.card = 9 → B.sum id + 51 > 120) := by decide

lemma S_max1 : ∀ x ∈ S_120_small, x ≤ 24 := by decide
lemma S_max2 : ∀ x ∈ S_120_small, ∀ y ∈ S_120_small, x ≠ y → x + y ≤ 44 := by decide
lemma S_max3 : ∀ x ∈ S_120_small, ∀ y ∈ S_120_small, ∀ z ∈ S_120_small, x ≠ y → y ≠ z → x ≠ z → x + y + z ≤ 59 := by decide

lemma no_subset_120_ge_13 (k : ℕ) (hk : 13 ≤ k) (D : Finset ℕ) (hD : D ⊆ Nat.divisors 120) (hcard : D.card = k) : D.sum id ≠ 120 := by
  by_contra h_sum
  let B := D ∩ S_120_big
  let A := D \ S_120_big
  have h_union : D = A ∪ B := by
    rw [Finset.sdiff_union_inter D S_120_big]
  have h_disj : Disjoint A B := by
    rw [disjoint_iff_ne]
    intro x hx y hy h_eq
    subst h_eq
    simp [A, B] at hx hy
    exact hx.2 hy.2
  have h_sum_total : D.sum id = A.sum id + B.sum id := by
    rw [h_union, Finset.sum_union h_disj]
  have h_card_total : D.card = A.card + B.card := by
    rw [h_union, Finset.card_union_of_disjoint h_disj]
  have h_A_sub : A ⊆ S_120_small := by
    intro x hx
    simp [A] at hx
    apply mem_small_elements_120 x (hD hx.1) hx.2
  have h_A_card_le : A.card ≤ 12 := by
    have h_le := Finset.card_le_card h_A_sub
    rw [S_120_small_card] at h_le
    exact h_le
  by_cases hB_empty : B = ∅
  · -- B is empty
    have h_B_card : B.card = 0 := by simp [hB_empty]
    omega
  · -- B is not empty
    have h_B_sub : B ⊆ S_120_big := by simp [B]
    have h_cases := test_120_cases B h_B_sub hB_empty
    have h_B_card_le : B.card ≤ 4 := by
      have h_le := Finset.card_le_card h_B_sub
      exact h_le
    have h_A_card_eq : A.card = k - B.card := by omega
    have h_rem_le : 13 - B.card ≤ 12 := h_cases.1
    -- Since k ≥ 13, A.card ≥ 13 - B.card
    have h_A_card_ge : A.card ≥ 13 - B.card := by omega
    -- Now we do a case-split on A.card
    have h_A_sum_ge : A.sum id ≥ if A.card = 12 then 110 else if A.card = 11 then 86 else if A.card = 10 then 66 else if A.card = 9 then 51 else 0 := by
      split_ifs with h12 h11 h10 h9
      · -- A.card = 12
        have h_eq : A = S_120_small := by
          apply Finset.eq_of_subset_of_card_le h_A_sub
          rw [S_120_small_card, h12]
        rw [h_eq, S_120_small_sum]
      · -- A.card = 11
        have h_sum_sub : S_120_small.sum id = (S_120_small \ A).sum id + A.sum id := by
          rw [← Finset.sum_sdiff h_A_sub]
        have h_card_sdiff : (S_120_small \ A).card = 1 := by
          rw [Finset.card_sdiff_of_subset h_A_sub, S_120_small_card, h11]
        rcases Finset.card_eq_one.mp h_card_sdiff with ⟨x, hx⟩
        have hx_mem : x ∈ S_120_small \ A := by rw [hx]; exact Finset.mem_singleton_self x
        rw [Finset.mem_sdiff] at hx_mem
        have hx_in : x ∈ S_120_small := hx_mem.1
        have hx_le : x ≤ 24 := S_max1 x hx_in
        have h_sdiff_sum : (S_120_small \ A).sum id = x := by
          rw [hx, Finset.sum_singleton]
          rfl
        rw [S_120_small_sum] at h_sum_sub
        omega
      · -- A.card = 10
        have h_sum_sub : S_120_small.sum id = (S_120_small \ A).sum id + A.sum id := by
          rw [← Finset.sum_sdiff h_A_sub]
        have h_card_sdiff : (S_120_small \ A).card = 2 := by
          rw [Finset.card_sdiff_of_subset h_A_sub, S_120_small_card, h10]
        rcases Finset.card_eq_two.mp h_card_sdiff with ⟨x, y, hxy, hxy_eq⟩
        have h_sub_sdiff : S_120_small \ A ⊆ S_120_small := Finset.sdiff_subset
        have hx_in : x ∈ S_120_small := by
          apply h_sub_sdiff
          rw [hxy_eq]
          exact Finset.mem_insert_self x {y}
        have hy_in : y ∈ S_120_small := by
          apply h_sub_sdiff
          rw [hxy_eq]
          simp
        have hxy_le : x + y ≤ 44 := S_max2 x hx_in y hy_in hxy
        have h_sdiff_sum : (S_120_small \ A).sum id = x + y := by
          rw [hxy_eq]
          simp [hxy]
        rw [S_120_small_sum] at h_sum_sub
        omega
      · -- A.card = 9
        have h_sum_sub : S_120_small.sum id = (S_120_small \ A).sum id + A.sum id := by
          rw [← Finset.sum_sdiff h_A_sub]
        have h_card_sdiff : (S_120_small \ A).card = 3 := by
          rw [Finset.card_sdiff_of_subset h_A_sub, S_120_small_card, h9]
        rcases Finset.card_eq_three.mp h_card_sdiff with ⟨x, y, z, hxy, hxz, hyz, hxyz_eq⟩
        have h_sub_sdiff : S_120_small \ A ⊆ S_120_small := Finset.sdiff_subset
        have hx_in : x ∈ S_120_small := by
          apply h_sub_sdiff
          rw [hxyz_eq]
          simp
        have hy_in : y ∈ S_120_small := by
          apply h_sub_sdiff
          rw [hxyz_eq]
          simp
        have hz_in : z ∈ S_120_small := by
          apply h_sub_sdiff
          rw [hxyz_eq]
          simp
        have hxyz_le : x + y + z ≤ 59 := S_max3 x hx_in y hy_in z hz_in hxy hyz hxz
        have h_sdiff_sum : (S_120_small \ A).sum id = x + y + z := by
          rw [hxyz_eq]
          simp [hxy, hyz, hxz]
          omega
        rw [S_120_small_sum] at h_sum_sub
        omega
      · omega
    -- Now we just use h_cases to show A.sum id + B.sum id > 120
    have h_final : A.sum id + B.sum id > 120 := by
      rcases h_cases with ⟨_, h_case12, h_case11, h_case10, h_case9⟩
      -- split into cases on B.card
      by_cases hB1 : B.card = 1
      · have h_A_card_12 : A.card = 12 := by omega
        have h_rem_12 : 13 - B.card = 12 := by omega
        have h_sum_A : A.sum id ≥ 110 := by
          revert h_A_sum_ge
          simp [h_A_card_12]
        have h_goal := h_case12 h_rem_12
        omega
      · by_cases hB2 : B.card = 2
        · have h_rem_11 : 13 - B.card = 11 := by omega
          by_cases hA12 : A.card = 12
          · have h_sum_A : A.sum id ≥ 110 := by
              revert h_A_sum_ge
              simp [hA12]
            omega
          · have h_A_card_11 : A.card = 11 := by omega
            have h_sum_A : A.sum id ≥ 86 := by
              revert h_A_sum_ge
              simp [h_A_card_11]
            have h_goal := h_case11 h_rem_11
            omega
        · by_cases hB3 : B.card = 3
          · have h_rem_10 : 13 - B.card = 10 := by omega
            by_cases hA12 : A.card = 12
            · have h_sum_A : A.sum id ≥ 110 := by revert h_A_sum_ge; simp [hA12]
              omega
            · by_cases hA11 : A.card = 11
              · have h_sum_A : A.sum id ≥ 86 := by revert h_A_sum_ge; simp [hA11]
                omega
              · have h_A_card_10 : A.card = 10 := by omega
                have h_sum_A : A.sum id ≥ 66 := by
                  revert h_A_sum_ge
                  simp [h_A_card_10]
                have h_goal := h_case10 h_rem_10
                omega
          · have h_B4 : B.card = 4 := by omega
            have h_rem_9 : 13 - B.card = 9 := by omega
            by_cases hA12 : A.card = 12
            · have h_sum_A : A.sum id ≥ 110 := by revert h_A_sum_ge; simp [hA12]
              omega
            · by_cases hA11 : A.card = 11
              · have h_sum_A : A.sum id ≥ 86 := by revert h_A_sum_ge; simp [hA11]
                omega
              · by_cases hA10 : A.card = 10
                · have h_sum_A : A.sum id ≥ 66 := by revert h_A_sum_ge; simp [hA10]
                  omega
                · have h_A_card_9 : A.card = 9 := by omega
                  have h_sum_A : A.sum id ≥ 51 := by
                    revert h_A_sum_ge
                    simp [h_A_card_9]
                  have h_goal := h_case9 h_rem_9
                  omega
    omega

-- ==================== 144 ====================

lemma divisors_144_eq : (Nat.divisors 144) = ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ) := by decide

lemma S_144_sum : ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ).sum id = 403 := by decide

lemma S_144_card : ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ).card = 15 := by rfl

lemma S_144_max1 : ∀ x ∈ ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ), x ≤ 144 := by decide

lemma S_144_max2 : ∀ x ∈ ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ),
  ∀ y ∈ ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ), x ≠ y → x + y ≤ 216 := by decide

lemma no_subset_144_ge_13 (k : ℕ) (hk : 13 ≤ k) (D : Finset ℕ) (hD : D ⊆ Nat.divisors 144) (hcard : D.card = k) : D.sum id ≠ 144 := by
  by_contra h_sum
  have h_union : Nat.divisors 144 = D ∪ (Nat.divisors 144 \ D) := by
    rw [Finset.union_comm]
    exact (Finset.sdiff_union_of_subset hD).symm
  have h_disj : Disjoint D (Nat.divisors 144 \ D) := Finset.disjoint_sdiff
  have h_sum_total : (Nat.divisors 144).sum id = D.sum id + (Nat.divisors 144 \ D).sum id := by
    conv_lhs => rw [h_union]
    rw [Finset.sum_union h_disj]
  have h_card_total : (Nat.divisors 144).card = D.card + (Nat.divisors 144 \ D).card := by
    conv_lhs => rw [h_union]
    rw [Finset.card_union_of_disjoint h_disj]
  have hS_card : (Nat.divisors 144).card = 15 := by
    rw [divisors_144_eq]
    rfl
  have hS_sum : (Nat.divisors 144).sum id = 403 := by
    rw [divisors_144_eq]
    decide
  generalize hc : (Nat.divisors 144 \ D).card = c
  have hc_le : c ≤ 2 := by omega
  have h_C_sum_le : (Nat.divisors 144 \ D).sum id ≤ 216 := by
    interval_cases c
    · -- c = 0
      have hC_empty : (Nat.divisors 144 \ D) = ∅ := Finset.card_eq_zero.mp hc
      rw [hC_empty, Finset.sum_empty]
      omega
    · -- c = 1
      rcases Finset.card_eq_one.mp hc with ⟨x, hx⟩
      have hx_mem : x ∈ (Nat.divisors 144 \ D) := by rw [hx]; exact Finset.mem_singleton_self x
      have hx_in : x ∈ Nat.divisors 144 := (Finset.mem_sdiff.mp hx_mem).1
      have hx_le : x ≤ 144 := by
        rw [divisors_144_eq] at hx_in
        exact S_144_max1 x hx_in
      have hC_sum : (Nat.divisors 144 \ D).sum id = x := by
        rw [hx, Finset.sum_singleton]
        rfl
      omega
    · -- c = 2
      rcases Finset.card_eq_two.mp hc with ⟨x, y, hxy, hxy_eq⟩
      have hx_mem : x ∈ (Nat.divisors 144 \ D) := by rw [hxy_eq]; exact Finset.mem_insert_self x {y}
      have hy_mem : y ∈ (Nat.divisors 144 \ D) := by rw [hxy_eq]; simp
      have hx_in : x ∈ Nat.divisors 144 := (Finset.mem_sdiff.mp hx_mem).1
      have hy_in : y ∈ Nat.divisors 144 := (Finset.mem_sdiff.mp hy_mem).1
      have hx_in' : x ∈ ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ) := by
        rwa [← divisors_144_eq]
      have hy_in' : y ∈ ({1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} : Finset ℕ) := by
        rwa [← divisors_144_eq]
      have hxy_le : x + y ≤ 216 := S_144_max2 x hx_in' y hy_in' hxy
      have hC_sum : (Nat.divisors 144 \ D).sum id = x + y := by
        rw [hxy_eq]
        simp [hxy]
      omega
  omega

-- ==================== 168 ====================

lemma divisors_168_eq : (Nat.divisors 168) = ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ) := by decide

lemma S_168_sum : ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ).sum id = 480 := by decide

lemma S_168_card : ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ).card = 16 := by rfl

lemma S_168_max1 : ∀ x ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ), x ≤ 168 := by decide

lemma S_168_max2 : ∀ x ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ),
  ∀ y ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ), x ≠ y → x + y ≤ 252 := by decide

lemma S_168_max3 : ∀ x ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ),
  ∀ y ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ),
  ∀ z ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ),
  x ≠ y → y ≠ z → x ≠ z → x + y + z ≤ 308 := by decide

lemma no_subset_168_ge_13 (k : ℕ) (hk : 13 ≤ k) (D : Finset ℕ) (hD : D ⊆ Nat.divisors 168) (hcard : D.card = k) : D.sum id ≠ 168 := by
  by_contra h_sum
  have h_union : Nat.divisors 168 = D ∪ (Nat.divisors 168 \ D) := by
    rw [Finset.union_comm]
    exact (Finset.sdiff_union_of_subset hD).symm
  have h_disj : Disjoint D (Nat.divisors 168 \ D) := Finset.disjoint_sdiff
  have h_sum_total : (Nat.divisors 168).sum id = D.sum id + (Nat.divisors 168 \ D).sum id := by
    conv_lhs => rw [h_union]
    rw [Finset.sum_union h_disj]
  have h_card_total : (Nat.divisors 168).card = D.card + (Nat.divisors 168 \ D).card := by
    conv_lhs => rw [h_union]
    rw [Finset.card_union_of_disjoint h_disj]
  have hS_card : (Nat.divisors 168).card = 16 := by
    rw [divisors_168_eq]
    rfl
  have hS_sum : (Nat.divisors 168).sum id = 480 := by
    rw [divisors_168_eq]
    decide
  generalize hc : (Nat.divisors 168 \ D).card = c
  have hc_le : c ≤ 3 := by omega
  have h_C_sum_le : (Nat.divisors 168 \ D).sum id ≤ 308 := by
    interval_cases c
    · -- c = 0
      have hC_empty : (Nat.divisors 168 \ D) = ∅ := Finset.card_eq_zero.mp hc
      rw [hC_empty, Finset.sum_empty]
      omega
    · -- c = 1
      rcases Finset.card_eq_one.mp hc with ⟨x, hx⟩
      have hx_mem : x ∈ (Nat.divisors 168 \ D) := by rw [hx]; exact Finset.mem_singleton_self x
      have hx_in : x ∈ Nat.divisors 168 := (Finset.mem_sdiff.mp hx_mem).1
      have hx_le : x ≤ 168 := by
        rw [divisors_168_eq] at hx_in
        exact S_168_max1 x hx_in
      have hC_sum : (Nat.divisors 168 \ D).sum id = x := by
        rw [hx, Finset.sum_singleton]
        rfl
      omega
    · -- c = 2
      rcases Finset.card_eq_two.mp hc with ⟨x, y, hxy, hxy_eq⟩
      have hx_mem : x ∈ (Nat.divisors 168 \ D) := by rw [hxy_eq]; exact Finset.mem_insert_self x {y}
      have hy_mem : y ∈ (Nat.divisors 168 \ D) := by rw [hxy_eq]; simp
      have hx_in : x ∈ Nat.divisors 168 := (Finset.mem_sdiff.mp hx_mem).1
      have hy_in : y ∈ Nat.divisors 168 := (Finset.mem_sdiff.mp hy_mem).1
      have hx_in' : x ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ) := by
        rwa [← divisors_168_eq]
      have hy_in' : y ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ) := by
        rwa [← divisors_168_eq]
      have hxy_le : x + y ≤ 252 := S_168_max2 x hx_in' y hy_in' hxy
      have hC_sum : (Nat.divisors 168 \ D).sum id = x + y := by
        rw [hxy_eq]
        simp [hxy]
      omega
    · -- c = 3
      rcases Finset.card_eq_three.mp hc with ⟨x, y, z, hxy, hxz, hyz, hxyz_eq⟩
      have hx_mem : x ∈ (Nat.divisors 168 \ D) := by rw [hxyz_eq]; simp
      have hy_mem : y ∈ (Nat.divisors 168 \ D) := by rw [hxyz_eq]; simp
      have hz_mem : z ∈ (Nat.divisors 168 \ D) := by rw [hxyz_eq]; simp
      have hx_in : x ∈ Nat.divisors 168 := (Finset.mem_sdiff.mp hx_mem).1
      have hy_in : y ∈ Nat.divisors 168 := (Finset.mem_sdiff.mp hy_mem).1
      have hz_in : z ∈ Nat.divisors 168 := (Finset.mem_sdiff.mp hz_mem).1
      have hx_in' : x ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ) := by
        rwa [← divisors_168_eq]
      have hy_in' : y ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ) := by
        rwa [← divisors_168_eq]
      have hz_in' : z ∈ ({1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} : Finset ℕ) := by
        rwa [← divisors_168_eq]
      have hxyz_le : x + y + z ≤ 308 := S_168_max3 x hx_in' y hy_in' z hz_in' hxy hyz hxz
      have hC_sum : (Nat.divisors 168 \ D).sum id = x + y + z := by
        rw [hxyz_eq]
        simp [hxy, hyz, hxz]
        omega
      omega
  omega


-- ==================== 180 ====================

lemma divisors_180_eq : (Nat.divisors 180) = ({1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180} : Finset ℕ) := by decide

lemma S_180_sum : ({1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180} : Finset ℕ).sum id = 546 := by decide

lemma S_180_card : ({1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180} : Finset ℕ).card = 18 := by rfl

lemma S_180_max1 : ∀ x ∈ ({1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180} : Finset ℕ), x ≤ 180 := by decide

lemma S_180_max2 : ∀ x ∈ ({1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180} : Finset ℕ),
  ∀ y ∈ ({1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180} : Finset ℕ), x ≠ y → x + y ≤ 270 := by decide

lemma S_180_max3 : ∀ x ∈ ({1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180} : Finset ℕ),
  ∀ y ∈ ({1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180} : Finset ℕ),
  ∀ z ∈ ({1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180} : Finset ℕ),
  x ≠ y → y ≠ z → x ≠ z → x + y + z ≤ 330 := by decide

lemma no_subset_180_ge_15 (k : ℕ) (hk : 15 ≤ k) (D : Finset ℕ) (hD : D ⊆ Nat.divisors 180) (hcard : D.card = k) : D.sum id ≠ 180 := by
  by_contra h_sum
  have h_union : Nat.divisors 180 = D ∪ (Nat.divisors 180 \ D) := by
    rw [Finset.union_comm]
    exact (Finset.sdiff_union_of_subset hD).symm
  have h_disj : Disjoint D (Nat.divisors 180 \ D) := Finset.disjoint_sdiff
  have h_sum_total : (Nat.divisors 180).sum id = D.sum id + (Nat.divisors 180 \ D).sum id := by
    conv_lhs => rw [h_union]
    rw [Finset.sum_union h_disj]
  have h_card_total : (Nat.divisors 180).card = D.card + (Nat.divisors 180 \ D).card := by
    conv_lhs => rw [h_union]
    rw [Finset.card_union_of_disjoint h_disj]
  have hS_card : (Nat.divisors 180).card = 18 := by
    rw [divisors_180_eq]
    rfl
  have hS_sum : (Nat.divisors 180).sum id = 546 := by
    rw [divisors_180_eq]
    decide
  generalize hc : (Nat.divisors 180 \ D).card = c
  have hc_le : c ≤ 3 := by omega
  have h_C_sum_le : (Nat.divisors 180 \ D).sum id ≤ 330 := by
    interval_cases c
    · -- c = 0
      have hC_empty : (Nat.divisors 180 \ D) = ∅ := Finset.card_eq_zero.mp hc
      rw [hC_empty, Finset.sum_empty]
      omega
    · -- c = 1
      rcases Finset.card_eq_one.mp hc with ⟨x, hx⟩
      have hx_mem : x ∈ (Nat.divisors 180 \ D) := by rw [hx]; exact Finset.mem_singleton_self x
      have hx_in : x ∈ Nat.divisors 180 := (Finset.mem_sdiff.mp hx_mem).1
      have hx_le : x ≤ 180 := by
        rw [divisors_180_eq] at hx_in
        exact S_180_max1 x hx_in
      have hC_sum : (Nat.divisors 180 \ D).sum id = x := by
        rw [hx, Finset.sum_singleton]
        rfl
      omega
    · -- c = 2
      rcases Finset.card_eq_two.mp hc with ⟨x, y, hxy, hxy_eq⟩
      have hx_mem : x ∈ (Nat.divisors 180 \ D) := by rw [hxy_eq]; exact Finset.mem_insert_self x {y}
      have hy_mem : y ∈ (Nat.divisors 180 \ D) := by rw [hxy_eq]; simp
      have hx_in : x ∈ Nat.divisors 180 := (Finset.mem_sdiff.mp hx_mem).1
      have hy_in : y ∈ Nat.divisors 180 := (Finset.mem_sdiff.mp hy_mem).1
      have hx_in' : x ∈ ({1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180} : Finset ℕ) := by
        rwa [← divisors_180_eq]
      have hy_in' : y ∈ ({1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180} : Finset ℕ) := by
        rwa [← divisors_180_eq]
      have hxy_le : x + y ≤ 270 := S_180_max2 x hx_in' y hy_in' hxy
      have hC_sum : (Nat.divisors 180 \ D).sum id = x + y := by
        rw [hxy_eq]
        simp [hxy]
      omega
    · -- c = 3
      rcases Finset.card_eq_three.mp hc with ⟨x, y, z, hxy, hxz, hyz, hxyz_eq⟩
      have hx_mem : x ∈ (Nat.divisors 180 \ D) := by rw [hxyz_eq]; simp
      have hy_mem : y ∈ (Nat.divisors 180 \ D) := by rw [hxyz_eq]; simp
      have hz_mem : z ∈ (Nat.divisors 180 \ D) := by rw [hxyz_eq]; simp
      have hx_in : x ∈ Nat.divisors 180 := (Finset.mem_sdiff.mp hx_mem).1
      have hy_in : y ∈ Nat.divisors 180 := (Finset.mem_sdiff.mp hy_mem).1
      have hz_in : z ∈ Nat.divisors 180 := (Finset.mem_sdiff.mp hz_mem).1
      have hx_in' : x ∈ ({1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180} : Finset ℕ) := by
        rwa [← divisors_180_eq]
      have hy_in' : y ∈ ({1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180} : Finset ℕ) := by
        rwa [← divisors_180_eq]
      have hz_in' : z ∈ ({1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180} : Finset ℕ) := by
        rwa [← divisors_180_eq]
      have hxyz_le : x + y + z ≤ 330 := S_180_max3 x hx_in' y hy_in' z hz_in' hxy hyz hxz
      have hC_sum : (Nat.divisors 180 \ D).sum id = x + y + z := by
        rw [hxyz_eq]
        simp [hxy, hyz, hxz]
        omega
      omega
  omega


lemma no_smaller_candidate_a08_ge_13_except (m : ℕ) (hm : m < 180) (k : ℕ) (hk : 13 ≤ k) (h_mem : m ∈ S_a08 k) :
  m = 120 ∨ m = 144 ∨ m = 168 := by
  have h_ab : 2 * m ≤ (Nat.divisors m).sum id := mem_S_a08_imp_abundant (by omega) h_mem
  have h_cd : k < (Nat.divisors m).card := mem_S_a08_imp_card_divisors (by omega) h_mem
  have h_dec : ∀ x < 180, 2 * x ≤ (Nat.divisors x).sum id ∧ 13 < (Nat.divisors x).card → x = 120 ∨ x = 144 ∨ x = 168 := by decide
  have h_cond : 2 * m ≤ (Nat.divisors m).sum id ∧ 13 < (Nat.divisors m).card := ⟨h_ab, by omega⟩
  exact h_dec m hm h_cond


lemma a081512_ge_180_of_ge_13 (k : ℕ) (hk : 13 ≤ k) (h_nonempty : (S_a08 k).Nonempty) : 180 ≤ a081512 k := by
  by_contra hc
  have h_lt : a081512 k < 180 := by omega
  have h_mem : a081512 k ∈ S_a08 k := Nat.sInf_mem h_nonempty
  rcases no_smaller_candidate_a08_ge_13_except (a081512 k) h_lt k hk h_mem with h120 | h144 | h168
  · -- case 120
    rcases h_mem with ⟨_, D, hD, hcard, hsum⟩
    rw [h120] at hsum hD
    exact no_subset_120_ge_13 k hk D hD hcard hsum
  · -- case 144
    rcases h_mem with ⟨_, D, hD, hcard, hsum⟩
    rw [h144] at hsum hD
    exact no_subset_144_ge_13 k hk D hD hcard hsum
  · -- case 168
    rcases h_mem with ⟨_, D, hD, hcard, hsum⟩
    rw [h168] at hsum hD
    exact no_subset_168_ge_13 k hk D hD hcard hsum
