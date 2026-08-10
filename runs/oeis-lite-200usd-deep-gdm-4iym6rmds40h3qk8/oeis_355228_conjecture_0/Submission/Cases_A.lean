import Submission.Defs
set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

open Finset Nat Set
-- Case n = 4
theorem twelve_mem_a081512_four : 12 ∈ a081512_candidates 4 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 6}
  refine ⟨by decide, by decide, by decide⟩

theorem a081512_four_le : a081512 4 ≤ 12 := by
  change sInf (a081512_candidates 4) ≤ 12



  exact Nat.sInf_le twelve_mem_a081512_four

theorem eighteen_mem_a_four : 18 ∈ a_candidates 4 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 6, 9}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem a_candidates_four_nonempty : (a_candidates 4).Nonempty := ⟨18, eighteen_mem_a_four⟩

theorem a_candidates_four_gt_twelve (m : ℕ) (hm : m ∈ a_candidates 4) : m > 12 := by
  by_contra h
  push_neg at h
  interval_cases m
  all_goals
    rw [mem_a_candidates_iff] at hm
    revert hm
    decide

theorem a_four_gt_twelve : a 4 > 12 := by
  unfold a
  have hmem := Nat.sInf_mem a_candidates_four_nonempty
  exact a_candidates_four_gt_twelve (sInf (a_candidates 4)) hmem

theorem a_four_gt_a081512_four : a 4 > a081512 4 :=
  lt_of_le_of_lt a081512_four_le a_four_gt_twelve


-- Case n = 5
theorem twentyfour_mem_a081512_five : 24 ∈ a081512_candidates 5 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 6, 12}
  refine ⟨by decide, by decide, by decide⟩

theorem a081512_five_le : a081512 5 ≤ 24 := by
  change sInf (a081512_candidates 5) ≤ 24
  exact Nat.sInf_le twentyfour_mem_a081512_five

theorem twentyeight_mem_a_five : 28 ∈ a_candidates 5 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 4, 7, 14}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem a_candidates_five_nonempty : (a_candidates 5).Nonempty := ⟨28, twentyeight_mem_a_five⟩

theorem a_candidates_five_gt_twentyfour (m : ℕ) (hm : m ∈ a_candidates 5) : m > 24 := by
  by_contra h
  push_neg at h
  interval_cases m
  all_goals
    rw [mem_a_candidates_iff] at hm
    revert hm
    decide

theorem a_five_gt_twentyfour : a 5 > 24 := by
  unfold a
  have hmem := Nat.sInf_mem a_candidates_five_nonempty
  exact a_candidates_five_gt_twentyfour (sInf (a_candidates 5)) hmem

theorem a_five_gt_a081512_five : a 5 > a081512 5 :=
  lt_of_le_of_lt a081512_five_le a_five_gt_twentyfour

lemma a_zero : a 0 = 0 := by
  change sInf (a_candidates 0) = 0
  rw [show a_candidates 0 = ∅ by
    ext m
    simp only [mem_a_candidates_iff, mem_empty_iff_false, iff_false, not_and]
    rintro hm ⟨D, hD_pow, hD_card, hD_sum, hD_lcm⟩
    rw [Finset.card_eq_zero] at hD_card
    subst hD_card
    simp at hD_sum
    omega, Nat.sInf_empty]

lemma a081512_zero : a081512 0 = 0 := by
  change sInf (a081512_candidates 0) = 0
  rw [a081512_candidates_zero, Nat.sInf_empty]

theorem a_zero_le_a081512_zero : a 0 ≤ a081512 0 := by
  rw [a_zero, a081512_zero]

theorem one_mem_a_one : 1 ∈ a_candidates 1 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem a_one_le : a 1 ≤ 1 := by
  change sInf (a_candidates 1) ≤ 1
  exact Nat.sInf_le one_mem_a_one

theorem one_mem_a081512_one : 1 ∈ a081512_candidates 1 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1}
  refine ⟨by decide, by decide, by decide⟩

theorem a081512_candidates_one_nonempty : (a081512_candidates 1).Nonempty := ⟨1, one_mem_a081512_one⟩

theorem a081512_one_ge : a081512 1 ≥ 1 := by
  change sInf (a081512_candidates 1) ≥ 1
  have hmem := Nat.sInf_mem a081512_candidates_one_nonempty
  rw [mem_a081512_candidates_iff] at hmem
  exact hmem.1

theorem a_one_le_a081512_one : a 1 ≤ a081512 1 :=
  le_trans a_one_le a081512_one_ge

lemma a_candidates_two : a_candidates 2 = ∅ := by
  ext m
  rw [mem_a_candidates_iff]
  simp only [mem_empty_iff_false, iff_false, not_and]
  rintro hm ⟨D, hD_pow, hD_card, hD_sum, hD_lcm⟩
  have h_mem : m ∈ a081512_candidates 2 := by
    rw [mem_a081512_candidates_iff]
    exact ⟨hm, D, hD_pow, hD_card, hD_sum⟩
  rw [a081512_candidates_two] at h_mem
  exact h_mem

theorem a_two : a 2 = 0 := by
  change sInf (a_candidates 2) = 0
  rw [a_candidates_two, Nat.sInf_empty]

theorem a081512_two : a081512 2 = 0 := by
  change sInf (a081512_candidates 2) = 0
  rw [a081512_candidates_two, Nat.sInf_empty]

theorem a_two_le_a081512_two : a 2 ≤ a081512 2 := by
  rw [a_two, a081512_two]

theorem six_mem_a_three : 6 ∈ a_candidates 3 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem a_three_le : a 3 ≤ 6 := by
  change sInf (a_candidates 3) ≤ 6
  exact Nat.sInf_le six_mem_a_three

theorem six_mem_a081512_three : 6 ∈ a081512_candidates 3 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3}
  refine ⟨by decide, by decide, by decide⟩

theorem a081512_candidates_three_nonempty : (a081512_candidates 3).Nonempty := ⟨6, six_mem_a081512_three⟩

theorem a081512_candidates_three_gt_five (m : ℕ) (hm : m ∈ a081512_candidates 3) : m ≥ 6 := by
  by_contra h
  push_neg at h
  interval_cases m
  all_goals
    rw [mem_a081512_candidates_iff] at hm
    revert hm
    decide

theorem a081512_three_ge : a081512 3 ≥ 6 := by
  change sInf (a081512_candidates 3) ≥ 6
  have hmem := Nat.sInf_mem a081512_candidates_three_nonempty
  exact a081512_candidates_three_gt_five (sInf (a081512_candidates 3)) hmem

theorem a_three_le_a081512_three : a 3 ≤ a081512 3 :=
  le_trans a_three_le a081512_three_ge


theorem twentyfour_mem_a_six : 24 ∈ a_candidates 6 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 6, 8}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem twentyfour_mem_a081512_six : 24 ∈ a081512_candidates 6 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 6, 8}
  refine ⟨by decide, by decide, by decide⟩

theorem a081512_candidates_six_ge (x : ℕ) (hx : x ∈ a081512_candidates 6) : 24 ≤ x := by
  by_contra! h
  interval_cases x
  all_goals
    rw [mem_a081512_candidates_iff] at hx
    revert hx
    decide


lemma not_mem_a081512_of_compl (k m : ℕ) (h_card_ge : (Nat.divisors m).card ≥ k)
    (h_empty : ((Nat.divisors m).powersetCard ((Nat.divisors m).card - k)).filter
      (fun t => t.sum id = (Nat.divisors m).sum id - m) = ∅) :
    m ∉ a081512_candidates k := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨hm, D, hD_sub, h_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_sub
  let C := (Nat.divisors m) \ D
  have hC_sub : C ⊆ Nat.divisors m := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    exact hx.1
  have h_inter : D ∩ Nat.divisors m = D := by
    ext x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hx1, hx2⟩; exact hx1
    · intro hx; exact ⟨hx, hD_sub hx⟩
  have hC_card : C.card = (Nat.divisors m).card - k := by
    dsimp [C]
    rw [Finset.card_sdiff]
    rw [h_inter]
    omega
  have h_sum_add : C.sum id + D.sum id = (Nat.divisors m).sum id := by
    dsimp [C]
    exact Finset.sum_sdiff hD_sub
  have hC_sum : C.sum id = (Nat.divisors m).sum id - m := by
    omega
  have hC_mem : C ∈ (Nat.divisors m).powersetCard ((Nat.divisors m).card - k) := by
    rw [Finset.mem_powersetCard]
    exact ⟨hC_sub, hC_card⟩
  have h_filt : C ∈ ((Nat.divisors m).powersetCard ((Nat.divisors m).card - k)).filter
    (fun t => t.sum id = (Nat.divisors m).sum id - m) := by
    rw [Finset.mem_filter]
    exact ⟨hC_mem, hC_sum⟩
  rw [h_empty] at h_filt
  have h_not : C ∉ (∅ : Finset (Finset ℕ)) := by simp
  exact h_not h_filt


lemma proper_divisors_sum_le {m : ℕ} (hm : 0 < m) {D : Finset ℕ} (hD : D ⊆ Nat.divisors m) (h_not : m ∉ D) :
    D.sum id ≤ D.card * (m / 2) := by
  have h_le : ∀ x ∈ D, x ≤ m / 2 := by
    intro x hx
    have h_div : x ∣ m := Nat.dvd_of_mem_divisors (hD hx)
    have h_lt : x < m := by
      by_contra! hc
      have h_eq : x = m := by
        have : x ≤ m := Nat.le_of_dvd hm h_div
        omega
      subst h_eq
      exact h_not hx
    exact proper_divisor_le_half hm h_div h_lt
  have h_sum := Finset.sum_le_card_nsmul D id (m / 2) h_le
  simp only [id_eq] at h_sum ⊢
  exact h_sum

lemma not_mem_a081512_of_sum_gt {m k : ℕ} (hk2 : 2 ≤ k) (hm : 0 < m) (hk : k ≤ (Nat.divisors m).card)
    (h_gt : (Nat.divisors m).sum id - 2 * m > ((Nat.divisors m).card - k - 1) * (m / 2)) :
    m ∉ a081512_candidates k := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_sub, h_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_sub
  have h_not_mem : m ∉ D := by
    intro hc_mem
    have h_sum_erase : D.sum id = m + (D.erase m).sum id := by
      rw [← D.sum_erase_add id hc_mem]
      simp only [id_eq, add_comm]
    have h_sum_simp : D.sum id = m := hD_sum
    have hD_erase_pos : (D.erase m).sum id > 0 := by
      have h_card_erase : (D.erase m).card = k - 1 := by
        rw [Finset.card_erase_of_mem hc_mem, h_card]
      have h_ne : (D.erase m).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hc_empty
        rw [hc_empty, Finset.card_empty] at h_card_erase
        omega
      rcases h_ne with ⟨x, hx⟩
      have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
      apply Finset.sum_pos
      · intro y hy
        have hy_D : y ∈ D := Finset.mem_of_mem_erase hy
        exact Nat.pos_of_mem_divisors (hD_sub hy_D)
      · exact ⟨x, hx⟩
    omega
  let C := (Nat.divisors m) \ D
  have hC_sub : C ⊆ Nat.divisors m := Finset.sdiff_subset
  have h_inter : D ∩ Nat.divisors m = D := by
    ext x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hx1, _⟩; exact hx1
    · intro hx; exact ⟨hx, hD_sub hx⟩
  have hC_card : C.card = (Nat.divisors m).card - k := by
    dsimp [C]
    rw [Finset.card_sdiff, h_inter, h_card]
  have h_sum_add : C.sum id + D.sum id = (Nat.divisors m).sum id := Finset.sum_sdiff hD_sub
  have hC_sum : C.sum id = (Nat.divisors m).sum id - m := by omega
  have hm_C : m ∈ C := by
    rw [Finset.mem_sdiff]
    refine ⟨Nat.mem_divisors_self m (by omega), h_not_mem⟩
  let C' := C.erase m
  have hC'_sub : C' ⊆ Nat.divisors m := by
    intro x hx
    rw [Finset.mem_erase] at hx
    exact hC_sub hx.2
  have hC'_not_mem : m ∉ C' := by
    intro hc
    exact (Finset.mem_erase.mp hc).1 rfl
  have hC'_card : C'.card = (Nat.divisors m).card - k - 1 := by
    rw [Finset.card_erase_of_mem hm_C, hC_card]
  have h_sum_ge : 2 * m < (Nat.divisors m).sum id := by omega
  have h_C_add : (Nat.divisors m).sum id = C.sum id + m := by omega
  have hC'_sum : C'.sum id = (Nat.divisors m).sum id - 2 * m := by
    have h_sum := C.sum_erase_add id hm_C
    dsimp [C'] at *
    simp only [id_eq] at *
    omega
  have h_le : C'.sum id ≤ C'.card * (m / 2) := by
    apply proper_divisors_sum_le hm hC'_sub hC'_not_mem
  rw [hC'_card] at h_le
  rw [hC'_sum] at h_le
  omega


theorem thirteen_mem_a_thirteen : 180 ∈ a_candidates 13 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 9, 10, 12, 18, 20, 30, 60}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem thirteen_mem_a081512_thirteen : 180 ∈ a081512_candidates 13 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 9, 10, 12, 18, 20, 30, 60}
  refine ⟨by decide, by decide, by decide⟩


def a_candidates_special (n : ℕ) : Set ℕ :=
  { m : ℕ | 0 < m ∧
    ∃ D : Finset ℕ,
      D ⊆ Nat.divisors m ∧
      D.card = n ∧
      D.sum id = m ∧
      D.lcm id = m ∧
      1 ∈ D ∧ 2 ∈ D ∧ 3 ∈ D }

lemma special_subset (n : ℕ) : a_candidates_special n ⊆ a_candidates n := by
  intro m hm
  rcases hm with ⟨hm0, D, hD_sub, hD_card, hD_sum, hD_lcm, _⟩
  exact ⟨hm0, D, hD_sub, hD_card, hD_sum, hD_lcm⟩

lemma twentyfour_mem_special : 24 ∈ a_candidates_special 6 := by
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 6, 8}
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

lemma dvd_of_lcm_dvd {x : ℕ} (h : 4 ∣ Nat.lcm 2 x) : 2 ∣ x := by
  by_cases h2 : 2 ∣ x
  · exact h2
  · have hgcd : Nat.gcd 2 x = 1 := by
      have h1 : Nat.gcd 2 x ∣ 2 := Nat.gcd_dvd_left 2 x
      have h_div : Nat.gcd 2 x = 1 ∨ Nat.gcd 2 x = 2 := by
        rcases h1 with ⟨c, hc⟩
        have h_pos : Nat.gcd 2 x > 0 := Nat.gcd_pos_of_pos_left x (by decide)
        have hc_pos : c > 0 := by
          by_contra!
          interval_cases c
          omega
        have hc_le : c ≤ 2 := by
          by_contra! hc_gt
          have h_mul : Nat.gcd 2 x * c ≥ 1 * 3 := by
            apply Nat.mul_le_mul
            · omega
            · omega
          omega
        interval_cases c
        · right; omega
        · left; omega
      rcases h_div with h_1 | h_2
      · exact h_1
      · have h_dvd : 2 ∣ x := by
          rw [← h_2]
          exact Nat.gcd_dvd_right 2 x
        exfalso
        exact h2 h_dvd
    have hlcm : Nat.lcm 2 x = 2 * x := by
      rw [Nat.lcm, hgcd, Nat.div_one]
    rw [hlcm] at h
    omega

lemma special_step {n : ℕ} {m : ℕ} (hm : m ∈ a_candidates_special (n + 6)) (hm_div : 4 ∣ m) :
    2 * m ∈ a_candidates_special (n + 7) := by
  rcases hm with ⟨hm0, D, hD_sub, hD_card, hD_sum, hD_lcm, h1, h2, h3⟩
  -- We want to construct D'
  let f : ℕ ↪ ℕ := ⟨fun x => 2 * x, fun x y h => by dsimp at h; omega⟩
  let D_erase := D.erase 2
  let D_map := D_erase.map f
  let D' := insert 1 (insert 3 D_map)
  
  have h_odd : ∀ x ∈ D_map, x % 2 = 0 := by
    intro x hx
    rw [Finset.mem_map] at hx
    rcases hx with ⟨d, hd, rfl⟩
    dsimp [f]
    omega
  have h1_not : 1 ∉ D_map := by
    intro hc
    have := h_odd 1 hc
    omega
  have h3_not : 3 ∉ D_map := by
    intro hc
    have := h_odd 3 hc
    omega
  have h_card_D_erase : D_erase.card = n + 5 := by
    dsimp [D_erase]
    rw [Finset.card_erase_of_mem h2]
    omega
  have h_card_D_map : D_map.card = n + 5 := by
    dsimp [D_map]
    rw [Finset.card_map, h_card_D_erase]
  have h_card_3 : (insert 3 D_map).card = n + 6 := by
    rw [Finset.card_insert_of_notMem h3_not, h_card_D_map]
  have h1_not_3 : 1 ∉ insert 3 D_map := by
    rw [Finset.mem_insert]
    push_neg
    exact ⟨by decide, h1_not⟩
  have h_card_D' : D'.card = n + 7 := by
    dsimp [D']
    rw [Finset.card_insert_of_notMem h1_not_3, h_card_3]

  have h_sum_3 : (insert 3 D_map).sum id = 3 + D_map.sum id := by
    rw [Finset.sum_insert h3_not]
    rfl
  have h_sum_D_map : D_map.sum id = 2 * D_erase.sum id := by
    dsimp [D_map]
    rw [Finset.sum_map]
    dsimp [f]
    rw [← Finset.mul_sum]
    rfl
  have h_sum_D_erase : D_erase.sum id = m - 2 := by
    dsimp [D_erase]
    have h_sum_erase := D.sum_erase_add id h2
    simp only [id_eq] at h_sum_erase
    have hD_sum_simp : (D.sum fun x => x) = m := hD_sum
    rw [hD_sum_simp] at h_sum_erase
    simp only [id_eq]
    omega
  have h_sum_D' : D'.sum id = 2 * m := by
    change (insert 1 (insert 3 D_map)).sum id = 2 * m
    rw [Finset.sum_insert h1_not_3, h_sum_3]
    dsimp [id]
    rw [h_sum_D_map, h_sum_D_erase]
    omega

  have h1_D' : 1 ∈ D' := by
    dsimp [D']
    exact Finset.mem_insert_self 1 _
  have h3_D' : 3 ∈ D' := by
    dsimp [D']
    rw [Finset.mem_insert]
    right
    exact Finset.mem_insert_self 3 _
  have h1_mem_erase : 1 ∈ D_erase := by
    dsimp [D_erase]
    rw [Finset.mem_erase]
    exact ⟨by decide, h1⟩
  have h2_mem_map : 2 ∈ D_map := by
    dsimp [D_map]
    rw [Finset.mem_map]
    refine ⟨1, h1_mem_erase, ?_⟩
    rfl
  have h2_D' : 2 ∈ D' := by
    dsimp [D']
    rw [Finset.mem_insert]
    right
    rw [Finset.mem_insert]
    right
    exact h2_mem_map

  have h_sub_D' : D' ⊆ Nat.divisors (2 * m) := by
    intro x hx
    dsimp [D'] at hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · rw [Nat.mem_divisors]
      refine ⟨⟨2 * m, by ring⟩, by omega⟩
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · rw [Nat.mem_divisors]
      have h3_div : 3 ∣ m := Nat.dvd_of_mem_divisors (hD_sub h3)
      rcases h3_div with ⟨c, rfl⟩
      refine ⟨⟨2 * c, by ring⟩, by omega⟩
    · rw [Finset.mem_map] at hx
      rcases hx with ⟨d, hd, rfl⟩
      dsimp [f]
      rw [Nat.mem_divisors]
      have hd_div : d ∣ m := Nat.dvd_of_mem_divisors (hD_sub (Finset.mem_of_mem_erase hd))
      rcases hd_div with ⟨c, rfl⟩
      refine ⟨⟨c, by ring⟩, by omega⟩

  have h_lcm_erase : D_erase.lcm id = m := by
    have h_lcm_ins : D.lcm id = Nat.lcm 2 (D_erase.lcm id) := by
      have h_eq : D = insert 2 D_erase := (Finset.insert_erase h2).symm
      nth_rw 1 [h_eq]
      rw [Finset.lcm_insert]
      rfl
    rw [hD_lcm] at h_lcm_ins
    have h_dvd : 2 ∣ D_erase.lcm id := dvd_of_lcm_dvd (h_lcm_ins ▸ hm_div)
    have h_lcm_eq : Nat.lcm 2 (D_erase.lcm id) = D_erase.lcm id := by
      have hgcd : Nat.gcd 2 (D_erase.lcm id) = 2 := Nat.gcd_eq_left h_dvd
      rw [Nat.lcm, hgcd]
      rw [Nat.mul_div_cancel_left _ (by decide)]
    omega

  have h_lcm_map_dvd : D_map.lcm id ∣ 2 * D_erase.lcm id := by
    apply Finset.lcm_dvd
    intro y hy
    rw [Finset.mem_map] at hy
    rcases hy with ⟨d, hd, rfl⟩
    dsimp [f]
    have hd_dvd := Finset.dvd_lcm (f := id) hd
    exact Nat.mul_dvd_mul_left 2 hd_dvd

  have h_lcm_map_ge : 2 * D_erase.lcm id ∣ D_map.lcm id := by
    have h_even : 2 ∣ D_map.lcm id := by
      have h2_mem : 2 ∈ D_map := h2_mem_map
      exact Finset.dvd_lcm (f := id) h2_mem
    rcases h_even with ⟨k, hk⟩
    have h_dvd_k : ∀ d ∈ D_erase, d ∣ k := by
      intro d hd
      have h_2d : 2 * d ∣ D_map.lcm id := by
        have hd_map : 2 * d ∈ D_map := by
          dsimp [D_map]
          rw [Finset.mem_map]
          refine ⟨d, hd, rfl⟩
        exact Finset.dvd_lcm (f := id) hd_map
      rw [hk] at h_2d
      rcases h_2d with ⟨c, hc⟩
      have hc' : 2 * k = 2 * (d * c) := by
        rw [mul_assoc] at hc
        exact hc
      have hk_eq : k = d * c := Nat.mul_left_cancel (by decide) hc'
      rw [hk_eq]
      exact dvd_mul_right d c
    have h_lcm_dvd_k : D_erase.lcm id ∣ k := Finset.lcm_dvd h_dvd_k
    rw [hk]
    exact Nat.mul_dvd_mul_left 2 h_lcm_dvd_k

  have h_lcm_map_eq : D_map.lcm id = 2 * m := by
    rw [h_lcm_erase] at h_lcm_map_dvd h_lcm_map_ge
    exact Nat.dvd_antisymm h_lcm_map_dvd h_lcm_map_ge

  have h_lcm_D' : D'.lcm id = 2 * m := by
    have h_lcm_sub : D_map ⊆ D' := by
      intro x hx
      dsimp [D']
      simp only [Finset.mem_insert, hx, or_true]
    have h_lcm_dvd_D' : D_map.lcm id ∣ D'.lcm id := Finset.lcm_mono h_lcm_sub
    rw [h_lcm_map_eq] at h_lcm_dvd_D'
    have h_D'_dvd_2m : D'.lcm id ∣ 2 * m := by
      apply Finset.lcm_dvd
      intro x hx
      have h_mem := h_sub_D' hx
      exact Nat.dvd_of_mem_divisors h_mem
    exact Nat.dvd_antisymm h_D'_dvd_2m h_lcm_dvd_D'

  refine ⟨by omega, D', h_sub_D', h_card_D', h_sum_D', h_lcm_D', h1_D', h2_D', h3_D'⟩

lemma twentyfour_mul_pow_two_mem_special (n : ℕ) :
    24 * 2^n ∈ a_candidates_special (n + 6) := by
  induction n with
  | zero =>
    exact twentyfour_mem_special
  | succ n ih =>
    have h_div : 4 ∣ 24 * 2^n := by
      use 6 * 2^n
      ring
    have h_step := special_step ih h_div
    have h_eq : 2 * (24 * 2^n) = 24 * 2^(n + 1) := by
      ring
    rw [h_eq] at h_step
    exact h_step

lemma twentyfour_mul_pow_two_mem_a_candidates (n : ℕ) :
    24 * 2^n ∈ a_candidates (n + 6) := by
  exact special_subset (n + 6) (twentyfour_mul_pow_two_mem_special n)




theorem a_six_le_a081512_six : a 6 ≤ a081512 6 := by
  unfold a a081512
  change sInf (a_candidates 6) ≤ sInf (a081512_candidates 6)
  have hB : (a081512_candidates 6).Nonempty := ⟨24, twentyfour_mem_a081512_six⟩
  have hB_ge : 24 ≤ sInf (a081512_candidates 6) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_six_ge (sInf (a081512_candidates 6)) hmem
  have hA_le : sInf (a_candidates 6) ≤ 24 := Nat.sInf_le twentyfour_mem_a_six
  exact le_trans hA_le hB_ge

theorem fortyeight_mem_a_seven : 48 ∈ a_candidates 7 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 6, 8, 12, 16}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem fortyeight_mem_a081512_seven : 48 ∈ a081512_candidates 7 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 6, 8, 12, 16}
  refine ⟨by decide, by decide, by decide⟩

theorem a081512_candidates_seven_ge (x : ℕ) (hx : x ∈ a081512_candidates 7) : 48 ≤ x := by
  by_contra! h
  interval_cases x
  all_goals
    rw [mem_a081512_candidates_iff] at hx
    revert hx
    decide

theorem a_seven_le_a081512_seven : a 7 ≤ a081512 7 := by
  unfold a a081512
  change sInf (a_candidates 7) ≤ sInf (a081512_candidates 7)
  have hB : (a081512_candidates 7).Nonempty := ⟨48, fortyeight_mem_a081512_seven⟩
  have hB_ge : 48 ≤ sInf (a081512_candidates 7) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_seven_ge (sInf (a081512_candidates 7)) hmem
  have hA_le : sInf (a_candidates 7) ≤ 48 := Nat.sInf_le fortyeight_mem_a_seven
  exact le_trans hA_le hB_ge

theorem sixty_mem_a_eight : 60 ∈ a_candidates 8 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 10, 15, 20}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem sixty_mem_a081512_eight : 60 ∈ a081512_candidates 8 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 10, 15, 20}
  refine ⟨by decide, by decide, by decide⟩

theorem a081512_candidates_eight_ge (x : ℕ) (hx : x ∈ a081512_candidates 8) : 60 ≤ x := by
  by_contra! h
  interval_cases x
  all_goals
    rw [mem_a081512_candidates_iff] at hx
    revert hx
    decide

theorem a_eight_le_a081512_eight : a 8 ≤ a081512 8 := by
  unfold a a081512
  change sInf (a_candidates 8) ≤ sInf (a081512_candidates 8)
  have hB : (a081512_candidates 8).Nonempty := ⟨60, sixty_mem_a081512_eight⟩
  have hB_ge : 60 ≤ sInf (a081512_candidates 8) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_eight_ge (sInf (a081512_candidates 8)) hmem
  have hA_le : sInf (a_candidates 8) ≤ 60 := Nat.sInf_le sixty_mem_a_eight
  exact le_trans hA_le hB_ge

theorem eightyfour_mem_a_nine : 84 ∈ a_candidates 9 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 6, 7, 12, 21, 28}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem eightyfour_mem_a081512_nine : 84 ∈ a081512_candidates 9 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 6, 7, 12, 21, 28}
  refine ⟨by decide, by decide, by decide⟩

theorem onehundredtwenty_mem_a_ten : 120 ∈ a_candidates 10 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 15, 20, 24, 40}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem onehundredtwenty_mem_a081512_ten : 120 ∈ a081512_candidates 10 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 15, 20, 24, 40}
  refine ⟨by decide, by decide, by decide⟩

theorem onehundredtwenty_mem_a_eleven : 120 ∈ a_candidates 11 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 12, 15, 24, 40}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem onehundredtwenty_mem_a081512_eleven : 120 ∈ a081512_candidates 11 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 12, 15, 24, 40}
  refine ⟨by decide, by decide, by decide⟩

theorem onehundredtwenty_mem_a_twelve : 120 ∈ a_candidates 12 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 24, 30}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem onehundredtwenty_mem_a081512_twelve : 120 ∈ a081512_candidates 12 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 24, 30}
  refine ⟨by decide, by decide, by decide⟩

lemma not_mem_a081512_9_36 : 36 ∉ a081512_candidates 9 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 9 (Nat.divisors 36)).filter (fun t => t.sum id = 36) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 9 (Nat.divisors 36)).filter (fun t => t.sum id = 36) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_9_48 : 48 ∉ a081512_candidates 9 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 9 (Nat.divisors 48)).filter (fun t => t.sum id = 48) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 9 (Nat.divisors 48)).filter (fun t => t.sum id = 48) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_9_60 : 60 ∉ a081512_candidates 9 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 9 (Nat.divisors 60)).filter (fun t => t.sum id = 60) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 9 (Nat.divisors 60)).filter (fun t => t.sum id = 60) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_9_72 : 72 ∉ a081512_candidates 9 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 9 (Nat.divisors 72)).filter (fun t => t.sum id = 72) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 9 (Nat.divisors 72)).filter (fun t => t.sum id = 72) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_9_80 : 80 ∉ a081512_candidates 9 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 9 (Nat.divisors 80)).filter (fun t => t.sum id = 80) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 9 (Nat.divisors 80)).filter (fun t => t.sum id = 80) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

theorem a081512_candidates_9_ge (x : ℕ) (hx : x ∈ a081512_candidates 9) : 84 ≤ x := by
  by_contra! h
  have h_decide : (List.range 84).all (fun y =>
      decide (if y = 36 ∨ y = 48 ∨ y = 60 ∨ y = 72 ∨ y = 80 then True
              else (Nat.divisors y).card < 9)) = true := by decide
  have h_mem : x ∈ List.range 84 := List.mem_range.mpr h
  have h_all := List.all_eq_true.mp h_decide x h_mem
  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 9 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow
  by_cases h36 : x = 36
  · subst h36
    exact not_mem_a081512_9_36 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h48 : x = 48
  · subst h48
    exact not_mem_a081512_9_48 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h60 : x = 60
  · subst h60
    exact not_mem_a081512_9_60 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h72 : x = 72
  · subst h72
    exact not_mem_a081512_9_72 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h80 : x = 80
  · subst h80
    exact not_mem_a081512_9_80 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  have h_not_cond : ¬ (x = 36 ∨ x = 48 ∨ x = 60 ∨ x = 72 ∨ x = 80) := by
    rintro (rfl | rfl | rfl | rfl | rfl)
    · exact h36 rfl
    · exact h48 rfl
    · exact h60 rfl
    · exact h72 rfl
    · exact h80 rfl
  have h_card : (Nat.divisors x).card < 9 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 36 ∨ x = 48 ∨ x = 60 ∨ x = 72 ∨ x = 80
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega

theorem a_nine_le_a081512_nine : a 9 ≤ a081512 9 := by
  unfold a a081512
  change sInf (a_candidates 9) ≤ sInf (a081512_candidates 9)
  have hB : (a081512_candidates 9).Nonempty := ⟨84, eightyfour_mem_a081512_nine⟩
  have hB_ge : 84 ≤ sInf (a081512_candidates 9) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_9_ge (sInf (a081512_candidates 9)) hmem
  have hA_le : sInf (a_candidates 9) ≤ 84 := Nat.sInf_le eightyfour_mem_a_nine
  exact le_trans hA_le hB_ge

lemma not_mem_a081512_10_48 : 48 ∉ a081512_candidates 10 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 10 (Nat.divisors 48)).filter (fun t => t.sum id = 48) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 10 (Nat.divisors 48)).filter (fun t => t.sum id = 48) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_10_60 : 60 ∉ a081512_candidates 10 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 10 (Nat.divisors 60)).filter (fun t => t.sum id = 60) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 10 (Nat.divisors 60)).filter (fun t => t.sum id = 60) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_10_72 : 72 ∉ a081512_candidates 10 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 10 (Nat.divisors 72)).filter (fun t => t.sum id = 72) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 10 (Nat.divisors 72)).filter (fun t => t.sum id = 72) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_10_80 : 80 ∉ a081512_candidates 10 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 10 (Nat.divisors 80)).filter (fun t => t.sum id = 80) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 10 (Nat.divisors 80)).filter (fun t => t.sum id = 80) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_10_84 : 84 ∉ a081512_candidates 10 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 10 (Nat.divisors 84)).filter (fun t => t.sum id = 84) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 10 (Nat.divisors 84)).filter (fun t => t.sum id = 84) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_10_90 : 90 ∉ a081512_candidates 10 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 10 (Nat.divisors 90)).filter (fun t => t.sum id = 90) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 10 (Nat.divisors 90)).filter (fun t => t.sum id = 90) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_10_96 : 96 ∉ a081512_candidates 10 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 10 (Nat.divisors 96)).filter (fun t => t.sum id = 96) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 10 (Nat.divisors 96)).filter (fun t => t.sum id = 96) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_10_108 : 108 ∉ a081512_candidates 10 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 10 (Nat.divisors 108)).filter (fun t => t.sum id = 108) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 10 (Nat.divisors 108)).filter (fun t => t.sum id = 108) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_10_112 : 112 ∉ a081512_candidates 10 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 10 (Nat.divisors 112)).filter (fun t => t.sum id = 112) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 10 (Nat.divisors 112)).filter (fun t => t.sum id = 112) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

theorem a081512_candidates_10_ge (x : ℕ) (hx : x ∈ a081512_candidates 10) : 120 ≤ x := by
  by_contra! h
  have h_decide : (List.range 120).all (fun y =>
      decide (if y = 48 ∨ y = 60 ∨ y = 72 ∨ y = 80 ∨ y = 84 ∨ y = 90 ∨ y = 96 ∨ y = 108 ∨ y = 112 then True
              else (Nat.divisors y).card < 10)) = true := by decide
  have h_mem : x ∈ List.range 120 := List.mem_range.mpr h
  have h_all := List.all_eq_true.mp h_decide x h_mem
  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 10 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow
  by_cases h48 : x = 48
  · subst h48
    exact not_mem_a081512_10_48 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h60 : x = 60
  · subst h60
    exact not_mem_a081512_10_60 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h72 : x = 72
  · subst h72
    exact not_mem_a081512_10_72 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h80 : x = 80
  · subst h80
    exact not_mem_a081512_10_80 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h84 : x = 84
  · subst h84
    exact not_mem_a081512_10_84 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h90 : x = 90
  · subst h90
    exact not_mem_a081512_10_90 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h96 : x = 96
  · subst h96
    exact not_mem_a081512_10_96 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h108 : x = 108
  · subst h108
    exact not_mem_a081512_10_108 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h112 : x = 112
  · subst h112
    exact not_mem_a081512_10_112 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  have h_not_cond : ¬ (x = 48 ∨ x = 60 ∨ x = 72 ∨ x = 80 ∨ x = 84 ∨ x = 90 ∨ x = 96 ∨ x = 108 ∨ x = 112) := by
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact h48 rfl
    · exact h60 rfl
    · exact h72 rfl
    · exact h80 rfl
    · exact h84 rfl
    · exact h90 rfl
    · exact h96 rfl
    · exact h108 rfl
    · exact h112 rfl
  have h_card : (Nat.divisors x).card < 10 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 48 ∨ x = 60 ∨ x = 72 ∨ x = 80 ∨ x = 84 ∨ x = 90 ∨ x = 96 ∨ x = 108 ∨ x = 112
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega

theorem a_ten_le_a081512_ten : a 10 ≤ a081512 10 := by
  unfold a a081512
  change sInf (a_candidates 10) ≤ sInf (a081512_candidates 10)
  have hB : (a081512_candidates 10).Nonempty := ⟨120, onehundredtwenty_mem_a081512_ten⟩
  have hB_ge : 120 ≤ sInf (a081512_candidates 10) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_10_ge (sInf (a081512_candidates 10)) hmem
  have hA_le : sInf (a_candidates 10) ≤ 120 := Nat.sInf_le onehundredtwenty_mem_a_ten
  exact le_trans hA_le hB_ge

lemma not_mem_a081512_11_60 : 60 ∉ a081512_candidates 11 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 11 (Nat.divisors 60)).filter (fun t => t.sum id = 60) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 11 (Nat.divisors 60)).filter (fun t => t.sum id = 60) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_11_72 : 72 ∉ a081512_candidates 11 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 11 (Nat.divisors 72)).filter (fun t => t.sum id = 72) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 11 (Nat.divisors 72)).filter (fun t => t.sum id = 72) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_11_84 : 84 ∉ a081512_candidates 11 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 11 (Nat.divisors 84)).filter (fun t => t.sum id = 84) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 11 (Nat.divisors 84)).filter (fun t => t.sum id = 84) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_11_90 : 90 ∉ a081512_candidates 11 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 11 (Nat.divisors 90)).filter (fun t => t.sum id = 90) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 11 (Nat.divisors 90)).filter (fun t => t.sum id = 90) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_11_96 : 96 ∉ a081512_candidates 11 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 11 (Nat.divisors 96)).filter (fun t => t.sum id = 96) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 11 (Nat.divisors 96)).filter (fun t => t.sum id = 96) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_11_108 : 108 ∉ a081512_candidates 11 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 11 (Nat.divisors 108)).filter (fun t => t.sum id = 108) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 11 (Nat.divisors 108)).filter (fun t => t.sum id = 108) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

theorem a081512_candidates_11_ge (x : ℕ) (hx : x ∈ a081512_candidates 11) : 120 ≤ x := by
  by_contra! h
  have h_decide : (List.range 120).all (fun y =>
      decide (if y = 60 ∨ y = 72 ∨ y = 84 ∨ y = 90 ∨ y = 96 ∨ y = 108 then True
              else (Nat.divisors y).card < 11)) = true := by decide
  have h_mem : x ∈ List.range 120 := List.mem_range.mpr h
  have h_all := List.all_eq_true.mp h_decide x h_mem
  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 11 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow
  by_cases h60 : x = 60
  · subst h60
    exact not_mem_a081512_11_60 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h72 : x = 72
  · subst h72
    exact not_mem_a081512_11_72 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h84 : x = 84
  · subst h84
    exact not_mem_a081512_11_84 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h90 : x = 90
  · subst h90
    exact not_mem_a081512_11_90 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h96 : x = 96
  · subst h96
    exact not_mem_a081512_11_96 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h108 : x = 108
  · subst h108
    exact not_mem_a081512_11_108 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  have h_not_cond : ¬ (x = 60 ∨ x = 72 ∨ x = 84 ∨ x = 90 ∨ x = 96 ∨ x = 108) := by
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact h60 rfl
    · exact h72 rfl
    · exact h84 rfl
    · exact h90 rfl
    · exact h96 rfl
    · exact h108 rfl
  have h_card : (Nat.divisors x).card < 11 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 60 ∨ x = 72 ∨ x = 84 ∨ x = 90 ∨ x = 96 ∨ x = 108
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega

theorem a_eleven_le_a081512_eleven : a 11 ≤ a081512 11 := by
  unfold a a081512
  change sInf (a_candidates 11) ≤ sInf (a081512_candidates 11)
  have hB : (a081512_candidates 11).Nonempty := ⟨120, onehundredtwenty_mem_a081512_eleven⟩
  have hB_ge : 120 ≤ sInf (a081512_candidates 11) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_11_ge (sInf (a081512_candidates 11)) hmem
  have hA_le : sInf (a_candidates 11) ≤ 120 := Nat.sInf_le onehundredtwenty_mem_a_eleven
  exact le_trans hA_le hB_ge

lemma not_mem_a081512_12_60 : 60 ∉ a081512_candidates 12 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 12 (Nat.divisors 60)).filter (fun t => t.sum id = 60) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 12 (Nat.divisors 60)).filter (fun t => t.sum id = 60) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_12_72 : 72 ∉ a081512_candidates 12 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 12 (Nat.divisors 72)).filter (fun t => t.sum id = 72) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 12 (Nat.divisors 72)).filter (fun t => t.sum id = 72) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_12_84 : 84 ∉ a081512_candidates 12 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 12 (Nat.divisors 84)).filter (fun t => t.sum id = 84) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 12 (Nat.divisors 84)).filter (fun t => t.sum id = 84) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_12_90 : 90 ∉ a081512_candidates 12 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 12 (Nat.divisors 90)).filter (fun t => t.sum id = 90) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 12 (Nat.divisors 90)).filter (fun t => t.sum id = 90) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_12_96 : 96 ∉ a081512_candidates 12 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 12 (Nat.divisors 96)).filter (fun t => t.sum id = 96) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 12 (Nat.divisors 96)).filter (fun t => t.sum id = 96) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

lemma not_mem_a081512_12_108 : 108 ∉ a081512_candidates 12 := by
  rw [mem_a081512_candidates_iff_powersetCard]
  push_neg
  intro _ D hD
  have h_empty : (Finset.powersetCard 12 (Nat.divisors 108)).filter (fun t => t.sum id = 108) = ∅ := by decide
  intro h_sum
  have h_mem : D ∈ (Finset.powersetCard 12 (Nat.divisors 108)).filter (fun t => t.sum id = 108) := by
    rw [Finset.mem_filter]
    exact ⟨hD, h_sum⟩
  rw [h_empty] at h_mem
  simp at h_mem

theorem a081512_candidates_12_ge (x : ℕ) (hx : x ∈ a081512_candidates 12) : 120 ≤ x := by
  by_contra! h
  have h_decide : (List.range 120).all (fun y =>
      decide (if y = 60 ∨ y = 72 ∨ y = 84 ∨ y = 90 ∨ y = 96 ∨ y = 108 then True
              else (Nat.divisors y).card < 12)) = true := by decide
  have h_mem : x ∈ List.range 120 := List.mem_range.mpr h
  have h_all := List.all_eq_true.mp h_decide x h_mem
  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 12 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow
  by_cases h60 : x = 60
  · subst h60
    exact not_mem_a081512_12_60 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h72 : x = 72
  · subst h72
    exact not_mem_a081512_12_72 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h84 : x = 84
  · subst h84
    exact not_mem_a081512_12_84 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h90 : x = 90
  · subst h90
    exact not_mem_a081512_12_90 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h96 : x = 96
  · subst h96
    exact not_mem_a081512_12_96 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h108 : x = 108
  · subst h108
    exact not_mem_a081512_12_108 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  have h_not_cond : ¬ (x = 60 ∨ x = 72 ∨ x = 84 ∨ x = 90 ∨ x = 96 ∨ x = 108) := by
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact h60 rfl
    · exact h72 rfl
    · exact h84 rfl
    · exact h90 rfl
    · exact h96 rfl
    · exact h108 rfl
  have h_card : (Nat.divisors x).card < 12 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 60 ∨ x = 72 ∨ x = 84 ∨ x = 90 ∨ x = 96 ∨ x = 108
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega

theorem a_twelve_le_a081512_twelve : a 12 ≤ a081512 12 := by
  unfold a a081512
  change sInf (a_candidates 12) ≤ sInf (a081512_candidates 12)
  have hB : (a081512_candidates 12).Nonempty := ⟨120, onehundredtwenty_mem_a081512_twelve⟩
  have hB_ge : 120 ≤ sInf (a081512_candidates 12) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_12_ge (sInf (a081512_candidates 12)) hmem
  have hA_le : sInf (a_candidates 12) ≤ 120 := Nat.sInf_le onehundredtwenty_mem_a_twelve
  exact le_trans hA_le hB_ge


lemma not_mem_a081512_13_120 : 120 ∉ a081512_candidates 13 := by
  apply not_mem_a081512_of_compl 13 120
  · decide
  · decide

lemma not_mem_a081512_13_144 : 144 ∉ a081512_candidates 13 := by
  apply not_mem_a081512_of_compl 13 144
  · decide
  · decide

lemma not_mem_a081512_13_168 : 168 ∉ a081512_candidates 13 := by
  apply not_mem_a081512_of_compl 13 168
  · decide
  · decide

theorem a081512_candidates_13_ge (x : ℕ) (hx : x ∈ a081512_candidates 13) : 180 ≤ x := by
  by_contra! h
  have h_decide : (List.range 180).all (fun y =>
      decide (if y = 120 ∨ y = 144 ∨ y = 168 then True
              else (Nat.divisors y).card < 13)) = true := by decide
  have h_mem : x ∈ List.range 180 := List.mem_range.mpr h
  have h_all := List.all_eq_true.mp h_decide x h_mem
  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 13 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow
  by_cases h120 : x = 120
  · subst h120
    exact not_mem_a081512_13_120 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h144 : x = 144
  · subst h144
    exact not_mem_a081512_13_144 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h168 : x = 168
  · subst h168
    exact not_mem_a081512_13_168 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  have h_not_cond : ¬ (x = 120 ∨ x = 144 ∨ x = 168) := by
    rintro (rfl | rfl | rfl)
    · exact h120 rfl
    · exact h144 rfl
    · exact h168 rfl
  have h_card : (Nat.divisors x).card < 13 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 120 ∨ x = 144 ∨ x = 168
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega

