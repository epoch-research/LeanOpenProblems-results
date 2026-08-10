import Submission.Cases_B
set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

open Finset Nat Set
theorem a_twentythree_le_a081512_twentythree : a 23 ≤ a081512 23 := by
  unfold a a081512
  change sInf (a_candidates 23) ≤ sInf (a081512_candidates 23)
  have hB : (a081512_candidates 23).Nonempty := ⟨720, twentythree_mem_a081512_twentythree⟩
  have hB_ge : 720 ≤ sInf (a081512_candidates 23) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_23_ge (sInf (a081512_candidates 23)) hmem
  have hA_le : sInf (a_candidates 23) ≤ 720 := Nat.sInf_le twentythree_mem_a_twentythree
  exact le_trans hA_le hB_ge


theorem twentyfour_mem_a_twentyfour : 840 ∈ a_candidates 24 := by
  rw [mem_a_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 4, 5, 6, 7, 8, 10, 12, 14, 15, 20, 21, 24, 28, 30, 35, 40, 42, 56, 60, 70, 120, 210}
  refine ⟨by decide, by decide, by decide, by decide⟩


theorem twentyfour_mem_a081512_twentyfour : 840 ∈ a081512_candidates 24 := by
  rw [mem_a081512_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 4, 5, 6, 7, 8, 10, 12, 14, 15, 20, 21, 24, 28, 30, 35, 40, 42, 56, 60, 70, 120, 210}
  refine ⟨by decide, by decide, by decide⟩


lemma not_mem_720_D_360 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 720) (hD_card : D.card ≥ 24) (hD_sum : D.sum id = 720)
    : 360 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 360).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 360).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 360).sum id > 360 := by
    let S_rem := (Nat.divisors 720) \ ({720} ∪ {360})
    have hD_erase_sub : D.erase 360 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 360 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 28 := by decide
    have hS_rem_sum : S_rem.sum id = 1338 := by decide
    let C_rem := S_rem \ (D.erase 360)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 360) ∩ S_rem = D.erase 360 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 5 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 774 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 5 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 774)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 774)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 774 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 360).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_720_D_240 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 720) (hD_card : D.card ≥ 23) (hD_sum : D.sum id = 360)
    (h_360 : 360 ∉ D)
    : 240 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 240).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 240).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 240).sum id > 120 := by
    let S_rem := (Nat.divisors 720) \ ({720} ∪ {360} ∪ {240})
    have hD_erase_sub : D.erase 240 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 240 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_360 (Finset.mem_of_mem_erase hy)
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 27 := by decide
    have hS_rem_sum : S_rem.sum id = 1098 := by decide
    let C_rem := S_rem \ (D.erase 240)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 240) ∩ S_rem = D.erase 240 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 5 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 614 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 5 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 614)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 614)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 614 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 240).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_720_D_180 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 720) (hD_card : D.card ≥ 22) (hD_sum : D.sum id = 120)
    (h_360 : 360 ∉ D)
    (h_240 : 240 ∉ D)
    : 180 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 180).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 180).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 180).sum id ≥ 412 := by
    let S_rem := (Nat.divisors 720) \ ({720} ∪ {360} ∪ {240} ∪ {180})
    have hD_erase_sub : D.erase 180 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 180 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_360 (Finset.mem_of_mem_erase hy)
        · subst pe_eq; exact h_240 (Finset.mem_of_mem_erase hy)
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 26 := by decide
    have hS_rem_sum : S_rem.sum id = 918 := by decide
    let C_rem := S_rem \ (D.erase 180)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 180) ∩ S_rem = D.erase 180 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 5 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 506 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 5 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 506)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 506)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 506 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 180).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_a081512_24_720 : 720 ∉ a081512_candidates 24 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_not_720 : 720 ∉ D := not_mem_s_in_D (by omega) hD_pow (by omega) hD_sum
  have h_not_360 : 360 ∉ D := not_mem_720_D_360 hD_pow (by omega) hD_sum 
  have h_not_240 : 240 ∉ D := not_mem_720_D_240 hD_pow (by omega) hD_sum h_not_360
  have h_not_180 : 180 ∉ D := not_mem_720_D_180 hD_pow (by omega) hD_sum h_not_360 h_not_240
  let S_final := (Nat.divisors 720) \ ({720} ∪ {360} ∪ {240} ∪ {180})
  have hD_sub_S : D ⊆ S_final := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨hD_pow hx, ?_⟩
    simp only [Finset.mem_union, Finset.mem_singleton]
    push_neg
    refine ⟨?_, ?_⟩
    · rintro rfl; exact h_not_720 hx
    · rintro pe_mem; rcases pe_mem with pe_eq
      · subst pe_eq; exact h_not_360 hx
      · subst pe_eq; exact h_not_240 hx
      · subst pe_eq; exact h_not_180 hx
  let C_final := S_final \ D
  have hC_sub : C_final ⊆ S_final := Finset.sdiff_subset
  have h_inter : D ∩ S_final = D := Finset.inter_eq_self_of_subset hD_sub_S
  have hC_card : C_final.card = 2 := by
    dsimp [C_final]
    rw [Finset.card_sdiff]
    rw [h_inter, hD_card]
    omega
  have hS_card : S_final.card = 26 := by decide
  have hS_sum : S_final.sum id = 918 := by decide
  have h_sum_add : C_final.sum id + D.sum id = S_final.sum id := Finset.sum_sdiff hD_sub_S
  have hC_sum : C_final.sum id = 198 := by omega
  have hC_mem : C_final ∈ S_final.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    exact ⟨hC_sub, hC_card⟩
  have h_filt : C_final ∈ (S_final.powersetCard 2).filter (fun t => t.sum id = 198) := by
    rw [Finset.mem_filter]
    exact ⟨hC_mem, hC_sum⟩
  have h_empty : (S_final.powersetCard 2).filter (fun t => t.sum id = 198) = ∅ := by decide
  rw [h_empty] at h_filt
  exact Finset.not_mem_empty C_final h_filt

lemma not_mem_a081512_24_756 : 756 ∉ a081512_candidates 24 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_eq : D = Nat.divisors 756 := Finset.eq_of_subset_of_card_le hD_pow (by omega)
  subst h_eq
  have h_sum_divs : (Nat.divisors 756).sum id = 2240 := by decide
  omega


lemma not_mem_a081512_24_780 : 780 ∉ a081512_candidates 24 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_eq : D = Nat.divisors 780 := Finset.eq_of_subset_of_card_le hD_pow (by omega)
  subst h_eq
  have h_sum_divs : (Nat.divisors 780).sum id = 2352 := by decide
  omega


lemma not_mem_a081512_24_792 : 792 ∉ a081512_candidates 24 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_eq : D = Nat.divisors 792 := Finset.eq_of_subset_of_card_le hD_pow (by omega)
  subst h_eq
  have h_sum_divs : (Nat.divisors 792).sum id = 2340 := by decide
  omega


theorem a081512_candidates_24_ge (x : ℕ) (hx : x ∈ a081512_candidates 24) : 840 ≤ x := by
  by_contra! h
  have hk21 : 24 ≥ 21 := by omega
  have hx720 : 720 ≤ x := a081512_candidates_ge_twentyone_ge_720 24 hk21 x hx

  have h_decide : ((List.range 120).map (· + 720)).all (fun y =>
      decide (if y = 720 ∨ y = 756 ∨ y = 780 ∨ y = 792 then True
              else (Nat.divisors y).card < 24)) = true := by decide
  have h_mem : x ∈ ((List.range 120).map (· + 720)) := by
    rw [List.mem_map]
    use x - 720
    constructor
    · rw [List.mem_range]; omega
    · omega
  have h_all := List.all_eq_true.mp h_decide x h_mem

  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 24 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow

  by_cases h720 : x = 720
  · subst h720; exact not_mem_a081512_24_720 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h756 : x = 756
  · subst h756; exact not_mem_a081512_24_756 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h780 : x = 780
  · subst h780; exact not_mem_a081512_24_780 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h792 : x = 792
  · subst h792; exact not_mem_a081512_24_792 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  have h_not_cond : ¬ (x = 720 ∨ x = 756 ∨ x = 780 ∨ x = 792) := by
    rintro (rfl | rfl | rfl | rfl)

    · exact h720 rfl

    · exact h756 rfl

    · exact h780 rfl

    · exact h792 rfl

  have h_card : (Nat.divisors x).card < 24 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 720 ∨ x = 756 ∨ x = 780 ∨ x = 792
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega


theorem a_twentyfour_le_a081512_twentyfour : a 24 ≤ a081512 24 := by
  unfold a a081512
  change sInf (a_candidates 24) ≤ sInf (a081512_candidates 24)
  have hB : (a081512_candidates 24).Nonempty := ⟨840, twentyfour_mem_a081512_twentyfour⟩
  have hB_ge : 840 ≤ sInf (a081512_candidates 24) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_24_ge (sInf (a081512_candidates 24)) hmem
  have hA_le : sInf (a_candidates 24) ≤ 840 := Nat.sInf_le twentyfour_mem_a_twentyfour
  exact le_trans hA_le hB_ge


theorem twentyfive_mem_a_twentyfive : 840 ∈ a_candidates 25 := by
  rw [mem_a_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 20, 21, 24, 28, 35, 40, 42, 56, 60, 70, 84, 105, 168}
  refine ⟨by decide, by decide, by decide, by decide⟩


theorem twentyfive_mem_a081512_twentyfive : 840 ∈ a081512_candidates 25 := by
  rw [mem_a081512_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 20, 21, 24, 28, 35, 40, 42, 56, 60, 70, 84, 105, 168}
  refine ⟨by decide, by decide, by decide⟩


lemma not_mem_720_D_360 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 720) (hD_card : D.card ≥ 25) (hD_sum : D.sum id = 720)
    : 360 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 360).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 360).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 360).sum id > 360 := by
    let S_rem := (Nat.divisors 720) \ ({720} ∪ {360})
    have hD_erase_sub : D.erase 360 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 360 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 28 := by decide
    have hS_rem_sum : S_rem.sum id = 1338 := by decide
    let C_rem := S_rem \ (D.erase 360)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 360) ∩ S_rem = D.erase 360 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 4 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 684 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 4 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 684)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 684)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 684 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 360).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_720_D_240 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 720) (hD_card : D.card ≥ 24) (hD_sum : D.sum id = 360)
    (h_360 : 360 ∉ D)
    : 240 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 240).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 240).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 240).sum id > 120 := by
    let S_rem := (Nat.divisors 720) \ ({720} ∪ {360} ∪ {240})
    have hD_erase_sub : D.erase 240 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 240 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_360 (Finset.mem_of_mem_erase hy)
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 27 := by decide
    have hS_rem_sum : S_rem.sum id = 1098 := by decide
    let C_rem := S_rem \ (D.erase 240)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 240) ∩ S_rem = D.erase 240 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 4 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 534 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 4 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 534)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 534)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 534 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 240).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_a081512_25_720 : 720 ∉ a081512_candidates 25 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_not_720 : 720 ∉ D := not_mem_s_in_D (by omega) hD_pow (by omega) hD_sum
  have h_not_360 : 360 ∉ D := not_mem_720_D_360 hD_pow (by omega) hD_sum 
  have h_not_240 : 240 ∉ D := not_mem_720_D_240 hD_pow (by omega) hD_sum h_not_360
  let S_final := (Nat.divisors 720) \ ({720} ∪ {360} ∪ {240})
  have hD_sub_S : D ⊆ S_final := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨hD_pow hx, ?_⟩
    simp only [Finset.mem_union, Finset.mem_singleton]
    push_neg
    refine ⟨?_, ?_⟩
    · rintro rfl; exact h_not_720 hx
    · rintro pe_mem; rcases pe_mem with pe_eq
      · subst pe_eq; exact h_not_360 hx
      · subst pe_eq; exact h_not_240 hx
  let C_final := S_final \ D
  have hC_sub : C_final ⊆ S_final := Finset.sdiff_subset
  have h_inter : D ∩ S_final = D := Finset.inter_eq_self_of_subset hD_sub_S
  have hC_card : C_final.card = 2 := by
    dsimp [C_final]
    rw [Finset.card_sdiff]
    rw [h_inter, hD_card]
    omega
  have hS_card : S_final.card = 27 := by decide
  have hS_sum : S_final.sum id = 1098 := by decide
  have h_sum_add : C_final.sum id + D.sum id = S_final.sum id := Finset.sum_sdiff hD_sub_S
  have hC_sum : C_final.sum id = 378 := by omega
  have hC_mem : C_final ∈ S_final.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    exact ⟨hC_sub, hC_card⟩
  have h_filt : C_final ∈ (S_final.powersetCard 2).filter (fun t => t.sum id = 378) := by
    rw [Finset.mem_filter]
    exact ⟨hC_mem, hC_sum⟩
  have h_empty : (S_final.powersetCard 2).filter (fun t => t.sum id = 378) = ∅ := by decide
  rw [h_empty] at h_filt
  exact Finset.not_mem_empty C_final h_filt

theorem a081512_candidates_25_ge (x : ℕ) (hx : x ∈ a081512_candidates 25) : 840 ≤ x := by
  by_contra! h
  have hk21 : 25 ≥ 21 := by omega
  have hx720 : 720 ≤ x := a081512_candidates_ge_twentyone_ge_720 25 hk21 x hx

  have h_decide : ((List.range 120).map (· + 720)).all (fun y =>
      decide (if y = 720 then True
              else (Nat.divisors y).card < 25)) = true := by decide
  have h_mem : x ∈ ((List.range 120).map (· + 720)) := by
    rw [List.mem_map]
    use x - 720
    constructor
    · rw [List.mem_range]; omega
    · omega
  have h_all := List.all_eq_true.mp h_decide x h_mem

  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 25 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow

  by_cases h720 : x = 720
  · subst h720; exact not_mem_a081512_25_720 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  have h_not_cond : ¬ (x = 720) := by
    rintro (rfl)

    · exact h720 rfl

  have h_card : (Nat.divisors x).card < 25 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 720
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega


theorem a_twentyfive_le_a081512_twentyfive : a 25 ≤ a081512 25 := by
  unfold a a081512
  change sInf (a_candidates 25) ≤ sInf (a081512_candidates 25)
  have hB : (a081512_candidates 25).Nonempty := ⟨840, twentyfive_mem_a081512_twentyfive⟩
  have hB_ge : 840 ≤ sInf (a081512_candidates 25) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_25_ge (sInf (a081512_candidates 25)) hmem
  have hA_le : sInf (a_candidates 25) ≤ 840 := Nat.sInf_le twentyfive_mem_a_twentyfive
  exact le_trans hA_le hB_ge


theorem twentysix_mem_a_twentysix : 1080 ∈ a_candidates 26 := by
  rw [mem_a_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 27, 30, 36, 40, 45, 54, 60, 72, 108, 120, 135, 216}
  refine ⟨by decide, by decide, by decide, by decide⟩


theorem twentysix_mem_a081512_twentysix : 1080 ∈ a081512_candidates 26 := by
  rw [mem_a081512_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 27, 30, 36, 40, 45, 54, 60, 72, 108, 120, 135, 216}
  refine ⟨by decide, by decide, by decide⟩


lemma not_mem_720_D_360 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 720) (hD_card : D.card ≥ 26) (hD_sum : D.sum id = 720)
    : 360 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 360).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 360).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 360).sum id > 360 := by
    let S_rem := (Nat.divisors 720) \ ({720} ∪ {360})
    have hD_erase_sub : D.erase 360 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 360 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 28 := by decide
    have hS_rem_sum : S_rem.sum id = 1338 := by decide
    let C_rem := S_rem \ (D.erase 360)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 360) ∩ S_rem = D.erase 360 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 3 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 564 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 3 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 3).filter (fun t => ¬ (t.sum id ≤ 564)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 3).filter (fun t => ¬ (t.sum id ≤ 564)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 564 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 360).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_a081512_26_720 : 720 ∉ a081512_candidates 26 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_not_720 : 720 ∉ D := not_mem_s_in_D (by omega) hD_pow (by omega) hD_sum
  have h_not_360 : 360 ∉ D := not_mem_720_D_360 hD_pow (by omega) hD_sum 
  let S_final := (Nat.divisors 720) \ ({720} ∪ {360})
  have hD_sub_S : D ⊆ S_final := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨hD_pow hx, ?_⟩
    simp only [Finset.mem_union, Finset.mem_singleton]
    push_neg
    refine ⟨?_, ?_⟩
    · rintro rfl; exact h_not_720 hx
    · rintro pe_mem; rcases pe_mem with pe_eq
      · subst pe_eq; exact h_not_360 hx
  let C_final := S_final \ D
  have hC_sub : C_final ⊆ S_final := Finset.sdiff_subset
  have h_inter : D ∩ S_final = D := Finset.inter_eq_self_of_subset hD_sub_S
  have hC_card : C_final.card = 2 := by
    dsimp [C_final]
    rw [Finset.card_sdiff]
    rw [h_inter, hD_card]
    omega
  have hS_card : S_final.card = 28 := by decide
  have hS_sum : S_final.sum id = 1338 := by decide
  have h_sum_add : C_final.sum id + D.sum id = S_final.sum id := Finset.sum_sdiff hD_sub_S
  have hC_sum : C_final.sum id = 618 := by omega
  have hC_mem : C_final ∈ S_final.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    exact ⟨hC_sub, hC_card⟩
  have h_filt : C_final ∈ (S_final.powersetCard 2).filter (fun t => t.sum id = 618) := by
    rw [Finset.mem_filter]
    exact ⟨hC_mem, hC_sum⟩
  have h_empty : (S_final.powersetCard 2).filter (fun t => t.sum id = 618) = ∅ := by decide
  rw [h_empty] at h_filt
  exact Finset.not_mem_empty C_final h_filt

lemma not_mem_840_D_420 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 840) (hD_card : D.card ≥ 26) (hD_sum : D.sum id = 840)
    : 420 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 420).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 420).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 420).sum id > 420 := by
    let S_rem := (Nat.divisors 840) \ ({840} ∪ {420})
    have hD_erase_sub : D.erase 420 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 420 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 30 := by decide
    have hS_rem_sum : S_rem.sum id = 1620 := by decide
    let C_rem := S_rem \ (D.erase 420)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 420) ∩ S_rem = D.erase 420 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 5 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 918 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 5 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 918)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 918)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 918 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 420).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_840_D_280 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 840) (hD_card : D.card ≥ 25) (hD_sum : D.sum id = 420)
    (h_420 : 420 ∉ D)
    : 280 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 280).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 280).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 280).sum id > 140 := by
    let S_rem := (Nat.divisors 840) \ ({840} ∪ {420} ∪ {280})
    have hD_erase_sub : D.erase 280 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 280 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_420 (Finset.mem_of_mem_erase hy)
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 29 := by decide
    have hS_rem_sum : S_rem.sum id = 1340 := by decide
    let C_rem := S_rem \ (D.erase 280)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 280) ∩ S_rem = D.erase 280 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 5 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 743 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 5 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 743)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 743)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 743 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 280).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_840_D_210 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 840) (hD_card : D.card ≥ 24) (hD_sum : D.sum id = 140)
    (h_420 : 420 ∉ D)
    (h_280 : 280 ∉ D)
    : 210 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 210).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 210).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 210).sum id ≥ 513 := by
    let S_rem := (Nat.divisors 840) \ ({840} ∪ {420} ∪ {280} ∪ {210})
    have hD_erase_sub : D.erase 210 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 210 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_420 (Finset.mem_of_mem_erase hy)
        · subst pe_eq; exact h_280 (Finset.mem_of_mem_erase hy)
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 28 := by decide
    have hS_rem_sum : S_rem.sum id = 1130 := by decide
    let C_rem := S_rem \ (D.erase 210)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 210) ∩ S_rem = D.erase 210 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 5 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 617 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 5 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 617)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 617)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 617 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 210).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_a081512_26_840 : 840 ∉ a081512_candidates 26 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_not_840 : 840 ∉ D := not_mem_s_in_D (by omega) hD_pow (by omega) hD_sum
  have h_not_420 : 420 ∉ D := not_mem_840_D_420 hD_pow (by omega) hD_sum 
  have h_not_280 : 280 ∉ D := not_mem_840_D_280 hD_pow (by omega) hD_sum h_not_420
  have h_not_210 : 210 ∉ D := not_mem_840_D_210 hD_pow (by omega) hD_sum h_not_420 h_not_280
  let S_final := (Nat.divisors 840) \ ({840} ∪ {420} ∪ {280} ∪ {210})
  have hD_sub_S : D ⊆ S_final := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨hD_pow hx, ?_⟩
    simp only [Finset.mem_union, Finset.mem_singleton]
    push_neg
    refine ⟨?_, ?_⟩
    · rintro rfl; exact h_not_840 hx
    · rintro pe_mem; rcases pe_mem with pe_eq
      · subst pe_eq; exact h_not_420 hx
      · subst pe_eq; exact h_not_280 hx
      · subst pe_eq; exact h_not_210 hx
  let C_final := S_final \ D
  have hC_sub : C_final ⊆ S_final := Finset.sdiff_subset
  have h_inter : D ∩ S_final = D := Finset.inter_eq_self_of_subset hD_sub_S
  have hC_card : C_final.card = 2 := by
    dsimp [C_final]
    rw [Finset.card_sdiff]
    rw [h_inter, hD_card]
    omega
  have hS_card : S_final.card = 28 := by decide
  have hS_sum : S_final.sum id = 1130 := by decide
  have h_sum_add : C_final.sum id + D.sum id = S_final.sum id := Finset.sum_sdiff hD_sub_S
  have hC_sum : C_final.sum id = 290 := by omega
  have hC_mem : C_final ∈ S_final.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    exact ⟨hC_sub, hC_card⟩
  have h_filt : C_final ∈ (S_final.powersetCard 2).filter (fun t => t.sum id = 290) := by
    rw [Finset.mem_filter]
    exact ⟨hC_mem, hC_sum⟩
  have h_empty : (S_final.powersetCard 2).filter (fun t => t.sum id = 290) = ∅ := by decide
  rw [h_empty] at h_filt
  exact Finset.not_mem_empty C_final h_filt

lemma not_mem_a081512_26_900 : 900 ∉ a081512_candidates 26 := by
  have h_div : (Nat.divisors 900).card = 27 := by decide
  by_cases h_le : k ≤ 27
  · have h_sum : (Nat.divisors 900).sum id = 2821 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 900).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_a081512_26_960 : 960 ∉ a081512_candidates 26 := by
  have h_div : (Nat.divisors 960).card = 28 := by decide
  by_cases h_le : k ≤ 28
  · have h_sum : (Nat.divisors 960).sum id = 3048 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 960).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_1008_D_504 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 1008) (hD_card : D.card ≥ 26) (hD_sum : D.sum id = 1008)
    : 504 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 504).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 504).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 504).sum id > 504 := by
    let S_rem := (Nat.divisors 1008) \ ({1008} ∪ {504})
    have hD_erase_sub : D.erase 504 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 504 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 28 := by decide
    have hS_rem_sum : S_rem.sum id = 1712 := by decide
    let C_rem := S_rem \ (D.erase 504)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 504) ∩ S_rem = D.erase 504 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 3 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 756 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 3 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 3).filter (fun t => ¬ (t.sum id ≤ 756)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 3).filter (fun t => ¬ (t.sum id ≤ 756)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 756 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 504).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_a081512_26_1008 : 1008 ∉ a081512_candidates 26 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_not_1008 : 1008 ∉ D := not_mem_s_in_D (by omega) hD_pow (by omega) hD_sum
  have h_not_504 : 504 ∉ D := not_mem_1008_D_504 hD_pow (by omega) hD_sum 
  let S_final := (Nat.divisors 1008) \ ({1008} ∪ {504})
  have hD_sub_S : D ⊆ S_final := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨hD_pow hx, ?_⟩
    simp only [Finset.mem_union, Finset.mem_singleton]
    push_neg
    refine ⟨?_, ?_⟩
    · rintro rfl; exact h_not_1008 hx
    · rintro pe_mem; rcases pe_mem with pe_eq
      · subst pe_eq; exact h_not_504 hx
  let C_final := S_final \ D
  have hC_sub : C_final ⊆ S_final := Finset.sdiff_subset
  have h_inter : D ∩ S_final = D := Finset.inter_eq_self_of_subset hD_sub_S
  have hC_card : C_final.card = 2 := by
    dsimp [C_final]
    rw [Finset.card_sdiff]
    rw [h_inter, hD_card]
    omega
  have hS_card : S_final.card = 28 := by decide
  have hS_sum : S_final.sum id = 1712 := by decide
  have h_sum_add : C_final.sum id + D.sum id = S_final.sum id := Finset.sum_sdiff hD_sub_S
  have hC_sum : C_final.sum id = 704 := by omega
  have hC_mem : C_final ∈ S_final.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    exact ⟨hC_sub, hC_card⟩
  have h_filt : C_final ∈ (S_final.powersetCard 2).filter (fun t => t.sum id = 704) := by
    rw [Finset.mem_filter]
    exact ⟨hC_mem, hC_sum⟩
  have h_empty : (S_final.powersetCard 2).filter (fun t => t.sum id = 704) = ∅ := by decide
  rw [h_empty] at h_filt
  exact Finset.not_mem_empty C_final h_filt

theorem a081512_candidates_26_ge (x : ℕ) (hx : x ∈ a081512_candidates 26) : 1080 ≤ x := by
  by_contra! h
  have hk21 : 26 ≥ 21 := by omega
  have hx720 : 720 ≤ x := a081512_candidates_ge_twentyone_ge_720 26 hk21 x hx

  have h_decide : ((List.range 360).map (· + 720)).all (fun y =>
      decide (if y = 720 ∨ y = 840 ∨ y = 900 ∨ y = 960 ∨ y = 1008 then True
              else (Nat.divisors y).card < 26)) = true := by decide
  have h_mem : x ∈ ((List.range 360).map (· + 720)) := by
    rw [List.mem_map]
    use x - 720
    constructor
    · rw [List.mem_range]; omega
    · omega
  have h_all := List.all_eq_true.mp h_decide x h_mem

  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 26 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow

  by_cases h720 : x = 720
  · subst h720; exact not_mem_a081512_26_720 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h840 : x = 840
  · subst h840; exact not_mem_a081512_26_840 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h900 : x = 900
  · subst h900; exact not_mem_a081512_26_900 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h960 : x = 960
  · subst h960; exact not_mem_a081512_26_960 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1008 : x = 1008
  · subst h1008; exact not_mem_a081512_26_1008 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  have h_not_cond : ¬ (x = 720 ∨ x = 840 ∨ x = 900 ∨ x = 960 ∨ x = 1008) := by
    rintro (rfl | rfl | rfl | rfl | rfl)

    · exact h720 rfl

    · exact h840 rfl

    · exact h900 rfl

    · exact h960 rfl

    · exact h1008 rfl

  have h_card : (Nat.divisors x).card < 26 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 720 ∨ x = 840 ∨ x = 900 ∨ x = 960 ∨ x = 1008
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega


theorem a_twentysix_le_a081512_twentysix : a 26 ≤ a081512 26 := by
  unfold a a081512
  change sInf (a_candidates 26) ≤ sInf (a081512_candidates 26)
  have hB : (a081512_candidates 26).Nonempty := ⟨1080, twentysix_mem_a081512_twentysix⟩
  have hB_ge : 1080 ≤ sInf (a081512_candidates 26) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_26_ge (sInf (a081512_candidates 26)) hmem
  have hA_le : sInf (a_candidates 26) ≤ 1080 := Nat.sInf_le twentysix_mem_a_twentysix
  exact le_trans hA_le hB_ge


theorem twentyseven_mem_a_twentyseven : 1260 ∈ a_candidates 27 := by
  rw [mem_a_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 18, 20, 21, 28, 30, 35, 36, 42, 45, 60, 63, 84, 90, 180, 420}
  refine ⟨by decide, by decide, by decide, by decide⟩


theorem twentyseven_mem_a081512_twentyseven : 1260 ∈ a081512_candidates 27 := by
  rw [mem_a081512_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 18, 20, 21, 28, 30, 35, 36, 42, 45, 60, 63, 84, 90, 180, 420}
  refine ⟨by decide, by decide, by decide⟩


lemma not_mem_a081512_27_720 : 720 ∉ a081512_candidates 27 := by
  have h_div : (Nat.divisors 720).card = 30 := by decide
  by_cases h_le : k ≤ 30
  · have h_sum : (Nat.divisors 720).sum id = 2418 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 720).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_840_D_420 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 840) (hD_card : D.card ≥ 27) (hD_sum : D.sum id = 840)
    : 420 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 420).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 420).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 420).sum id > 420 := by
    let S_rem := (Nat.divisors 840) \ ({840} ∪ {420})
    have hD_erase_sub : D.erase 420 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 420 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 30 := by decide
    have hS_rem_sum : S_rem.sum id = 1620 := by decide
    let C_rem := S_rem \ (D.erase 420)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 420) ∩ S_rem = D.erase 420 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 4 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 798 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 4 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 798)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 798)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 798 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 420).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_840_D_280 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 840) (hD_card : D.card ≥ 26) (hD_sum : D.sum id = 420)
    (h_420 : 420 ∉ D)
    : 280 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 280).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 280).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 280).sum id > 140 := by
    let S_rem := (Nat.divisors 840) \ ({840} ∪ {420} ∪ {280})
    have hD_erase_sub : D.erase 280 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 280 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_420 (Finset.mem_of_mem_erase hy)
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 29 := by decide
    have hS_rem_sum : S_rem.sum id = 1340 := by decide
    let C_rem := S_rem \ (D.erase 280)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 280) ∩ S_rem = D.erase 280 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 4 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 638 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 4 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 638)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 638)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 638 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 280).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_a081512_27_840 : 840 ∉ a081512_candidates 27 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_not_840 : 840 ∉ D := not_mem_s_in_D (by omega) hD_pow (by omega) hD_sum
  have h_not_420 : 420 ∉ D := not_mem_840_D_420 hD_pow (by omega) hD_sum 
  have h_not_280 : 280 ∉ D := not_mem_840_D_280 hD_pow (by omega) hD_sum h_not_420
  let S_final := (Nat.divisors 840) \ ({840} ∪ {420} ∪ {280})
  have hD_sub_S : D ⊆ S_final := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨hD_pow hx, ?_⟩
    simp only [Finset.mem_union, Finset.mem_singleton]
    push_neg
    refine ⟨?_, ?_⟩
    · rintro rfl; exact h_not_840 hx
    · rintro pe_mem; rcases pe_mem with pe_eq
      · subst pe_eq; exact h_not_420 hx
      · subst pe_eq; exact h_not_280 hx
  let C_final := S_final \ D
  have hC_sub : C_final ⊆ S_final := Finset.sdiff_subset
  have h_inter : D ∩ S_final = D := Finset.inter_eq_self_of_subset hD_sub_S
  have hC_card : C_final.card = 2 := by
    dsimp [C_final]
    rw [Finset.card_sdiff]
    rw [h_inter, hD_card]
    omega
  have hS_card : S_final.card = 29 := by decide
  have hS_sum : S_final.sum id = 1340 := by decide
  have h_sum_add : C_final.sum id + D.sum id = S_final.sum id := Finset.sum_sdiff hD_sub_S
  have hC_sum : C_final.sum id = 500 := by omega
  have hC_mem : C_final ∈ S_final.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    exact ⟨hC_sub, hC_card⟩
  have h_filt : C_final ∈ (S_final.powersetCard 2).filter (fun t => t.sum id = 500) := by
    rw [Finset.mem_filter]
    exact ⟨hC_mem, hC_sum⟩
  have h_empty : (S_final.powersetCard 2).filter (fun t => t.sum id = 500) = ∅ := by decide
  rw [h_empty] at h_filt
  exact Finset.not_mem_empty C_final h_filt

lemma not_mem_a081512_27_900 : 900 ∉ a081512_candidates 27 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_eq : D = Nat.divisors 900 := Finset.eq_of_subset_of_card_le hD_pow (by omega)
  subst h_eq
  have h_sum_divs : (Nat.divisors 900).sum id = 2821 := by decide
  omega


lemma not_mem_a081512_27_960 : 960 ∉ a081512_candidates 27 := by
  have h_div : (Nat.divisors 960).card = 28 := by decide
  by_cases h_le : k ≤ 28
  · have h_sum : (Nat.divisors 960).sum id = 3048 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 960).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_a081512_27_1008 : 1008 ∉ a081512_candidates 27 := by
  have h_div : (Nat.divisors 1008).card = 30 := by decide
  by_cases h_le : k ≤ 30
  · have h_sum : (Nat.divisors 1008).sum id = 3224 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 1008).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_1080_D_540 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 1080) (hD_card : D.card ≥ 27) (hD_sum : D.sum id = 1080)
    : 540 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 540).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 540).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 540).sum id > 540 := by
    let S_rem := (Nat.divisors 1080) \ ({1080} ∪ {540})
    have hD_erase_sub : D.erase 540 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 540 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 30 := by decide
    have hS_rem_sum : S_rem.sum id = 1980 := by decide
    let C_rem := S_rem \ (D.erase 540)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 540) ∩ S_rem = D.erase 540 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 4 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 1026 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 4 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 1026)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 1026)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 1026 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 540).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_1080_D_360 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 1080) (hD_card : D.card ≥ 26) (hD_sum : D.sum id = 540)
    (h_540 : 540 ∉ D)
    : 360 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 360).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 360).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 360).sum id > 180 := by
    let S_rem := (Nat.divisors 1080) \ ({1080} ∪ {540} ∪ {360})
    have hD_erase_sub : D.erase 360 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 360 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_540 (Finset.mem_of_mem_erase hy)
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 29 := by decide
    have hS_rem_sum : S_rem.sum id = 1620 := by decide
    let C_rem := S_rem \ (D.erase 360)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 360) ∩ S_rem = D.erase 360 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 4 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 801 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 4 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 801)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 801)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 801 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 360).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_a081512_27_1080 : 1080 ∉ a081512_candidates 27 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_not_1080 : 1080 ∉ D := not_mem_s_in_D (by omega) hD_pow (by omega) hD_sum
  have h_not_540 : 540 ∉ D := not_mem_1080_D_540 hD_pow (by omega) hD_sum 
  have h_not_360 : 360 ∉ D := not_mem_1080_D_360 hD_pow (by omega) hD_sum h_not_540
  let S_final := (Nat.divisors 1080) \ ({1080} ∪ {540} ∪ {360})
  have hD_sub_S : D ⊆ S_final := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨hD_pow hx, ?_⟩
    simp only [Finset.mem_union, Finset.mem_singleton]
    push_neg
    refine ⟨?_, ?_⟩
    · rintro rfl; exact h_not_1080 hx
    · rintro pe_mem; rcases pe_mem with pe_eq
      · subst pe_eq; exact h_not_540 hx
      · subst pe_eq; exact h_not_360 hx
  let C_final := S_final \ D
  have hC_sub : C_final ⊆ S_final := Finset.sdiff_subset
  have h_inter : D ∩ S_final = D := Finset.inter_eq_self_of_subset hD_sub_S
  have hC_card : C_final.card = 2 := by
    dsimp [C_final]
    rw [Finset.card_sdiff]
    rw [h_inter, hD_card]
    omega
  have hS_card : S_final.card = 29 := by decide
  have hS_sum : S_final.sum id = 1620 := by decide
  have h_sum_add : C_final.sum id + D.sum id = S_final.sum id := Finset.sum_sdiff hD_sub_S
  have hC_sum : C_final.sum id = 540 := by omega
  have hC_mem : C_final ∈ S_final.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    exact ⟨hC_sub, hC_card⟩
  have h_filt : C_final ∈ (S_final.powersetCard 2).filter (fun t => t.sum id = 540) := by
    rw [Finset.mem_filter]
    exact ⟨hC_mem, hC_sum⟩
  have h_empty : (S_final.powersetCard 2).filter (fun t => t.sum id = 540) = ∅ := by decide
  rw [h_empty] at h_filt
  exact Finset.not_mem_empty C_final h_filt

lemma not_mem_a081512_27_1200 : 1200 ∉ a081512_candidates 27 := by
  have h_div : (Nat.divisors 1200).card = 30 := by decide
  by_cases h_le : k ≤ 30
  · have h_sum : (Nat.divisors 1200).sum id = 3844 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 1200).card := Finset.card_le_card hD_sub
    omega


theorem a081512_candidates_27_ge (x : ℕ) (hx : x ∈ a081512_candidates 27) : 1260 ≤ x := by
  by_contra! h
  have hk21 : 27 ≥ 21 := by omega
  have hx720 : 720 ≤ x := a081512_candidates_ge_twentyone_ge_720 27 hk21 x hx

  have h_decide : ((List.range 540).map (· + 720)).all (fun y =>
      decide (if y = 720 ∨ y = 840 ∨ y = 900 ∨ y = 960 ∨ y = 1008 ∨ y = 1080 ∨ y = 1200 then True
              else (Nat.divisors y).card < 27)) = true := by decide
  have h_mem : x ∈ ((List.range 540).map (· + 720)) := by
    rw [List.mem_map]
    use x - 720
    constructor
    · rw [List.mem_range]; omega
    · omega
  have h_all := List.all_eq_true.mp h_decide x h_mem

  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 27 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow

  by_cases h720 : x = 720
  · subst h720; exact not_mem_a081512_27_720 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h840 : x = 840
  · subst h840; exact not_mem_a081512_27_840 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h900 : x = 900
  · subst h900; exact not_mem_a081512_27_900 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h960 : x = 960
  · subst h960; exact not_mem_a081512_27_960 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1008 : x = 1008
  · subst h1008; exact not_mem_a081512_27_1008 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1080 : x = 1080
  · subst h1080; exact not_mem_a081512_27_1080 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1200 : x = 1200
  · subst h1200; exact not_mem_a081512_27_1200 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  have h_not_cond : ¬ (x = 720 ∨ x = 840 ∨ x = 900 ∨ x = 960 ∨ x = 1008 ∨ x = 1080 ∨ x = 1200) := by
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)

    · exact h720 rfl

    · exact h840 rfl

    · exact h900 rfl

    · exact h960 rfl

    · exact h1008 rfl

    · exact h1080 rfl

    · exact h1200 rfl

  have h_card : (Nat.divisors x).card < 27 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 720 ∨ x = 840 ∨ x = 900 ∨ x = 960 ∨ x = 1008 ∨ x = 1080 ∨ x = 1200
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega


theorem a_twentyseven_le_a081512_twentyseven : a 27 ≤ a081512 27 := by
  unfold a a081512
  change sInf (a_candidates 27) ≤ sInf (a081512_candidates 27)
  have hB : (a081512_candidates 27).Nonempty := ⟨1260, twentyseven_mem_a081512_twentyseven⟩
  have hB_ge : 1260 ≤ sInf (a081512_candidates 27) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_27_ge (sInf (a081512_candidates 27)) hmem
  have hA_le : sInf (a_candidates 27) ≤ 1260 := Nat.sInf_le twentyseven_mem_a_twentyseven
  exact le_trans hA_le hB_ge


theorem twentyeight_mem_a_twentyeight : 1260 ∈ a_candidates 28 := by
  rw [mem_a_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 18, 20, 21, 28, 30, 35, 36, 42, 45, 60, 63, 84, 90, 105, 180, 315}
  refine ⟨by decide, by decide, by decide, by decide⟩


theorem twentyeight_mem_a081512_twentyeight : 1260 ∈ a081512_candidates 28 := by
  rw [mem_a081512_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 18, 20, 21, 28, 30, 35, 36, 42, 45, 60, 63, 84, 90, 105, 180, 315}
  refine ⟨by decide, by decide, by decide⟩


lemma not_mem_a081512_28_720 : 720 ∉ a081512_candidates 28 := by
  have h_div : (Nat.divisors 720).card = 30 := by decide
  by_cases h_le : k ≤ 30
  · have h_sum : (Nat.divisors 720).sum id = 2418 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 720).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_840_D_420 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 840) (hD_card : D.card ≥ 28) (hD_sum : D.sum id = 840)
    : 420 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 420).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 420).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 420).sum id > 420 := by
    let S_rem := (Nat.divisors 840) \ ({840} ∪ {420})
    have hD_erase_sub : D.erase 420 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 420 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 30 := by decide
    have hS_rem_sum : S_rem.sum id = 1620 := by decide
    let C_rem := S_rem \ (D.erase 420)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 420) ∩ S_rem = D.erase 420 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 3 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 658 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 3 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 3).filter (fun t => ¬ (t.sum id ≤ 658)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 3).filter (fun t => ¬ (t.sum id ≤ 658)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 658 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 420).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_a081512_28_840 : 840 ∉ a081512_candidates 28 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_not_840 : 840 ∉ D := not_mem_s_in_D (by omega) hD_pow (by omega) hD_sum
  have h_not_420 : 420 ∉ D := not_mem_840_D_420 hD_pow (by omega) hD_sum 
  let S_final := (Nat.divisors 840) \ ({840} ∪ {420})
  have hD_sub_S : D ⊆ S_final := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨hD_pow hx, ?_⟩
    simp only [Finset.mem_union, Finset.mem_singleton]
    push_neg
    refine ⟨?_, ?_⟩
    · rintro rfl; exact h_not_840 hx
    · rintro pe_mem; rcases pe_mem with pe_eq
      · subst pe_eq; exact h_not_420 hx
  let C_final := S_final \ D
  have hC_sub : C_final ⊆ S_final := Finset.sdiff_subset
  have h_inter : D ∩ S_final = D := Finset.inter_eq_self_of_subset hD_sub_S
  have hC_card : C_final.card = 2 := by
    dsimp [C_final]
    rw [Finset.card_sdiff]
    rw [h_inter, hD_card]
    omega
  have hS_card : S_final.card = 30 := by decide
  have hS_sum : S_final.sum id = 1620 := by decide
  have h_sum_add : C_final.sum id + D.sum id = S_final.sum id := Finset.sum_sdiff hD_sub_S
  have hC_sum : C_final.sum id = 780 := by omega
  have hC_mem : C_final ∈ S_final.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    exact ⟨hC_sub, hC_card⟩
  have h_filt : C_final ∈ (S_final.powersetCard 2).filter (fun t => t.sum id = 780) := by
    rw [Finset.mem_filter]
    exact ⟨hC_mem, hC_sum⟩
  have h_empty : (S_final.powersetCard 2).filter (fun t => t.sum id = 780) = ∅ := by decide
  rw [h_empty] at h_filt
  exact Finset.not_mem_empty C_final h_filt

lemma not_mem_a081512_28_960 : 960 ∉ a081512_candidates 28 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_eq : D = Nat.divisors 960 := Finset.eq_of_subset_of_card_le hD_pow (by omega)
  subst h_eq
  have h_sum_divs : (Nat.divisors 960).sum id = 3048 := by decide
  omega


lemma not_mem_a081512_28_1008 : 1008 ∉ a081512_candidates 28 := by
  have h_div : (Nat.divisors 1008).card = 30 := by decide
  by_cases h_le : k ≤ 30
  · have h_sum : (Nat.divisors 1008).sum id = 3224 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 1008).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_1080_D_540 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 1080) (hD_card : D.card ≥ 28) (hD_sum : D.sum id = 1080)
    : 540 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 540).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 540).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 540).sum id > 540 := by
    let S_rem := (Nat.divisors 1080) \ ({1080} ∪ {540})
    have hD_erase_sub : D.erase 540 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 540 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 30 := by decide
    have hS_rem_sum : S_rem.sum id = 1980 := by decide
    let C_rem := S_rem \ (D.erase 540)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 540) ∩ S_rem = D.erase 540 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 3 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 846 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 3 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 3).filter (fun t => ¬ (t.sum id ≤ 846)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 3).filter (fun t => ¬ (t.sum id ≤ 846)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 846 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 540).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_a081512_28_1080 : 1080 ∉ a081512_candidates 28 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_not_1080 : 1080 ∉ D := not_mem_s_in_D (by omega) hD_pow (by omega) hD_sum
  have h_not_540 : 540 ∉ D := not_mem_1080_D_540 hD_pow (by omega) hD_sum 
  let S_final := (Nat.divisors 1080) \ ({1080} ∪ {540})
  have hD_sub_S : D ⊆ S_final := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨hD_pow hx, ?_⟩
    simp only [Finset.mem_union, Finset.mem_singleton]
    push_neg
    refine ⟨?_, ?_⟩
    · rintro rfl; exact h_not_1080 hx
    · rintro pe_mem; rcases pe_mem with pe_eq
      · subst pe_eq; exact h_not_540 hx
  let C_final := S_final \ D
  have hC_sub : C_final ⊆ S_final := Finset.sdiff_subset
  have h_inter : D ∩ S_final = D := Finset.inter_eq_self_of_subset hD_sub_S
  have hC_card : C_final.card = 2 := by
    dsimp [C_final]
    rw [Finset.card_sdiff]
    rw [h_inter, hD_card]
    omega
  have hS_card : S_final.card = 30 := by decide
  have hS_sum : S_final.sum id = 1980 := by decide
  have h_sum_add : C_final.sum id + D.sum id = S_final.sum id := Finset.sum_sdiff hD_sub_S
  have hC_sum : C_final.sum id = 900 := by omega
  have hC_mem : C_final ∈ S_final.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    exact ⟨hC_sub, hC_card⟩
  have h_filt : C_final ∈ (S_final.powersetCard 2).filter (fun t => t.sum id = 900) := by
    rw [Finset.mem_filter]
    exact ⟨hC_mem, hC_sum⟩
  have h_empty : (S_final.powersetCard 2).filter (fun t => t.sum id = 900) = ∅ := by decide
  rw [h_empty] at h_filt
  exact Finset.not_mem_empty C_final h_filt

lemma not_mem_a081512_28_1200 : 1200 ∉ a081512_candidates 28 := by
  have h_div : (Nat.divisors 1200).card = 30 := by decide
  by_cases h_le : k ≤ 30
  · have h_sum : (Nat.divisors 1200).sum id = 3844 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 1200).card := Finset.card_le_card hD_sub
    omega


theorem a081512_candidates_28_ge (x : ℕ) (hx : x ∈ a081512_candidates 28) : 1260 ≤ x := by
  by_contra! h
  have hk21 : 28 ≥ 21 := by omega
  have hx720 : 720 ≤ x := a081512_candidates_ge_twentyone_ge_720 28 hk21 x hx

  have h_decide : ((List.range 540).map (· + 720)).all (fun y =>
      decide (if y = 720 ∨ y = 840 ∨ y = 960 ∨ y = 1008 ∨ y = 1080 ∨ y = 1200 then True
              else (Nat.divisors y).card < 28)) = true := by decide
  have h_mem : x ∈ ((List.range 540).map (· + 720)) := by
    rw [List.mem_map]
    use x - 720
    constructor
    · rw [List.mem_range]; omega
    · omega
  have h_all := List.all_eq_true.mp h_decide x h_mem

  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 28 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow

  by_cases h720 : x = 720
  · subst h720; exact not_mem_a081512_28_720 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h840 : x = 840
  · subst h840; exact not_mem_a081512_28_840 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h960 : x = 960
  · subst h960; exact not_mem_a081512_28_960 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1008 : x = 1008
  · subst h1008; exact not_mem_a081512_28_1008 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1080 : x = 1080
  · subst h1080; exact not_mem_a081512_28_1080 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1200 : x = 1200
  · subst h1200; exact not_mem_a081512_28_1200 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  have h_not_cond : ¬ (x = 720 ∨ x = 840 ∨ x = 960 ∨ x = 1008 ∨ x = 1080 ∨ x = 1200) := by
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)

    · exact h720 rfl

    · exact h840 rfl

    · exact h960 rfl

    · exact h1008 rfl

    · exact h1080 rfl

    · exact h1200 rfl

  have h_card : (Nat.divisors x).card < 28 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 720 ∨ x = 840 ∨ x = 960 ∨ x = 1008 ∨ x = 1080 ∨ x = 1200
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega


theorem a_twentyeight_le_a081512_twentyeight : a 28 ≤ a081512 28 := by
  unfold a a081512
  change sInf (a_candidates 28) ≤ sInf (a081512_candidates 28)
  have hB : (a081512_candidates 28).Nonempty := ⟨1260, twentyeight_mem_a081512_twentyeight⟩
  have hB_ge : 1260 ≤ sInf (a081512_candidates 28) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_28_ge (sInf (a081512_candidates 28)) hmem
  have hA_le : sInf (a_candidates 28) ≤ 1260 := Nat.sInf_le twentyeight_mem_a_twentyeight
  exact le_trans hA_le hB_ge


theorem twentynine_mem_a_twentynine : 1260 ∈ a_candidates 29 := by
  rw [mem_a_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 18, 20, 21, 28, 30, 35, 36, 42, 45, 60, 63, 70, 84, 90, 140, 180, 210}
  refine ⟨by decide, by decide, by decide, by decide⟩


theorem twentynine_mem_a081512_twentynine : 1260 ∈ a081512_candidates 29 := by
  rw [mem_a081512_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 18, 20, 21, 28, 30, 35, 36, 42, 45, 60, 63, 70, 84, 90, 140, 180, 210}
  refine ⟨by decide, by decide, by decide⟩


lemma not_mem_a081512_29_720 : 720 ∉ a081512_candidates 29 := by
  have h_div : (Nat.divisors 720).card = 30 := by decide
  by_cases h_le : k ≤ 30
  · have h_sum : (Nat.divisors 720).sum id = 2418 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 720).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_a081512_29_840 : 840 ∉ a081512_candidates 29 := by
  have h_div : (Nat.divisors 840).card = 32 := by decide
  by_cases h_le : k ≤ 32
  · have h_sum : (Nat.divisors 840).sum id = 2880 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 840).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_a081512_29_1008 : 1008 ∉ a081512_candidates 29 := by
  have h_div : (Nat.divisors 1008).card = 30 := by decide
  by_cases h_le : k ≤ 30
  · have h_sum : (Nat.divisors 1008).sum id = 3224 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 1008).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_a081512_29_1080 : 1080 ∉ a081512_candidates 29 := by
  have h_div : (Nat.divisors 1080).card = 32 := by decide
  by_cases h_le : k ≤ 32
  · have h_sum : (Nat.divisors 1080).sum id = 3600 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 1080).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_a081512_29_1200 : 1200 ∉ a081512_candidates 29 := by
  have h_div : (Nat.divisors 1200).card = 30 := by decide
  by_cases h_le : k ≤ 30
  · have h_sum : (Nat.divisors 1200).sum id = 3844 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 1200).card := Finset.card_le_card hD_sub
    omega


theorem a081512_candidates_29_ge (x : ℕ) (hx : x ∈ a081512_candidates 29) : 1260 ≤ x := by
  by_contra! h
  have hk21 : 29 ≥ 21 := by omega
  have hx720 : 720 ≤ x := a081512_candidates_ge_twentyone_ge_720 29 hk21 x hx

  have h_decide : ((List.range 540).map (· + 720)).all (fun y =>
      decide (if y = 720 ∨ y = 840 ∨ y = 1008 ∨ y = 1080 ∨ y = 1200 then True
              else (Nat.divisors y).card < 29)) = true := by decide
  have h_mem : x ∈ ((List.range 540).map (· + 720)) := by
    rw [List.mem_map]
    use x - 720
    constructor
    · rw [List.mem_range]; omega
    · omega
  have h_all := List.all_eq_true.mp h_decide x h_mem

  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 29 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow

  by_cases h720 : x = 720
  · subst h720; exact not_mem_a081512_29_720 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h840 : x = 840
  · subst h840; exact not_mem_a081512_29_840 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1008 : x = 1008
  · subst h1008; exact not_mem_a081512_29_1008 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1080 : x = 1080
  · subst h1080; exact not_mem_a081512_29_1080 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1200 : x = 1200
  · subst h1200; exact not_mem_a081512_29_1200 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  have h_not_cond : ¬ (x = 720 ∨ x = 840 ∨ x = 1008 ∨ x = 1080 ∨ x = 1200) := by
    rintro (rfl | rfl | rfl | rfl | rfl)

    · exact h720 rfl

    · exact h840 rfl

    · exact h1008 rfl

    · exact h1080 rfl

    · exact h1200 rfl

  have h_card : (Nat.divisors x).card < 29 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 720 ∨ x = 840 ∨ x = 1008 ∨ x = 1080 ∨ x = 1200
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega


theorem a_twentynine_le_a081512_twentynine : a 29 ≤ a081512 29 := by
  unfold a a081512
  change sInf (a_candidates 29) ≤ sInf (a081512_candidates 29)
  have hB : (a081512_candidates 29).Nonempty := ⟨1260, twentynine_mem_a081512_twentynine⟩
  have hB_ge : 1260 ≤ sInf (a081512_candidates 29) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_29_ge (sInf (a081512_candidates 29)) hmem
  have hA_le : sInf (a_candidates 29) ≤ 1260 := Nat.sInf_le twentynine_mem_a_twentynine
  exact le_trans hA_le hB_ge


theorem thirty_mem_a_thirty : 1680 ∈ a_candidates 30 := by
  rw [mem_a_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 16, 20, 21, 24, 28, 30, 35, 40, 42, 48, 60, 70, 80, 84, 105, 120, 210, 560}
  refine ⟨by decide, by decide, by decide, by decide⟩


theorem thirty_mem_a081512_thirty : 1680 ∈ a081512_candidates 30 := by
  rw [mem_a081512_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 16, 20, 21, 24, 28, 30, 35, 40, 42, 48, 60, 70, 80, 84, 105, 120, 210, 560}
  refine ⟨by decide, by decide, by decide⟩


lemma not_mem_a081512_30_720 : 720 ∉ a081512_candidates 30 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_eq : D = Nat.divisors 720 := Finset.eq_of_subset_of_card_le hD_pow (by omega)
  subst h_eq
  have h_sum_divs : (Nat.divisors 720).sum id = 2418 := by decide
  omega


lemma not_mem_a081512_30_840 : 840 ∉ a081512_candidates 30 := by
  have h_div : (Nat.divisors 840).card = 32 := by decide
  by_cases h_le : k ≤ 32
  · have h_sum : (Nat.divisors 840).sum id = 2880 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 840).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_a081512_30_1008 : 1008 ∉ a081512_candidates 30 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_eq : D = Nat.divisors 1008 := Finset.eq_of_subset_of_card_le hD_pow (by omega)
  subst h_eq
  have h_sum_divs : (Nat.divisors 1008).sum id = 3224 := by decide
  omega


lemma not_mem_a081512_30_1080 : 1080 ∉ a081512_candidates 30 := by
  have h_div : (Nat.divisors 1080).card = 32 := by decide
  by_cases h_le : k ≤ 32
  · have h_sum : (Nat.divisors 1080).sum id = 3600 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 1080).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_a081512_30_1200 : 1200 ∉ a081512_candidates 30 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_eq : D = Nat.divisors 1200 := Finset.eq_of_subset_of_card_le hD_pow (by omega)
  subst h_eq
  have h_sum_divs : (Nat.divisors 1200).sum id = 3844 := by decide
  omega


lemma not_mem_1260_D_630 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 1260) (hD_card : D.card ≥ 30) (hD_sum : D.sum id = 1260)
    : 630 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 630).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 630).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 630).sum id > 630 := by
    let S_rem := (Nat.divisors 1260) \ ({1260} ∪ {630})
    have hD_erase_sub : D.erase 630 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 630 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 34 := by decide
    have hS_rem_sum : S_rem.sum id = 2478 := by decide
    let C_rem := S_rem \ (D.erase 630)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 630) ∩ S_rem = D.erase 630 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 5 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 1377 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 5 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 1377)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 1377)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 1377 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 630).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_1260_D_420 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 1260) (hD_card : D.card ≥ 29) (hD_sum : D.sum id = 630)
    (h_630 : 630 ∉ D)
    : 420 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 420).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 420).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 420).sum id > 210 := by
    let S_rem := (Nat.divisors 1260) \ ({1260} ∪ {630} ∪ {420})
    have hD_erase_sub : D.erase 420 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 420 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_630 (Finset.mem_of_mem_erase hy)
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 33 := by decide
    have hS_rem_sum : S_rem.sum id = 2058 := by decide
    let C_rem := S_rem \ (D.erase 420)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 420) ∩ S_rem = D.erase 420 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 5 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 1097 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 5 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 1097)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 1097)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 1097 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 420).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_1260_D_315 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 1260) (hD_card : D.card ≥ 28) (hD_sum : D.sum id = 210)
    (h_630 : 630 ∉ D)
    (h_420 : 420 ∉ D)
    : 315 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 315).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 315).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 315).sum id ≥ 835 := by
    let S_rem := (Nat.divisors 1260) \ ({1260} ∪ {630} ∪ {420} ∪ {315})
    have hD_erase_sub : D.erase 315 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 315 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_630 (Finset.mem_of_mem_erase hy)
        · subst pe_eq; exact h_420 (Finset.mem_of_mem_erase hy)
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 32 := by decide
    have hS_rem_sum : S_rem.sum id = 1743 := by decide
    let C_rem := S_rem \ (D.erase 315)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 315) ∩ S_rem = D.erase 315 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 5 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 908 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 5 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 908)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 908)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 908 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 315).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_a081512_30_1260 : 1260 ∉ a081512_candidates 30 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_not_1260 : 1260 ∉ D := not_mem_s_in_D (by omega) hD_pow (by omega) hD_sum
  have h_not_630 : 630 ∉ D := not_mem_1260_D_630 hD_pow (by omega) hD_sum 
  have h_not_420 : 420 ∉ D := not_mem_1260_D_420 hD_pow (by omega) hD_sum h_not_630
  have h_not_315 : 315 ∉ D := not_mem_1260_D_315 hD_pow (by omega) hD_sum h_not_630 h_not_420
  let S_final := (Nat.divisors 1260) \ ({1260} ∪ {630} ∪ {420} ∪ {315})
  have hD_sub_S : D ⊆ S_final := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨hD_pow hx, ?_⟩
    simp only [Finset.mem_union, Finset.mem_singleton]
    push_neg
    refine ⟨?_, ?_⟩
    · rintro rfl; exact h_not_1260 hx
    · rintro pe_mem; rcases pe_mem with pe_eq
      · subst pe_eq; exact h_not_630 hx
      · subst pe_eq; exact h_not_420 hx
      · subst pe_eq; exact h_not_315 hx
  let C_final := S_final \ D
  have hC_sub : C_final ⊆ S_final := Finset.sdiff_subset
  have h_inter : D ∩ S_final = D := Finset.inter_eq_self_of_subset hD_sub_S
  have hC_card : C_final.card = 2 := by
    dsimp [C_final]
    rw [Finset.card_sdiff]
    rw [h_inter, hD_card]
    omega
  have hS_card : S_final.card = 32 := by decide
  have hS_sum : S_final.sum id = 1743 := by decide
  have h_sum_add : C_final.sum id + D.sum id = S_final.sum id := Finset.sum_sdiff hD_sub_S
  have hC_sum : C_final.sum id = 483 := by omega
  have hC_mem : C_final ∈ S_final.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    exact ⟨hC_sub, hC_card⟩
  have h_filt : C_final ∈ (S_final.powersetCard 2).filter (fun t => t.sum id = 483) := by
    rw [Finset.mem_filter]
    exact ⟨hC_mem, hC_sum⟩
  have h_empty : (S_final.powersetCard 2).filter (fun t => t.sum id = 483) = ∅ := by decide
  rw [h_empty] at h_filt
  exact Finset.not_mem_empty C_final h_filt

lemma not_mem_a081512_30_1320 : 1320 ∉ a081512_candidates 30 := by
  have h_div : (Nat.divisors 1320).card = 32 := by decide
  by_cases h_le : k ≤ 32
  · have h_sum : (Nat.divisors 1320).sum id = 4320 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 1320).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_1440_D_720 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 1440) (hD_card : D.card ≥ 30) (hD_sum : D.sum id = 1440)
    : 720 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 720).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 720).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 720).sum id > 720 := by
    let S_rem := (Nat.divisors 1440) \ ({1440} ∪ {720})
    have hD_erase_sub : D.erase 720 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 720 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 34 := by decide
    have hS_rem_sum : S_rem.sum id = 2754 := by decide
    let C_rem := S_rem \ (D.erase 720)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 720) ∩ S_rem = D.erase 720 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 5 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 1548 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 5 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 1548)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 1548)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 1548 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 720).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_1440_D_480 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 1440) (hD_card : D.card ≥ 29) (hD_sum : D.sum id = 720)
    (h_720 : 720 ∉ D)
    : 480 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 480).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 480).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 480).sum id > 240 := by
    let S_rem := (Nat.divisors 1440) \ ({1440} ∪ {720} ∪ {480})
    have hD_erase_sub : D.erase 480 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 480 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_720 (Finset.mem_of_mem_erase hy)
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 33 := by decide
    have hS_rem_sum : S_rem.sum id = 2274 := by decide
    let C_rem := S_rem \ (D.erase 480)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 480) ∩ S_rem = D.erase 480 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 5 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 1228 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 5 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 1228)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 1228)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 1228 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 480).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_1440_D_360 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 1440) (hD_card : D.card ≥ 28) (hD_sum : D.sum id = 240)
    (h_720 : 720 ∉ D)
    (h_480 : 480 ∉ D)
    : 360 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 360).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 360).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 360).sum id ≥ 902 := by
    let S_rem := (Nat.divisors 1440) \ ({1440} ∪ {720} ∪ {480} ∪ {360})
    have hD_erase_sub : D.erase 360 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 360 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_720 (Finset.mem_of_mem_erase hy)
        · subst pe_eq; exact h_480 (Finset.mem_of_mem_erase hy)
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 32 := by decide
    have hS_rem_sum : S_rem.sum id = 1914 := by decide
    let C_rem := S_rem \ (D.erase 360)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 360) ∩ S_rem = D.erase 360 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 5 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 1012 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 5 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 1012)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 5).filter (fun t => ¬ (t.sum id ≤ 1012)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 1012 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 360).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_a081512_30_1440 : 1440 ∉ a081512_candidates 30 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_not_1440 : 1440 ∉ D := not_mem_s_in_D (by omega) hD_pow (by omega) hD_sum
  have h_not_720 : 720 ∉ D := not_mem_1440_D_720 hD_pow (by omega) hD_sum 
  have h_not_480 : 480 ∉ D := not_mem_1440_D_480 hD_pow (by omega) hD_sum h_not_720
  have h_not_360 : 360 ∉ D := not_mem_1440_D_360 hD_pow (by omega) hD_sum h_not_720 h_not_480
  let S_final := (Nat.divisors 1440) \ ({1440} ∪ {720} ∪ {480} ∪ {360})
  have hD_sub_S : D ⊆ S_final := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨hD_pow hx, ?_⟩
    simp only [Finset.mem_union, Finset.mem_singleton]
    push_neg
    refine ⟨?_, ?_⟩
    · rintro rfl; exact h_not_1440 hx
    · rintro pe_mem; rcases pe_mem with pe_eq
      · subst pe_eq; exact h_not_720 hx
      · subst pe_eq; exact h_not_480 hx
      · subst pe_eq; exact h_not_360 hx
  let C_final := S_final \ D
  have hC_sub : C_final ⊆ S_final := Finset.sdiff_subset
  have h_inter : D ∩ S_final = D := Finset.inter_eq_self_of_subset hD_sub_S
  have hC_card : C_final.card = 2 := by
    dsimp [C_final]
    rw [Finset.card_sdiff]
    rw [h_inter, hD_card]
    omega
  have hS_card : S_final.card = 32 := by decide
  have hS_sum : S_final.sum id = 1914 := by decide
  have h_sum_add : C_final.sum id + D.sum id = S_final.sum id := Finset.sum_sdiff hD_sub_S
  have hC_sum : C_final.sum id = 474 := by omega
  have hC_mem : C_final ∈ S_final.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    exact ⟨hC_sub, hC_card⟩
  have h_filt : C_final ∈ (S_final.powersetCard 2).filter (fun t => t.sum id = 474) := by
    rw [Finset.mem_filter]
    exact ⟨hC_mem, hC_sum⟩
  have h_empty : (S_final.powersetCard 2).filter (fun t => t.sum id = 474) = ∅ := by decide
  rw [h_empty] at h_filt
  exact Finset.not_mem_empty C_final h_filt

lemma not_mem_a081512_30_1512 : 1512 ∉ a081512_candidates 30 := by
  have h_div : (Nat.divisors 1512).card = 32 := by decide
  by_cases h_le : k ≤ 32
  · have h_sum : (Nat.divisors 1512).sum id = 4800 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 1512).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_a081512_30_1560 : 1560 ∉ a081512_candidates 30 := by
  have h_div : (Nat.divisors 1560).card = 32 := by decide
  by_cases h_le : k ≤ 32
  · have h_sum : (Nat.divisors 1560).sum id = 5040 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 1560).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_a081512_30_1584 : 1584 ∉ a081512_candidates 30 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_eq : D = Nat.divisors 1584 := Finset.eq_of_subset_of_card_le hD_pow (by omega)
  subst h_eq
  have h_sum_divs : (Nat.divisors 1584).sum id = 4836 := by decide
  omega


lemma not_mem_a081512_30_1620 : 1620 ∉ a081512_candidates 30 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_eq : D = Nat.divisors 1620 := Finset.eq_of_subset_of_card_le hD_pow (by omega)
  subst h_eq
  have h_sum_divs : (Nat.divisors 1620).sum id = 5082 := by decide
  omega


theorem a081512_candidates_30_ge (x : ℕ) (hx : x ∈ a081512_candidates 30) : 1680 ≤ x := by
  by_contra! h
  have hk21 : 30 ≥ 21 := by omega
  have hx720 : 720 ≤ x := a081512_candidates_ge_twentyone_ge_720 30 hk21 x hx

  have h_decide : ((List.range 960).map (· + 720)).all (fun y =>
      decide (if y = 720 ∨ y = 840 ∨ y = 1008 ∨ y = 1080 ∨ y = 1200 ∨ y = 1260 ∨ y = 1320 ∨ y = 1440 ∨ y = 1512 ∨ y = 1560 ∨ y = 1584 ∨ y = 1620 then True
              else (Nat.divisors y).card < 30)) = true := by decide
  have h_mem : x ∈ ((List.range 960).map (· + 720)) := by
    rw [List.mem_map]
    use x - 720
    constructor
    · rw [List.mem_range]; omega
    · omega
  have h_all := List.all_eq_true.mp h_decide x h_mem

  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 30 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow

  by_cases h720 : x = 720
  · subst h720; exact not_mem_a081512_30_720 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h840 : x = 840
  · subst h840; exact not_mem_a081512_30_840 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1008 : x = 1008
  · subst h1008; exact not_mem_a081512_30_1008 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1080 : x = 1080
  · subst h1080; exact not_mem_a081512_30_1080 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1200 : x = 1200
  · subst h1200; exact not_mem_a081512_30_1200 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1260 : x = 1260
  · subst h1260; exact not_mem_a081512_30_1260 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1320 : x = 1320
  · subst h1320; exact not_mem_a081512_30_1320 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1440 : x = 1440
  · subst h1440; exact not_mem_a081512_30_1440 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1512 : x = 1512
  · subst h1512; exact not_mem_a081512_30_1512 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1560 : x = 1560
  · subst h1560; exact not_mem_a081512_30_1560 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1584 : x = 1584
  · subst h1584; exact not_mem_a081512_30_1584 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1620 : x = 1620
  · subst h1620; exact not_mem_a081512_30_1620 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  have h_not_cond : ¬ (x = 720 ∨ x = 840 ∨ x = 1008 ∨ x = 1080 ∨ x = 1200 ∨ x = 1260 ∨ x = 1320 ∨ x = 1440 ∨ x = 1512 ∨ x = 1560 ∨ x = 1584 ∨ x = 1620) := by
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)

    · exact h720 rfl

    · exact h840 rfl

    · exact h1008 rfl

    · exact h1080 rfl

    · exact h1200 rfl

    · exact h1260 rfl

    · exact h1320 rfl

    · exact h1440 rfl

    · exact h1512 rfl

    · exact h1560 rfl

    · exact h1584 rfl

    · exact h1620 rfl

  have h_card : (Nat.divisors x).card < 30 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 720 ∨ x = 840 ∨ x = 1008 ∨ x = 1080 ∨ x = 1200 ∨ x = 1260 ∨ x = 1320 ∨ x = 1440 ∨ x = 1512 ∨ x = 1560 ∨ x = 1584 ∨ x = 1620
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega


theorem a_thirty_le_a081512_thirty : a 30 ≤ a081512 30 := by
  unfold a a081512
  change sInf (a_candidates 30) ≤ sInf (a081512_candidates 30)
  have hB : (a081512_candidates 30).Nonempty := ⟨1680, thirty_mem_a081512_thirty⟩
  have hB_ge : 1680 ≤ sInf (a081512_candidates 30) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_30_ge (sInf (a081512_candidates 30)) hmem
  have hA_le : sInf (a_candidates 30) ≤ 1680 := Nat.sInf_le thirty_mem_a_thirty
  exact le_trans hA_le hB_ge


theorem thirtyone_mem_a_thirtyone : 1680 ∈ a_candidates 31 := by
  rw [mem_a_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 16, 20, 21, 24, 28, 30, 35, 40, 42, 48, 56, 60, 70, 80, 105, 120, 168, 210, 420}
  refine ⟨by decide, by decide, by decide, by decide⟩


theorem thirtyone_mem_a081512_thirtyone : 1680 ∈ a081512_candidates 31 := by
  rw [mem_a081512_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 16, 20, 21, 24, 28, 30, 35, 40, 42, 48, 56, 60, 70, 80, 105, 120, 168, 210, 420}
  refine ⟨by decide, by decide, by decide⟩


lemma not_mem_a081512_31_840 : 840 ∉ a081512_candidates 31 := by
  have h_div : (Nat.divisors 840).card = 32 := by decide
  by_cases h_le : k ≤ 32
  · have h_sum : (Nat.divisors 840).sum id = 2880 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 840).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_a081512_31_1080 : 1080 ∉ a081512_candidates 31 := by
  have h_div : (Nat.divisors 1080).card = 32 := by decide
  by_cases h_le : k ≤ 32
  · have h_sum : (Nat.divisors 1080).sum id = 3600 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 1080).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_1260_D_630 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 1260) (hD_card : D.card ≥ 31) (hD_sum : D.sum id = 1260)
    : 630 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 630).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 630).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 630).sum id > 630 := by
    let S_rem := (Nat.divisors 1260) \ ({1260} ∪ {630})
    have hD_erase_sub : D.erase 630 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 630 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 34 := by decide
    have hS_rem_sum : S_rem.sum id = 2478 := by decide
    let C_rem := S_rem \ (D.erase 630)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 630) ∩ S_rem = D.erase 630 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 4 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 1197 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 4 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 1197)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 1197)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 1197 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 630).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_1260_D_420 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 1260) (hD_card : D.card ≥ 30) (hD_sum : D.sum id = 630)
    (h_630 : 630 ∉ D)
    : 420 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 420).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 420).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 420).sum id > 210 := by
    let S_rem := (Nat.divisors 1260) \ ({1260} ∪ {630} ∪ {420})
    have hD_erase_sub : D.erase 420 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 420 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_630 (Finset.mem_of_mem_erase hy)
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 33 := by decide
    have hS_rem_sum : S_rem.sum id = 2058 := by decide
    let C_rem := S_rem \ (D.erase 420)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 420) ∩ S_rem = D.erase 420 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 4 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 957 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 4 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 957)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 957)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 957 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 420).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_a081512_31_1260 : 1260 ∉ a081512_candidates 31 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_not_1260 : 1260 ∉ D := not_mem_s_in_D (by omega) hD_pow (by omega) hD_sum
  have h_not_630 : 630 ∉ D := not_mem_1260_D_630 hD_pow (by omega) hD_sum 
  have h_not_420 : 420 ∉ D := not_mem_1260_D_420 hD_pow (by omega) hD_sum h_not_630
  let S_final := (Nat.divisors 1260) \ ({1260} ∪ {630} ∪ {420})
  have hD_sub_S : D ⊆ S_final := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨hD_pow hx, ?_⟩
    simp only [Finset.mem_union, Finset.mem_singleton]
    push_neg
    refine ⟨?_, ?_⟩
    · rintro rfl; exact h_not_1260 hx
    · rintro pe_mem; rcases pe_mem with pe_eq
      · subst pe_eq; exact h_not_630 hx
      · subst pe_eq; exact h_not_420 hx
  let C_final := S_final \ D
  have hC_sub : C_final ⊆ S_final := Finset.sdiff_subset
  have h_inter : D ∩ S_final = D := Finset.inter_eq_self_of_subset hD_sub_S
  have hC_card : C_final.card = 2 := by
    dsimp [C_final]
    rw [Finset.card_sdiff]
    rw [h_inter, hD_card]
    omega
  have hS_card : S_final.card = 33 := by decide
  have hS_sum : S_final.sum id = 2058 := by decide
  have h_sum_add : C_final.sum id + D.sum id = S_final.sum id := Finset.sum_sdiff hD_sub_S
  have hC_sum : C_final.sum id = 798 := by omega
  have hC_mem : C_final ∈ S_final.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    exact ⟨hC_sub, hC_card⟩
  have h_filt : C_final ∈ (S_final.powersetCard 2).filter (fun t => t.sum id = 798) := by
    rw [Finset.mem_filter]
    exact ⟨hC_mem, hC_sum⟩
  have h_empty : (S_final.powersetCard 2).filter (fun t => t.sum id = 798) = ∅ := by decide
  rw [h_empty] at h_filt
  exact Finset.not_mem_empty C_final h_filt

lemma not_mem_a081512_31_1320 : 1320 ∉ a081512_candidates 31 := by
  have h_div : (Nat.divisors 1320).card = 32 := by decide
  by_cases h_le : k ≤ 32
  · have h_sum : (Nat.divisors 1320).sum id = 4320 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 1320).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_1440_D_720 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 1440) (hD_card : D.card ≥ 31) (hD_sum : D.sum id = 1440)
    : 720 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 720).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 720).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 720).sum id > 720 := by
    let S_rem := (Nat.divisors 1440) \ ({1440} ∪ {720})
    have hD_erase_sub : D.erase 720 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 720 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 34 := by decide
    have hS_rem_sum : S_rem.sum id = 2754 := by decide
    let C_rem := S_rem \ (D.erase 720)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 720) ∩ S_rem = D.erase 720 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 4 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 1368 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 4 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 1368)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 1368)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 1368 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 720).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_1440_D_480 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 1440) (hD_card : D.card ≥ 30) (hD_sum : D.sum id = 720)
    (h_720 : 720 ∉ D)
    : 480 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 480).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 480).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 480).sum id > 240 := by
    let S_rem := (Nat.divisors 1440) \ ({1440} ∪ {720} ∪ {480})
    have hD_erase_sub : D.erase 480 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 480 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_720 (Finset.mem_of_mem_erase hy)
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 33 := by decide
    have hS_rem_sum : S_rem.sum id = 2274 := by decide
    let C_rem := S_rem \ (D.erase 480)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 480) ∩ S_rem = D.erase 480 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 4 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 1068 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 4 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 1068)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 4).filter (fun t => ¬ (t.sum id ≤ 1068)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 1068 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 480).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_a081512_31_1440 : 1440 ∉ a081512_candidates 31 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_not_1440 : 1440 ∉ D := not_mem_s_in_D (by omega) hD_pow (by omega) hD_sum
  have h_not_720 : 720 ∉ D := not_mem_1440_D_720 hD_pow (by omega) hD_sum 
  have h_not_480 : 480 ∉ D := not_mem_1440_D_480 hD_pow (by omega) hD_sum h_not_720
  let S_final := (Nat.divisors 1440) \ ({1440} ∪ {720} ∪ {480})
  have hD_sub_S : D ⊆ S_final := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨hD_pow hx, ?_⟩
    simp only [Finset.mem_union, Finset.mem_singleton]
    push_neg
    refine ⟨?_, ?_⟩
    · rintro rfl; exact h_not_1440 hx
    · rintro pe_mem; rcases pe_mem with pe_eq
      · subst pe_eq; exact h_not_720 hx
      · subst pe_eq; exact h_not_480 hx
  let C_final := S_final \ D
  have hC_sub : C_final ⊆ S_final := Finset.sdiff_subset
  have h_inter : D ∩ S_final = D := Finset.inter_eq_self_of_subset hD_sub_S
  have hC_card : C_final.card = 2 := by
    dsimp [C_final]
    rw [Finset.card_sdiff]
    rw [h_inter, hD_card]
    omega
  have hS_card : S_final.card = 33 := by decide
  have hS_sum : S_final.sum id = 2274 := by decide
  have h_sum_add : C_final.sum id + D.sum id = S_final.sum id := Finset.sum_sdiff hD_sub_S
  have hC_sum : C_final.sum id = 834 := by omega
  have hC_mem : C_final ∈ S_final.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    exact ⟨hC_sub, hC_card⟩
  have h_filt : C_final ∈ (S_final.powersetCard 2).filter (fun t => t.sum id = 834) := by
    rw [Finset.mem_filter]
    exact ⟨hC_mem, hC_sum⟩
  have h_empty : (S_final.powersetCard 2).filter (fun t => t.sum id = 834) = ∅ := by decide
  rw [h_empty] at h_filt
  exact Finset.not_mem_empty C_final h_filt

lemma not_mem_a081512_31_1512 : 1512 ∉ a081512_candidates 31 := by
  have h_div : (Nat.divisors 1512).card = 32 := by decide
  by_cases h_le : k ≤ 32
  · have h_sum : (Nat.divisors 1512).sum id = 4800 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 1512).card := Finset.card_le_card hD_sub
    omega


lemma not_mem_a081512_31_1560 : 1560 ∉ a081512_candidates 31 := by
  have h_div : (Nat.divisors 1560).card = 32 := by decide
  by_cases h_le : k ≤ 32
  · have h_sum : (Nat.divisors 1560).sum id = 5040 := by decide
    apply not_mem_a081512_of_sum_gt (by omega) (by omega)
    omega
  · intro hc
    rw [mem_a081512_candidates_iff] at hc
    rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
    rw [Finset.mem_powerset] at hD_sub
    have : D.card ≤ (Nat.divisors 1560).card := Finset.card_le_card hD_sub
    omega


theorem a081512_candidates_31_ge (x : ℕ) (hx : x ∈ a081512_candidates 31) : 1680 ≤ x := by
  by_contra! h
  have hk21 : 31 ≥ 21 := by omega
  have hx720 : 720 ≤ x := a081512_candidates_ge_twentyone_ge_720 31 hk21 x hx

  have h_decide : ((List.range 960).map (· + 720)).all (fun y =>
      decide (if y = 840 ∨ y = 1080 ∨ y = 1260 ∨ y = 1320 ∨ y = 1440 ∨ y = 1512 ∨ y = 1560 then True
              else (Nat.divisors y).card < 31)) = true := by decide
  have h_mem : x ∈ ((List.range 960).map (· + 720)) := by
    rw [List.mem_map]
    use x - 720
    constructor
    · rw [List.mem_range]; omega
    · omega
  have h_all := List.all_eq_true.mp h_decide x h_mem

  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 31 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow

  by_cases h840 : x = 840
  · subst h840; exact not_mem_a081512_31_840 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1080 : x = 1080
  · subst h1080; exact not_mem_a081512_31_1080 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1260 : x = 1260
  · subst h1260; exact not_mem_a081512_31_1260 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1320 : x = 1320
  · subst h1320; exact not_mem_a081512_31_1320 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1440 : x = 1440
  · subst h1440; exact not_mem_a081512_31_1440 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1512 : x = 1512
  · subst h1512; exact not_mem_a081512_31_1512 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1560 : x = 1560
  · subst h1560; exact not_mem_a081512_31_1560 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  have h_not_cond : ¬ (x = 840 ∨ x = 1080 ∨ x = 1260 ∨ x = 1320 ∨ x = 1440 ∨ x = 1512 ∨ x = 1560) := by
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)

    · exact h840 rfl

    · exact h1080 rfl

    · exact h1260 rfl

    · exact h1320 rfl

    · exact h1440 rfl

    · exact h1512 rfl

    · exact h1560 rfl

  have h_card : (Nat.divisors x).card < 31 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 840 ∨ x = 1080 ∨ x = 1260 ∨ x = 1320 ∨ x = 1440 ∨ x = 1512 ∨ x = 1560
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega


theorem a_thirtyone_le_a081512_thirtyone : a 31 ≤ a081512 31 := by
  unfold a a081512
  change sInf (a_candidates 31) ≤ sInf (a081512_candidates 31)
  have hB : (a081512_candidates 31).Nonempty := ⟨1680, thirtyone_mem_a081512_thirtyone⟩
  have hB_ge : 1680 ≤ sInf (a081512_candidates 31) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_31_ge (sInf (a081512_candidates 31)) hmem
  have hA_le : sInf (a_candidates 31) ≤ 1680 := Nat.sInf_le thirtyone_mem_a_thirtyone
  exact le_trans hA_le hB_ge


theorem thirtytwo_mem_a_thirtytwo : 1680 ∈ a_candidates 32 := by
  rw [mem_a_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 16, 20, 21, 24, 28, 30, 35, 40, 42, 48, 56, 60, 70, 80, 84, 105, 120, 168, 210, 336}
  refine ⟨by decide, by decide, by decide, by decide⟩


theorem thirtytwo_mem_a081512_thirtytwo : 1680 ∈ a081512_candidates 32 := by
  rw [mem_a081512_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 16, 20, 21, 24, 28, 30, 35, 40, 42, 48, 56, 60, 70, 80, 84, 105, 120, 168, 210, 336}
  refine ⟨by decide, by decide, by decide⟩


lemma not_mem_a081512_32_840 : 840 ∉ a081512_candidates 32 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_eq : D = Nat.divisors 840 := Finset.eq_of_subset_of_card_le hD_pow (by omega)
  subst h_eq
  have h_sum_divs : (Nat.divisors 840).sum id = 2880 := by decide
  omega


lemma not_mem_a081512_32_1080 : 1080 ∉ a081512_candidates 32 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_eq : D = Nat.divisors 1080 := Finset.eq_of_subset_of_card_le hD_pow (by omega)
  subst h_eq
  have h_sum_divs : (Nat.divisors 1080).sum id = 3600 := by decide
  omega


lemma not_mem_1260_D_630 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 1260) (hD_card : D.card ≥ 32) (hD_sum : D.sum id = 1260)
    : 630 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 630).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 630).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 630).sum id > 630 := by
    let S_rem := (Nat.divisors 1260) \ ({1260} ∪ {630})
    have hD_erase_sub : D.erase 630 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 630 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 34 := by decide
    have hS_rem_sum : S_rem.sum id = 2478 := by decide
    let C_rem := S_rem \ (D.erase 630)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 630) ∩ S_rem = D.erase 630 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 3 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 987 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 3 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 3).filter (fun t => ¬ (t.sum id ≤ 987)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 3).filter (fun t => ¬ (t.sum id ≤ 987)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 987 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 630).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_a081512_32_1260 : 1260 ∉ a081512_candidates 32 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_not_1260 : 1260 ∉ D := not_mem_s_in_D (by omega) hD_pow (by omega) hD_sum
  have h_not_630 : 630 ∉ D := not_mem_1260_D_630 hD_pow (by omega) hD_sum 
  let S_final := (Nat.divisors 1260) \ ({1260} ∪ {630})
  have hD_sub_S : D ⊆ S_final := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨hD_pow hx, ?_⟩
    simp only [Finset.mem_union, Finset.mem_singleton]
    push_neg
    refine ⟨?_, ?_⟩
    · rintro rfl; exact h_not_1260 hx
    · rintro pe_mem; rcases pe_mem with pe_eq
      · subst pe_eq; exact h_not_630 hx
  let C_final := S_final \ D
  have hC_sub : C_final ⊆ S_final := Finset.sdiff_subset
  have h_inter : D ∩ S_final = D := Finset.inter_eq_self_of_subset hD_sub_S
  have hC_card : C_final.card = 2 := by
    dsimp [C_final]
    rw [Finset.card_sdiff]
    rw [h_inter, hD_card]
    omega
  have hS_card : S_final.card = 34 := by decide
  have hS_sum : S_final.sum id = 2478 := by decide
  have h_sum_add : C_final.sum id + D.sum id = S_final.sum id := Finset.sum_sdiff hD_sub_S
  have hC_sum : C_final.sum id = 1218 := by omega
  have hC_mem : C_final ∈ S_final.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    exact ⟨hC_sub, hC_card⟩
  have h_filt : C_final ∈ (S_final.powersetCard 2).filter (fun t => t.sum id = 1218) := by
    rw [Finset.mem_filter]
    exact ⟨hC_mem, hC_sum⟩
  have h_empty : (S_final.powersetCard 2).filter (fun t => t.sum id = 1218) = ∅ := by decide
  rw [h_empty] at h_filt
  exact Finset.not_mem_empty C_final h_filt

lemma not_mem_a081512_32_1320 : 1320 ∉ a081512_candidates 32 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_eq : D = Nat.divisors 1320 := Finset.eq_of_subset_of_card_le hD_pow (by omega)
  subst h_eq
  have h_sum_divs : (Nat.divisors 1320).sum id = 4320 := by decide
  omega


lemma not_mem_1440_D_720 {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors 1440) (hD_card : D.card ≥ 32) (hD_sum : D.sum id = 1440)
    : 720 ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase 720).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase 720).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase 720).sum id > 720 := by
    let S_rem := (Nat.divisors 1440) \ ({1440} ∪ {720})
    have hD_erase_sub : D.erase 720 ⊆ S_rem := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨hD_pow (Finset.mem_of_mem_erase hy), ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_⟩
      · intro hc_eq; subst hc_eq; exact Finset.not_mem_erase 720 D hy
      · rintro pe_mem; rcases pe_mem with pe_eq
        · subst pe_eq; exact h_mem
    have hS_rem_card : S_rem.card = 34 := by decide
    have hS_rem_sum : S_rem.sum id = 2754 := by decide
    let C_rem := S_rem \ (D.erase 720)
    have hC_rem_sub : C_rem ⊆ S_rem := Finset.sdiff_subset
    have h_inter : (D.erase 720) ∩ S_rem = D.erase 720 := Finset.inter_eq_self_of_subset hD_erase_sub
    have hC_rem_card : C_rem.card = 3 := by
      dsimp [C_rem]
      rw [Finset.card_sdiff]
      rw [h_inter, hD_erase_card]
      omega
    have hC_rem_sum_le : C_rem.sum id ≤ 1128 := by
      have h_mem_pow : C_rem ∈ S_rem.powersetCard 3 := by
        rw [Finset.mem_powersetCard]
        exact ⟨hC_rem_sub, hC_rem_card⟩
      have h_all : (S_rem.powersetCard 3).filter (fun t => ¬ (t.sum id ≤ 1128)) = ∅ := by decide
      have h_mem_filter : C_rem ∉ (S_rem.powersetCard 3).filter (fun t => ¬ (t.sum id ≤ 1128)) := by rw [h_all]; simp
      have h_all_eq : C_rem.sum id ≤ 1128 := by
        by_contra! h_not
        apply h_mem_filter
        rw [Finset.mem_filter]
        exact ⟨h_mem_pow, h_not⟩
      exact h_all_eq
    have h_sum_add_rem : C_rem.sum id + (D.erase 720).sum id = S_rem.sum id := Finset.sum_sdiff hD_erase_sub
    omega
  omega


lemma not_mem_a081512_32_1440 : 1440 ∉ a081512_candidates 32 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_not_1440 : 1440 ∉ D := not_mem_s_in_D (by omega) hD_pow (by omega) hD_sum
  have h_not_720 : 720 ∉ D := not_mem_1440_D_720 hD_pow (by omega) hD_sum 
  let S_final := (Nat.divisors 1440) \ ({1440} ∪ {720})
  have hD_sub_S : D ⊆ S_final := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨hD_pow hx, ?_⟩
    simp only [Finset.mem_union, Finset.mem_singleton]
    push_neg
    refine ⟨?_, ?_⟩
    · rintro rfl; exact h_not_1440 hx
    · rintro pe_mem; rcases pe_mem with pe_eq
      · subst pe_eq; exact h_not_720 hx
  let C_final := S_final \ D
  have hC_sub : C_final ⊆ S_final := Finset.sdiff_subset
  have h_inter : D ∩ S_final = D := Finset.inter_eq_self_of_subset hD_sub_S
  have hC_card : C_final.card = 2 := by
    dsimp [C_final]
    rw [Finset.card_sdiff]
    rw [h_inter, hD_card]
    omega
  have hS_card : S_final.card = 34 := by decide
  have hS_sum : S_final.sum id = 2754 := by decide
  have h_sum_add : C_final.sum id + D.sum id = S_final.sum id := Finset.sum_sdiff hD_sub_S
  have hC_sum : C_final.sum id = 1314 := by omega
  have hC_mem : C_final ∈ S_final.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    exact ⟨hC_sub, hC_card⟩
  have h_filt : C_final ∈ (S_final.powersetCard 2).filter (fun t => t.sum id = 1314) := by
    rw [Finset.mem_filter]
    exact ⟨hC_mem, hC_sum⟩
  have h_empty : (S_final.powersetCard 2).filter (fun t => t.sum id = 1314) = ∅ := by decide
  rw [h_empty] at h_filt
  exact Finset.not_mem_empty C_final h_filt

lemma not_mem_a081512_32_1512 : 1512 ∉ a081512_candidates 32 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_eq : D = Nat.divisors 1512 := Finset.eq_of_subset_of_card_le hD_pow (by omega)
  subst h_eq
  have h_sum_divs : (Nat.divisors 1512).sum id = 4800 := by decide
  omega


lemma not_mem_a081512_32_1560 : 1560 ∉ a081512_candidates 32 := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨_, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_eq : D = Nat.divisors 1560 := Finset.eq_of_subset_of_card_le hD_pow (by omega)
  subst h_eq
  have h_sum_divs : (Nat.divisors 1560).sum id = 5040 := by decide
  omega


theorem a081512_candidates_32_ge (x : ℕ) (hx : x ∈ a081512_candidates 32) : 1680 ≤ x := by
  by_contra! h
  have hk21 : 32 ≥ 21 := by omega
  have hx720 : 720 ≤ x := a081512_candidates_ge_twentyone_ge_720 32 hk21 x hx

  have h_decide : ((List.range 960).map (· + 720)).all (fun y =>
      decide (if y = 840 ∨ y = 1080 ∨ y = 1260 ∨ y = 1320 ∨ y = 1440 ∨ y = 1512 ∨ y = 1560 then True
              else (Nat.divisors y).card < 32)) = true := by decide
  have h_mem : x ∈ ((List.range 960).map (· + 720)) := by
    rw [List.mem_map]
    use x - 720
    constructor
    · rw [List.mem_range]; omega
    · omega
  have h_all := List.all_eq_true.mp h_decide x h_mem

  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 32 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow

  by_cases h840 : x = 840
  · subst h840; exact not_mem_a081512_32_840 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1080 : x = 1080
  · subst h1080; exact not_mem_a081512_32_1080 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1260 : x = 1260
  · subst h1260; exact not_mem_a081512_32_1260 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1320 : x = 1320
  · subst h1320; exact not_mem_a081512_32_1320 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1440 : x = 1440
  · subst h1440; exact not_mem_a081512_32_1440 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1512 : x = 1512
  · subst h1512; exact not_mem_a081512_32_1512 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  by_cases h1560 : x = 1560
  · subst h1560; exact not_mem_a081512_32_1560 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩

  have h_not_cond : ¬ (x = 840 ∨ x = 1080 ∨ x = 1260 ∨ x = 1320 ∨ x = 1440 ∨ x = 1512 ∨ x = 1560) := by
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)

    · exact h840 rfl

    · exact h1080 rfl

    · exact h1260 rfl

    · exact h1320 rfl

    · exact h1440 rfl

    · exact h1512 rfl

    · exact h1560 rfl

  have h_card : (Nat.divisors x).card < 32 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 840 ∨ x = 1080 ∨ x = 1260 ∨ x = 1320 ∨ x = 1440 ∨ x = 1512 ∨ x = 1560
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega


theorem a_thirtytwo_le_a081512_thirtytwo : a 32 ≤ a081512 32 := by
  unfold a a081512
  change sInf (a_candidates 32) ≤ sInf (a081512_candidates 32)
  have hB : (a081512_candidates 32).Nonempty := ⟨1680, thirtytwo_mem_a081512_thirtytwo⟩
  have hB_ge : 1680 ≤ sInf (a081512_candidates 32) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_32_ge (sInf (a081512_candidates 32)) hmem
  have hA_le : sInf (a_candidates 32) ≤ 1680 := Nat.sInf_le thirtytwo_mem_a_thirtytwo
  exact le_trans hA_le hB_ge




-- Heavy Helper Lemmas relocated from Defs.lean --


lemma seven_twenty_mem_special : 720 ∈ a_candidates_special 21 := by
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 30, 36, 45, 72, 144, 240}
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

lemma seven_twenty_mul_pow_two_mem_special_helper (d : ℕ) :
    720 * 2^d ∈ a_candidates_special (d + 21) := by
  induction d with
  | zero =>
    exact seven_twenty_mem_special
  | succ d ih =>
    have h_div : 4 ∣ 720 * 2^d := by
      use 180 * 2^d
      ring
    have h_step := special_step (n := d + 15) ih h_div
    have h_eq : 2 * (720 * 2^d) = 720 * 2^(d + 1) := by
      ring
    have h_card : d + 15 + 7 = d + 1 + 21 := by omega
    rw [h_eq] at h_step
    rw [h_card] at h_step
    exact h_step


lemma a081512_candidates_step {k m : ℕ} (hm : m ∈ a081512_candidates k) (hk : k ≥ 2) :
    4 * m ∈ a081512_candidates (k + 1) := by
  rw [mem_a081512_candidates_iff] at hm
  rcases hm with ⟨hm0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  rw [mem_a081512_candidates_iff]
  simp_rw [Finset.mem_powerset]
  refine ⟨by omega, ?_⟩
  let f : ℕ ↪ ℕ := ⟨fun x => 2 * x, fun x y h => by dsimp at h; omega⟩
  let D' := D.map f
  have h_2m_not_mem : 2 * m ∉ D' := by
    intro hc
    rw [Finset.mem_map] at hc
    rcases hc with ⟨d, hd, h_eq⟩
    dsimp [f] at h_eq
    have h_dm : d = m := by omega
    have hd_lt_m : ∀ x ∈ D, x < m := by
      intro x hx
      have h_div_x : x ∈ Nat.divisors m := hD_pow hx
      have h_le_m : x ≤ m := Nat.le_of_dvd hm0 (Nat.dvd_of_mem_divisors h_div_x)
      have h_ne_m : x ≠ m := by
        intro hc_eq
        have hx_m : m ∈ D := hc_eq.symm ▸ hx
        have h_sum_gt : D.sum id > m := by
          have hD_pos : ∀ y ∈ D, 0 < y := by
            intro y hy
            exact Nat.pos_of_mem_divisors (hD_pow hy)
          have h_sum_erase : D.sum id = m + (D.erase m).sum id := by
            have h_sum := D.sum_erase_add id hx_m
            simp only [id_eq] at h_sum ⊢
            omega
          have hD_erase_ne : (D.erase m).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hc_empty
            have h_card_erase : #(D.erase m) = k - 1 := by
              rw [Finset.card_erase_of_mem hx_m, hD_card]
            rw [hc_empty, Finset.card_empty] at h_card_erase
            omega
          rcases hD_erase_ne with ⟨y, hy⟩
          have hy_pos : y > 0 := hD_pos y (Finset.mem_of_mem_erase hy)
          have h_sum_erase_pos : (D.erase m).sum id > 0 := by
            apply Finset.sum_pos
            · intro x hx
              have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
              exact hD_pos x hx_D
            · exact ⟨y, hy⟩
          simp only [id_eq] at h_sum_erase h_sum_erase_pos ⊢
          omega
        simp only [id_eq] at hD_sum h_sum_gt
        omega
      omega
    have h_lt : d < m := hd_lt_m d hd
    omega

  let D_new := insert (2 * m) D'
  use D_new
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · rw [Nat.mem_divisors]
      refine ⟨⟨2, by omega⟩, by omega⟩
    · rw [Finset.mem_map] at hx
      rcases hx with ⟨d, hd, rfl⟩
      dsimp [f]
      rw [Nat.mem_divisors]
      have hd_div : d ∣ m := Nat.dvd_of_mem_divisors (hD_pow hd)
      rcases hd_div with ⟨c, rfl⟩
      refine ⟨⟨2 * c, by ring⟩, by omega⟩
  · rw [Finset.card_insert_of_notMem h_2m_not_mem]
    rw [Finset.card_map, hD_card]
  · rw [Finset.sum_insert h_2m_not_mem]
    simp only [id_eq]
    rw [Finset.sum_map]
    dsimp [f]
    have h_sum_map : (D.sum fun x => 2 * x) = 2 * D.sum id := by
      rw [← Finset.mul_sum]
      rfl
    rw [h_sum_map, hD_sum]
    omega

lemma a081512_candidates_nonempty (n : ℕ) : (a081512_candidates (n + 6)).Nonempty := by
  induction n with
  | zero =>
    exact ⟨24, twentyfour_mem_a081512_six⟩
  | succ n ih =>
    rcases ih with ⟨m, hm⟩
    have hm_step := a081512_candidates_step hm (by omega)
    exact ⟨4 * m, hm_step⟩




lemma not_mem_a081512_ge_32_840 (k : ℕ) (hk : k ≥ 32) : 840 ∉ a081512_candidates k := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨hc0, D, hD_sub, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_sub
  have h_div_card : (Nat.divisors 840).card = 32 := by decide
  have h_card_le : D.card ≤ (Nat.divisors 840).card := Finset.card_le_card hD_sub
  have h_eq : k = 32 := by omega
  subst h_eq
  exact not_mem_a081512_32_840 ⟨hc0, D, hD_sub, hD_card, hD_sum⟩

lemma not_mem_a081512_ge_32_1080 (k : ℕ) (hk : k ≥ 32) : 1080 ∉ a081512_candidates k := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨hc0, D, hD_sub, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_sub
  have h_div_card : (Nat.divisors 1080).card = 32 := by decide
  have h_card_le : D.card ≤ (Nat.divisors 1080).card := Finset.card_le_card hD_sub
  have h_eq : k = 32 := by omega
  subst h_eq
  exact not_mem_a081512_32_1080 ⟨hc0, D, hD_sub, hD_card, hD_sum⟩

lemma not_mem_a081512_ge_32_1320 (k : ℕ) (hk : k ≥ 32) : 1320 ∉ a081512_candidates k := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨hc0, D, hD_sub, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_sub
  have h_div_card : (Nat.divisors 1320).card = 32 := by decide
  have h_card_le : D.card ≤ (Nat.divisors 1320).card := Finset.card_le_card hD_sub
  have h_eq : k = 32 := by omega
  subst h_eq
  exact not_mem_a081512_32_1320 ⟨hc0, D, hD_sub, hD_card, hD_sum⟩

lemma not_mem_a081512_ge_32_1512 (k : ℕ) (hk : k ≥ 32) : 1512 ∉ a081512_candidates k := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨hc0, D, hD_sub, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_sub
  have h_div_card : (Nat.divisors 1512).card = 32 := by decide
  have h_card_le : D.card ≤ (Nat.divisors 1512).card := Finset.card_le_card hD_sub
  have h_eq : k = 32 := by omega
  subst h_eq
  exact not_mem_a081512_32_1512 ⟨hc0, D, hD_sub, hD_card, hD_sum⟩

lemma not_mem_a081512_ge_32_1560 (k : ℕ) (hk : k ≥ 32) : 1560 ∉ a081512_candidates k := by
  intro hc
  rw [mem_a081512_candidates_iff] at hc
  rcases hc with ⟨hc0, D, hD_sub, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_sub
  have h_div_card : (Nat.divisors 1560).card = 32 := by decide
  have h_card_le : D.card ≤ (Nat.divisors 1560).card := Finset.card_le_card hD_sub
  have h_eq : k = 32 := by omega
  subst h_eq
  exact not_mem_a081512_32_1560 ⟨hc0, D, hD_sub, hD_card, hD_sum⟩

lemma not_mem_a081512_ge_32_1260 (k : ℕ) (hk : k ≥ 32) : 1260 ∉ a081512_candidates k := by
  by_cases hk32 : k = 32
  · subst hk32; exact not_mem_a081512_32_1260
  · have hk33 : k ≥ 33 := by omega
    have h_div : (Nat.divisors 1260).card = 36 := by decide
    by_cases h_le : k ≤ 36
    · have h_sum : (Nat.divisors 1260).sum id = 4368 := by decide
      apply not_mem_a081512_of_sum_gt (by omega) (by omega) (by omega)
      omega
    · intro hc
      rw [mem_a081512_candidates_iff] at hc
      rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
      rw [Finset.mem_powerset] at hD_sub
      have : D.card ≤ (Nat.divisors 1260).card := Finset.card_le_card hD_sub
      omega

lemma not_mem_a081512_ge_32_1440 (k : ℕ) (hk : k ≥ 32) : 1440 ∉ a081512_candidates k := by
  by_cases hk32 : k = 32
  · subst hk32; exact not_mem_a081512_32_1440
  · have hk33 : k ≥ 33 := by omega
    have h_div : (Nat.divisors 1440).card = 36 := by decide
    by_cases h_le : k ≤ 36
    · have h_sum : (Nat.divisors 1440).sum id = 4920 := by decide
      apply not_mem_a081512_of_sum_gt (by omega) (by omega) (by omega)
      omega
    · intro hc
      rw [mem_a081512_candidates_iff] at hc
      rcases hc with ⟨_, D, hD_sub, hD_card, _⟩
      rw [Finset.mem_powerset] at hD_sub
      have : D.card ≤ (Nat.divisors 1440).card := Finset.card_le_card hD_sub
      omega

theorem a081512_candidates_ge_thirtytwo_ge_1680 (k : ℕ) (hk : k ≥ 32) (x : ℕ) (hx : x ∈ a081512_candidates k) : 1680 ≤ x := by
  have hx720 : 720 ≤ x := a081512_candidates_ge_twentyone_ge_720 k (by omega) x hx
  by_contra! h
  have h_decide : ((List.range 960).map (· + 720)).all (fun y =>
      decide (if y = 840 ∨ y = 1080 ∨ y = 1260 ∨ y = 1320 ∨ y = 1440 ∨ y = 1512 ∨ y = 1560 then True
              else (Nat.divisors y).card < 32)) = true := by decide
  have h_mem : x ∈ ((List.range 960).map (· + 720)) := by
    rw [List.mem_map]
    use x - 720
    constructor
    · rw [List.mem_range]; omega
    · omega
  have h_all := List.all_eq_true.mp h_decide x h_mem
  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : k ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow
  by_cases h840 : x = 840
  · subst h840; exact not_mem_a081512_ge_32_840 k hk ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h1080 : x = 1080
  · subst h1080; exact not_mem_a081512_ge_32_1080 k hk ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h1260 : x = 1260
  · subst h1260; exact not_mem_a081512_ge_32_1260 k hk ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h1320 : x = 1320
  · subst h1320; exact not_mem_a081512_ge_32_1320 k hk ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h1440 : x = 1440
  · subst h1440; exact not_mem_a081512_ge_32_1440 k hk ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h1512 : x = 1512
  · subst h1512; exact not_mem_a081512_ge_32_1512 k hk ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h1560 : x = 1560
  · subst h1560; exact not_mem_a081512_ge_32_1560 k hk ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  have h_not_cond : ¬ (x = 840 ∨ x = 1080 ∨ x = 1260 ∨ x = 1320 ∨ x = 1440 ∨ x = 1512 ∨ x = 1560) := by
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact h840 rfl
    · exact h1080 rfl
    · exact h1260 rfl
    · exact h1320 rfl
    · exact h1440 rfl
    · exact h1512 rfl
    · exact h1560 rfl
  have h_card : (Nat.divisors x).card < 32 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 840 ∨ x = 1080 ∨ x = 1260 ∨ x = 1320 ∨ x = 1440 ∨ x = 1512 ∨ x = 1560
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega
