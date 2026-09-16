import Submission.ProofNodupFinal
import Mathlib

theorem sup_add_one {α : Type} [Fintype α] [Nonempty α] (f : α → ℕ) :
  Finset.sup Finset.univ (fun a => f a + 1) = Finset.sup Finset.univ f + 1 := by
  have h_ne : (Finset.univ : Finset α).Nonempty := Finset.univ_nonempty
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    have h : f i ≤ Finset.sup Finset.univ f := Finset.le_sup (Finset.mem_univ i)
    omega
  · have ⟨i, hi, h_sup⟩ := Finset.exists_mem_eq_sup Finset.univ h_ne f
    rw [h_sup]
    apply Finset.le_sup (Finset.mem_univ i)

theorem sup_add_two {α : Type} [Fintype α] [Nonempty α] (f : α → ℕ) :
  Finset.sup Finset.univ (fun a => f a + 2) = Finset.sup Finset.univ f + 2 := by
  have h_ne : (Finset.univ : Finset α).Nonempty := Finset.univ_nonempty
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    have h : f i ≤ Finset.sup Finset.univ f := Finset.le_sup (Finset.mem_univ i)
    omega
  · have ⟨i, hi, h_sup⟩ := Finset.exists_mem_eq_sup Finset.univ h_ne f
    rw [h_sup]
    apply Finset.le_sup (Finset.mem_univ i)

theorem univ_succ (L : ℕ) :
  (Finset.univ : Finset (Fin (L + 1))) = 
  insert (Fin.last L) (Finset.image Fin.castSucc Finset.univ) := by
  ext i
  simp

theorem sup_map1 {L : ℕ} (hL : L > 0) (x : Fin L → ℕ) :
  Finset.sup Finset.univ (map1 x) = Finset.sup Finset.univ x + 1 := by
  rw [univ_succ L]
  rw [Finset.sup_insert]
  have h_last : map1 x (Fin.last L) = 1 := map1_ends_in_1 x
  rw [h_last]
  haveI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  have h_image : Finset.sup (Finset.image Fin.castSucc Finset.univ) (map1 x) = Finset.sup Finset.univ x + 1 := by
    rw [Finset.sup_image]
    have h_comp : (map1 x ∘ Fin.castSucc) = fun i => x i + 1 := by
      ext i
      change map1 x (Fin.castSucc i) = x i + 1
      rw [map1, Fin.snoc_castSucc]
      rfl
    rw [h_comp]
    exact sup_add_one x
  have h_full : max 1 (Finset.sup (Finset.image Fin.castSucc Finset.univ) (map1 x)) = max 1 (Finset.sup Finset.univ x + 1) := by congr 1
  rw [h_full]
  have h_ne : (Finset.univ : Finset (Fin L)).Nonempty := Finset.univ_nonempty
  have ⟨i, hi, h_sup⟩ := Finset.exists_mem_eq_sup Finset.univ h_ne x
  rw [h_sup]
  apply max_eq_right
  omega

def ImageCond {L : ℕ} (x : Fin L → ℕ) : Prop :=
  let max_val := Finset.sup Finset.univ x
  ∀ k, 1 ≤ k ∧ k ≤ max_val → ∃ i, x i = k

theorem image_map1 {L : ℕ} (hL : L > 0) (x : Fin L → ℕ) (hx : ImageCond x) : ImageCond (map1 x) := by
  intro k hk
  have h_sup := sup_map1 hL x
  rw [h_sup] at hk
  by_cases h : k = 1
  · use Fin.last L
    rw [h, map1_ends_in_1]
  · have h_k : 1 ≤ k - 1 ∧ k - 1 ≤ Finset.sup Finset.univ x := by omega
    have ⟨i, hi⟩ := hx (k - 1) h_k
    use Fin.castSucc i
    have ha : map1 x (Fin.castSucc i) = x i + 1 := by
      rw [map1, Fin.snoc_castSucc]
      rfl
    rw [ha]
    omega

theorem sup_map2 {L : ℕ} (x : Fin L → ℕ) (hx : ∃ i, x i = 1) :
  Finset.sup Finset.univ (map2 x) = Finset.sup Finset.univ x := by
  rw [univ_succ L]
  rw [Finset.sup_insert]
  have h_last : map2 x (Fin.last L) = 1 := map2_ends_in_1 x
  rw [h_last]
  have h_image : Finset.sup (Finset.image Fin.castSucc Finset.univ) (map2 x) = Finset.sup Finset.univ x := by
    rw [Finset.sup_image]
    have h_comp : (map2 x ∘ Fin.castSucc) = x := by
      ext i
      change map2 x (Fin.castSucc i) = x i
      rw [map2, Fin.snoc_castSucc]
    rw [h_comp]
  have h_full : max 1 (Finset.sup (Finset.image Fin.castSucc Finset.univ) (map2 x)) = max 1 (Finset.sup Finset.univ x) := by congr 1
  rw [h_full]
  rcases hx with ⟨i, hi⟩
  have h_le : 1 ≤ Finset.sup Finset.univ x := by
    have : x i ≤ Finset.sup Finset.univ x := Finset.le_sup (Finset.mem_univ i)
    omega
  apply max_eq_right h_le

theorem image_map2 {L : ℕ} (x : Fin L → ℕ) (hx1 : ∃ i, x i = 1) (hx : ImageCond x) : ImageCond (map2 x) := by
  intro k hk
  have h_sup := sup_map2 x hx1
  rw [h_sup] at hk
  have ⟨i, hi⟩ := hx k hk
  use Fin.castSucc i
  have ha : map2 x (Fin.castSucc i) = x i := by
    rw [map2, Fin.snoc_castSucc]
  rw [ha, hi]

theorem sup_map3 {L : ℕ} (hL : L > 0) (x : Fin L → ℕ) (hx_pos : ∀ i, x i > 0) :
  Finset.sup Finset.univ (map3 x) = Finset.sup Finset.univ x + 1 := by
  rw [univ_succ (L+1)]
  rw [Finset.sup_insert]
  have h_last : map3 x (Fin.last (L+1)) = 2 := map3_ends_in_2 x
  rw [h_last]
  have h_image : Finset.sup (Finset.image Fin.castSucc Finset.univ) (map3 x) = Finset.sup Finset.univ x + 1 := by
    rw [Finset.sup_image]
    have h_comp : (map3 x ∘ Fin.castSucc) = map1 x := by
      ext i
      change map3 x (Fin.castSucc i) = map1 x i
      rw [map3, map1, Fin.snoc_castSucc]
    rw [h_comp]
    exact sup_map1 hL x
  have h_full : max 2 (Finset.sup (Finset.image Fin.castSucc Finset.univ) (map3 x)) = max 2 (Finset.sup Finset.univ x + 1) := by congr 1
  rw [h_full]
  haveI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  have h_ne : (Finset.univ : Finset (Fin L)).Nonempty := Finset.univ_nonempty
  have ⟨i, hi, h_sup⟩ := Finset.exists_mem_eq_sup Finset.univ h_ne x
  rw [h_sup]
  have : x i ≥ 1 := hx_pos i
  apply max_eq_right
  omega

theorem image_map3 {L : ℕ} (hL : L > 0) (x : Fin L → ℕ) (hx_pos : ∀ i, x i > 0) (hx : ImageCond x) : ImageCond (map3 x) := by
  intro k hk
  have h_sup := sup_map3 hL x hx_pos
  rw [h_sup] at hk
  have h_map1 := image_map1 hL x hx
  have h_k : 1 ≤ k ∧ k ≤ Finset.sup Finset.univ (map1 x) := by
    have hs := sup_map1 hL x
    omega
  have ⟨i, hi⟩ := h_map1 k h_k
  use Fin.castSucc i
  have ha : map3 x (Fin.castSucc i) = map1 x i := by
    rw [map3, map1, Fin.snoc_castSucc]
  rw [ha, hi]

theorem sup_map4 {L : ℕ} (hL : L > 0) (x : Fin L → ℕ) (hx_pos : ∀ i, x i > 0) (hx1 : ∃ i, x i = 1) :
  Finset.sup Finset.univ (map4 x) = Finset.sup Finset.univ x + 2 := by
  rw [univ_succ (L+1)]
  rw [Finset.sup_insert]
  have h_last : map4 x (Fin.last (L+1)) = 2 := map4_ends_in_2 x
  rw [h_last]
  have h_image : Finset.sup (Finset.image Fin.castSucc Finset.univ) (map4 x) = Finset.sup Finset.univ x + 2 := by
    rw [Finset.sup_image]
    have h_comp : (map4 x ∘ Fin.castSucc) = (Fin.snoc (shift_seq x 2) 1 : Fin (L+1) → ℕ) := by
      ext i
      change map4 x (Fin.castSucc i) = (Fin.snoc (shift_seq x 2) 1 : Fin (L+1) → ℕ) i
      rw [map4, Fin.snoc_castSucc]
    rw [h_comp]
    rw [univ_succ L]
    rw [Finset.sup_insert]
    have h_last2 : (Fin.snoc (shift_seq x 2) 1 : Fin (L+1) → ℕ) (Fin.last L) = 1 := Fin.snoc_last _ _
    rw [h_last2]
    have h_image2 : Finset.sup (Finset.image Fin.castSucc Finset.univ) (Fin.snoc (shift_seq x 2) 1 : Fin (L+1) → ℕ) = Finset.sup Finset.univ x + 2 := by
      rw [Finset.sup_image]
      have h_comp2 : ((Fin.snoc (shift_seq x 2) 1 : Fin (L+1) → ℕ) ∘ Fin.castSucc) = fun i => x i + 2 := by
        ext i
        change (Fin.snoc (shift_seq x 2) 1 : Fin (L+1) → ℕ) (Fin.castSucc i) = x i + 2
        rw [Fin.snoc_castSucc]
        rfl
      rw [h_comp2]
      haveI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
      exact sup_add_two x
    have h_full2 : max 1 (Finset.sup (Finset.image Fin.castSucc Finset.univ) (Fin.snoc (shift_seq x 2) 1 : Fin (L+1) → ℕ)) = max 1 (Finset.sup Finset.univ x + 2) := by congr 1
    rw [h_full2]
    haveI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
    have h_ne : (Finset.univ : Finset (Fin L)).Nonempty := Finset.univ_nonempty
    have ⟨i, hi, h_sup⟩ := Finset.exists_mem_eq_sup Finset.univ h_ne x
    rw [h_sup]
    have : x i ≥ 1 := hx_pos i
    apply max_eq_right
    omega
  have h_full : max 2 (Finset.sup (Finset.image Fin.castSucc Finset.univ) (map4 x)) = max 2 (Finset.sup Finset.univ x + 2) := by congr 1
  rw [h_full]
  haveI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  have h_ne : (Finset.univ : Finset (Fin L)).Nonempty := Finset.univ_nonempty
  have ⟨i, hi, h_sup⟩ := Finset.exists_mem_eq_sup Finset.univ h_ne x
  rw [h_sup]
  have : x i ≥ 1 := hx_pos i
  apply max_eq_right
  omega

theorem image_map4 {L : ℕ} (hL : L > 0) (x : Fin L → ℕ) (hx_pos : ∀ i, x i > 0) (hx1 : ∃ i, x i = 1) (hx : ImageCond x) : ImageCond (map4 x) := by
  intro k hk
  have h_sup := sup_map4 hL x hx_pos hx1
  rw [h_sup] at hk
  by_cases h1 : k = 2
  · use Fin.last (L+1)
    rw [h1, map4_ends_in_2]
  · by_cases h2 : k = 1
    · use Fin.castSucc (Fin.last L)
      rw [h2]
      rw [map4, Fin.snoc_castSucc, Fin.snoc_last]
    · have h_k : 1 ≤ k - 2 ∧ k - 2 ≤ Finset.sup Finset.univ x := by omega
      have ⟨i, hi⟩ := hx (k - 2) h_k
      use Fin.castSucc (Fin.castSucc i)
      have : map4 x (Fin.castSucc (Fin.castSucc i)) = x i + 2 := by
        rw [map4, Fin.snoc_castSucc, Fin.snoc_castSucc]
        rfl
      rw [this]
      omega

def Cond3 {L : ℕ} (x : Fin L → ℕ) : Prop :=
  ∀ i j : Fin L, i < j → j.val ≠ i.val + 1 → x i ≥ x j

theorem cond3_map1 {L : ℕ} (x : Fin L → ℕ) (hx : Cond3 x) : Cond3 (map1 x) := by
  intro i j hij hneq
  by_cases hj : j.val < L
  · have hi : i.val < L := by omega
    have h1 : map1 x i = x ⟨i.val, hi⟩ + 1 := by
      have : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
      calc map1 x i = map1 x (Fin.castSucc ⟨i.val, hi⟩) := congrArg _ this
      _ = x ⟨i.val, hi⟩ + 1 := by rw [map1, Fin.snoc_castSucc]; rfl
    have h2 : map1 x j = x ⟨j.val, hj⟩ + 1 := by
      have : j = Fin.castSucc ⟨j.val, hj⟩ := Fin.ext rfl
      calc map1 x j = map1 x (Fin.castSucc ⟨j.val, hj⟩) := congrArg _ this
      _ = x ⟨j.val, hj⟩ + 1 := by rw [map1, Fin.snoc_castSucc]; rfl
    rw [h1, h2]
    have := hx ⟨i.val, hi⟩ ⟨j.val, hj⟩ (by exact hij) (by exact hneq)
    omega
  · have hj_L : j.val = L := by omega
    have h2 : map1 x j = 1 := by
      have : j = Fin.last L := Fin.ext (by have : (Fin.last L).val = L := rfl; omega)
      calc map1 x j = map1 x (Fin.last L) := congrArg _ this
      _ = 1 := map1_ends_in_1 x
    rw [h2]
    have hi : i.val < L := by omega
    have h1 : map1 x i = x ⟨i.val, hi⟩ + 1 := by
      have : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
      calc map1 x i = map1 x (Fin.castSucc ⟨i.val, hi⟩) := congrArg _ this
      _ = x ⟨i.val, hi⟩ + 1 := by rw [map1, Fin.snoc_castSucc]; rfl
    rw [h1]
    omega

theorem cond3_map2 {L : ℕ} (x : Fin L → ℕ) (hx_pos : ∀ i, x i > 0) (hx : Cond3 x) : Cond3 (map2 x) := by
  intro i j hij hneq
  by_cases hj : j.val < L
  · have hi : i.val < L := by omega
    have h1 : map2 x i = x ⟨i.val, hi⟩ := by
      have : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
      calc map2 x i = map2 x (Fin.castSucc ⟨i.val, hi⟩) := congrArg _ this
      _ = x ⟨i.val, hi⟩ := by rw [map2, Fin.snoc_castSucc]
    have h2 : map2 x j = x ⟨j.val, hj⟩ := by
      have : j = Fin.castSucc ⟨j.val, hj⟩ := Fin.ext rfl
      calc map2 x j = map2 x (Fin.castSucc ⟨j.val, hj⟩) := congrArg _ this
      _ = x ⟨j.val, hj⟩ := by rw [map2, Fin.snoc_castSucc]
    rw [h1, h2]
    have := hx ⟨i.val, hi⟩ ⟨j.val, hj⟩ (by exact hij) (by exact hneq)
    omega
  · have hj_L : j.val = L := by omega
    have h2 : map2 x j = 1 := by
      have : j = Fin.last L := Fin.ext (by have : (Fin.last L).val = L := rfl; omega)
      calc map2 x j = map2 x (Fin.last L) := congrArg _ this
      _ = 1 := map2_ends_in_1 x
    rw [h2]
    have hi : i.val < L := by omega
    have h1 : map2 x i = x ⟨i.val, hi⟩ := by
      have : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
      calc map2 x i = map2 x (Fin.castSucc ⟨i.val, hi⟩) := congrArg _ this
      _ = x ⟨i.val, hi⟩ := by rw [map2, Fin.snoc_castSucc]
    rw [h1]
    have := hx_pos ⟨i.val, hi⟩
    omega

theorem cond3_map3 {L : ℕ} (x : Fin L → ℕ) (hx_pos : ∀ i, x i > 0) (hx : Cond3 x) : Cond3 (map3 x) := by
  intro i j hij hneq
  by_cases hj : j.val < L + 1
  · by_cases hj2 : j.val < L
    · have hi : i.val < L := by omega
      have h1 : map3 x i = x ⟨i.val, hi⟩ + 1 := by
        have : i = Fin.castSucc (Fin.castSucc ⟨i.val, hi⟩) := Fin.ext rfl
        calc map3 x i = map3 x (Fin.castSucc (Fin.castSucc ⟨i.val, hi⟩)) := congrArg _ this
        _ = x ⟨i.val, hi⟩ + 1 := by rw [map3, Fin.snoc_castSucc, Fin.snoc_castSucc]; rfl
      have h2 : map3 x j = x ⟨j.val, hj2⟩ + 1 := by
        have : j = Fin.castSucc (Fin.castSucc ⟨j.val, hj2⟩) := Fin.ext rfl
        calc map3 x j = map3 x (Fin.castSucc (Fin.castSucc ⟨j.val, hj2⟩)) := congrArg _ this
        _ = x ⟨j.val, hj2⟩ + 1 := by rw [map3, Fin.snoc_castSucc, Fin.snoc_castSucc]; rfl
      rw [h1, h2]
      have := hx ⟨i.val, hi⟩ ⟨j.val, hj2⟩ (by exact hij) (by exact hneq)
      omega
    · have hj_L : j.val = L := by omega
      have h2 : map3 x j = 1 := by
        have : j = Fin.castSucc (Fin.last L) := Fin.ext (by have : (Fin.castSucc (Fin.last L)).val = L := rfl; omega)
        calc map3 x j = map3 x (Fin.castSucc (Fin.last L)) := congrArg _ this
        _ = 1 := by rw [map3, Fin.snoc_castSucc, Fin.snoc_last]
      rw [h2]
      have hi : i.val < L := by omega
      have h1 : map3 x i = x ⟨i.val, hi⟩ + 1 := by
        have : i = Fin.castSucc (Fin.castSucc ⟨i.val, hi⟩) := Fin.ext rfl
        calc map3 x i = map3 x (Fin.castSucc (Fin.castSucc ⟨i.val, hi⟩)) := congrArg _ this
        _ = x ⟨i.val, hi⟩ + 1 := by rw [map3, Fin.snoc_castSucc, Fin.snoc_castSucc]; rfl
      rw [h1]
      omega
  · have hj_L1 : j.val = L + 1 := by omega
    have h2 : map3 x j = 2 := by
      have : j = Fin.last (L + 1) := Fin.ext (by have : (Fin.last (L + 1)).val = L + 1 := rfl; omega)
      calc map3 x j = map3 x (Fin.last (L + 1)) := congrArg _ this
      _ = 2 := map3_ends_in_2 x
    rw [h2]
    have hi : i.val < L := by omega
    have h1 : map3 x i = x ⟨i.val, hi⟩ + 1 := by
      have : i = Fin.castSucc (Fin.castSucc ⟨i.val, hi⟩) := Fin.ext rfl
      calc map3 x i = map3 x (Fin.castSucc (Fin.castSucc ⟨i.val, hi⟩)) := congrArg _ this
      _ = x ⟨i.val, hi⟩ + 1 := by rw [map3, Fin.snoc_castSucc, Fin.snoc_castSucc]; rfl
    rw [h1]
    have := hx_pos ⟨i.val, hi⟩
    omega

theorem cond3_map4 {L : ℕ} (x : Fin L → ℕ) (hx_pos : ∀ i, x i > 0) (hx : Cond3 x) : Cond3 (map4 x) := by
  intro i j hij hneq
  by_cases hj : j.val < L + 1
  · by_cases hj2 : j.val < L
    · have hi : i.val < L := by omega
      have h1 : map4 x i = x ⟨i.val, hi⟩ + 2 := by
        have : i = Fin.castSucc (Fin.castSucc ⟨i.val, hi⟩) := Fin.ext rfl
        calc map4 x i = map4 x (Fin.castSucc (Fin.castSucc ⟨i.val, hi⟩)) := congrArg _ this
        _ = x ⟨i.val, hi⟩ + 2 := by rw [map4, Fin.snoc_castSucc, Fin.snoc_castSucc]; rfl
      have h2 : map4 x j = x ⟨j.val, hj2⟩ + 2 := by
        have : j = Fin.castSucc (Fin.castSucc ⟨j.val, hj2⟩) := Fin.ext rfl
        calc map4 x j = map4 x (Fin.castSucc (Fin.castSucc ⟨j.val, hj2⟩)) := congrArg _ this
        _ = x ⟨j.val, hj2⟩ + 2 := by rw [map4, Fin.snoc_castSucc, Fin.snoc_castSucc]; rfl
      rw [h1, h2]
      have := hx ⟨i.val, hi⟩ ⟨j.val, hj2⟩ (by exact hij) (by exact hneq)
      omega
    · have hj_L : j.val = L := by omega
      have h2 : map4 x j = 1 := by
        have : j = Fin.castSucc (Fin.last L) := Fin.ext (by have : (Fin.castSucc (Fin.last L)).val = L := rfl; omega)
        calc map4 x j = map4 x (Fin.castSucc (Fin.last L)) := congrArg _ this
        _ = 1 := by rw [map4, Fin.snoc_castSucc, Fin.snoc_last]
      rw [h2]
      have hi : i.val < L := by omega
      have h1 : map4 x i = x ⟨i.val, hi⟩ + 2 := by
        have : i = Fin.castSucc (Fin.castSucc ⟨i.val, hi⟩) := Fin.ext rfl
        calc map4 x i = map4 x (Fin.castSucc (Fin.castSucc ⟨i.val, hi⟩)) := congrArg _ this
        _ = x ⟨i.val, hi⟩ + 2 := by rw [map4, Fin.snoc_castSucc, Fin.snoc_castSucc]; rfl
      rw [h1]
      omega
  · have hj_L1 : j.val = L + 1 := by omega
    have h2 : map4 x j = 2 := by
      have : j = Fin.last (L + 1) := Fin.ext (by have : (Fin.last (L + 1)).val = L + 1 := rfl; omega)
      calc map4 x j = map4 x (Fin.last (L + 1)) := congrArg _ this
      _ = 2 := map4_ends_in_2 x
    rw [h2]
    have hi : i.val < L := by omega
    have h1 : map4 x i = x ⟨i.val, hi⟩ + 2 := by
      have : i = Fin.castSucc (Fin.castSucc ⟨i.val, hi⟩) := Fin.ext rfl
      calc map4 x i = map4 x (Fin.castSucc (Fin.castSucc ⟨i.val, hi⟩)) := congrArg _ this
      _ = x ⟨i.val, hi⟩ + 2 := by rw [map4, Fin.snoc_castSucc, Fin.snoc_castSucc]; rfl
    rw [h1]
    have := hx_pos ⟨i.val, hi⟩
    omega

