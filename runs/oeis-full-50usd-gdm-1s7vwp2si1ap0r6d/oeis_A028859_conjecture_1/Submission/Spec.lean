import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 3
  | (n + 2) => 2 * a (n + 1) + 2 * a n
termination_by n

def append_val {L : ℕ} (τ : Fin L → ℕ) (v : ℕ) : Fin (L + 1) → ℕ :=
  fun i => if h : i.val < L then τ ⟨i.val, h⟩ else v

def append_two_vals {L : ℕ} (τ : Fin L → ℕ) (v1 v2 : ℕ) : Fin (L + 2) → ℕ :=
  fun i =>
    if h : i.val < L then τ ⟨i.val, h⟩
    else if i.val = L then v1
    else v2

lemma append_val_inj {L : ℕ} (v : ℕ) (τ1 τ2 : Fin L → ℕ)
    (h : append_val τ1 v = append_val τ2 v) : τ1 = τ2 := by
  ext i
  have h_val : append_val τ1 v ⟨i.val, by omega⟩ = append_val τ2 v ⟨i.val, by omega⟩ := by rw [h]
  dsimp [append_val] at h_val
  split_ifs at h_val
  · exact h_val
  · omega

lemma append_two_vals_inj {L : ℕ} (v1 v2 : ℕ) (τ1 τ2 : Fin L → ℕ)
    (h : append_two_vals τ1 v1 v2 = append_two_vals τ2 v1 v2) : τ1 = τ2 := by
  ext i
  have h_val : append_two_vals τ1 v1 v2 ⟨i.val, by omega⟩ = append_two_vals τ2 v1 v2 ⟨i.val, by omega⟩ := by rw [h]
  dsimp [append_two_vals] at h_val
  split_ifs at h_val
  · exact h_val
  · omega
  · omega

def map_A (n : ℕ) (τ : Fin (n + 2) → ℕ) : Fin (n + 3) → ℕ := append_val τ 1
def map_B (n : ℕ) (τ : Fin (n + 2) → ℕ) : Fin (n + 3) → ℕ := append_val (fun i => τ i + 1) 1
def map_C (n : ℕ) (τ : Fin (n + 1) → ℕ) : Fin (n + 3) → ℕ := append_two_vals (fun i => τ i + 1) 1 2
def map_D (n : ℕ) (τ : Fin (n + 1) → ℕ) : Fin (n + 3) → ℕ := append_two_vals (fun i => τ i + 2) 1 2

lemma map_A_inj (n : ℕ) : Function.Injective (map_A n) := by
  intro τ1 τ2 h
  exact append_val_inj 1 τ1 τ2 h

lemma map_B_inj (n : ℕ) : Function.Injective (map_B n) := by
  intro τ1 τ2 h
  have h1 := append_val_inj 1 (fun i => τ1 i + 1) (fun i => τ2 i + 1) h
  ext i
  have h2 : (fun i => τ1 i + 1) i = (fun i => τ2 i + 1) i := by rw [h1]
  dsimp at h2
  omega

lemma map_C_inj (n : ℕ) : Function.Injective (map_C n) := by
  intro τ1 τ2 h
  have h1 := append_two_vals_inj 1 2 (fun i => τ1 i + 1) (fun i => τ2 i + 1) h
  ext i
  have h2 : (fun i => τ1 i + 1) i = (fun i => τ2 i + 1) i := by rw [h1]
  dsimp at h2
  omega

lemma map_D_inj (n : ℕ) : Function.Injective (map_D n) := by
  intro τ1 τ2 h
  have h1 := append_two_vals_inj 1 2 (fun i => τ1 i + 2) (fun i => τ2 i + 2) h
  ext i
  have h2 : (fun i => τ1 i + 2) i = (fun i => τ2 i + 2) i := by rw [h1]
  dsimp at h2
  omega

def emb_A (n : ℕ) : (Fin (n + 2) → ℕ) ↪ (Fin (n + 3) → ℕ) := ⟨map_A n, map_A_inj n⟩
def emb_B (n : ℕ) : (Fin (n + 2) → ℕ) ↪ (Fin (n + 3) → ℕ) := ⟨map_B n, map_B_inj n⟩
def emb_C (n : ℕ) : (Fin (n + 1) → ℕ) ↪ (Fin (n + 3) → ℕ) := ⟨map_C n, map_C_inj n⟩
def emb_D (n : ℕ) : (Fin (n + 1) → ℕ) ↪ (Fin (n + 3) → ℕ) := ⟨map_D n, map_D_inj n⟩

noncomputable def F (n : ℕ) : Finset (Fin (n + 1) → ℕ) :=
  match n with
  | 0 => { fun _ => 1 }
  | 1 => { (fun _ => 1), (fun i => if i.val = 0 then 1 else 2), (fun i => if i.val = 0 then 2 else 1) }
  | n + 2 =>
    let FA := (F (n+1)).map (emb_A n)
    let FB := (F (n+1)).map (emb_B n)
    let FC := (F n).map (emb_C n)
    let FD := (F n).map (emb_D n)
    FA ∪ FB ∪ FC ∪ FD

def S_aux (n : ℕ) : Set (Fin (n + 1) → ℕ) :=
  { σ : Fin (n + 1) → ℕ |
    (∀ i : Fin (n + 1), σ i > 0) ∧
    let max_val := Finset.sup Finset.univ σ
    (∀ k : ℕ, 1 ≤ k ∧ k ≤ max_val → ∃ i : Fin (n + 1), σ i = k) ∧
    (∀ i j : Fin (n + 1), i < j → j.val ≠ i.val + 1 → σ i ≥ σ j)
  }

lemma Prop_one (n : ℕ) : ∀ τ ∈ F n, ∃ i, τ i = 1 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | n
  · intro τ hτ
    simp [F] at hτ
    subst hτ
    use ⟨0, by omega⟩
  · intro τ hτ
    simp [F] at hτ
    rcases hτ with h | h | h
    · subst h; use ⟨0, by omega⟩
    · subst h; use ⟨0, by omega⟩; rfl
    · subst h; use ⟨1, by omega⟩; rfl
  · intro τ hτ
    dsimp [F] at hτ
    simp only [Finset.mem_union, Finset.mem_map] at hτ
    rcases hτ with (((h | h) | h) | h)
    · obtain ⟨τ0, hτ0, rfl⟩ := h
      use ⟨n + 2, by omega⟩
      dsimp [emb_A, map_A, append_val]
      split_ifs <;> omega
    · obtain ⟨τ0, hτ0, rfl⟩ := h
      use ⟨n + 2, by omega⟩
      dsimp [emb_B, map_B, append_val]
      split_ifs <;> omega
    · obtain ⟨τ0, hτ0, rfl⟩ := h
      use ⟨n + 1, by omega⟩
      dsimp [emb_C, map_C, append_two_vals]
      split_ifs <;> omega
    · obtain ⟨τ0, hτ0, rfl⟩ := h
      use ⟨n + 1, by omega⟩
      dsimp [emb_D, map_D, append_two_vals]
      split_ifs <;> omega

lemma Prop_pos (n : ℕ) : ∀ τ ∈ F n, ∀ i, τ i > 0 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | n
  · intro τ hτ i
    simp [F] at hτ
    subst hτ
    dsimp
    omega
  · intro τ hτ i
    simp [F] at hτ
    rcases hτ with h | h | h
    · subst h; dsimp; omega
    · subst h; dsimp; split_ifs <;> omega
    · subst h; dsimp; split_ifs <;> omega
  · intro τ hτ i
    dsimp [F] at hτ
    simp only [Finset.mem_union, Finset.mem_map] at hτ
    rcases hτ with (((h | h) | h) | h)
    · obtain ⟨τ0, hτ0, rfl⟩ := h
      dsimp [emb_A, map_A, append_val]
      split_ifs with h_ifs
      · have h_pos := ih (n + 1) (by omega) τ0 hτ0 ⟨i.val, by omega⟩
        exact h_pos
      · omega
    · obtain ⟨τ0, hτ0, rfl⟩ := h
      dsimp [emb_B, map_B, append_val]
      split_ifs with h_ifs
      · have h_pos := ih (n + 1) (by omega) τ0 hτ0 ⟨i.val, by omega⟩
        omega
      · omega
    · obtain ⟨τ0, hτ0, rfl⟩ := h
      dsimp [emb_C, map_C, append_two_vals]
      split_ifs with h_ifs1 h_ifs2
      · have h_pos := ih n (by omega) τ0 hτ0 ⟨i.val, by omega⟩
        omega
      · omega
      · omega
    · obtain ⟨τ0, hτ0, rfl⟩ := h
      dsimp [emb_D, map_D, append_two_vals]
      split_ifs with h_ifs1 h_ifs2
      · have h_pos := ih n (by omega) τ0 hτ0 ⟨i.val, by omega⟩
        omega
      · omega
      · omega

lemma disjoint_FA_FB (n : ℕ) (h_one : ∀ τ ∈ F (n+1), ∃ i, τ i = 1) (h_pos : ∀ τ ∈ F (n+1), ∀ i, τ i > 0) :
    Disjoint ((F (n+1)).map (emb_A n)) ((F (n+1)).map (emb_B n)) := by
  rw [Finset.disjoint_left]
  intro σ hA hB
  simp only [Finset.mem_map] at hA hB
  obtain ⟨τ1, hτ1, rfl⟩ := hA
  obtain ⟨τ2, hτ2, h_eq⟩ := hB
  obtain ⟨i, hi⟩ := h_one τ1 hτ1
  have h_val := congr_fun h_eq ⟨i.val, by omega⟩
  dsimp [emb_A, map_A, emb_B, map_B, append_val] at h_val
  have h_lt : i.val < n + 2 := i.isLt
  rw [if_pos h_lt] at h_val
  rw [if_pos h_lt] at h_val
  have h_pos_τ2 := h_pos τ2 hτ2 i
  omega

lemma disjoint_FA_FC (n : ℕ) :
    Disjoint ((F (n+1)).map (emb_A n)) ((F n).map (emb_C n)) := by
  rw [Finset.disjoint_left]
  intro σ hA hC
  simp only [Finset.mem_map] at hA hC
  obtain ⟨τ1, hτ1, rfl⟩ := hA
  obtain ⟨τ2, hτ2, h_eq⟩ := hC
  have h_val := congr_fun h_eq ⟨n + 2, by omega⟩
  dsimp [emb_A, map_A, emb_C, map_C, append_val, append_two_vals] at h_val
  split_ifs at h_val <;> omega

lemma disjoint_FA_FD (n : ℕ) :
    Disjoint ((F (n+1)).map (emb_A n)) ((F n).map (emb_D n)) := by
  rw [Finset.disjoint_left]
  intro σ hA hD
  simp only [Finset.mem_map] at hA hD
  obtain ⟨τ1, hτ1, rfl⟩ := hA
  obtain ⟨τ2, hτ2, h_eq⟩ := hD
  have h_val := congr_fun h_eq ⟨n + 2, by omega⟩
  dsimp [emb_A, map_A, emb_D, map_D, append_val, append_two_vals] at h_val
  split_ifs at h_val <;> omega

lemma disjoint_FB_FC (n : ℕ) :
    Disjoint ((F (n+1)).map (emb_B n)) ((F n).map (emb_C n)) := by
  rw [Finset.disjoint_left]
  intro σ hB hC
  simp only [Finset.mem_map] at hB hC
  obtain ⟨τ1, hτ1, rfl⟩ := hB
  obtain ⟨τ2, hτ2, h_eq⟩ := hC
  have h_val := congr_fun h_eq ⟨n + 2, by omega⟩
  dsimp [emb_B, map_B, emb_C, map_C, append_val, append_two_vals] at h_val
  split_ifs at h_val <;> omega

lemma disjoint_FB_FD (n : ℕ) :
    Disjoint ((F (n+1)).map (emb_B n)) ((F n).map (emb_D n)) := by
  rw [Finset.disjoint_left]
  intro σ hB hD
  simp only [Finset.mem_map] at hB hD
  obtain ⟨τ1, hτ1, rfl⟩ := hB
  obtain ⟨τ2, hτ2, h_eq⟩ := hD
  have h_val := congr_fun h_eq ⟨n + 2, by omega⟩
  dsimp [emb_B, map_B, emb_D, map_D, append_val, append_two_vals] at h_val
  split_ifs at h_val <;> omega

lemma disjoint_FC_FD (n : ℕ) (h_one : ∀ τ ∈ F n, ∃ i, τ i = 1) (h_pos : ∀ τ ∈ F n, ∀ i, τ i > 0) :
    Disjoint ((F n).map (emb_C n)) ((F n).map (emb_D n)) := by
  rw [Finset.disjoint_left]
  intro σ hC hD
  simp only [Finset.mem_map] at hC hD
  obtain ⟨τ1, hτ1, rfl⟩ := hC
  obtain ⟨τ2, hτ2, h_eq⟩ := hD
  obtain ⟨i, hi⟩ := h_one τ1 hτ1
  have h_val := congr_fun h_eq ⟨i.val, by omega⟩
  dsimp [emb_C, map_C, emb_D, map_D, append_two_vals] at h_val
  have h_lt : i.val < n + 1 := i.isLt
  rw [if_pos h_lt] at h_val
  rw [if_pos h_lt] at h_val
  have h_pos_τ2 := h_pos τ2 hτ2 i
  omega

lemma card_union_four {α : Type*} [DecidableEq α] (A B C D : Finset α)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D) :
    (A ∪ B ∪ C ∪ D).card = A.card + B.card + C.card + D.card := by
  have hABC : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_union_left]
    exact ⟨hAC, hBC⟩
  have hABCD : Disjoint (A ∪ B ∪ C) D := by
    rw [Finset.disjoint_union_left]
    refine ⟨?_, hCD⟩
    rw [Finset.disjoint_union_left]
    exact ⟨hAD, hBD⟩
  rw [Finset.card_union_of_disjoint hABCD]
  rw [Finset.card_union_of_disjoint hABC]
  rw [Finset.card_union_of_disjoint hAB]

lemma F_card (n : ℕ) : (F n).card = a n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | n
  · have h1 : (F 0).card = 1 := Finset.card_singleton _
    have h2 : a 0 = 1 := by unfold a; rfl
    rw [h1, h2]
  · have h_f1 : (fun _ => 1 : Fin 2 → ℕ) ≠ (fun i => if i.val = 0 then 1 else 2) := by
      intro h_eq
      have h_val := congr_fun h_eq ⟨1, by omega⟩
      dsimp at h_val
      omega
    have h_f1_3 : (fun _ => 1 : Fin 2 → ℕ) ≠ (fun i => if i.val = 0 then 2 else 1) := by
      intro h_eq
      have h_val := congr_fun h_eq ⟨0, by omega⟩
      dsimp at h_val
      omega
    have h_f2_3 : (fun i => if i.val = 0 then 1 else 2 : Fin 2 → ℕ) ≠ (fun i => if i.val = 0 then 2 else 1) := by
      intro h_eq
      have h_val := congr_fun h_eq ⟨0, by omega⟩
      dsimp at h_val
      omega
    have h_card : (F 1).card = 3 := by
      dsimp [F]
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rfl
        · simp only [Finset.mem_singleton]
          exact h_f2_3
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨h_f1, h_f1_3⟩
    have h2 : a 1 = 3 := by unfold a; rfl
    rw [h_card, h2]
  · dsimp [F]
    have h_card := card_union_four
      ((F (n+1)).map (emb_A n))
      ((F (n+1)).map (emb_B n))
      ((F n).map (emb_C n))
      ((F n).map (emb_D n))
      (disjoint_FA_FB n (Prop_one (n+1)) (Prop_pos (n+1)))
      (disjoint_FA_FC n)
      (disjoint_FA_FD n)
      (disjoint_FB_FC n)
      (disjoint_FB_FD n)
      (disjoint_FC_FD n (Prop_one n) (Prop_pos n))
    rw [h_card]
    simp only [Finset.card_map]
    have ih1 := ih (n + 1) (by omega)
    have ih2 := ih n (by omega)
    rw [ih1, ih2]
    rw [a.eq_3 n]
    omega

lemma sup_append_val_one_le {L : ℕ} (hL : L > 0) (τ : Fin L → ℕ) (h_pos : ∀ i, τ i > 0) :
    Finset.sup Finset.univ (append_val τ 1) ≤ Finset.sup Finset.univ τ := by
  apply Finset.sup_le
  intro i _
  dsimp [append_val]
  split_ifs with h
  · apply Finset.le_sup (Finset.mem_univ _)
  · have h_in : ⟨0, hL⟩ ∈ (Finset.univ : Finset (Fin L)) := Finset.mem_univ _
    have h_le := Finset.le_sup h_in (f := τ)
    have h_pos0 := h_pos ⟨0, hL⟩
    omega

lemma sup_append_val_one_ge {L : ℕ} (hL : L > 0) (τ : Fin L → ℕ) :
    Finset.sup Finset.univ τ ≤ Finset.sup Finset.univ (append_val τ 1) := by
  apply Finset.sup_le
  intro i _
  have h_in : ⟨i.val, by omega⟩ ∈ (Finset.univ : Finset (Fin (L + 1))) := Finset.mem_univ _
  have h_le := Finset.le_sup h_in (f := append_val τ 1)
  dsimp [append_val] at h_le
  split_ifs at h_le with h
  · exact h_le
  · omega

lemma sup_append_val_plus_one_le {L : ℕ} (hL : L > 0) (τ : Fin L → ℕ) (h_pos : ∀ i, τ i > 0) :
    Finset.sup Finset.univ (append_val (fun i => τ i + 1) 1) ≤ Finset.sup Finset.univ τ + 1 := by
  apply Finset.sup_le
  intro i _
  dsimp [append_val]
  split_ifs with h
  · have h_le : τ ⟨i.val, h⟩ ≤ Finset.sup Finset.univ τ := Finset.le_sup (Finset.mem_univ _)
    omega
  · have h_in : ⟨0, hL⟩ ∈ (Finset.univ : Finset (Fin L)) := Finset.mem_univ _
    have h_le := Finset.le_sup h_in (f := τ)
    have h_pos0 := h_pos ⟨0, hL⟩
    omega

lemma sup_add_one {L : ℕ} (hL : L > 0) (τ : Fin L → ℕ) :
    Finset.sup Finset.univ (fun i => τ i + 1) = Finset.sup Finset.univ τ + 1 := by
  apply LE.le.antisymm
  · apply Finset.sup_le
    intro i _
    have h_le : τ i ≤ Finset.sup Finset.univ τ := Finset.le_sup (Finset.mem_univ i)
    omega
  · have h_le : ∀ i, τ i ≤ Finset.sup Finset.univ (fun i => τ i + 1) - 1 := by
      intro i
      have h_le2 : τ i + 1 ≤ Finset.sup Finset.univ (fun i => τ i + 1) := Finset.le_sup (f := fun i => τ i + 1) (Finset.mem_univ i)
      omega
    have h_sup_le : Finset.sup Finset.univ τ ≤ Finset.sup Finset.univ (fun i => τ i + 1) - 1 := by
      apply Finset.sup_le
      intro i _
      exact h_le i
    have h_pos : Finset.sup Finset.univ (fun i => τ i + 1) ≥ 1 := by
      have h_in : ⟨0, hL⟩ ∈ (Finset.univ : Finset (Fin L)) := Finset.mem_univ _
      have h_le2 := Finset.le_sup h_in (f := fun i => τ i + 1)
      dsimp at h_le2
      omega
    omega

lemma sup_add_two {L : ℕ} (hL : L > 0) (τ : Fin L → ℕ) :
    Finset.sup Finset.univ (fun i => τ i + 2) = Finset.sup Finset.univ τ + 2 := by
  apply LE.le.antisymm
  · apply Finset.sup_le
    intro i _
    have h_le : τ i ≤ Finset.sup Finset.univ τ := Finset.le_sup (Finset.mem_univ i)
    omega
  · have h_le : ∀ i, τ i ≤ Finset.sup Finset.univ (fun i => τ i + 2) - 2 := by
      intro i
      have h_le2 : τ i + 2 ≤ Finset.sup Finset.univ (fun i => τ i + 2) := Finset.le_sup (f := fun i => τ i + 2) (Finset.mem_univ i)
      omega
    have h_sup_le : Finset.sup Finset.univ τ ≤ Finset.sup Finset.univ (fun i => τ i + 2) - 2 := by
      apply Finset.sup_le
      intro i _
      exact h_le i
    have h_pos : Finset.sup Finset.univ (fun i => τ i + 2) ≥ 2 := by
      have h_in : ⟨0, hL⟩ ∈ (Finset.univ : Finset (Fin L)) := Finset.mem_univ _
      have h_le2 := Finset.le_sup h_in (f := fun i => τ i + 2)
      dsimp at h_le2
      omega
    omega

lemma sup_append_val_plus_one_ge {L : ℕ} (hL : L > 0) (τ : Fin L → ℕ) :
    Finset.sup Finset.univ τ + 1 ≤ Finset.sup Finset.univ (append_val (fun i => τ i + 1) 1) := by
  have h_le : ∀ i : Fin L, τ i + 1 ≤ Finset.sup Finset.univ (append_val (fun i => τ i + 1) 1) := by
    intro i
    have h_in : ⟨i.val, by omega⟩ ∈ (Finset.univ : Finset (Fin (L + 1))) := Finset.mem_univ _
    have h_le2 := Finset.le_sup h_in (f := append_val (fun i => τ i + 1) 1)
    dsimp [append_val] at h_le2
    split_ifs at h_le2 with h
    · exact h_le2
    · omega
  have h_sup_le : Finset.sup Finset.univ (fun i => τ i + 1) ≤ Finset.sup Finset.univ (append_val (fun i => τ i + 1) 1) := by
    apply Finset.sup_le
    intro i _
    exact h_le i
  rw [sup_add_one hL τ] at h_sup_le
  exact h_sup_le

lemma sup_append_two_vals_plus_one_le {L : ℕ} (hL : L > 0) (τ : Fin L → ℕ) (h_pos : ∀ i, τ i > 0) :
    Finset.sup Finset.univ (append_two_vals (fun i => τ i + 1) 1 2) ≤ Finset.sup Finset.univ τ + 1 := by
  apply Finset.sup_le
  intro i _
  dsimp [append_two_vals]
  split_ifs with h1 h2
  · have h_le : τ ⟨i.val, h1⟩ ≤ Finset.sup Finset.univ τ := Finset.le_sup (Finset.mem_univ _)
    omega
  · have h_in : ⟨0, hL⟩ ∈ (Finset.univ : Finset (Fin L)) := Finset.mem_univ _
    have h_le := Finset.le_sup h_in (f := τ)
    have h_pos0 := h_pos ⟨0, hL⟩
    omega
  · have h_in : ⟨0, hL⟩ ∈ (Finset.univ : Finset (Fin L)) := Finset.mem_univ _
    have h_le := Finset.le_sup h_in (f := τ)
    have h_pos0 := h_pos ⟨0, hL⟩
    omega

lemma sup_append_two_vals_plus_one_ge {L : ℕ} (hL : L > 0) (τ : Fin L → ℕ) :
    Finset.sup Finset.univ τ + 1 ≤ Finset.sup Finset.univ (append_two_vals (fun i => τ i + 1) 1 2) := by
  have h_le : ∀ i : Fin L, τ i + 1 ≤ Finset.sup Finset.univ (append_two_vals (fun i => τ i + 1) 1 2) := by
    intro i
    have h_in : ⟨i.val, by omega⟩ ∈ (Finset.univ : Finset (Fin (L + 2))) := Finset.mem_univ _
    have h_le2 := Finset.le_sup h_in (f := append_two_vals (fun i => τ i + 1) 1 2)
    dsimp [append_two_vals] at h_le2
    split_ifs at h_le2 with h1 h2
    · exact h_le2
    · omega
    · omega
  have h_sup_le : Finset.sup Finset.univ (fun i => τ i + 1) ≤ Finset.sup Finset.univ (append_two_vals (fun i => τ i + 1) 1 2) := by
    apply Finset.sup_le
    intro i _
    exact h_le i
  rw [sup_add_one hL τ] at h_sup_le
  exact h_sup_le

lemma sup_append_two_vals_plus_two_le {L : ℕ} (hL : L > 0) (τ : Fin L → ℕ) (h_pos : ∀ i, τ i > 0) :
    Finset.sup Finset.univ (append_two_vals (fun i => τ i + 2) 1 2) ≤ Finset.sup Finset.univ τ + 2 := by
  apply Finset.sup_le
  intro i _
  dsimp [append_two_vals]
  split_ifs with h1 h2
  · have h_le : τ ⟨i.val, h1⟩ ≤ Finset.sup Finset.univ τ := Finset.le_sup (Finset.mem_univ _)
    omega
  · have h_in : ⟨0, hL⟩ ∈ (Finset.univ : Finset (Fin L)) := Finset.mem_univ _
    have h_le := Finset.le_sup h_in (f := τ)
    have h_pos0 := h_pos ⟨0, hL⟩
    omega
  · have h_in : ⟨0, hL⟩ ∈ (Finset.univ : Finset (Fin L)) := Finset.mem_univ _
    have h_le := Finset.le_sup h_in (f := τ)
    have h_pos0 := h_pos ⟨0, hL⟩
    omega

lemma sup_append_two_vals_plus_two_ge {L : ℕ} (hL : L > 0) (τ : Fin L → ℕ) :
    Finset.sup Finset.univ τ + 2 ≤ Finset.sup Finset.univ (append_two_vals (fun i => τ i + 2) 1 2) := by
  have h_le : ∀ i : Fin L, τ i + 2 ≤ Finset.sup Finset.univ (append_two_vals (fun i => τ i + 2) 1 2) := by
    intro i
    have h_in : ⟨i.val, by omega⟩ ∈ (Finset.univ : Finset (Fin (L + 2))) := Finset.mem_univ _
    have h_le2 := Finset.le_sup h_in (f := append_two_vals (fun i => τ i + 2) 1 2)
    dsimp [append_two_vals] at h_le2
    split_ifs at h_le2 with h1 h2
    · exact h_le2
    · omega
    · omega
  have h_sup_le : Finset.sup Finset.univ (fun i => τ i + 2) ≤ Finset.sup Finset.univ (append_two_vals (fun i => τ i + 2) 1 2) := by
    apply Finset.sup_le
    intro i _
    exact h_le i
  rw [sup_add_two hL τ] at h_sup_le
  exact h_sup_le

lemma map_A_mem_S (n : ℕ) (τ : Fin (n + 2) → ℕ) (hτ : τ ∈ S_aux (n+1)) : map_A n τ ∈ S_aux (n+2) := by
  obtain ⟨h_pos, h_cov, h_dec⟩ := hτ
  dsimp [S_aux]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    dsimp [map_A, append_val]
    split_ifs with h
    · exact h_pos ⟨i.val, h⟩
    · omega
  · intro k hk
    have h_eq : Finset.sup Finset.univ (map_A n τ) = Finset.sup Finset.univ τ := by
      apply LE.le.antisymm
      · exact sup_append_val_one_le (by omega) τ h_pos
      · exact sup_append_val_one_ge (by omega) τ
    rw [h_eq] at hk
    obtain ⟨i0, hi0⟩ := h_cov k hk
    use ⟨i0.val, by omega⟩
    dsimp [map_A, append_val]
    split_ifs with h
    · exact hi0
    · omega
  · intro i j hij h_nonadj
    dsimp [map_A, append_val]
    split_ifs with h1 h2
    · have hij0 : (⟨i.val, h1⟩ : Fin (n+2)) < ⟨j.val, h2⟩ := hij
      have h_nonadj0 : (⟨j.val, h2⟩ : Fin (n+2)).val ≠ (⟨i.val, h1⟩ : Fin (n+2)).val + 1 := h_nonadj
      exact h_dec ⟨i.val, h1⟩ ⟨j.val, h2⟩ hij0 h_nonadj0
    · have h_pos_i := h_pos ⟨i.val, h1⟩
      omega
    · omega
    · omega

lemma map_B_mem_S (n : ℕ) (τ : Fin (n + 2) → ℕ) (hτ : τ ∈ S_aux (n+1)) : map_B n τ ∈ S_aux (n+2) := by
  obtain ⟨h_pos, h_cov, h_dec⟩ := hτ
  dsimp [S_aux]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    dsimp [map_B, append_val]
    split_ifs with h
    · have := h_pos ⟨i.val, h⟩
      omega
    · omega
  · intro k hk
    have h_eq : Finset.sup Finset.univ (map_B n τ) = Finset.sup Finset.univ τ + 1 := by
      apply LE.le.antisymm
      · exact sup_append_val_plus_one_le (by omega) τ h_pos
      · exact sup_append_val_plus_one_ge (by omega) τ
    rw [h_eq] at hk
    if hk1 : k = 1 then
      use ⟨n + 2, by omega⟩
      dsimp [map_B, append_val]
      split_ifs with h
      · omega
      · exact hk1.symm
    else
      have hk_sub : 1 ≤ k - 1 ∧ k - 1 ≤ Finset.sup Finset.univ τ := by omega
      obtain ⟨i0, hi0⟩ := h_cov (k - 1) hk_sub
      use ⟨i0.val, by omega⟩
      dsimp [map_B, append_val]
      split_ifs with h
      · omega
      · omega
  · intro i j hij h_nonadj
    dsimp [map_B, append_val]
    split_ifs with h1 h2
    · have hij0 : (⟨i.val, h1⟩ : Fin (n+2)) < ⟨j.val, h2⟩ := hij
      have h_nonadj0 : (⟨j.val, h2⟩ : Fin (n+2)).val ≠ (⟨i.val, h1⟩ : Fin (n+2)).val + 1 := h_nonadj
      have h_dec0 := h_dec ⟨i.val, h1⟩ ⟨j.val, h2⟩ hij0 h_nonadj0
      omega
    · have h_pos_i := h_pos ⟨i.val, h1⟩
      omega
    · omega
    · omega

lemma map_C_mem_S (n : ℕ) (τ : Fin (n + 1) → ℕ) (hτ : τ ∈ S_aux n) (h_one : ∃ i, τ i = 1) : map_C n τ ∈ S_aux (n+2) := by
  obtain ⟨h_pos, h_cov, h_dec⟩ := hτ
  dsimp [S_aux]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    dsimp [map_C, append_two_vals]
    split_ifs with h1 h2
    · have := h_pos ⟨i.val, h1⟩
      omega
    · omega
    · omega
  · intro k hk
    have h_eq : Finset.sup Finset.univ (map_C n τ) = Finset.sup Finset.univ τ + 1 := by
      apply LE.le.antisymm
      · exact sup_append_two_vals_plus_one_le (by omega) τ h_pos
      · exact sup_append_two_vals_plus_one_ge (by omega) τ
    rw [h_eq] at hk
    if hk1 : k = 1 then
      use ⟨n + 1, by omega⟩
      dsimp [map_C, append_two_vals]
      split_ifs with h1 h2 <;> try omega
    else if hk2 : k = 2 then
      use ⟨n + 2, by omega⟩
      dsimp [map_C, append_two_vals]
      split_ifs with h1 h2 <;> try omega
    else
      have hk_sub : 1 ≤ k - 1 ∧ k - 1 ≤ Finset.sup Finset.univ τ := by omega
      obtain ⟨i0, hi0⟩ := h_cov (k - 1) hk_sub
      use ⟨i0.val, by omega⟩
      dsimp [map_C, append_two_vals]
      split_ifs with h1 h2 <;> try omega
  · intro i j hij h_nonadj
    have h_pos_i : i.val < n + 1 → τ ⟨i.val, by omega⟩ > 0 := fun h => h_pos ⟨i.val, h⟩
    dsimp [map_C, append_two_vals]
    by_cases h_i : i.val < n + 1
    · by_cases h_j : j.val < n + 1
      · rw [dif_pos h_i, dif_pos h_j]
        have hij0 : (⟨i.val, h_i⟩ : Fin (n+1)) < ⟨j.val, h_j⟩ := hij
        have h_nonadj0 : (⟨j.val, h_j⟩ : Fin (n+1)).val ≠ (⟨i.val, h_i⟩ : Fin (n+1)).val + 1 := h_nonadj
        have h_dec0 := h_dec ⟨i.val, h_i⟩ ⟨j.val, h_j⟩ hij0 h_nonadj0
        omega
      · rw [dif_pos h_i, dif_neg h_j]
        by_cases h_j2 : j.val = n + 1
        · rw [if_pos h_j2]
          have := h_pos_i h_i
          omega
        · rw [if_neg h_j2]
          have := h_pos_i h_i
          omega
    · rw [dif_neg h_i]
      by_cases h_i2 : i.val = n + 1
      · rw [if_pos h_i2]
        have h_j : ¬ j.val < n + 1 := by omega
        have h_j2 : ¬ j.val = n + 1 := by omega
        rw [dif_neg h_j, if_neg h_j2]
        omega
      · omega

lemma map_D_mem_S (n : ℕ) (τ : Fin (n + 1) → ℕ) (hτ : τ ∈ S_aux n) (h_one : ∃ i, τ i = 1) : map_D n τ ∈ S_aux (n+2) := by
  obtain ⟨h_pos, h_cov, h_dec⟩ := hτ
  dsimp [S_aux]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    dsimp [map_D, append_two_vals]
    split_ifs with h1 h2
    · have := h_pos ⟨i.val, h1⟩
      omega
    · omega
    · omega
  · intro k hk
    have h_eq : Finset.sup Finset.univ (map_D n τ) = Finset.sup Finset.univ τ + 2 := by
      apply LE.le.antisymm
      · exact sup_append_two_vals_plus_two_le (by omega) τ h_pos
      · exact sup_append_two_vals_plus_two_ge (by omega) τ
    rw [h_eq] at hk
    if hk1 : k = 1 then
      use ⟨n + 1, by omega⟩
      dsimp [map_D, append_two_vals]
      split_ifs with h1 h2 <;> try omega
    else if hk2 : k = 2 then
      use ⟨n + 2, by omega⟩
      dsimp [map_D, append_two_vals]
      split_ifs with h1 h2 <;> try omega
    else
      have hk_sub : 1 ≤ k - 2 ∧ k - 2 ≤ Finset.sup Finset.univ τ := by omega
      obtain ⟨i0, hi0⟩ := h_cov (k - 2) hk_sub
      use ⟨i0.val, by omega⟩
      dsimp [map_D, append_two_vals]
      split_ifs with h1 h2 <;> try omega
  · intro i j hij h_nonadj
    have h_pos_i : i.val < n + 1 → τ ⟨i.val, by omega⟩ > 0 := fun h => h_pos ⟨i.val, h⟩
    dsimp [map_D, append_two_vals]
    by_cases h_i : i.val < n + 1
    · by_cases h_j : j.val < n + 1
      · rw [dif_pos h_i, dif_pos h_j]
        have hij0 : (⟨i.val, h_i⟩ : Fin (n+1)) < ⟨j.val, h_j⟩ := hij
        have h_nonadj0 : (⟨j.val, h_j⟩ : Fin (n+1)).val ≠ (⟨i.val, h_i⟩ : Fin (n+1)).val + 1 := h_nonadj
        have h_dec0 := h_dec ⟨i.val, h_i⟩ ⟨j.val, h_j⟩ hij0 h_nonadj0
        omega
      · rw [dif_pos h_i, dif_neg h_j]
        by_cases h_j2 : j.val = n + 1
        · rw [if_pos h_j2]
          have := h_pos_i h_i
          omega
        · rw [if_neg h_j2]
          have := h_pos_i h_i
          omega
    · rw [dif_neg h_i]
      by_cases h_i2 : i.val = n + 1
      · rw [if_pos h_i2]
        have h_j : ¬ j.val < n + 1 := by omega
        have h_j2 : ¬ j.val = n + 1 := by omega
        rw [dif_neg h_j, if_neg h_j2]
        omega
      · omega

lemma F_subset_S (n : ℕ) : ∀ σ ∈ F n, σ ∈ S_aux n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | n
  · intro σ hσ
    simp [F] at hσ
    subst hσ
    refine ⟨?_, ?_, ?_⟩
    · intro i; dsimp; omega
    · intro k hk
      have h_max : Finset.sup Finset.univ (fun (_ : Fin 1) => 1) = 1 := by rfl
      rw [h_max] at hk
      have : k = 1 := by omega
      use ⟨0, by omega⟩
      dsimp; exact this.symm
    · intro i j hij
      omega
  · intro σ hσ
    simp [F] at hσ
    rcases hσ with h | h | h
    · subst h
      refine ⟨?_, ?_, ?_⟩
      · intro i; dsimp; omega
      · intro k hk
        have h_max : Finset.sup Finset.univ (fun (_ : Fin 2) => 1) = 1 := by rfl
        rw [h_max] at hk
        have : k = 1 := by omega
        use ⟨0, by omega⟩
        dsimp; exact this.symm
      · intro i j hij h_nonadj
        omega
    · subst h
      refine ⟨?_, ?_, ?_⟩
      · intro i; dsimp; split_ifs <;> omega
      · intro k hk
        have h_max : Finset.sup Finset.univ (fun (i : Fin 2) => if i = 0 then 1 else 2) = 2 := by rfl
        rw [h_max] at hk
        have hk_eq : k = 1 ∨ k = 2 := by omega
        rcases hk_eq with rfl | rfl
        · use ⟨0, by omega⟩; decide
        · use ⟨1, by omega⟩; decide
      · intro i j hij h_nonadj
        omega
    · subst h
      refine ⟨?_, ?_, ?_⟩
      · intro i; dsimp; split_ifs <;> omega
      · intro k hk
        have h_max : Finset.sup Finset.univ (fun (i : Fin 2) => if i = 0 then 2 else 1) = 2 := by rfl
        rw [h_max] at hk
        have hk_eq : k = 1 ∨ k = 2 := by omega
        rcases hk_eq with rfl | rfl
        · use ⟨1, by omega⟩; decide
        · use ⟨0, by omega⟩; decide
      · intro i j hij h_nonadj
        omega
  · intro σ hσ
    dsimp [F] at hσ
    simp only [Finset.mem_union, Finset.mem_map] at hσ
    rcases hσ with (((h | h) | h) | h)
    · obtain ⟨τ0, hτ0, rfl⟩ := h
      have ih1 := ih (n + 1) (by omega) τ0 hτ0
      exact map_A_mem_S n τ0 ih1
    · obtain ⟨τ0, hτ0, rfl⟩ := h
      have ih1 := ih (n + 1) (by omega) τ0 hτ0
      exact map_B_mem_S n τ0 ih1
    · obtain ⟨τ0, hτ0, rfl⟩ := h
      have ih1 := ih n (by omega) τ0 hτ0
      exact map_C_mem_S n τ0 ih1 (Prop_one n τ0 hτ0)
    · obtain ⟨τ0, hτ0, rfl⟩ := h
      have ih1 := ih n (by omega) τ0 hτ0
      exact map_D_mem_S n τ0 ih1 (Prop_one n τ0 hτ0)


lemma S_subset_F_zero (σ : Fin 1 → ℕ) (hσ : σ ∈ S_aux 0) : σ ∈ F 0 := by
  obtain ⟨h_pos, h_cov, h_dec⟩ := hσ
  have h_univ : (Finset.univ : Finset (Fin 1)) = {⟨0, by omega⟩} := by decide
  have h_max : Finset.sup Finset.univ σ = σ ⟨0, by omega⟩ := by
    rw [h_univ, Finset.sup_singleton]
  have h_cov0 := h_cov 1
  have h_cov1 : 1 ≤ 1 ∧ 1 ≤ Finset.sup Finset.univ σ := by
    refine ⟨by omega, ?_⟩
    rw [h_max]
    exact h_pos ⟨0, by omega⟩
  obtain ⟨i, hi⟩ := h_cov0 h_cov1
  have h_i0 : i = ⟨0, by omega⟩ := by ext; omega
  rw [h_i0] at hi
  dsimp [F]
  simp only [Finset.mem_singleton]
  ext x
  have h_x0 : x = ⟨0, by omega⟩ := by ext; omega
  rw [h_x0]
  exact hi

lemma S_subset_F_one (σ : Fin 2 → ℕ) (hσ : σ ∈ S_aux 1) : σ ∈ F 1 := by
  obtain ⟨h_pos, h_cov, h_dec⟩ := hσ
  have h_0 := h_pos ⟨0, by omega⟩
  have h_1 := h_pos ⟨1, by omega⟩
  have h_max_le_2 : Finset.sup Finset.univ σ ≤ 2 := by
    by_contra h_gt
    have h_gt : Finset.sup Finset.univ σ ≥ 3 := by omega
    obtain ⟨i1, hi1⟩ := h_cov 1 (by omega)
    obtain ⟨i2, hi2⟩ := h_cov 2 (by omega)
    obtain ⟨i3, hi3⟩ := h_cov 3 (by omega)
    rcases i1 with ⟨_|_|x1, h1⟩ <;> rcases i2 with ⟨_|_|x2, h2⟩ <;> rcases i3 with ⟨_|_|x3, h3⟩ <;> omega
  have h_max_val_cases : Finset.sup Finset.univ σ = 1 ∨ Finset.sup Finset.univ σ = 2 := by
    have h_sup_ge : Finset.sup Finset.univ σ ≥ 1 := by
      have h_in : ⟨0, by omega⟩ ∈ (Finset.univ : Finset (Fin 2)) := Finset.mem_univ _
      have h_le := Finset.le_sup h_in (f := σ)
      omega
    omega
  dsimp [F]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases h_max_val_cases with h_max1 | h_max2
  · have h_0_eq : σ ⟨0, by omega⟩ = 1 := by
      have h_in : ⟨0, by omega⟩ ∈ (Finset.univ : Finset (Fin 2)) := Finset.mem_univ _
      have h_le := Finset.le_sup h_in (f := σ)
      rw [h_max1] at h_le
      omega
    have h_1_eq : σ ⟨1, by omega⟩ = 1 := by
      have h_in : ⟨1, by omega⟩ ∈ (Finset.univ : Finset (Fin 2)) := Finset.mem_univ _
      have h_le := Finset.le_sup h_in (f := σ)
      rw [h_max1] at h_le
      omega
    left
    ext i
    rcases i with ⟨_|_|x, hx⟩
    · have h_eq : (⟨0, hx⟩ : Fin 2) = ⟨0, by omega⟩ := rfl
      rw [h_eq]
      exact h_0_eq
    · have h_eq : (⟨1, hx⟩ : Fin 2) = ⟨1, by omega⟩ := rfl
      rw [h_eq]
      exact h_1_eq
    · omega
  · obtain ⟨i1, hi1⟩ := h_cov 1 (by omega)
    obtain ⟨i2, hi2⟩ := h_cov 2 (by omega)
    rcases i1 with ⟨_|_|x1, h1⟩ <;> rcases i2 with ⟨_|_|x2, h2⟩ <;> try omega
    · right; left
      ext i
      rcases i with ⟨_|_|x, hx⟩
      · have h_eq0 : (⟨0, hx⟩ : Fin 2) = ⟨0, h1⟩ := rfl
        rw [h_eq0]
        exact hi1
      · have h_eq1 : (⟨1, hx⟩ : Fin 2) = ⟨1, h2⟩ := rfl
        rw [h_eq1]
        exact hi2
      · omega
    · right; right
      ext i
      rcases i with ⟨_|_|x, hx⟩
      · have h_eq0 : (⟨0, hx⟩ : Fin 2) = ⟨0, h2⟩ := rfl
        rw [h_eq0]
        exact hi2
      · have h_eq1 : (⟨1, hx⟩ : Fin 2) = ⟨1, h1⟩ := rfl
        rw [h_eq1]
        exact hi1
      · omega

lemma S_subset_F_step (n : ℕ) (ih_n : ∀ σ ∈ S_aux n, σ ∈ F n) (ih_n1 : ∀ σ ∈ S_aux (n+1), σ ∈ F (n+1))
    (σ : Fin (n + 3) → ℕ) (hσ : σ ∈ S_aux (n+2)) : σ ∈ F (n+2) := by
  obtain ⟨h_pos, h_cov, h_dec⟩ := hσ
  have h_last : σ ⟨n + 2, by omega⟩ = 1 ∨ σ ⟨n + 2, by omega⟩ ≥ 2 := by
    have := h_pos ⟨n + 2, by omega⟩
    omega
  rcases h_last with h_last1 | h_last2
  · let τ : Fin (n + 2) → ℕ := fun i => σ ⟨i.val, by omega⟩
    by_cases h_one : ∃ i : Fin (n + 2), τ i = 1
    · have h_τ_S : τ ∈ S_aux (n + 1) := by
        refine ⟨?_, ?_, ?_⟩
        · intro i; exact h_pos ⟨i.val, by omega⟩
        · have h_sup : Finset.sup Finset.univ σ = Finset.sup Finset.univ τ := by
            apply LE.le.antisymm
            · apply Finset.sup_le
              intro i _
              by_cases hi : i.val < n + 2
              · have h_in : ⟨i.val, hi⟩ ∈ (Finset.univ : Finset (Fin (n+2))) := Finset.mem_univ _
                exact Finset.le_sup h_in (f := τ)
              · have : i.val = n + 2 := by omega
                have h_i0 : i = ⟨n + 2, by omega⟩ := by ext; exact this
                rw [h_i0, h_last1]
                rcases h_one with ⟨i0, hi0⟩
                have h_in : i0 ∈ (Finset.univ : Finset (Fin (n+2))) := Finset.mem_univ _
                have h_le := Finset.le_sup h_in (f := τ)
                omega
            · apply Finset.sup_le
              intro i _
              have h_in : ⟨i.val, by omega⟩ ∈ (Finset.univ : Finset (Fin (n+3))) := Finset.mem_univ _
              exact Finset.le_sup h_in (f := σ)
          intro k hk
          rw [← h_sup] at hk
          obtain ⟨i0, hi0⟩ := h_cov k hk
          by_cases hi0_lt : i0.val < n + 2
          · use ⟨i0.val, hi0_lt⟩
          · have : i0.val = n + 2 := by omega
            have h_i0_eq : i0 = ⟨n + 2, by omega⟩ := by ext; exact this
            rw [h_i0_eq] at hi0
            rw [hi0] at h_last1
            rcases h_one with ⟨i1, hi1⟩
            use i1
            omega
        · intro i j hij h_nonadj
          have hij0 : (⟨i.val, by omega⟩ : Fin (n+3)) < ⟨j.val, by omega⟩ := hij
          have h_nonadj0 : (⟨j.val, by omega⟩ : Fin (n+3)).val ≠ (⟨i.val, by omega⟩ : Fin (n+3)).val + 1 := h_nonadj
          exact h_dec ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij0 h_nonadj0
      have h_in_F := ih_n1 τ h_τ_S
      dsimp [F]
      simp only [Finset.mem_union, Finset.mem_map]
      left; left; left
      use τ
      refine ⟨h_in_F, ?_⟩
      ext x
      dsimp [emb_A, map_A, append_val]
      split_ifs with h
      · rfl
      · have : x.val = n + 2 := by omega
        have h_x : x = ⟨n + 2, by omega⟩ := by ext; exact this
        rw [h_x, h_last1]
    · have h_τ_ge : ∀ i : Fin (n + 2), τ i ≥ 2 := by
        intro i
        have h_pos_i := h_pos ⟨i.val, by omega⟩
        have h_ne : τ i ≠ 1 := by
          intro h_eq
          exact h_one ⟨i, h_eq⟩
        dsimp [τ] at *
        omega
      let τ' : Fin (n + 2) → ℕ := fun i => τ i - 1
      have h_τ'_S : τ' ∈ S_aux (n + 1) := by
        refine ⟨?_, ?_, ?_⟩
        · intro i; dsimp [τ']; have := h_τ_ge i; omega
        · have h_sup_τ : Finset.sup Finset.univ τ = Finset.sup Finset.univ τ' + 1 := by
            have h_τ_eq : τ = fun i => τ' i + 1 := by
              ext i
              dsimp [τ']
              have := h_τ_ge i
              omega
            rw [h_τ_eq]
            apply sup_add_one (by omega) τ'
          have h_sup_σ : Finset.sup Finset.univ σ = Finset.sup Finset.univ τ := by
            apply LE.le.antisymm
            · apply Finset.sup_le
              intro i _
              by_cases hi : i.val < n + 2
              · have h_in : ⟨i.val, hi⟩ ∈ (Finset.univ : Finset (Fin (n+2))) := Finset.mem_univ _
                exact Finset.le_sup h_in (f := τ)
              · have : i.val = n + 2 := by omega
                have h_i0 : i = ⟨n + 2, by omega⟩ := by ext; exact this
                rw [h_i0, h_last1]
                have h_in : ⟨0, by omega⟩ ∈ (Finset.univ : Finset (Fin (n+2))) := Finset.mem_univ _
                have h_le := Finset.le_sup h_in (f := τ)
                have := h_τ_ge ⟨0, by omega⟩
                omega
            · apply Finset.sup_le
              intro i _
              have h_in : ⟨i.val, by omega⟩ ∈ (Finset.univ : Finset (Fin (n+3))) := Finset.mem_univ _
              exact Finset.le_sup h_in (f := σ)
          intro k hk
          have hk_cov : 1 ≤ k + 1 ∧ k + 1 ≤ Finset.sup Finset.univ σ := by
            rw [h_sup_σ, h_sup_τ]
            omega
          obtain ⟨i0, hi0⟩ := h_cov (k + 1) hk_cov
          by_cases hi0_lt : i0.val < n + 2
          · use ⟨i0.val, hi0_lt⟩
            dsimp [τ', τ]
            omega
          · have : i0.val = n + 2 := by omega
            have h_i0_eq : i0 = ⟨n + 2, by omega⟩ := by ext; exact this
            rw [h_i0_eq] at hi0
            rw [h_last1] at hi0
            omega
        · intro i j hij h_nonadj
          have hij0 : (⟨i.val, by omega⟩ : Fin (n+3)) < ⟨j.val, by omega⟩ := hij
          have h_nonadj0 : (⟨j.val, by omega⟩ : Fin (n+3)).val ≠ (⟨i.val, by omega⟩ : Fin (n+3)).val + 1 := h_nonadj
          have h_dec0 := h_dec ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij0 h_nonadj0
          dsimp [τ', τ]
          omega
      have h_in_F := ih_n1 τ' h_τ'_S
      dsimp [F]
      simp only [Finset.mem_union, Finset.mem_map]
      left; left; right
      use τ'
      refine ⟨h_in_F, ?_⟩
      ext x
      dsimp [emb_B, map_B, append_val]
      split_ifs with h
      · have h_ge := h_τ_ge ⟨x.val, h⟩
        dsimp [τ] at h_ge
        dsimp [τ', τ]
        omega
      · have : x.val = n + 2 := by omega
        have h_x : x = ⟨n + 2, by omega⟩ := by ext; exact this
        rw [h_x, h_last1]
  · have h_n1_eq : σ ⟨n + 1, by omega⟩ = 1 := by
      by_contra h_ne
      have h_all : ∀ i : Fin (n+3), σ i ≠ 1 := by
        intro i
        by_cases hi1 : i.val < n + 1
        · have hij : i.val < n + 2 := by omega
          have h_nonadj0 : n + 2 ≠ i.val + 1 := by omega
          have h_dec0 := h_dec i ⟨n + 2, by omega⟩ hij h_nonadj0
          omega
        · by_cases hi2 : i.val = n + 1
          · have h_eq : i = ⟨n + 1, by omega⟩ := by ext; exact hi2
            rw [h_eq]
            exact h_ne
          · have h_val : i.val = n + 2 := by omega
            have h_eq : i = ⟨n + 2, by omega⟩ := Fin.ext h_val
            have : σ i = σ ⟨n + 2, by omega⟩ := by rw [h_eq]
            rw [this]
            omega
      have h_sup : Finset.sup Finset.univ σ ≥ 2 := by
        have h_in : ⟨n+2, by omega⟩ ∈ (Finset.univ : Finset (Fin (n+3))) := Finset.mem_univ _
        have h_le := Finset.le_sup h_in (f := σ)
        omega
      have h_cov1 := h_cov 1 (by omega)
      rcases h_cov1 with ⟨i0, hi0⟩
      exact h_all i0 hi0
    have h_last_eq : σ ⟨n + 2, by omega⟩ = 2 := by
      by_contra h_ne
      have h_all : ∀ i : Fin (n+3), σ i ≠ 2 := by
        intro i
        by_cases hi1 : i.val < n + 1
        · have hij : i.val < n + 2 := by omega
          have h_nonadj0 : n + 2 ≠ i.val + 1 := by omega
          have h_dec0 := h_dec i ⟨n + 2, by omega⟩ hij h_nonadj0
          omega
        · by_cases hi2 : i.val = n + 1
          · have h_eq : i = ⟨n + 1, by omega⟩ := by ext; exact hi2
            rw [h_eq, h_n1_eq]
            omega
          · have h_val : i.val = n + 2 := by omega
            have h_eq : i = ⟨n + 2, by omega⟩ := Fin.ext h_val
            have : σ i = σ ⟨n + 2, by omega⟩ := by rw [h_eq]
            rw [this]
            omega
      have h_sup : Finset.sup Finset.univ σ ≥ 3 := by
        have h_in : ⟨n+2, by omega⟩ ∈ (Finset.univ : Finset (Fin (n+3))) := Finset.mem_univ _
        have h_le := Finset.le_sup h_in (f := σ)
        omega
      have h_cov2 := h_cov 2 (by omega)
      rcases h_cov2 with ⟨i0, hi0⟩
      exact h_all i0 hi0
    let τ : Fin (n + 1) → ℕ := fun i => σ ⟨i.val, by omega⟩
    have h_τ_ge : ∀ i : Fin (n + 1), τ i ≥ 2 := by
      intro i
      dsimp [τ]
      have hij : i.val < n + 2 := by omega
      have h_nonadj0 : n + 2 ≠ i.val + 1 := by omega
      have h_dec0 := h_dec ⟨i.val, by omega⟩ ⟨n + 2, by omega⟩ hij h_nonadj0
      rw [h_last_eq] at h_dec0
      exact h_dec0
    by_cases h_two : ∃ i : Fin (n + 1), τ i = 2
    · let τ' : Fin (n + 1) → ℕ := fun i => τ i - 1
      have h_τ'_S : τ' ∈ S_aux n := by
        refine ⟨?_, ?_, ?_⟩
        · intro i; dsimp [τ']; have := h_τ_ge i; omega
        · have h_sup_τ : Finset.sup Finset.univ τ = Finset.sup Finset.univ τ' + 1 := by
            have h_τ_eq : τ = fun i => τ' i + 1 := by
              ext i
              dsimp [τ']
              have := h_τ_ge i
              omega
            rw [h_τ_eq]
            apply sup_add_one (by omega) τ'
          have h_sup_σ : Finset.sup Finset.univ σ = Finset.sup Finset.univ τ := by
            apply LE.le.antisymm
            · apply Finset.sup_le
              intro i _
              by_cases hi : i.val < n + 1
              · have h_in : ⟨i.val, hi⟩ ∈ (Finset.univ : Finset (Fin (n+1))) := Finset.mem_univ _
                exact Finset.le_sup h_in (f := τ)
              · by_cases hi2 : i.val = n + 1
                · have h_eq : i = ⟨n + 1, by omega⟩ := by ext; exact hi2
                  rw [h_eq, h_n1_eq]
                  have := h_τ_ge ⟨0, by omega⟩
                  have h_in : ⟨0, by omega⟩ ∈ (Finset.univ : Finset (Fin (n+1))) := Finset.mem_univ _
                  have h_le := Finset.le_sup h_in (f := τ)
                  omega
                · have : i.val = n + 2 := by omega
                  have h_eq : i = ⟨n + 2, by omega⟩ := by ext; exact this
                  rw [h_eq, h_last_eq]
                  have := h_τ_ge ⟨0, by omega⟩
                  have h_in : ⟨0, by omega⟩ ∈ (Finset.univ : Finset (Fin (n+1))) := Finset.mem_univ _
                  have h_le := Finset.le_sup h_in (f := τ)
                  omega
            · apply Finset.sup_le
              intro i _
              have h_in : ⟨i.val, by omega⟩ ∈ (Finset.univ : Finset (Fin (n+3))) := Finset.mem_univ _
              exact Finset.le_sup h_in (f := σ)
          intro k hk
          have hk_cov : 1 ≤ k + 1 ∧ k + 1 ≤ Finset.sup Finset.univ σ := by
            rw [h_sup_σ, h_sup_τ]
            omega
          obtain ⟨i0, hi0⟩ := h_cov (k + 1) hk_cov
          by_cases hi0_lt : i0.val < n + 1
          · use ⟨i0.val, hi0_lt⟩
            dsimp [τ', τ]
            omega
          · by_cases hi0_eq : i0.val = n + 1
            · have h_eq : i0 = ⟨n + 1, by omega⟩ := by ext; exact hi0_eq
              rw [h_eq, h_n1_eq] at hi0
              omega
            · have : i0.val = n + 2 := by omega
              have h_eq : i0 = ⟨n + 2, by omega⟩ := by ext; exact this
              rw [h_eq, h_last_eq] at hi0
              rcases h_two with ⟨i2, hi2⟩
              use i2
              dsimp [τ']
              rw [hi2]
              omega
        · intro i j hij h_nonadj
          have hij0 : (⟨i.val, by omega⟩ : Fin (n+3)) < ⟨j.val, by omega⟩ := hij
          have h_nonadj0 : (⟨j.val, by omega⟩ : Fin (n+3)).val ≠ (⟨i.val, by omega⟩ : Fin (n+3)).val + 1 := h_nonadj
          have h_dec0 := h_dec ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij0 h_nonadj0
          dsimp [τ', τ]
          omega
      have h_in_F := ih_n τ' h_τ'_S
      dsimp [F]
      simp only [Finset.mem_union, Finset.mem_map]
      left; right
      use τ'
      refine ⟨h_in_F, ?_⟩
      ext x
      dsimp [emb_C, map_C, append_two_vals]
      split_ifs with h1 h2
      · have h_ge := h_τ_ge ⟨x.val, h1⟩
        dsimp [τ] at h_ge
        dsimp [τ', τ]
        omega
      · have : x.val = n + 1 := by omega
        have h_x : x = ⟨n + 1, by omega⟩ := by ext; exact this
        rw [h_x, h_n1_eq]
      · have : x.val = n + 2 := by omega
        have h_x : x = ⟨n + 2, by omega⟩ := by ext; exact this
        rw [h_x, h_last_eq]
    · have h_τ_ge3 : ∀ i : Fin (n + 1), τ i ≥ 3 := by
        intro i
        have := h_τ_ge i
        have h_ne : τ i ≠ 2 := by
          intro h_eq
          exact h_two ⟨i, h_eq⟩
        dsimp [τ] at *
        omega
      let τ' : Fin (n + 1) → ℕ := fun i => τ i - 2
      have h_τ'_S : τ' ∈ S_aux n := by
        refine ⟨?_, ?_, ?_⟩
        · intro i; dsimp [τ']; have := h_τ_ge3 i; omega
        · have h_sup_τ : Finset.sup Finset.univ τ = Finset.sup Finset.univ τ' + 2 := by
            have h_τ_eq : τ = fun i => τ' i + 2 := by
              ext i
              dsimp [τ']
              have := h_τ_ge3 i
              omega
            rw [h_τ_eq]
            apply sup_add_two (by omega) τ'
          have h_sup_σ : Finset.sup Finset.univ σ = Finset.sup Finset.univ τ := by
            apply LE.le.antisymm
            · apply Finset.sup_le
              intro i _
              by_cases hi : i.val < n + 1
              · have h_in : ⟨i.val, hi⟩ ∈ (Finset.univ : Finset (Fin (n+1))) := Finset.mem_univ _
                exact Finset.le_sup h_in (f := τ)
              · by_cases hi2 : i.val = n + 1
                · have h_eq : i = ⟨n + 1, by omega⟩ := by ext; exact hi2
                  rw [h_eq, h_n1_eq]
                  have := h_τ_ge ⟨0, by omega⟩
                  have h_in : ⟨0, by omega⟩ ∈ (Finset.univ : Finset (Fin (n+1))) := Finset.mem_univ _
                  have h_le := Finset.le_sup h_in (f := τ)
                  omega
                · have : i.val = n + 2 := by omega
                  have h_eq : i = ⟨n + 2, by omega⟩ := by ext; exact this
                  rw [h_eq, h_last_eq]
                  have := h_τ_ge ⟨0, by omega⟩
                  have h_in : ⟨0, by omega⟩ ∈ (Finset.univ : Finset (Fin (n+1))) := Finset.mem_univ _
                  have h_le := Finset.le_sup h_in (f := τ)
                  omega
            · apply Finset.sup_le
              intro i _
              have h_in : ⟨i.val, by omega⟩ ∈ (Finset.univ : Finset (Fin (n+3))) := Finset.mem_univ _
              exact Finset.le_sup h_in (f := σ)
          intro k hk
          have hk_cov : 1 ≤ k + 2 ∧ k + 2 ≤ Finset.sup Finset.univ σ := by
            rw [h_sup_σ, h_sup_τ]
            omega
          obtain ⟨i0, hi0⟩ := h_cov (k + 2) hk_cov
          by_cases hi0_lt : i0.val < n + 1
          · use ⟨i0.val, hi0_lt⟩
            dsimp [τ', τ]
            omega
          · by_cases hi0_eq : i0.val = n + 1
            · have h_eq : i0 = ⟨n + 1, by omega⟩ := by ext; exact hi0_eq
              rw [h_eq, h_n1_eq] at hi0
              omega
            · have : i0.val = n + 2 := by omega
              have h_eq : i0 = ⟨n + 2, by omega⟩ := by ext; exact this
              rw [h_eq, h_last_eq] at hi0
              omega
        · intro i j hij h_nonadj
          have hij0 : (⟨i.val, by omega⟩ : Fin (n+3)) < ⟨j.val, by omega⟩ := hij
          have h_nonadj0 : (⟨j.val, by omega⟩ : Fin (n+3)).val ≠ (⟨i.val, by omega⟩ : Fin (n+3)).val + 1 := h_nonadj
          have h_dec0 := h_dec ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij0 h_nonadj0
          dsimp [τ', τ]
          omega
      have h_in_F := ih_n τ' h_τ'_S
      dsimp [F]
      simp only [Finset.mem_union, Finset.mem_map]
      right
      use τ'
      refine ⟨h_in_F, ?_⟩
      ext x
      dsimp [emb_D, map_D, append_two_vals]
      split_ifs with h1 h2
      · have h_ge := h_τ_ge3 ⟨x.val, h1⟩
        dsimp [τ] at h_ge
        dsimp [τ', τ]
        omega
      · have : x.val = n + 1 := by omega
        have h_x : x = ⟨n + 1, by omega⟩ := by ext; exact this
        rw [h_x, h_n1_eq]
      · have : x.val = n + 2 := by omega
        have h_x : x = ⟨n + 2, by omega⟩ := by ext; exact this
        rw [h_x, h_last_eq]

lemma S_subset_F (n : ℕ) : ∀ σ ∈ S_aux n, σ ∈ F n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | n
  · intro σ hσ; exact S_subset_F_zero σ hσ
  · intro σ hσ; exact S_subset_F_one σ hσ
  · intro σ hσ
    have ih1 := ih (n + 1) (by omega)
    have ih2 := ih n (by omega)
    exact S_subset_F_step n ih2 ih1 σ hσ

theorem oeis_A028859_conjecture_1 (n : ℕ) :
  let L := n + 1
  let Sequence := Fin L → ℕ
  let S : Set Sequence :=
    { σ : Sequence |
      L > 0 ∧ -- L = n + 1 ensures this is true for n ≥ 0
      (∀ i : Fin L, σ i > 0) ∧ -- All elements are positive integers
      -- Property 1: Covers initial interval
      let max_val := Finset.sup Finset.univ σ -- max value exists since Fin L is finite and non-empty
      (∀ k : ℕ, 1 ≤ k ∧ k ≤ max_val → ∃ i : Fin L, σ i = k) ∧
      -- Property 2: Non-adjacent parts are weakly decreasing
      (∀ i j : Fin L, i < j → j.val ≠ i.val + 1 → σ i ≥ σ j)
    }
  -- The set S is finite. We state the conjecture as the existence of a finset F
  -- corresponding to S with the correct cardinality, which is the standard way to relate set
  -- size to a natural number when the Fintype instance is not trivial.
  ∃ (F : Finset Sequence), F.toSet = S ∧ F.card = a n
:= by
  use F n
  refine ⟨?_, F_card n⟩
  ext σ
  simp only [Finset.mem_coe]
  constructor
  · intro hσ
    have h_aux := F_subset_S n σ hσ
    refine ⟨by omega, h_aux⟩
  · intro hσ
    obtain ⟨hL, h_aux⟩ := hσ
    exact S_subset_F n σ h_aux
