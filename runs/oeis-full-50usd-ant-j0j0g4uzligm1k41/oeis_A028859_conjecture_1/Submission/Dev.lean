import FormalConjectures.Util.ProblemImports

open Finset

namespace A028859

/-- Validity predicate matching the problem's set membership. -/
def Valid {L : ℕ} (σ : Fin L → ℕ) : Prop :=
  (∀ i, 0 < σ i) ∧
  (∀ k, 1 ≤ k → k ≤ Finset.univ.sup σ → ∃ i, σ i = k) ∧
  (∀ i j : Fin L, i < j → (j : ℕ) ≠ (i : ℕ) + 1 → σ j ≤ σ i)

/-- sup over `Fin (m+1)` of a `cons`. -/
lemma sup_cons {m : ℕ} (v : ℕ) (τ : Fin m → ℕ) :
    Finset.univ.sup (Fin.cons v τ : Fin (m+1) → ℕ) = v ⊔ Finset.univ.sup τ := by
  rw [Fin.univ_succ, Finset.sup_cons, Finset.sup_map]
  have : (Fin.cons v τ ∘ Fin.succ) = τ := by ext i; simp
  simp [this]

/-- sup of tail ≤ sup. -/
lemma sup_tail_le {L : ℕ} (σ : Fin (L+1) → ℕ) :
    Finset.univ.sup (Fin.tail σ) ≤ Finset.univ.sup σ := by
  apply Finset.sup_le
  intro i _
  exact Finset.le_sup (Finset.mem_univ (Fin.succ i))

lemma le_sup' {L : ℕ} (σ : Fin L → ℕ) (i : Fin L) : σ i ≤ Finset.univ.sup σ :=
  Finset.le_sup (Finset.mem_univ i)

end A028859

namespace A028859

lemma valid_sup_le {L : ℕ} (σ : Fin L → ℕ) (h : Valid σ) :
    Finset.univ.sup σ ≤ L := by
  obtain ⟨hpos, hcov, hmono⟩ := h
  set M := Finset.univ.sup σ with hM
  have key : ∀ j : Fin M, ∃ i : Fin L, σ i = (j:ℕ) + 1 := by
    intro j
    have h1 : 1 ≤ (j:ℕ)+1 := Nat.succ_le_succ (Nat.zero_le _)
    have h2 : (j:ℕ)+1 ≤ M := by have := j.isLt; omega
    exact hcov _ h1 h2
  choose f hf using key
  have finj : Function.Injective f := by
    intro a b hab
    have e1 : ((a:ℕ)+1) = ((b:ℕ)+1) := by rw [← hf a, ← hf b, hab]
    exact Fin.ext (by omega)
  have := Fintype.card_le_of_injective f finj
  simpa using this

lemma valid_le_L {L : ℕ} (σ : Fin L → ℕ) (h : Valid σ) (i : Fin L) : σ i ≤ L :=
  le_trans (le_sup' σ i) (valid_sup_le σ h)

lemma sv_finite (L : ℕ) : {σ : Fin L → ℕ | Valid σ}.Finite := by
  apply Set.Finite.subset (Set.Finite.pi' (fun _ : Fin L => Set.finite_Iic L))
  intro σ hσ i
  simp only [Set.mem_Iic]
  exact valid_le_L σ hσ i

end A028859

namespace A028859

/-- For a valid non-ascent sequence, the head is the maximum. -/
lemma head_is_max {L : ℕ} (σ : Fin (L+2) → ℕ) (h : Valid σ) (hna : σ 1 ≤ σ 0) :
    ∀ j, σ j ≤ σ 0 := by
  intro j
  obtain ⟨hpos, hcov, hmono⟩ := h
  rcases eq_or_ne (j : ℕ) 0 with hj | hj
  · have : j = 0 := Fin.ext hj
    rw [this]
  · rcases eq_or_ne (j : ℕ) 1 with hj1 | hj1
    · have : j = 1 := Fin.ext (by simpa using hj1)
      rw [this]; exact hna
    · have h0 : ((0 : Fin (L+2)):ℕ) = 0 := by simp
      have h0j : (0 : Fin (L+2)) < j := by rw [Fin.lt_def]; omega
      exact hmono 0 j h0j (by omega)

lemma head_eq_sup {L : ℕ} (σ : Fin (L+2) → ℕ) (h : Valid σ) (hna : σ 1 ≤ σ 0) :
    σ 0 = Finset.univ.sup σ :=
  le_antisymm (le_sup' σ 0) (Finset.sup_le (fun j _ => head_is_max σ h hna j))

end A028859

namespace A028859

/-- Dropping the maximal head from a valid sequence yields a valid sequence. -/
lemma tail_valid {L : ℕ} (σ : Fin (L+1) → ℕ) (h : Valid σ) (hmax : ∀ j, σ j ≤ σ 0) :
    Valid (Fin.tail σ) := by
  obtain ⟨hpos, hcov, hmono⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro i; exact hpos _
  · intro k hk1 hk2
    have hle : Finset.univ.sup (Fin.tail σ) ≤ Finset.univ.sup σ := sup_tail_le σ
    have hk2' : k ≤ Finset.univ.sup σ := le_trans hk2 hle
    obtain ⟨p, hp⟩ := hcov k hk1 hk2'
    rcases Fin.eq_zero_or_eq_succ p with hp0 | ⟨p', hp'⟩
    · subst hp0
      have hsσ : Finset.univ.sup σ ≤ σ 0 := Finset.sup_le (fun j _ => hmax j)
      have heq : Finset.univ.sup (Fin.tail σ) = k := by
        have hle2 : Finset.univ.sup (Fin.tail σ) ≤ k :=
          le_trans hle (le_trans hsσ (le_of_eq hp))
        omega
      have hpos2 : 0 < Finset.univ.sup (Fin.tail σ) := by omega
      have hne : (Finset.univ : Finset (Fin L)).Nonempty := by
        rcases (Finset.univ : Finset (Fin L)).eq_empty_or_nonempty with he | hne
        · rw [he] at hpos2; simp at hpos2
        · exact hne
      obtain ⟨q, _, hq⟩ := Finset.exists_mem_eq_sup Finset.univ hne (Fin.tail σ)
      exact ⟨q, by rw [← hq, heq]⟩
    · subst hp'
      exact ⟨p', hp⟩
  · intro i j hij hjne
    have hs : Fin.succ i < Fin.succ j := Fin.succ_lt_succ_iff.mpr hij
    have hcond : (Fin.succ j : ℕ) ≠ (Fin.succ i : ℕ) + 1 := by
      simp only [Fin.val_succ]; omega
    exact hmono (Fin.succ i) (Fin.succ j) hs hcond

end A028859

namespace A028859

/-- Prepending a value `v` with `sup τ ≤ v ≤ sup τ + 1` to a valid sequence is valid. -/
lemma prepend1 {m : ℕ} (τ : Fin (m+1) → ℕ) (h : Valid τ) (v : ℕ)
    (hlo : Finset.univ.sup τ ≤ v) (hhi : v ≤ Finset.univ.sup τ + 1) :
    Valid (Fin.cons v τ : Fin (m+2) → ℕ) := by
  obtain ⟨hpos, hcov, hmono⟩ := h
  set S := Finset.univ.sup τ with hS
  have hsupv : Finset.univ.sup (Fin.cons v τ : Fin (m+2) → ℕ) = v := by
    rw [sup_cons]; exact sup_eq_left.mpr hlo
  have hSpos : 1 ≤ S := le_trans (hpos 0) (le_sup' τ 0)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · rw [Fin.cons_zero]; omega
    · rw [Fin.cons_succ]; exact hpos i'
  · intro k hk1 hk2
    rw [hsupv] at hk2
    by_cases hkS : k ≤ S
    · obtain ⟨j, hj⟩ := hcov k hk1 hkS
      exact ⟨Fin.succ j, by rw [Fin.cons_succ]; exact hj⟩
    · push_neg at hkS
      exact ⟨0, by rw [Fin.cons_zero]; omega⟩
  · intro i j hij hjne
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact absurd hij (lt_irrefl _)
      · rw [Fin.cons_zero, Fin.cons_succ]
        exact le_trans (le_sup' τ j') hlo
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact absurd hij (by simp [Fin.lt_def])
      · rw [Fin.cons_succ, Fin.cons_succ]
        have hij' : i' < j' := Fin.succ_lt_succ_iff.mp hij
        have hjne' : (j' : ℕ) ≠ (i' : ℕ) + 1 := by
          have hh : (Fin.succ j' : ℕ) ≠ (Fin.succ i' : ℕ) + 1 := hjne
          simp only [Fin.val_succ] at hh; omega
        exact hmono i' j' hij' hjne'

end A028859

namespace A028859

/-- Prepending `v` then `v+1` (with `sup υ ≤ v ≤ sup υ + 1`) to a valid sequence is valid. -/
lemma prepend2 {m : ℕ} (υ : Fin (m+1) → ℕ) (h : Valid υ) (v : ℕ)
    (hlo : Finset.univ.sup υ ≤ v) (hhi : v ≤ Finset.univ.sup υ + 1) :
    Valid (Fin.cons v (Fin.cons (v+1) υ) : Fin (m+3) → ℕ) := by
  obtain ⟨hpos, hcov, hmono⟩ := h
  set S := Finset.univ.sup υ with hS
  have hSpos : 1 ≤ S := le_trans (hpos 0) (le_sup' υ 0)
  have hsupv : Finset.univ.sup (Fin.cons v (Fin.cons (v+1) υ) : Fin (m+3) → ℕ) = v + 1 := by
    rw [sup_cons, sup_cons]
    have h1 : (v+1) ⊔ S = v+1 := sup_eq_left.mpr (le_trans hlo (Nat.le_succ v))
    rw [h1]; exact sup_eq_right.mpr (Nat.le_succ v)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i1, rfl⟩
    · rw [Fin.cons_zero]; omega
    · rw [Fin.cons_succ]
      rcases Fin.eq_zero_or_eq_succ i1 with rfl | ⟨i2, rfl⟩
      · rw [Fin.cons_zero]; omega
      · rw [Fin.cons_succ]; exact hpos i2
  · intro k hk1 hk2
    rw [hsupv] at hk2
    by_cases hkS : k ≤ S
    · obtain ⟨j, hj⟩ := hcov k hk1 hkS
      exact ⟨Fin.succ (Fin.succ j), by rw [Fin.cons_succ, Fin.cons_succ]; exact hj⟩
    · push_neg at hkS
      by_cases hkv : k = v
      · exact ⟨0, by rw [Fin.cons_zero]; omega⟩
      · exact ⟨Fin.succ 0, by rw [Fin.cons_succ, Fin.cons_zero]; omega⟩
  · intro i j hij hjne
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j1, rfl⟩
    · exact absurd hij (by simp [Fin.lt_def])
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i1, rfl⟩
      · rcases Fin.eq_zero_or_eq_succ j1 with rfl | ⟨j2, rfl⟩
        · simp at hjne
        · simp only [Fin.cons_zero, Fin.cons_succ]
          exact le_trans (le_sup' υ j2) hlo
      · have hi1j1 : i1 < j1 := Fin.succ_lt_succ_iff.mp hij
        rcases Fin.eq_zero_or_eq_succ i1 with rfl | ⟨i2, rfl⟩
        · rcases Fin.eq_zero_or_eq_succ j1 with rfl | ⟨j2, rfl⟩
          · exact absurd hi1j1 (lt_irrefl _)
          · simp only [Fin.cons_zero, Fin.cons_succ]
            exact le_trans (le_trans (le_sup' υ j2) hlo) (Nat.le_succ v)
        · rcases Fin.eq_zero_or_eq_succ j1 with rfl | ⟨j2, rfl⟩
          · exact absurd hi1j1 (by simp [Fin.lt_def])
          · simp only [Fin.cons_succ]
            have hi2j2 : i2 < j2 := Fin.succ_lt_succ_iff.mp hi1j1
            have hjne' : (j2 : ℕ) ≠ (i2 : ℕ) + 1 := by
              have hh : (Fin.succ (Fin.succ j2) : ℕ) ≠ (Fin.succ (Fin.succ i2) : ℕ) + 1 := hjne
              simp only [Fin.val_succ] at hh; omega
            exact hmono i2 j2 hi2j2 hjne'

end A028859

namespace A028859

/-- Dropping the top two elements (the max and one below) from a valid ascent sequence is valid. -/
lemma drop2_valid {L : ℕ} (σ : Fin (L+2) → ℕ) (h : Valid σ) (hasc : σ 0 < σ 1) :
    Valid (Fin.tail (Fin.tail σ)) := by
  obtain ⟨hpos, hcov, hmono⟩ := h
  have h0 : ((0 : Fin (L+2)):ℕ) = 0 := by simp
  have hsup2_le0 : Finset.univ.sup (Fin.tail (Fin.tail σ)) ≤ σ 0 := by
    apply Finset.sup_le
    intro i _
    show σ (Fin.succ (Fin.succ i)) ≤ σ 0
    apply hmono 0 (Fin.succ (Fin.succ i))
    · rw [Fin.lt_def]; simp [Fin.val_succ]
    · simp only [Fin.val_succ]; omega
  refine ⟨?_, ?_, ?_⟩
  · intro i; exact hpos _
  · intro k hk1 hk2
    have hle : Finset.univ.sup (Fin.tail (Fin.tail σ)) ≤ Finset.univ.sup σ :=
      le_trans (sup_tail_le (Fin.tail σ)) (sup_tail_le σ)
    have hk2' : k ≤ Finset.univ.sup σ := le_trans hk2 hle
    obtain ⟨p, hp⟩ := hcov k hk1 hk2'
    rcases Fin.eq_zero_or_eq_succ p with hp0 | ⟨p', hpp⟩
    · subst hp0
      have heq : Finset.univ.sup (Fin.tail (Fin.tail σ)) = k := by
        have hb : Finset.univ.sup (Fin.tail (Fin.tail σ)) ≤ k :=
          le_trans hsup2_le0 (le_of_eq hp)
        omega
      have hpos2 : 0 < Finset.univ.sup (Fin.tail (Fin.tail σ)) := by omega
      have hne : (Finset.univ : Finset (Fin L)).Nonempty := by
        rcases (Finset.univ : Finset (Fin L)).eq_empty_or_nonempty with he | hne
        · rw [he] at hpos2; simp at hpos2
        · exact hne
      obtain ⟨q, _, hq⟩ := Finset.exists_mem_eq_sup Finset.univ hne (Fin.tail (Fin.tail σ))
      exact ⟨q, by rw [← hq, heq]⟩
    · subst hpp
      rcases Fin.eq_zero_or_eq_succ p' with hp'0 | ⟨p'', hp''⟩
      · subst hp'0
        exfalso
        have hb : k ≤ σ 0 := le_trans hk2 hsup2_le0
        have hs1 : (Fin.succ (0 : Fin (L+1)) : Fin (L+2)) = 1 := by ext; simp
        rw [hs1] at hp
        omega
      · subst hp''
        exact ⟨p'', hp⟩
  · intro i j hij hjne
    show σ (Fin.succ (Fin.succ j)) ≤ σ (Fin.succ (Fin.succ i))
    apply hmono (Fin.succ (Fin.succ i)) (Fin.succ (Fin.succ j))
    · exact Fin.succ_lt_succ_iff.mpr (Fin.succ_lt_succ_iff.mpr hij)
    · simp only [Fin.val_succ]; omega

end A028859

namespace A028859

/-- For any valid sequence, the sup of the tail-of-tail is ≤ the head. -/
lemma sup_tt_le_head {L : ℕ} (σ : Fin (L+2) → ℕ) (h : Valid σ) :
    Finset.univ.sup (Fin.tail (Fin.tail σ)) ≤ σ 0 := by
  obtain ⟨hpos, hcov, hmono⟩ := h
  have h0 : ((0 : Fin (L+2)):ℕ) = 0 := by simp
  apply Finset.sup_le
  intro i _
  show σ (Fin.succ (Fin.succ i)) ≤ σ 0
  apply hmono 0 (Fin.succ (Fin.succ i))
  · rw [Fin.lt_def]; simp [Fin.val_succ]
  · simp only [Fin.val_succ]; omega

/-- Non-ascent: head ≤ sup(tail) + 1. -/
lemma nonasc_head_le {L : ℕ} (σ : Fin (L+2) → ℕ) (h : Valid σ) (hna : σ 1 ≤ σ 0) :
    σ 0 ≤ Finset.univ.sup (Fin.tail σ) + 1 := by
  obtain ⟨hpos, hcov, hmono⟩ := h
  by_cases hM : σ 0 ≤ 1
  · have : 0 ≤ Finset.univ.sup (Fin.tail σ) := Nat.zero_le _
    omega
  · push_neg at hM
    have hMsup : σ 0 = Finset.univ.sup σ := head_eq_sup σ ⟨hpos, hcov, hmono⟩ hna
    have hk1 : 1 ≤ σ 0 - 1 := by omega
    have hk2 : σ 0 - 1 ≤ Finset.univ.sup σ := by rw [← hMsup]; omega
    obtain ⟨p, hp⟩ := hcov (σ 0 - 1) hk1 hk2
    rcases Fin.eq_zero_or_eq_succ p with hp0 | ⟨p', hpp⟩
    · subst hp0; omega
    · subst hpp
      have hge : σ 0 - 1 ≤ Finset.univ.sup (Fin.tail σ) := hp ▸ le_sup' (Fin.tail σ) p'
      omega

/-- Non-ascent: head equals sup(tail) or sup(tail)+1. -/
lemma nonasc_cases {L : ℕ} (σ : Fin (L+2) → ℕ) (h : Valid σ) (hna : σ 1 ≤ σ 0) :
    σ 0 = Finset.univ.sup (Fin.tail σ) ∨ σ 0 = Finset.univ.sup (Fin.tail σ) + 1 := by
  have hMsup : σ 0 = Finset.univ.sup σ := head_eq_sup σ h hna
  have hlo : Finset.univ.sup (Fin.tail σ) ≤ σ 0 := by rw [hMsup]; exact sup_tail_le σ
  have hhi : σ 0 ≤ Finset.univ.sup (Fin.tail σ) + 1 := nonasc_head_le σ h hna
  omega

/-- Ascent: σ 1 is the maximum. -/
lemma asc_head1_max {L : ℕ} (σ : Fin (L+2) → ℕ) (h : Valid σ) (hasc : σ 0 < σ 1) :
    ∀ j, σ j ≤ σ 1 := by
  intro j
  obtain ⟨hpos, hcov, hmono⟩ := h
  have h0 : ((0 : Fin (L+2)):ℕ) = 0 := by simp
  rcases eq_or_ne (j : ℕ) 0 with hj | hj
  · have hj' : j = 0 := Fin.ext hj
    rw [hj']; omega
  · rcases eq_or_ne (j : ℕ) 1 with hj1 | hj1
    · have hj1' : j = 1 := Fin.ext (by simpa using hj1)
      rw [hj1']
    · have h0j : (0 : Fin (L+2)) < j := by rw [Fin.lt_def]; omega
      have hle := hmono 0 j h0j (by omega)
      omega

/-- Ascent: σ 1 = σ 0 + 1. -/
lemma asc_succ {L : ℕ} (σ : Fin (L+2) → ℕ) (h : Valid σ) (hasc : σ 0 < σ 1) :
    σ 1 = σ 0 + 1 := by
  obtain ⟨hpos, hcov, hmono⟩ := h
  have hmax1 : σ 1 = Finset.univ.sup σ :=
    le_antisymm (le_sup' σ 1) (Finset.sup_le (fun j _ => asc_head1_max σ ⟨hpos,hcov,hmono⟩ hasc j))
  by_contra hne
  have hge : σ 1 ≥ σ 0 + 2 := by omega
  have hk1 : 1 ≤ σ 0 + 1 := by omega
  have hk2 : σ 0 + 1 ≤ Finset.univ.sup σ := by rw [← hmax1]; omega
  obtain ⟨p, hp⟩ := hcov (σ 0 + 1) hk1 hk2
  have h0 : ((0 : Fin (L+2)):ℕ) = 0 := by simp
  rcases Fin.eq_zero_or_eq_succ p with hp0 | ⟨p', hpp⟩
  · subst hp0; omega
  · subst hpp
    rcases Fin.eq_zero_or_eq_succ p' with hp'0 | ⟨p'', hp''⟩
    · subst hp'0
      have hs1 : (Fin.succ (0 : Fin (L+1)) : Fin (L+2)) = 1 := by ext; simp
      rw [hs1] at hp; omega
    · subst hp''
      have hle : σ (Fin.succ (Fin.succ p'')) ≤ σ 0 := by
        apply hmono 0 (Fin.succ (Fin.succ p''))
        · rw [Fin.lt_def]; simp [Fin.val_succ]
        · simp only [Fin.val_succ]; omega
      omega

/-- Ascent: head ≤ sup(tail-of-tail) + 1. -/
lemma asc_head_le {L : ℕ} (σ : Fin (L+2) → ℕ) (h : Valid σ) (hasc : σ 0 < σ 1) :
    σ 0 ≤ Finset.univ.sup (Fin.tail (Fin.tail σ)) + 1 := by
  obtain ⟨hpos, hcov, hmono⟩ := h
  have hsucc : σ 1 = σ 0 + 1 := asc_succ σ ⟨hpos,hcov,hmono⟩ hasc
  have hmax1 : σ 1 = Finset.univ.sup σ :=
    le_antisymm (le_sup' σ 1) (Finset.sup_le (fun j _ => asc_head1_max σ ⟨hpos,hcov,hmono⟩ hasc j))
  by_cases hM : σ 0 ≤ 1
  · have : 0 ≤ Finset.univ.sup (Fin.tail (Fin.tail σ)) := Nat.zero_le _
    omega
  · push_neg at hM
    have hk1 : 1 ≤ σ 0 - 1 := by omega
    have hk2 : σ 0 - 1 ≤ Finset.univ.sup σ := by rw [← hmax1]; omega
    obtain ⟨p, hp⟩ := hcov (σ 0 - 1) hk1 hk2
    have h0 : ((0 : Fin (L+2)):ℕ) = 0 := by simp
    rcases Fin.eq_zero_or_eq_succ p with hp0 | ⟨p', hpp⟩
    · subst hp0; omega
    · subst hpp
      rcases Fin.eq_zero_or_eq_succ p' with hp'0 | ⟨p'', hp''⟩
      · subst hp'0
        have hs1 : (Fin.succ (0 : Fin (L+1)) : Fin (L+2)) = 1 := by ext; simp
        rw [hs1] at hp; omega
      · subst hp''
        have hge : σ 0 - 1 ≤ Finset.univ.sup (Fin.tail (Fin.tail σ)) :=
          hp ▸ le_sup' (Fin.tail (Fin.tail σ)) p''
        omega

/-- Ascent: head equals sup(tail-of-tail) or that plus 1. -/
lemma asc_cases {L : ℕ} (σ : Fin (L+2) → ℕ) (h : Valid σ) (hasc : σ 0 < σ 1) :
    σ 0 = Finset.univ.sup (Fin.tail (Fin.tail σ)) ∨
    σ 0 = Finset.univ.sup (Fin.tail (Fin.tail σ)) + 1 := by
  have hlo : Finset.univ.sup (Fin.tail (Fin.tail σ)) ≤ σ 0 := sup_tt_le_head σ h
  have hhi : σ 0 ≤ Finset.univ.sup (Fin.tail (Fin.tail σ)) + 1 := asc_head_le σ h hasc
  omega

end A028859

namespace A028859

def Sset (L : ℕ) : Set (Fin L → ℕ) := {σ | Valid σ}

noncomputable def cnt (L : ℕ) : ℕ := (Sset L).ncard

lemma sset_finite (L : ℕ) : (Sset L).Finite := sv_finite L

/-- Non-ascent piece (parametrised by offset `b ∈ {0,1}`) has cardinality `cnt (N+2)`. -/
lemma ncard_nonasc_piece (N b : ℕ) (hb : b ≤ 1) :
    {σ : Fin (N+3) → ℕ |
       Valid σ ∧ σ 1 ≤ σ 0 ∧ σ 0 = Finset.univ.sup (Fin.tail σ) + b}.ncard
      = cnt (N+2) := by
  set P := {σ : Fin (N+3) → ℕ |
       Valid σ ∧ σ 1 ≤ σ 0 ∧ σ 0 = Finset.univ.sup (Fin.tail σ) + b} with hP
  have hInj : Set.InjOn (fun σ : Fin (N+3) → ℕ => Fin.tail σ) P := by
    intro σ hσ σ' hσ' he
    simp only at he
    have h00 : σ 0 = σ' 0 := by rw [hσ.2.2, hσ'.2.2, he]
    calc σ = Fin.cons (σ 0) (Fin.tail σ) := (Fin.cons_self_tail σ).symm
      _ = Fin.cons (σ' 0) (Fin.tail σ') := by rw [h00, he]
      _ = σ' := Fin.cons_self_tail σ'
  have hImg : (fun σ : Fin (N+3) → ℕ => Fin.tail σ) '' P = Sset (N+2) := by
    ext τ
    constructor
    · rintro ⟨σ, hσP, rfl⟩
      exact tail_valid σ hσP.1 (head_is_max σ hσP.1 hσP.2.1)
    · intro hτ
      refine ⟨Fin.cons (Finset.univ.sup τ + b) τ, ?_, ?_⟩
      · refine ⟨prepend1 τ hτ (Finset.univ.sup τ + b) (Nat.le_add_right _ _) (by omega), ?_, ?_⟩
        · have h1eq : (1 : Fin (N+3)) = Fin.succ (0 : Fin (N+2)) := by ext; simp
          rw [h1eq, Fin.cons_succ]
          exact le_trans (le_sup' τ 0) (Nat.le_add_right _ _)
        · rw [Fin.cons_zero, Fin.tail_cons]
      · simp only [Fin.tail_cons]
  have := Set.ncard_image_of_injOn hInj
  rw [hImg] at this
  rw [← this]
  rfl

end A028859

namespace A028859

/-- Ascent piece (parametrised by offset `b ∈ {0,1}`) has cardinality `cnt (N+1)`. -/
lemma ncard_asc_piece (N b : ℕ) (hb : b ≤ 1) :
    {σ : Fin (N+3) → ℕ |
       Valid σ ∧ σ 0 < σ 1 ∧ σ 0 = Finset.univ.sup (Fin.tail (Fin.tail σ)) + b}.ncard
      = cnt (N+1) := by
  set P := {σ : Fin (N+3) → ℕ |
       Valid σ ∧ σ 0 < σ 1 ∧ σ 0 = Finset.univ.sup (Fin.tail (Fin.tail σ)) + b} with hP
  have hInj : Set.InjOn (fun σ : Fin (N+3) → ℕ => Fin.tail (Fin.tail σ)) P := by
    intro σ hσ σ' hσ' he
    simp only at he
    have h00 : σ 0 = σ' 0 := by rw [hσ.2.2, hσ'.2.2, he]
    have h11 : σ 1 = σ' 1 := by
      rw [asc_succ σ hσ.1 hσ.2.1, asc_succ σ' hσ'.1 hσ'.2.1, h00]
    funext x
    rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨x', rfl⟩
    · exact h00
    · rcases Fin.eq_zero_or_eq_succ x' with rfl | ⟨x'', rfl⟩
      · have hs0 : (Fin.succ (0 : Fin (N+2)) : Fin (N+3)) = 1 := by ext; simp
        show σ (Fin.succ 0) = σ' (Fin.succ 0)
        rw [hs0]; exact h11
      · exact congrFun he x''
  have hImg : (fun σ : Fin (N+3) → ℕ => Fin.tail (Fin.tail σ)) '' P = Sset (N+1) := by
    ext υ
    constructor
    · rintro ⟨σ, hσP, rfl⟩
      exact drop2_valid σ hσP.1 hσP.2.1
    · intro hυ
      set v := Finset.univ.sup υ + b with hv
      refine ⟨Fin.cons v (Fin.cons (v + 1) υ), ?_, ?_⟩
      · have e0 : (Fin.cons v (Fin.cons (v + 1) υ) : Fin (N+3) → ℕ) 0 = v := Fin.cons_zero _ _
        have e1 : (Fin.cons v (Fin.cons (v + 1) υ) : Fin (N+3) → ℕ) 1 = v + 1 := by
          have h1eq : (1 : Fin (N+3)) = Fin.succ (0 : Fin (N+2)) := by ext; simp
          rw [h1eq, Fin.cons_succ, Fin.cons_zero]
        have htt : Fin.tail (Fin.tail (Fin.cons v (Fin.cons (v + 1) υ) : Fin (N+3) → ℕ)) = υ := by
          simp only [Fin.tail_cons]
        refine ⟨?_, ?_, ?_⟩
        · exact prepend2 υ hυ v (Nat.le_add_right _ _) (by omega)
        · rw [e0, e1]; omega
        · rw [e0, htt]
      · simp only [Fin.tail_cons]
  have := Set.ncard_image_of_injOn hInj
  rw [hImg] at this
  rw [← this]
  rfl

end A028859

namespace A028859

lemma cnt_rec (N : ℕ) : cnt (N+3) = 2 * cnt (N+2) + 2 * cnt (N+1) := by
  classical
  set S0 := {σ : Fin (N+3) → ℕ |
      Valid σ ∧ σ 1 ≤ σ 0 ∧ σ 0 = Finset.univ.sup (Fin.tail σ) + 0} with hS0
  set S1 := {σ : Fin (N+3) → ℕ |
      Valid σ ∧ σ 1 ≤ σ 0 ∧ σ 0 = Finset.univ.sup (Fin.tail σ) + 1} with hS1
  set T0 := {σ : Fin (N+3) → ℕ |
      Valid σ ∧ σ 0 < σ 1 ∧ σ 0 = Finset.univ.sup (Fin.tail (Fin.tail σ)) + 0} with hT0
  set T1 := {σ : Fin (N+3) → ℕ |
      Valid σ ∧ σ 0 < σ 1 ∧ σ 0 = Finset.univ.sup (Fin.tail (Fin.tail σ)) + 1} with hT1
  have fin0 : S0.Finite := (sset_finite (N+3)).subset (fun σ h => h.1)
  have fin1 : S1.Finite := (sset_finite (N+3)).subset (fun σ h => h.1)
  have finT0 : T0.Finite := (sset_finite (N+3)).subset (fun σ h => h.1)
  have finT1 : T1.Finite := (sset_finite (N+3)).subset (fun σ h => h.1)
  have dS : Disjoint S0 S1 := by
    rw [Set.disjoint_left]; intro σ h0 h1
    have a := h0.2.2; have b := h1.2.2; omega
  have dT : Disjoint T0 T1 := by
    rw [Set.disjoint_left]; intro σ h0 h1
    have a := h0.2.2; have b := h1.2.2; omega
  have dST : Disjoint (S0 ∪ S1) (T0 ∪ T1) := by
    rw [Set.disjoint_left]; intro σ hS hT
    rcases hS with h | h <;> rcases hT with h' | h' <;>
      exact absurd (lt_of_lt_of_le h'.2.1 h.2.1) (lt_irrefl _)
  have hcover : Sset (N+3) = (S0 ∪ S1) ∪ (T0 ∪ T1) := by
    ext σ
    constructor
    · intro hv
      have hv' : Valid σ := hv
      by_cases ha : σ 1 ≤ σ 0
      · rcases nonasc_cases σ hv' ha with hc | hc
        · exact Or.inl (Or.inl ⟨hv', ha, by omega⟩)
        · exact Or.inl (Or.inr ⟨hv', ha, by omega⟩)
      · push_neg at ha
        rcases asc_cases σ hv' ha with hc | hc
        · exact Or.inr (Or.inl ⟨hv', ha, by omega⟩)
        · exact Or.inr (Or.inr ⟨hv', ha, by omega⟩)
    · intro h
      rcases h with (h | h) | (h | h) <;> exact h.1
  have hncard : cnt (N+3) = ((S0 ∪ S1) ∪ (T0 ∪ T1)).ncard := by
    rw [cnt, hcover]
  rw [hncard, Set.ncard_union_eq dST (fin0.union fin1) (finT0.union finT1),
     Set.ncard_union_eq dS fin0 fin1, Set.ncard_union_eq dT finT0 finT1]
  have e0 : S0.ncard = cnt (N+2) := by rw [hS0]; exact ncard_nonasc_piece N 0 (by norm_num)
  have e1 : S1.ncard = cnt (N+2) := by rw [hS1]; exact ncard_nonasc_piece N 1 (by norm_num)
  have eT0 : T0.ncard = cnt (N+1) := by rw [hT0]; exact ncard_asc_piece N 0 (by norm_num)
  have eT1 : T1.ncard = cnt (N+1) := by rw [hT1]; exact ncard_asc_piece N 1 (by norm_num)
  rw [e0, e1, eT0, eT1]; ring

end A028859

namespace A028859

lemma cnt_one : cnt 1 = 1 := by
  have hset : Sset 1 = {(fun _ : Fin 1 => 1)} := by
    ext σ
    constructor
    · intro hv
      obtain ⟨hpos, hcov, hmono⟩ := hv
      have hsup : Finset.univ.sup σ = σ 0 :=
        le_antisymm (Finset.sup_le (fun i _ => le_of_eq (by rw [Subsingleton.elim i 0])))
          (le_sup' σ 0)
      have h0 : σ 0 = 1 := by
        by_contra hne
        have hge : 2 ≤ σ 0 := by have := hpos 0; omega
        obtain ⟨i, hi⟩ := hcov 1 (le_refl 1) (by rw [hsup]; omega)
        rw [Subsingleton.elim i 0] at hi
        omega
      funext i
      rw [Subsingleton.elim i 0]; exact h0
    · intro h
      rw [Set.mem_singleton_iff] at h
      subst h
      refine ⟨fun _ => one_pos, ?_, ?_⟩
      · intro k hk1 hk2
        have hsup : Finset.univ.sup (fun _ : Fin 1 => 1) = 1 := by simp
        rw [hsup] at hk2
        refine ⟨0, ?_⟩; show (1 : ℕ) = k; omega
      · intro i j hij hne
        exact absurd hij (by rw [Subsingleton.elim i j]; exact lt_irrefl _)
  rw [cnt, hset]; exact Set.ncard_singleton _

end A028859

namespace A028859

lemma sup_fin2 (a b : ℕ) : Finset.univ.sup (![a, b] : Fin 2 → ℕ) = max a b := by
  apply le_antisymm
  · apply Finset.sup_le; intro i _; fin_cases i <;> simp
  · refine max_le ?_ ?_
    · simpa using le_sup' (![a, b] : Fin 2 → ℕ) 0
    · simpa using le_sup' (![a, b] : Fin 2 → ℕ) 1

lemma mono2 (σ : Fin 2 → ℕ) : ∀ i j : Fin 2, i < j → (j : ℕ) ≠ (i : ℕ) + 1 → σ j ≤ σ i := by
  intro i j hij hne
  exfalso
  rw [Fin.lt_def] at hij
  have hi := i.isLt; have hj := j.isLt
  omega

lemma valid_11 : Valid (![1, 1] : Fin 2 → ℕ) := by
  refine ⟨?_, ?_, mono2 _⟩
  · intro i; fin_cases i <;> norm_num
  · intro k hk1 hk2; rw [sup_fin2] at hk2; simp at hk2
    exact ⟨0, by simp; omega⟩

lemma valid_12 : Valid (![1, 2] : Fin 2 → ℕ) := by
  refine ⟨?_, ?_, mono2 _⟩
  · intro i; fin_cases i <;> norm_num
  · intro k hk1 hk2; rw [sup_fin2] at hk2; simp at hk2
    interval_cases k
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

lemma valid_21 : Valid (![2, 1] : Fin 2 → ℕ) := by
  refine ⟨?_, ?_, mono2 _⟩
  · intro i; fin_cases i <;> norm_num
  · intro k hk1 hk2; rw [sup_fin2] at hk2; simp at hk2
    interval_cases k
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩

lemma cnt_two : cnt 2 = 3 := by
  rw [cnt, Set.ncard_eq_three]
  refine ⟨![1,1], ![1,2], ![2,1], by decide, by decide, by decide, ?_⟩
  ext σ
  constructor
  · intro hv
    obtain ⟨hpos, hcov, hmono⟩ := hv
    have hb := valid_sup_le σ ⟨hpos, hcov, hmono⟩
    have hs0 : σ 0 ≤ 2 := le_trans (le_sup' σ 0) hb
    have hs1 : σ 1 ≤ 2 := le_trans (le_sup' σ 1) hb
    have hp0 := hpos 0; have hp1 := hpos 1
    have hsupv : Finset.univ.sup σ = max (σ 0) (σ 1) := by
      apply le_antisymm
      · apply Finset.sup_le; intro i _; fin_cases i <;> simp
      · exact max_le (le_sup' σ 0) (le_sup' σ 1)
    have h1le : 1 ≤ Finset.univ.sup σ := le_trans hp0 (le_sup' σ 0)
    obtain ⟨i, hi⟩ := hcov 1 (le_refl 1) h1le
    have heta : σ = ![σ 0, σ 1] := by funext x; fin_cases x <;> rfl
    have h1mem : σ 0 = 1 ∨ σ 1 = 1 := by
      rcases Fin.eq_zero_or_eq_succ i with h | ⟨i', h⟩
      · subst h; exact Or.inl hi
      · subst h
        have hi0 : i' = 0 := Subsingleton.elim _ _
        subst hi0
        right
        have hs1eq : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := by ext; simp
        rw [hs1eq] at hi; exact hi
    have hcase : (σ 0 = 1 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 2) ∨ (σ 0 = 2 ∧ σ 1 = 1) := by
      omega
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hcase with ⟨e0, e1⟩ | ⟨e0, e1⟩ | ⟨e0, e1⟩
    · exact Or.inl (by rw [heta, e0, e1])
    · exact Or.inr (Or.inl (by rw [heta, e0, e1]))
    · exact Or.inr (Or.inr (by rw [heta, e0, e1]))
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl
    · exact valid_11
    · exact valid_12
    · exact valid_21

end A028859

def a' : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | (n+2) => 2 * a' (n+1) + 2 * a' n

namespace A028859

lemma cnt_eq_a (n : ℕ) : cnt (n+1) = a' n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact cnt_one
    | 1 => exact cnt_two
    | (m+2) =>
      have h1 : cnt (m+2) = a' (m+1) := ih (m+1) (by omega)
      have h2 : cnt (m+1) = a' m := ih m (by omega)
      have hr := cnt_rec m
      have ha : a' (m+2) = 2 * a' (m+1) + 2 * a' m := rfl
      show cnt (m+3) = a' (m+2)
      rw [hr, h1, h2, ha]

end A028859

theorem test_conj (n : ℕ) :
  let L := n + 1
  let Sequence := Fin L → ℕ
  let S : Set Sequence :=
    { σ : Sequence |
      L > 0 ∧
      (∀ i : Fin L, σ i > 0) ∧
      (let max_val := Finset.sup Finset.univ σ;
       (∀ k : ℕ, 1 ≤ k ∧ k ≤ max_val → ∃ i : Fin L, σ i = k)) ∧
      (∀ i j : Fin L, i < j → j.val ≠ i.val + 1 → σ i ≥ σ j) }
  ∃ (F : Finset Sequence), F.toSet = S ∧ F.card = a' n := by
  intro L Sequence S
  have hSeq : S = {σ : Fin (n+1) → ℕ | A028859.Valid σ} := by
    ext σ
    constructor
    · rintro ⟨_, hpos, hcov, hmono⟩
      refine ⟨hpos, ?_, ?_⟩
      · intro k hk1 hk2; exact hcov k ⟨hk1, hk2⟩
      · intro i j hij hne; exact hmono i j hij hne
    · rintro ⟨hpos, hcov, hmono⟩
      refine ⟨Nat.succ_pos n, hpos, ?_, ?_⟩
      · show ∀ k : ℕ, 1 ≤ k ∧ k ≤ Finset.sup Finset.univ σ → ∃ i, σ i = k
        intro k hk; exact hcov k hk.1 hk.2
      · intro i j hij hne; exact hmono i j hij hne
  have hfin : ({σ : Fin (n+1) → ℕ | A028859.Valid σ}).Finite := A028859.sv_finite (n+1)
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · rw [hSeq]; exact hfin.coe_toFinset
  · have hc : hfin.toFinset.card = a' n := by
      rw [← Set.ncard_eq_toFinset_card _ hfin]
      exact A028859.cnt_eq_a n
    exact hc
