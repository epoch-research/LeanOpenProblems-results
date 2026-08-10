import FormalConjectures.Util.ProblemImports

/--
A028859 (OEIS): $a(n+2) = 2 \cdot a(n+1) + 2 \cdot a(n)$; $a(0) = 1$, $a(1) = 3$.
-/
def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 3
  | (n + 2) => 2 * a (n + 1) + 2 * a n
termination_by n

set_option linter.unusedVariables false

open Finset

/-- predicate in the conjecture for length L -/
def Good (L : ℕ) (σ : Fin L → ℕ) : Prop :=
  L > 0 ∧
  (∀ i : Fin L, σ i > 0) ∧
  (let max_val := Finset.sup Finset.univ σ
   (∀ k : ℕ, 1 ≤ k ∧ k ≤ max_val → ∃ i : Fin L, σ i = k) ∧
   (∀ i j : Fin L, i < j → j.val ≠ i.val + 1 → σ i ≥ σ j))

lemma sup_add_const {L c : ℕ} (hL : L > 0) (σ : Fin L → ℕ) :
    (Finset.univ.sup fun i : Fin L => σ i + c) = (Finset.univ.sup σ) + c := by
  apply le_antisymm
  · rw [Finset.sup_le_iff]
    intro i hi
    exact Nat.add_le_add_right (Finset.le_sup (f := σ) (by simp : i ∈ (Finset.univ : Finset (Fin L)))) c
  · rcases Finset.sup_mem_of_nonempty (s := (Finset.univ : Finset (Fin L))) (f := σ)
      (by simpa [Finset.univ_nonempty_iff] using (show Nonempty (Fin L) from Fin.pos_iff_nonempty.mp hL)) with ⟨i, hi, hsup⟩
    rw [← hsup]
    exact Finset.le_sup (s := (Finset.univ : Finset (Fin L))) (f := fun i : Fin L => σ i + c) (by simp : i ∈ (Finset.univ : Finset (Fin L)))


lemma sup_snoc {L x : ℕ} (σ : Fin L → ℕ) :
    (Finset.univ.sup (Fin.snoc σ x : Fin (L+1) → ℕ)) = (Finset.univ.sup σ) ⊔ x := by
  apply le_antisymm
  · rw [Finset.sup_le_iff]
    intro i hi
    cases i using Fin.lastCases with
    | last => simp [Fin.snoc_last]
    | cast i =>
        simp only [Fin.snoc_castSucc]
        exact le_sup_of_le_left (Finset.le_sup (s := (Finset.univ : Finset (Fin L))) (f := σ) (by simp : i ∈ (Finset.univ : Finset (Fin L))))
  · rw [sup_le_iff]
    constructor
    · rw [Finset.sup_le_iff]
      intro i hi
      simpa [Fin.snoc_castSucc] using
        (Finset.le_sup (s := (Finset.univ : Finset (Fin (L+1)))) (f := (Fin.snoc σ x : Fin (L+1) → ℕ)) (by simp : i.castSucc ∈ (Finset.univ : Finset (Fin (L+1)))))
    · simpa [Fin.snoc_last] using
        (Finset.le_sup (s := (Finset.univ : Finset (Fin (L+1)))) (f := (Fin.snoc σ x : Fin (L+1) → ℕ)) (by simp : Fin.last L ∈ (Finset.univ : Finset (Fin (L+1)))))

lemma sup_snoc_one {L : ℕ} (σ : Fin L → ℕ) :
    (Finset.univ.sup (Fin.snoc σ 1 : Fin (L+1) → ℕ)) = (Finset.univ.sup σ) ⊔ 1 := by
  apply le_antisymm
  · rw [Finset.sup_le_iff]
    intro i hi
    cases i using Fin.lastCases with
    | last => simp [Fin.snoc_last]
    | cast i =>
        simp only [Fin.snoc_castSucc]
        exact le_sup_of_le_left (Finset.le_sup (s := (Finset.univ : Finset (Fin L))) (f := σ) (by simp : i ∈ (Finset.univ : Finset (Fin L))))
  · rw [sup_le_iff]
    constructor
    · rw [Finset.sup_le_iff]
      intro i hi
      simpa [Fin.snoc_castSucc] using
        (Finset.le_sup (s := (Finset.univ : Finset (Fin (L+1)))) (f := (Fin.snoc σ 1 : Fin (L+1) → ℕ)) (by simp : i.castSucc ∈ (Finset.univ : Finset (Fin (L+1)))))
    · simpa [Fin.snoc_last] using
        (Finset.le_sup (s := (Finset.univ : Finset (Fin (L+1)))) (f := (Fin.snoc σ 1 : Fin (L+1) → ℕ)) (by simp : Fin.last L ∈ (Finset.univ : Finset (Fin (L+1)))))

lemma Good_snoc_one {L : ℕ} {σ : Fin L → ℕ} (h : Good L σ) :
    Good (L+1) (Fin.snoc σ 1) := by
  rcases h with ⟨hL, hpos, hcov, hord⟩
  dsimp [Good] at *
  refine ⟨Nat.succ_pos L, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = Fin.last L
    · subst hi; simp [Fin.snoc_last]
    · have : ∃ j : Fin L, i = j.castSucc := by
        refine ⟨⟨i.val, ?_⟩, ?_⟩
        · have hlt : i.val < L + 1 := i.isLt
          have neLast : i.val ≠ L := by
            intro hv; apply hi; ext; simp [hv, Fin.last]
          omega
        · ext; simp
      rcases this with ⟨j, rfl⟩
      simpa [Fin.snoc_castSucc] using hpos j
  · intro k hk
    -- cover: if k=1 use last, else use old cover after showing k≤old sup
    by_cases hk1 : k = 1
    · subst hk1; exact ⟨Fin.last L, by simp [Fin.snoc_last]⟩
    · have hkge : 2 ≤ k := by omega
      have hksup : k ≤ (Finset.univ.sup σ) ⊔ 1 := by
        simpa [sup_snoc_one σ] using hk.2
      have hsuple : k ≤ Finset.univ.sup σ := by
        rcases le_sup_iff.mp hksup with h' | h'
        · exact h'
        · omega
      rcases hcov k ⟨hk.1, hsuple⟩ with ⟨i, hi⟩
      exact ⟨i.castSucc, by simpa [Fin.snoc_castSucc, hi]⟩
  · intro i j hij hnadj
    cases j using Fin.lastCases with
    | last =>
        cases i using Fin.lastCases with
        | last => simp at hij
        | cast i =>
            simp only [Fin.snoc_castSucc, Fin.snoc_last]
            exact hpos i
    | cast j =>
        cases i using Fin.lastCases with
        | last =>
            have : ¬ (Fin.last L < j.castSucc) := by
              exact not_lt_of_ge (Fin.le_last _)
            exact False.elim (this hij)
        | cast i =>
            simp only [Fin.snoc_castSucc]
            apply hord i j
            · simpa using hij
            · intro hbad
              apply hnadj
              simpa [hbad]

lemma Good_snoc_succ_one {L : ℕ} {σ : Fin L → ℕ} (h : Good L σ) :
    Good (L+1) (Fin.snoc (fun i : Fin L => σ i + 1) 1) := by
  rcases h with ⟨hL, hpos, hcov, hord⟩
  dsimp [Good] at *
  refine ⟨Nat.succ_pos L, ?_, ?_, ?_⟩
  · intro i
    cases i using Fin.lastCases with
    | last => simp [Fin.snoc_last]
    | cast i => simp [Fin.snoc_castSucc, hpos i]
  · intro k hk
    by_cases hk1 : k = 1
    · subst hk1; exact ⟨Fin.last L, by simp [Fin.snoc_last]⟩
    · have hkge : 2 ≤ k := by omega
      have hksup : k ≤ (Finset.univ.sup σ + 1) := by
        have hs : (Finset.univ.sup (Fin.snoc (fun i : Fin L => σ i + 1) 1 : Fin (L+1) → ℕ)) = Finset.univ.sup σ + 1 := by
          rw [sup_snoc_one]
          rw [sup_add_const hL]
          omega
        simpa [hs] using hk.2
      have hkold : k - 1 ≤ Finset.univ.sup σ := by omega
      have hkoldpos : 1 ≤ k - 1 := by omega
      rcases hcov (k-1) ⟨hkoldpos, hkold⟩ with ⟨i, hi⟩
      refine ⟨i.castSucc, ?_⟩
      simp [Fin.snoc_castSucc, hi]
      omega
  · intro i j hij hnadj
    cases j using Fin.lastCases with
    | last =>
        cases i using Fin.lastCases with
        | last => simp at hij
        | cast i =>
            simp only [Fin.snoc_castSucc, Fin.snoc_last]
            exact Nat.succ_le_succ (Nat.zero_le (σ i))
    | cast j =>
        cases i using Fin.lastCases with
        | last =>
            exact False.elim ((not_lt_of_ge (Fin.le_last _)) hij)
        | cast i =>
            simp only [Fin.snoc_castSucc]
            exact Nat.add_le_add_right (hord i j (by simpa using hij) (by intro hbad; apply hnadj; simpa [hbad])) 1

lemma Good_last_le_two {L : ℕ} {σ : Fin (L+2) → ℕ} (h : Good (L+2) σ) :
    σ (Fin.last (L+1)) ≤ 2 := by
  rcases h with ⟨hposLen, hpos, hcov, hord⟩
  dsimp [Good] at *
  by_contra hnot
  have hlast3 : 3 ≤ σ (Fin.last (L+1)) := by omega
  have hmax : σ (Fin.last (L+1)) ≤ Finset.univ.sup σ :=
    Finset.le_sup (s := (Finset.univ : Finset (Fin (L+2)))) (f := σ) (by simp : Fin.last (L+1) ∈ (Finset.univ : Finset (Fin (L+2))))
  rcases hcov 1 ⟨by omega, by omega⟩ with ⟨i1, hi1⟩
  rcases hcov 2 ⟨by omega, by omega⟩ with ⟨i2, hi2⟩
  have i1_pen : i1 = (Fin.last L).castSucc := by
    by_cases hlt : i1 < Fin.last (L+1)
    · by_cases hadj : (Fin.last (L+1)).val = i1.val + 1
      · ext; simp [Fin.last] at hadj ⊢; omega
      · have hge := hord i1 (Fin.last (L+1)) hlt hadj
        omega
    · have hle : Fin.last (L+1) ≤ i1 := le_of_not_gt hlt
      have hlelast : i1 ≤ Fin.last (L+1) := Fin.le_last i1
      have : i1 = Fin.last (L+1) := le_antisymm hlelast hle
      have : σ (Fin.last (L+1)) = 1 := by simpa [this] using hi1
      omega
  have i2_pen : i2 = (Fin.last L).castSucc := by
    by_cases hlt : i2 < Fin.last (L+1)
    · by_cases hadj : (Fin.last (L+1)).val = i2.val + 1
      · ext; simp [Fin.last] at hadj ⊢; omega
      · have hge := hord i2 (Fin.last (L+1)) hlt hadj
        omega
    · have hle : Fin.last (L+1) ≤ i2 := le_of_not_gt hlt
      have hlelast : i2 ≤ Fin.last (L+1) := Fin.le_last i2
      have : i2 = Fin.last (L+1) := le_antisymm hlelast hle
      have : σ (Fin.last (L+1)) = 2 := by simpa [this] using hi2
      omega
  have : (1:ℕ) = 2 := by
    calc
      (1:ℕ) = σ i1 := hi1.symm
      _ = σ ((Fin.last L).castSucc) := by rw [i1_pen]
      _ = σ i2 := by rw [i2_pen]
      _ = 2 := hi2
  omega

lemma Good_last_eq_one_or_two {L : ℕ} {σ : Fin (L+2) → ℕ} (h : Good (L+2) σ) :
    σ (Fin.last (L+1)) = 1 ∨ σ (Fin.last (L+1)) = 2 := by
  have hp := (h.2.1 (Fin.last (L+1)))
  have hle := Good_last_le_two h
  omega

lemma Good_exists_one {L : ℕ} {σ : Fin L → ℕ} (h : Good L σ) : ∃ i : Fin L, σ i = 1 := by
  rcases h with ⟨hL,hpos,hcov,hord⟩
  dsimp [Good] at *
  let i0 : Fin L := ⟨0, hL⟩
  have hsup : 1 ≤ Finset.univ.sup σ := by
    exact le_trans (hpos i0) (Finset.le_sup (s := (Finset.univ : Finset (Fin L))) (f := σ) (by simp : i0 ∈ (Finset.univ : Finset (Fin L))))
  exact hcov 1 ⟨by omega, hsup⟩





lemma Good_init_of_last_one_of_exists_one {L : ℕ} (hL : L > 0) {τ : Fin (L+1) → ℕ}
    (hg : Good (L+1) τ) (hlast : τ (Fin.last L) = 1)
    (hex : ∃ i : Fin L, τ i.castSucc = 1) : Good L (Fin.init τ) := by
  rcases hg with ⟨hlen, hpos, hcov, hord⟩
  dsimp [Good] at *
  refine ⟨hL, ?_, ?_, ?_⟩
  · intro i
    simpa [Fin.init] using hpos i.castSucc
  · intro k hk
    have hsuple : Finset.univ.sup (Fin.init τ) ≤ Finset.univ.sup τ := by
      rw [Finset.sup_le_iff]
      intro i hi
      simpa [Fin.init] using
        (Finset.le_sup (s := (Finset.univ : Finset (Fin (L+1)))) (f := τ) (by simp : i.castSucc ∈ (Finset.univ : Finset (Fin (L+1)))))
    have hkfull : k ≤ Finset.univ.sup τ := le_trans hk.2 hsuple
    rcases hcov k ⟨hk.1, hkfull⟩ with ⟨j, hj⟩
    cases j using Fin.lastCases with
    | last =>
        have hk1 : k = 1 := by simpa [hlast] using hj.symm
        rcases hex with ⟨i, hi⟩
        subst hk1
        exact ⟨i, by simpa [Fin.init] using hi⟩
    | cast j =>
        exact ⟨j, by simpa [Fin.init] using hj⟩
  · intro i j hij hnadj
    simpa [Fin.init] using hord i.castSucc j.castSucc (by simpa using hij) (by intro h; apply hnadj; simpa using h)

lemma Good_pred_init_of_last_one_of_no_one {L : ℕ} (hL : L > 0) {τ : Fin (L+1) → ℕ}
    (hg : Good (L+1) τ) (hlast : τ (Fin.last L) = 1)
    (hnone : ∀ i : Fin L, τ i.castSucc ≠ 1) : Good L (fun i : Fin L => τ i.castSucc - 1) := by
  rcases hg with ⟨hlen, hpos, hcov, hord⟩
  dsimp [Good] at *
  refine ⟨hL, ?_, ?_, ?_⟩
  · intro i
    have hgt := hpos i.castSucc
    have hne := hnone i
    omega
  · intro k hk
    have hsup_le : Finset.univ.sup (fun i : Fin L => τ i.castSucc - 1) ≤ Finset.univ.sup τ - 1 := by
      rw [Finset.sup_le_iff]
      intro i hi
      have hti : τ i.castSucc ≤ Finset.univ.sup τ :=
        Finset.le_sup (s := (Finset.univ : Finset (Fin (L+1)))) (f := τ) (by simp : i.castSucc ∈ (Finset.univ : Finset (Fin (L+1))))
      omega
    have hkfull : k + 1 ≤ Finset.univ.sup τ := by
      have := le_trans hk.2 hsup_le
      omega
    rcases hcov (k+1) ⟨by omega, hkfull⟩ with ⟨j, hj⟩
    cases j using Fin.lastCases with
    | last =>
        have : k + 1 = 1 := by simpa [hlast] using hj.symm
        omega
    | cast j =>
        refine ⟨j, ?_⟩
        simp [hj]
  · intro i j hij hnadj
    have hge := hord i.castSucc j.castSucc (by simpa using hij) (by intro h; apply hnadj; simpa using h)
    omega

lemma Good_snoc_succ_one_two {L : ℕ} {σ : Fin L → ℕ} (h : Good L σ) :
    Good (L+2) (Fin.snoc (Fin.snoc (fun i : Fin L => σ i + 1) 1) 2) := by
  rcases h with ⟨hL, hpos, hcov, hord⟩
  dsimp [Good] at *
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro i
    cases i using Fin.lastCases with
    | last => simp [Fin.snoc_last]
    | cast i =>
        cases i using Fin.lastCases with
        | last => simp [Fin.snoc_last, Fin.snoc_castSucc]
        | cast i => simp [Fin.snoc_castSucc]
  · intro k hk
    have hsup_eq : (Finset.univ.sup (Fin.snoc (Fin.snoc (fun i : Fin L => σ i + 1) 1) 2 : Fin (L+2) → ℕ)) = Finset.univ.sup σ + 1 := by
      rw [sup_snoc]
      rw [sup_snoc_one]
      rw [sup_add_const hL]
      have hspos : 1 ≤ Finset.univ.sup σ := by
        exact le_trans (hpos ⟨0, hL⟩) (Finset.le_sup (s := (Finset.univ : Finset (Fin L))) (f := σ) (by simp : (⟨0, hL⟩ : Fin L) ∈ (Finset.univ : Finset (Fin L))))
      omega
    by_cases hk1 : k = 1
    · subst hk1
      exact ⟨(Fin.last L).castSucc, by simp [Fin.snoc_castSucc, Fin.snoc_last]⟩
    · have hkold : k - 1 ≤ Finset.univ.sup σ := by
        have := hk.2
        rw [hsup_eq] at this
        omega
      have hkoldpos : 1 ≤ k - 1 := by omega
      rcases hcov (k-1) ⟨hkoldpos, hkold⟩ with ⟨i, hi⟩
      refine ⟨i.castSucc.castSucc, ?_⟩
      simp [Fin.snoc_castSucc, hi]
      omega
  · intro i j hij hnadj
    cases j using Fin.lastCases with
    | last =>
        cases i using Fin.lastCases with
        | last => simp at hij
        | cast i =>
            cases i using Fin.lastCases with
            | last => simp [Fin.snoc_castSucc, Fin.snoc_last] at hnadj
            | cast i =>
                simp only [Fin.snoc_castSucc, Fin.snoc_last]
                have : 1 ≤ σ i := hpos i
                omega
    | cast j =>
        cases j using Fin.lastCases with
        | last =>
            cases i using Fin.lastCases with
            | last => exact False.elim ((not_lt_of_ge (Fin.le_last _)) hij)
            | cast i =>
                cases i using Fin.lastCases with
                | last => simp at hij
                | cast i =>
                    simp only [Fin.snoc_castSucc, Fin.snoc_last]
                    have : 1 ≤ σ i := hpos i
                    omega
        | cast j =>
            cases i using Fin.lastCases with
            | last => exact False.elim ((not_lt_of_ge (Fin.le_last _)) hij)
            | cast i =>
                cases i using Fin.lastCases with
                | last => exact False.elim ((not_lt_of_ge (Fin.le_last _)) (by simpa using hij : Fin.last L < j.castSucc))
                | cast i =>
                    simp only [Fin.snoc_castSucc]
                    exact Nat.add_le_add_right (hord i j (by simpa using hij) (by intro hbad; apply hnadj; simpa [hbad])) 1

lemma Good_snoc_add_two_one_two {L : ℕ} {σ : Fin L → ℕ} (h : Good L σ) :
    Good (L+2) (Fin.snoc (Fin.snoc (fun i : Fin L => σ i + 2) 1) 2) := by
  rcases h with ⟨hL, hpos, hcov, hord⟩
  dsimp [Good] at *
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro i
    cases i using Fin.lastCases with
    | last => simp [Fin.snoc_last]
    | cast i =>
        cases i using Fin.lastCases with
        | last => simp [Fin.snoc_last, Fin.snoc_castSucc]
        | cast i => simp [Fin.snoc_castSucc]
  · intro k hk
    have hsup_eq : (Finset.univ.sup (Fin.snoc (Fin.snoc (fun i : Fin L => σ i + 2) 1) 2 : Fin (L+2) → ℕ)) = Finset.univ.sup σ + 2 := by
      rw [sup_snoc]
      rw [sup_snoc_one]
      rw [sup_add_const hL]
      have hspos : 1 ≤ Finset.univ.sup σ := by
        exact le_trans (hpos ⟨0, hL⟩) (Finset.le_sup (s := (Finset.univ : Finset (Fin L))) (f := σ) (by simp : (⟨0, hL⟩ : Fin L) ∈ (Finset.univ : Finset (Fin L))))
      omega
    by_cases hk1 : k = 1
    · subst hk1
      exact ⟨(Fin.last L).castSucc, by simp [Fin.snoc_castSucc, Fin.snoc_last]⟩
    · by_cases hk2 : k = 2
      · subst hk2
        exact ⟨Fin.last (L+1), by simp [Fin.snoc_last]⟩
      · have hkold : k - 2 ≤ Finset.univ.sup σ := by
          have := hk.2
          rw [hsup_eq] at this
          omega
        have hkoldpos : 1 ≤ k - 2 := by omega
        rcases hcov (k-2) ⟨hkoldpos, hkold⟩ with ⟨i, hi⟩
        refine ⟨i.castSucc.castSucc, ?_⟩
        simp [Fin.snoc_castSucc, hi]
        omega
  · intro i j hij hnadj
    cases j using Fin.lastCases with
    | last =>
        cases i using Fin.lastCases with
        | last => simp at hij
        | cast i =>
            cases i using Fin.lastCases with
            | last => simp [Fin.snoc_castSucc, Fin.snoc_last] at hnadj
            | cast i =>
                simp only [Fin.snoc_castSucc, Fin.snoc_last]
                have : 0 ≤ σ i := Nat.zero_le _
                omega
    | cast j =>
        cases j using Fin.lastCases with
        | last =>
            cases i using Fin.lastCases with
            | last => exact False.elim ((not_lt_of_ge (Fin.le_last _)) hij)
            | cast i =>
                cases i using Fin.lastCases with
                | last => simp at hij
                | cast i =>
                    simp only [Fin.snoc_castSucc, Fin.snoc_last]
                    have : 0 ≤ σ i := Nat.zero_le _
                    omega
        | cast j =>
            cases i using Fin.lastCases with
            | last => exact False.elim ((not_lt_of_ge (Fin.le_last _)) hij)
            | cast i =>
                cases i using Fin.lastCases with
                | last => exact False.elim ((not_lt_of_ge (Fin.le_last _)) (by simpa using hij : Fin.last L < j.castSucc))
                | cast i =>
                    simp only [Fin.snoc_castSucc]
                    exact Nat.add_le_add_right (hord i j (by simpa using hij) (by intro hbad; apply hnadj; simpa [hbad])) 2

lemma Good_penult_eq_one_of_last_two {L : ℕ} {τ : Fin (L+2) → ℕ}
    (hg : Good (L+2) τ) (hlast : τ (Fin.last (L+1)) = 2) :
    τ ((Fin.last L).castSucc) = 1 := by
  rcases hg with ⟨hlen, hpos, hcov, hord⟩
  dsimp [Good] at *
  have hmax : 1 ≤ Finset.univ.sup τ := by
    have hle : τ (Fin.last (L+1)) ≤ Finset.univ.sup τ :=
      Finset.le_sup (s := (Finset.univ : Finset (Fin (L+2)))) (f := τ) (by simp : Fin.last (L+1) ∈ (Finset.univ : Finset (Fin (L+2))))
    omega
  rcases hcov 1 ⟨by omega, hmax⟩ with ⟨i, hi⟩
  have ipen : i = (Fin.last L).castSucc := by
    by_cases hlt : i < Fin.last (L+1)
    · by_cases hadj : (Fin.last (L+1)).val = i.val + 1
      · ext; simp [Fin.last] at hadj ⊢; omega
      · have hge := hord i (Fin.last (L+1)) hlt hadj
        omega
    · have hle : Fin.last (L+1) ≤ i := le_of_not_gt hlt
      have hlelast : i ≤ Fin.last (L+1) := Fin.le_last i
      have : i = Fin.last (L+1) := le_antisymm hlelast hle
      have : τ (Fin.last (L+1)) = 1 := by simpa [this] using hi
      omega
  simpa [ipen] using hi

lemma Good_pred_prefix_of_last_two_of_exists_two {L : ℕ} (hL : L > 0) {τ : Fin (L+2) → ℕ}
    (hg : Good (L+2) τ) (hlast : τ (Fin.last (L+1)) = 2)
    (hex : ∃ i : Fin L, τ i.castSucc.castSucc = 2) :
    Good L (fun i : Fin L => τ i.castSucc.castSucc - 1) := by
  rcases hg with ⟨hlen, hpos, hcov, hord⟩
  dsimp [Good] at *
  have hpen : τ ((Fin.last L).castSucc) = 1 := Good_penult_eq_one_of_last_two ⟨hlen,hpos,hcov,hord⟩ hlast
  have hprefix_ge2 : ∀ i : Fin L, 2 ≤ τ i.castSucc.castSucc := by
    intro i
    have hge := hord i.castSucc.castSucc (Fin.last (L+1)) (by change i.castSucc.castSucc.val < (Fin.last (L+1)).val; simp [Fin.last]) (by intro heq; simp [Fin.last] at heq; omega)
    omega
  refine ⟨hL, ?_, ?_, ?_⟩
  · intro i; have := hprefix_ge2 i; omega
  · intro k hk
    by_cases hk1 : k = 1
    · rcases hex with ⟨i, hi⟩
      subst hk1
      exact ⟨i, by simp [hi]⟩
    · have hsup_le : Finset.univ.sup (fun i : Fin L => τ i.castSucc.castSucc - 1) ≤ Finset.univ.sup τ - 1 := by
        rw [Finset.sup_le_iff]
        intro i hi
        have hti : τ i.castSucc.castSucc ≤ Finset.univ.sup τ :=
          Finset.le_sup (s := (Finset.univ : Finset (Fin (L+2)))) (f := τ) (by simp : i.castSucc.castSucc ∈ (Finset.univ : Finset (Fin (L+2))))
        omega
      have hkfull : k + 1 ≤ Finset.univ.sup τ := by
        have := le_trans hk.2 hsup_le
        omega
      rcases hcov (k+1) ⟨by omega, hkfull⟩ with ⟨j, hj⟩
      cases j using Fin.lastCases with
      | last =>
          have : k + 1 = 2 := by simpa [hlast] using hj.symm
          omega
      | cast j =>
          cases j using Fin.lastCases with
          | last =>
              have : k + 1 = 1 := by simpa [hpen] using hj.symm
              omega
          | cast j =>
              refine ⟨j, ?_⟩
              simp [hj]
  · intro i j hij hnadj
    have hge := hord i.castSucc.castSucc j.castSucc.castSucc (by simpa using hij) (by intro h; apply hnadj; simpa using h)
    omega

lemma Good_sub_two_prefix_of_last_two_of_no_two {L : ℕ} (hL : L > 0) {τ : Fin (L+2) → ℕ}
    (hg : Good (L+2) τ) (hlast : τ (Fin.last (L+1)) = 2)
    (hnone : ∀ i : Fin L, τ i.castSucc.castSucc ≠ 2) :
    Good L (fun i : Fin L => τ i.castSucc.castSucc - 2) := by
  rcases hg with ⟨hlen, hpos, hcov, hord⟩
  dsimp [Good] at *
  have hpen : τ ((Fin.last L).castSucc) = 1 := Good_penult_eq_one_of_last_two ⟨hlen,hpos,hcov,hord⟩ hlast
  have hprefix_ge3 : ∀ i : Fin L, 3 ≤ τ i.castSucc.castSucc := by
    intro i
    have hge := hord i.castSucc.castSucc (Fin.last (L+1)) (by change i.castSucc.castSucc.val < (Fin.last (L+1)).val; simp [Fin.last]) (by intro heq; simp [Fin.last] at heq; omega)
    have hne := hnone i
    omega
  refine ⟨hL, ?_, ?_, ?_⟩
  · intro i; have := hprefix_ge3 i; omega
  · intro k hk
    have hsup_le : Finset.univ.sup (fun i : Fin L => τ i.castSucc.castSucc - 2) ≤ Finset.univ.sup τ - 2 := by
      rw [Finset.sup_le_iff]
      intro i hi
      have hti : τ i.castSucc.castSucc ≤ Finset.univ.sup τ :=
        Finset.le_sup (s := (Finset.univ : Finset (Fin (L+2)))) (f := τ) (by simp : i.castSucc.castSucc ∈ (Finset.univ : Finset (Fin (L+2))))
      omega
    have hkfull : k + 2 ≤ Finset.univ.sup τ := by
      have := le_trans hk.2 hsup_le
      omega
    rcases hcov (k+2) ⟨by omega, hkfull⟩ with ⟨j, hj⟩
    cases j using Fin.lastCases with
    | last =>
        have : k + 2 = 2 := by simpa [hlast] using hj.symm
        omega
    | cast j =>
        cases j using Fin.lastCases with
        | last =>
            have : k + 2 = 1 := by simpa [hpen] using hj.symm
            omega
        | cast j =>
            refine ⟨j, ?_⟩
            simp [hj]
  · intro i j hij hnadj
    have hge := hord i.castSucc.castSucc j.castSucc.castSucc (by simpa using hij) (by intro h; apply hnadj; simpa using h)
    omega

def embLast1 (L : ℕ) : (Fin L → ℕ) ↪ (Fin (L+1) → ℕ) where
  toFun σ := Fin.snoc σ 1
  inj' := by
    intro σ τ h
    funext i
    simpa [Fin.snoc_castSucc] using congr_fun h i.castSucc

def embSuccLast1 (L : ℕ) : (Fin L → ℕ) ↪ (Fin (L+1) → ℕ) where
  toFun σ := Fin.snoc (fun i : Fin L => σ i + 1) 1
  inj' := by
    intro σ τ h
    funext i
    have hh : σ i + 1 = τ i + 1 := by simpa [Fin.snoc_castSucc] using congr_fun h i.castSucc
    omega

def embSuccLast12 (L : ℕ) : (Fin L → ℕ) ↪ (Fin (L+2) → ℕ) where
  toFun σ := Fin.snoc (Fin.snoc (fun i : Fin L => σ i + 1) 1) 2
  inj' := by
    intro σ τ h
    funext i
    have hh : σ i + 1 = τ i + 1 := by
      simpa [Fin.snoc_castSucc] using congr_fun h i.castSucc.castSucc
    omega

def embAddTwoLast12 (L : ℕ) : (Fin L → ℕ) ↪ (Fin (L+2) → ℕ) where
  toFun σ := Fin.snoc (Fin.snoc (fun i : Fin L => σ i + 2) 1) 2
  inj' := by
    intro σ τ h
    funext i
    have hh : σ i + 2 = τ i + 2 := by
      simpa [Fin.snoc_castSucc] using congr_fun h i.castSucc.castSucc
    omega


lemma Good_classify {L : ℕ} (hL : L > 0) (τ : Fin (L+2) → ℕ) :
    Good (L+2) τ ↔
      (∃ σ : Fin (L+1) → ℕ, Good (L+1) σ ∧ τ = (embLast1 (L+1)) σ) ∨
      (∃ σ : Fin (L+1) → ℕ, Good (L+1) σ ∧ τ = (embSuccLast1 (L+1)) σ) ∨
      (∃ σ : Fin L → ℕ, Good L σ ∧ τ = (embSuccLast12 L) σ) ∨
      (∃ σ : Fin L → ℕ, Good L σ ∧ τ = (embAddTwoLast12 L) σ) := by
  constructor
  · intro hg
    rcases Good_last_eq_one_or_two (L:=L) hg with hlast | hlast
    · by_cases hex : ∃ i : Fin (L+1), τ i.castSucc = 1
      · left
        refine ⟨Fin.init τ, Good_init_of_last_one_of_exists_one (by omega) hg hlast hex, ?_⟩
        calc
          τ = Fin.snoc (Fin.init τ) (τ (Fin.last (L+1))) := (Fin.snoc_init_self τ).symm
          _ = (embLast1 (L+1)) (Fin.init τ) := by rw [hlast]; rfl
      · right; left
        let σ : Fin (L+1) → ℕ := fun i => τ i.castSucc - 1
        refine ⟨σ, Good_pred_init_of_last_one_of_no_one (by omega) hg hlast (by simpa using hex), ?_⟩
        funext i
        cases i using Fin.lastCases with
        | last => simp [embSuccLast1, hlast]
        | cast i =>
            have hp := (hg.2.1 i.castSucc)
            have hn : τ i.castSucc ≠ 1 := by intro hi; exact hex ⟨i, hi⟩
            simp [σ, embSuccLast1, Fin.snoc_castSucc]
            omega
    · right; right
      have hpen : τ ((Fin.last L).castSucc) = 1 := Good_penult_eq_one_of_last_two hg hlast
      by_cases hex : ∃ i : Fin L, τ i.castSucc.castSucc = 2
      · left
        let σ : Fin L → ℕ := fun i => τ i.castSucc.castSucc - 1
        refine ⟨σ, Good_pred_prefix_of_last_two_of_exists_two hL hg hlast hex, ?_⟩
        funext i
        cases i using Fin.lastCases with
        | last => simp [embSuccLast12, hlast]
        | cast i =>
            cases i using Fin.lastCases with
            | last => simp [embSuccLast12, hpen]
            | cast i =>
                have hge : 2 ≤ τ i.castSucc.castSucc := by
                  have hge' := (hg.2.2.2 i.castSucc.castSucc (Fin.last (L+1)) (by change i.castSucc.castSucc.val < (Fin.last (L+1)).val; simp [Fin.last]) (by intro heq; simp [Fin.last] at heq; omega))
                  omega
                simp [σ, embSuccLast12, Fin.snoc_castSucc]
                omega
      · right
        let σ : Fin L → ℕ := fun i => τ i.castSucc.castSucc - 2
        refine ⟨σ, Good_sub_two_prefix_of_last_two_of_no_two hL hg hlast (by simpa using hex), ?_⟩
        funext i
        cases i using Fin.lastCases with
        | last => simp [embAddTwoLast12, hlast]
        | cast i =>
            cases i using Fin.lastCases with
            | last => simp [embAddTwoLast12, hpen]
            | cast i =>
                have hge : 3 ≤ τ i.castSucc.castSucc := by
                  have hge' := (hg.2.2.2 i.castSucc.castSucc (Fin.last (L+1)) (by change i.castSucc.castSucc.val < (Fin.last (L+1)).val; simp [Fin.last]) (by intro heq; simp [Fin.last] at heq; omega))
                  have hn : τ i.castSucc.castSucc ≠ 2 := by intro hi; exact hex ⟨i, hi⟩
                  omega
                simp [σ, embAddTwoLast12, Fin.snoc_castSucc]
                omega
  · intro h
    rcases h with ⟨σ,hg,rfl⟩ | ⟨σ,hg,rfl⟩ | ⟨σ,hg,rfl⟩ | ⟨σ,hg,rfl⟩
    · exact Good_snoc_one hg
    · exact Good_snoc_succ_one hg
    · exact Good_snoc_succ_one_two hg
    · exact Good_snoc_add_two_one_two hg

lemma disjoint_last1_succLast1 {L : ℕ} {F : Finset (Fin L → ℕ)}
    (hF : ∀ σ, σ ∈ F → Good L σ) :
    Disjoint (F.map (embLast1 L)) (F.map (embSuccLast1 L)) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [Finset.mem_map] at hx hy
  rcases hx with ⟨σ, hσmem, rfl⟩
  rcases hy with ⟨τ, hτmem, heq⟩
  rcases Good_exists_one (hF σ hσmem) with ⟨i, hi⟩
  have hcong := congr_fun heq i.castSucc
  simp [embLast1, embSuccLast1, Fin.snoc_castSucc, hi] at hcong
  have htpos := (hF τ hτmem).2.1 i
  omega

lemma disjoint_last12_addtwo {L : ℕ} {F : Finset (Fin L → ℕ)}
    (hF : ∀ σ, σ ∈ F → Good L σ) :
    Disjoint (F.map (embSuccLast12 L)) (F.map (embAddTwoLast12 L)) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [Finset.mem_map] at hx hy
  rcases hx with ⟨σ, hσmem, rfl⟩
  rcases hy with ⟨τ, hτmem, heq⟩
  rcases Good_exists_one (hF σ hσmem) with ⟨i, hi⟩
  have hcong := congr_fun heq i.castSucc.castSucc
  simp [embSuccLast12, embAddTwoLast12, Fin.snoc_castSucc, hi] at hcong
  have htpos := (hF τ hτmem).2.1 i
  omega

lemma disjoint_last1_last2_A {L : ℕ} {F₁ : Finset (Fin (L+1) → ℕ)} {F₀ : Finset (Fin L → ℕ)} :
    Disjoint (F₁.map (embLast1 (L+1))) (F₀.map (embSuccLast12 L)) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [Finset.mem_map] at hx hy
  rcases hx with ⟨σ, hσ, rfl⟩
  rcases hy with ⟨τ, hτ, heq⟩
  have hcong := congr_fun heq (Fin.last (L+1))
  simp [embLast1, embSuccLast12, Fin.snoc_last] at hcong

lemma disjoint_last1_last2_B {L : ℕ} {F₁ : Finset (Fin (L+1) → ℕ)} {F₀ : Finset (Fin L → ℕ)} :
    Disjoint (F₁.map (embLast1 (L+1))) (F₀.map (embAddTwoLast12 L)) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [Finset.mem_map] at hx hy
  rcases hx with ⟨σ, hσ, rfl⟩
  rcases hy with ⟨τ, hτ, heq⟩
  have hcong := congr_fun heq (Fin.last (L+1))
  simp [embLast1, embAddTwoLast12, Fin.snoc_last] at hcong

lemma disjoint_succLast1_last2_A {L : ℕ} {F₁ : Finset (Fin (L+1) → ℕ)} {F₀ : Finset (Fin L → ℕ)} :
    Disjoint (F₁.map (embSuccLast1 (L+1))) (F₀.map (embSuccLast12 L)) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [Finset.mem_map] at hx hy
  rcases hx with ⟨σ, hσ, rfl⟩
  rcases hy with ⟨τ, hτ, heq⟩
  have hcong := congr_fun heq (Fin.last (L+1))
  simp [embSuccLast1, embSuccLast12, Fin.snoc_last] at hcong

lemma disjoint_succLast1_last2_B {L : ℕ} {F₁ : Finset (Fin (L+1) → ℕ)} {F₀ : Finset (Fin L → ℕ)} :
    Disjoint (F₁.map (embSuccLast1 (L+1))) (F₀.map (embAddTwoLast12 L)) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [Finset.mem_map] at hx hy
  rcases hx with ⟨σ, hσ, rfl⟩
  rcases hy with ⟨τ, hτ, heq⟩
  have hcong := congr_fun heq (Fin.last (L+1))
  simp [embSuccLast1, embAddTwoLast12, Fin.snoc_last] at hcong


lemma Good_fin_one_iff (σ : Fin 1 → ℕ) : Good 1 σ ↔ σ = (fun _ => 1) := by
  constructor
  · intro h
    rcases h with ⟨hlen,hpos,hcov,hord⟩
    dsimp [Good] at *
    funext i
    fin_cases i
    have hle : σ 0 ≤ 1 := by
      by_contra hnot
      have hs2 : 2 ≤ σ 0 := by omega
      have hmax : 1 ≤ Finset.univ.sup σ := by
        exact le_trans (by omega : 1 ≤ σ 0) (Finset.le_sup (s := (Finset.univ : Finset (Fin 1))) (f := σ) (by simp : (0 : Fin 1) ∈ (Finset.univ : Finset (Fin 1))))
      rcases hcov 1 ⟨by omega, hmax⟩ with ⟨j,hj⟩
      fin_cases j
      have : σ 0 = 1 := by simpa using hj
      omega
    exact le_antisymm hle (hpos 0)
  · intro h
    subst h
    dsimp [Good]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro i; fin_cases i; omega
    · intro k hk
      refine ⟨0, ?_⟩
      simp at hk ⊢
      omega
    · intro i j hij hnadj
      fin_cases i <;> fin_cases j <;> simp at hij

lemma Good_fin_two_iff (σ : Fin 2 → ℕ) :
    Good 2 σ ↔ σ = Fin.snoc (fun _ : Fin 1 => 1) 1 ∨
      σ = Fin.snoc (fun _ : Fin 1 => 1 + 1) 1 ∨
      σ = Fin.snoc (Fin.snoc (fun i : Fin 0 => i.elim0) 1) 2 := by
  constructor
  · intro h
    have hlast := Good_last_eq_one_or_two (L:=0) h
    rcases h with ⟨hlen,hpos,hcov,hord⟩
    dsimp [Good] at *
    rcases hlast with hl | hl
    · by_cases hf1 : σ 0 = 1
      · left
        funext i
        fin_cases i
        · simpa [Fin.snoc_castSucc] using hf1
        · simpa [Fin.snoc_last] using hl
      · have hf2 : σ 0 = 2 := by
          have hle : σ 0 ≤ 2 := by
            by_contra hn
            have hs3 : 3 ≤ σ 0 := by omega
            have hsup : 2 ≤ Finset.univ.sup σ := by
              exact le_trans (by omega : 2 ≤ σ 0) (Finset.le_sup (s := (Finset.univ : Finset (Fin 2))) (f := σ) (by simp : (0 : Fin 2) ∈ (Finset.univ : Finset (Fin 2))))
            rcases hcov 2 ⟨by omega, hsup⟩ with ⟨j,hj⟩
            fin_cases j
            · have : σ 0 = 2 := by simpa using hj
              omega
            · have : σ 1 = 2 := by simpa using hj
              omega
          exact le_antisymm hle (by have hp := hpos 0; omega)
        right; left
        funext i
        fin_cases i
        · simpa [Fin.snoc_castSucc] using hf2
        · simpa [Fin.snoc_last] using hl
    · right; right
      have hf : σ 0 = 1 := by
        have hpen := Good_penult_eq_one_of_last_two (L:=0) ⟨hlen,hpos,hcov,hord⟩ hl
        simpa using hpen
      funext i
      fin_cases i
      · simpa [Fin.snoc, hf]
      · simpa [Fin.snoc, hl]
  · intro h
    rcases h with h | h | h
    · subst h
      exact Good_snoc_one (by simpa [Good] using (Good_fin_one_iff (fun _ : Fin 1 => 1)).2 rfl)
    · subst h
      exact Good_snoc_succ_one (by simpa [Good] using (Good_fin_one_iff (fun _ : Fin 1 => 1)).2 rfl)
    · subst h
      dsimp [Good]
      refine ⟨by omega, ?_, ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [Fin.snoc]
      · intro k hk
        have hsup : Finset.univ.sup (Fin.snoc (Fin.snoc (fun i : Fin 0 => i.elim0) 1) 2 : Fin 2 → ℕ) = 2 := by
          rw [sup_snoc]
          rw [sup_snoc]
          norm_num
        rw [hsup] at hk
        have hk12 : k = 1 ∨ k = 2 := by omega
        rcases hk12 with rfl | rfl
        · exact ⟨0, by norm_num [Fin.snoc]⟩
        · exact ⟨1, by norm_num [Fin.snoc]⟩
      · intro i j hij hnadj
        fin_cases i <;> fin_cases j <;> simp [Fin.snoc] at hij hnadj ⊢

theorem exists_good_fin : ∀ n : ℕ, ∃ F : Finset (Fin (n+1) → ℕ), F.toSet = {σ | Good (n+1) σ} ∧ F.card = a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    classical
    rcases n with _ | _ | n
    · refine ⟨{(fun _ : Fin 1 => 1)}, ?_, ?_⟩
      · ext σ; simp [Good_fin_one_iff]
      · simp [a]
    · let s1 : Fin 2 → ℕ := Fin.snoc (fun _ : Fin 1 => 1) 1
      let s2 : Fin 2 → ℕ := Fin.snoc (fun _ : Fin 1 => 2) 1
      let s3 : Fin 2 → ℕ := Fin.snoc (Fin.snoc (fun i : Fin 0 => i.elim0) 1) 2
      refine ⟨{s1, s2, s3}, ?_, ?_⟩
      · ext σ
        simp [Good_fin_two_iff, s1, s2, s3]
      · have h12 : s1 ≠ s2 := by
          intro h
          have := congr_fun h (0 : Fin 2)
          norm_num [s1, s2, Fin.snoc] at this
        have h13 : s1 ≠ s3 := by
          intro h
          have := congr_fun h (1 : Fin 2)
          norm_num [s1, s3, Fin.snoc] at this
        have h23 : s2 ≠ s3 := by
          intro h
          have := congr_fun h (0 : Fin 2)
          norm_num [s2, s3, Fin.snoc] at this
        simp [s1, s2, s3, h12, h13, h23, a]
    · obtain ⟨F1, hF1, hc1⟩ := ih (n+1) (by omega)
      obtain ⟨F0, hF0, hc0⟩ := ih n (by omega)
      let FA := F1.map (embLast1 (n+2))
      let FB := F1.map (embSuccLast1 (n+2))
      let FC := F0.map (embSuccLast12 (n+1))
      let FD := F0.map (embAddTwoLast12 (n+1))
      let F := (FA ∪ FB) ∪ (FC ∪ FD)
      have hF1Good : ∀ σ, σ ∈ F1 → Good (n+2) σ := by
        intro σ hσ
        have hs : σ ∈ (F1 : Set (Fin (n+2) → ℕ)) := hσ
        change σ ∈ F1.toSet at hs
        rw [hF1] at hs
        exact hs
      have hF0Good : ∀ σ, σ ∈ F0 → Good (n+1) σ := by
        intro σ hσ
        have hs : σ ∈ (F0 : Set (Fin (n+1) → ℕ)) := hσ
        change σ ∈ F0.toSet at hs
        rw [hF0] at hs
        exact hs
      have hAB : Disjoint FA FB := by simpa [FA, FB] using disjoint_last1_succLast1 (F:=F1) hF1Good
      have hCD : Disjoint FC FD := by simpa [FC, FD] using disjoint_last12_addtwo (F:=F0) hF0Good
      have hAC : Disjoint FA FC := by simpa [FA, FC] using (disjoint_last1_last2_A (L:=n+1) (F₁:=F1) (F₀:=F0))
      have hAD : Disjoint FA FD := by simpa [FA, FD] using (disjoint_last1_last2_B (L:=n+1) (F₁:=F1) (F₀:=F0))
      have hBC : Disjoint FB FC := by simpa [FB, FC] using (disjoint_succLast1_last2_A (L:=n+1) (F₁:=F1) (F₀:=F0))
      have hBD : Disjoint FB FD := by simpa [FB, FD] using (disjoint_succLast1_last2_B (L:=n+1) (F₁:=F1) (F₀:=F0))
      have hA_CD : Disjoint FA (FC ∪ FD) := by
        rw [Finset.disjoint_left]
        intro x hx hy
        rw [Finset.mem_union] at hy
        rcases hy with hy | hy
        · exact (Finset.disjoint_left.mp hAC hx) hy
        · exact (Finset.disjoint_left.mp hAD hx) hy
      have hB_CD : Disjoint FB (FC ∪ FD) := by
        rw [Finset.disjoint_left]
        intro x hx hy
        rw [Finset.mem_union] at hy
        rcases hy with hy | hy
        · exact (Finset.disjoint_left.mp hBC hx) hy
        · exact (Finset.disjoint_left.mp hBD hx) hy
      have hAB_CD : Disjoint (FA ∪ FB) (FC ∪ FD) := by
        rw [Finset.disjoint_left]
        intro x hx hy
        rw [Finset.mem_union] at hx
        rcases hx with hx | hx
        · exact (Finset.disjoint_left.mp hA_CD hx) hy
        · exact (Finset.disjoint_left.mp hB_CD hx) hy
      refine ⟨F, ?_, ?_⟩
      · ext τ
        simp [F, FA, FB, FC, FD, Finset.mem_map, hF1, hF0, Good_classify (Nat.succ_pos n) τ, eq_comm]
      · dsimp [F]
        rw [Finset.card_union_of_disjoint hAB_CD]
        rw [Finset.card_union_of_disjoint hAB]
        rw [Finset.card_union_of_disjoint hCD]
        simp [FA, FB, FC, FD, Finset.card_map, hc1, hc0, a]
        omega








/--
A028859 Conjecture: Also the number of length $n + 1$ sequences that cover an initial
interval of positive integers and whose non-adjacent parts are weakly decreasing.

Formally: The cardinality of the set of sequences $\sigma :     ext{Fin}(n+1)   o \mathbb{N}$
satisfying the two properties is equal to $a(n)$.
-/
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
  classical
  obtain ⟨F, hF, hcard⟩ := exists_good_fin n
  refine ⟨F, ?_, hcard⟩
  simpa [Good] using hF



