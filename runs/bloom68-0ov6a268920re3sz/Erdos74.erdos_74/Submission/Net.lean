import Mathlib

namespace E74

universe u

variable {V : Type u}

/-- pigeonhole: some scale `R0 * 5^i` (with `i ≤ m*m`) has no pair of distinct points of `W` at
distance in `(R, 5R]`. -/
lemma exists_gap_scale (W : Finset V) (d : V → V → ℕ∞) (R0 m : ℕ)
    (hW : W.card ≤ m) :
    ∃ i, i ≤ m * m ∧ ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' →
      ¬ (((R0 * 5 ^ i : ℕ) : ℕ∞) < d w w' ∧ d w w' ≤ ((5 * (R0 * 5 ^ i) : ℕ) : ℕ∞)) := by
  classical
  by_contra hcon
  push_neg at hcon
  -- for every `i ≤ m*m` there is a bad pair
  have hex : ∀ i : ℕ, i ≤ m * m → ∃ p : V × V, p.1 ∈ W ∧ p.2 ∈ W ∧ p.1 ≠ p.2 ∧
      ((R0 * 5 ^ i : ℕ) : ℕ∞) < d p.1 p.2 ∧ d p.1 p.2 ≤ ((5 * (R0 * 5 ^ i) : ℕ) : ℕ∞) := by
    intro i hi
    obtain ⟨w, hw, w', hw', hne, h1, h2⟩ := hcon i hi
    exact ⟨(w, w'), hw, hw', hne, h1, h2⟩
  obtain ⟨w0, hw0, -⟩ := hcon 0 (Nat.zero_le _)
  haveI : Nonempty V := ⟨w0⟩
  choose! p hp using hex
  have hcard : (Finset.range (m * m + 1)).card ≤ (W ×ˢ W).card := by
    apply Finset.card_le_card_of_injOn p
    · intro i hi
      have hi' : i ≤ m * m := by
        have := Finset.mem_range.1 hi
        omega
      have := hp i hi'
      simp [Finset.mem_product, this.1, this.2.1]
    · intro i hi j hj hij
      have hi' : i ≤ m * m := by
        have := Finset.mem_range.1 hi
        omega
      have hj' : j ≤ m * m := by
        have := Finset.mem_range.1 hj
        omega
      by_contra hne
      have key : ∀ i j : ℕ, i < j → i ≤ m * m → j ≤ m * m → p i = p j → False := by
        intro i j hlt hi hj heq
        obtain ⟨_, _, _, hi1, hi2⟩ := hp i hi
        obtain ⟨_, _, _, hj1, hj2⟩ := hp j hj
        rw [heq] at hi2
        have hle : (5 * (R0 * 5 ^ i) : ℕ) ≤ R0 * 5 ^ j := by
          calc 5 * (R0 * 5 ^ i) = R0 * 5 ^ (i + 1) := by ring
            _ ≤ R0 * 5 ^ j := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hlt)
        have hle' : (((5 * (R0 * 5 ^ i) : ℕ)) : ℕ∞) ≤ ((R0 * 5 ^ j : ℕ) : ℕ∞) := by
          exact_mod_cast hle
        exact absurd (lt_of_le_of_lt (hi2.trans hle') hj1) (lt_irrefl _)
      rcases lt_or_gt_of_ne hne with h | h
      · exact key i j h hi' hj' hij
      · exact key j i h hj' hi' hij.symm
  rw [Finset.card_range, Finset.card_product] at hcard
  have : W.card * W.card ≤ m * m := Nat.mul_le_mul hW hW
  omega

/-- a maximal `R`-separated subset of `W` (a net). -/
lemma exists_net (W : Finset V) (d : V → V → ℕ∞) (hsymm : ∀ x y, d x y = d y x)
    (hself : ∀ x, d x x = 0) (R : ℕ)
    (hgap : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' →
      ¬ ((R : ℕ∞) < d w w' ∧ d w w' ≤ ((5 * R : ℕ) : ℕ∞))) :
    ∃ C : Finset V, C ⊆ W ∧ (∀ w ∈ W, ∃ c ∈ C, d c w ≤ (R : ℕ∞)) ∧
      (∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → ((5 * R : ℕ) : ℕ∞) < d c c') := by
  classical
  let fam : Finset (Finset V) :=
    W.powerset.filter (fun C => ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → (R : ℕ∞) < d c c')
  have hne : fam.Nonempty := ⟨∅, by simp [fam]⟩
  obtain ⟨C, hC⟩ := Finset.exists_maximal hne
  have hCfam : C ∈ fam := hC.1
  have hCW : C ⊆ W := (Finset.mem_powerset.1 (Finset.mem_filter.1 hCfam).1)
  have hCsep : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → (R : ℕ∞) < d c c' :=
    (Finset.mem_filter.1 hCfam).2
  refine ⟨C, hCW, ?_, ?_⟩
  · intro w hw
    by_contra hnone
    push_neg at hnone
    have hwC : w ∉ C := by
      intro hwC
      have := hnone w hwC
      rw [hself] at this
      exact absurd this (by simp)
    have hins : insert w C ∈ fam := by
      refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.insert_subset hw hCW), ?_⟩
      intro c hc c' hc' hcc'
      rcases Finset.mem_insert.1 hc with h1 | h1
      · rcases Finset.mem_insert.1 hc' with h2 | h2
        · exact absurd (h1.trans h2.symm) hcc'
        · rw [h1, hsymm]; exact hnone c' h2
      · rcases Finset.mem_insert.1 hc' with h2 | h2
        · rw [h2]; exact hnone c h1
        · exact hCsep c h1 c' h2 hcc'
    have := hC.2 hins (Finset.subset_insert w C)
    exact hwC (this (Finset.mem_insert_self w C))
  · intro c hc c' hc' hcc'
    have h1 := hCsep c hc c' hc' hcc'
    by_contra hle
    push_neg at hle
    exact hgap c (hCW hc) c' (hCW hc') hcc' ⟨h1, hle⟩

end E74
