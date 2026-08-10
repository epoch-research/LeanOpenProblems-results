import FormalConjectures.Util.ProblemImports
open Set

example : IsSidon ({0,2} : Set ℕ) := by
  -- should be Sidon
  intro i hi j hj k hk l hl hsum
  simp at hi hj hk hl
  omega

example : ¬ IsSidon ({0,1,2} : Set ℕ) := by
  intro h
  have bad := h 0 (by simp) 2 (by simp) 1 (by simp) 1 (by simp) (by norm_num : 0 + 1 = 2 + 1)
  -- wait variable order in IsSidon: i1+j? check hsum is i1+i2 = j1+j2, so choose i1=0,j1=1,i2=2,j2=1 gives 2=2
  simp at bad

example : False := by
  have h02 : IsSidon ({0,2} : Set ℕ) := by
    intro i hi j hj k hk l hl hsum
    simp at hi hj hk hl
    omega
  -- Try theorem to insert 1 and prove Sidon {0,2} ∪ {1} = {0,1,2}; RHS should fail.
  have hiff := Set.IsSidon.insert (A := ({0,2} : Set ℕ)) (m := 1) h02
  have rhs : (1 ∈ ({0,2} : Set ℕ) ∨ ∀ᵉ (a ∈ ({0,2} : Set ℕ)) (b ∈ ({0,2} : Set ℕ)), 1 + 1 ≠ a + b ∧ ∀ c ∈ ({0,2} : Set ℕ), 1 + a ≠ b + c) := by
    right
    simp
  have hsidon_union : IsSidon (({0,2} : Set ℕ) ∪ {1}) := hiff.mpr rhs
  have hnot : ¬ IsSidon (({0,2} : Set ℕ) ∪ {1}) := by
    intro h
    have bad := h 0 (by simp) 1 (by simp) 2 (by simp) 1 (by simp) (by norm_num : 0 + 2 = 1 + 1)
    simp at bad
  exact hnot hsidon_union
