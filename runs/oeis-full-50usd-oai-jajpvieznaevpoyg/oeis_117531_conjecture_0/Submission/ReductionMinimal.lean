import FormalConjectures.Util.ProblemImports
open Finset Nat
noncomputable def a (n : ℕ) : ℕ :=
  let pn : ℕ := Nat.nth Nat.Prime (n - 1)
  Finset.card (Finset.filter (fun k : ℕ => Nat.Prime (k ^ 2 - k + pn)) (Finset.Icc 1 n))

lemma a_lt_iff_exists_bad (n : ℕ) (hn : 1 ≤ n) :
    a n < n ↔ ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (n - 1)) := by
  constructor
  · intro hlt
    by_contra hnot
    push_neg at hnot
    unfold a at hlt
    have hall : ({x ∈ Icc 1 n | Nat.Prime (x ^ 2 - x + nth Nat.Prime (n - 1))} : Finset ℕ) = Icc 1 n := by
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.filter_subset _ _
      · rw [Finset.card_filter]
        -- This is not the right route; leave as probe
        sorry
    sorry
  · intro hbad
    rcases hbad with ⟨k,hk,hkp⟩
    unfold a
    have hss : ({x ∈ Icc 1 n | Nat.Prime (x ^ 2 - x + nth Nat.Prime (n - 1))} : Finset ℕ) ⊂ Icc 1 n := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      have : k ∈ ({x ∈ Icc 1 n | Nat.Prime (x ^ 2 - x + nth Nat.Prime (n - 1))} : Finset ℕ) := by simpa [heq] using hk
      exact hkp ((Finset.mem_filter.mp this).2)
    have hc := Finset.card_lt_card hss
    simpa [Nat.card_Icc, hn] using hc
