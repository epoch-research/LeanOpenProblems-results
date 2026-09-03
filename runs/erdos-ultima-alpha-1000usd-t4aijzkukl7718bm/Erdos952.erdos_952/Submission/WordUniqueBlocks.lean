import FormalConjecturesUtil

/-! A combinatorial characterization of words with finite distinguishing
blocks at every position. -/
namespace Erdos952Investigation
namespace WordUniqueBlocks
set_option maxHeartbeats 0

variable {α : Type*}

def NoRecurrentSuffix (w : ℕ → α) : Prop :=
  ∀ a : ℕ, ∃ L N : ℕ, ∀ b ≥ N, ∃ i < L, w (b+i) ≠ w (a+i)

lemma equal_suffixes_of_le {w : ℕ → α} (hw : NoRecurrentSuffix w)
    {a b : ℕ} (hab : a ≤ b) (he : ∀ i, w (a+i) = w (b+i)) : a = b := by
  by_contra hne
  have hk : 0 < b-a := by omega
  have hperiod (m i : ℕ) : w (a+(b-a)*m+i) = w (a+i) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hh : a+(b-a)*(m+1)+i = b+((b-a)*m+i) := by
        rw [Nat.mul_add,Nat.mul_one]
        omega
      rw [hh,← he,← Nat.add_assoc,ih]
  obtain ⟨L,N,hN⟩ := hw a
  have hbig : N ≤ a+(b-a)*(N+1) := by nlinarith
  obtain ⟨i,hi,hni⟩ := hN (a+(b-a)*(N+1)) hbig
  exact hni (hperiod (N+1) i)

lemma equal_suffixes {w : ℕ → α} (hw : NoRecurrentSuffix w)
    {a b : ℕ} (he : ∀ i, w (a+i) = w (b+i)) : a = b := by
  rcases le_total a b with hab | hba
  · exact equal_suffixes_of_le hw hab he
  · exact (equal_suffixes_of_le hw hba (fun i => (he i).symm)).symm

/-- An infinite word with no recurrent suffix has a finite distinguishing
block at every position. -/
theorem unique_block {w : ℕ → α} (hw : NoRecurrentSuffix w) (a : ℕ) :
    ∃ L : ℕ, 0 < L ∧ ∀ b : ℕ, (∀ i < L, w (b+i) = w (a+i)) → b = a := by
  classical
  obtain ⟨L,N,hN⟩ := hw a
  have hf (b : Fin N) : ∃ K : ℕ, (∀ i < K, w (b.val+i) = w (a+i)) → b.val = a := by
    by_cases hba : b.val = a
    · exact ⟨0,fun _ => hba⟩
    · have he : ∃ i, w (b.val+i) ≠ w (a+i) := by
        by_contra! hh
        exact hba (equal_suffixes hw hh)
      obtain ⟨i,hi⟩ := he
      exact ⟨i+1,fun hh => False.elim (hi (hh i (by omega)))⟩
  choose K hK using hf
  let M := (Finset.univ : Finset (Fin N)).sup K
  refine ⟨max (max L M) 1,by omega,?_⟩
  intro b hb
  by_cases hsmall : b < N
  · apply hK ⟨b,hsmall⟩
    intro i hi
    have hKM : K ⟨b,hsmall⟩ ≤ M := Finset.le_sup (Finset.mem_univ _)
    exact hb i (by omega)
  · obtain ⟨i,hi,hni⟩ := hN b (by omega)
    exact False.elim (hni (hb i (by omega)))

lemma no_recurrent_suffix_of_unique_block {w : ℕ → α}
    (hw : ∀ a, ∃ L, ∀ b, (∀ i < L, w (b+i) = w (a+i)) → b = a) :
    NoRecurrentSuffix w := by
  intro a
  obtain ⟨L,hL⟩ := hw a
  refine ⟨L,a+1,?_⟩
  intro b hb
  by_contra! he
  have hh := hL b he
  omega

#print axioms unique_block
end WordUniqueBlocks
end Erdos952Investigation
