import FormalConjecturesUtil

/-!
# A finite-prefix compactness reduction for Sidon sets

This file proves only the compactness reduction: it assumes the existence of finite
Sidon sets satisfying all prescribed counting inequalities through each finite bound.
It does not prove those finite existence statements.
-/

namespace Erdos39

private def sidonPrefix (K : ℕ) (f : ℕ → Bool) : Set ℕ :=
  {n | n ≤ K ∧ f n = true}

private def finiteSidonPrefix (K : ℕ) (f : Fin (K + 1) → Bool) : Set ℕ :=
  {n | ∃ hn : n < K + 1, f ⟨n, hn⟩ = true}

private theorem finiteSidonPrefix_restrict (K : ℕ) (f : ℕ → Bool) :
    finiteSidonPrefix K (fun i => f i) = sidonPrefix K f := by
  ext n
  simp [finiteSidonPrefix, sidonPrefix]

private theorem interval_inter_sidonPrefix (f : ℕ → Bool) {N K : ℕ} (hNK : N ≤ K) :
    Set.Icc 1 N ∩ sidonPrefix K f = Set.Icc 1 N ∩ {n | f n = true} := by
  ext n
  simp only [Set.mem_inter_iff, Set.mem_Icc, sidonPrefix, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hn, _, hf⟩
    exact ⟨hn, hf⟩
  · rintro ⟨hn, hf⟩
    exact ⟨hn, hn.2.trans hNK, hf⟩

private def goodSidonPrefix (bound : ℕ → ℕ) (K : ℕ) : Set (ℕ → Bool) :=
  {f | IsSidon (sidonPrefix K f) ∧
    ∀ N ≤ K, bound N ≤ (Set.Icc 1 N ∩ sidonPrefix K f).ncard}

private theorem isClosed_goodSidonPrefix (bound : ℕ → ℕ) (K : ℕ) :
    IsClosed (goodSidonPrefix bound K) := by
  let r : (ℕ → Bool) → (Fin (K + 1) → Bool) := fun f i => f i
  have hr : Continuous r := continuous_pi fun i => continuous_apply i.val
  have heq : goodSidonPrefix bound K = r ⁻¹'
      {g | IsSidon (finiteSidonPrefix K g) ∧
        ∀ N ≤ K, bound N ≤ (Set.Icc 1 N ∩ finiteSidonPrefix K g).ncard} := by
    ext f
    simp only [goodSidonPrefix, Set.mem_setOf_eq, Set.mem_preimage,
      r, finiteSidonPrefix_restrict]
  rw [heq]
  exact (isClosed_discrete _).preimage hr

/-- Finite Sidon witnesses satisfying all prefix bounds simultaneously up to `K`
yield a single Sidon set satisfying the bounds for every `N`. The witnesses need
not be contained in `[1,K]`, and the conclusion does not assert infinitude. -/
theorem finite_prefix_compactness (bound : ℕ → ℕ)
    (h : ∀ K : ℕ, ∃ B : Finset ℕ, IsSidon (B : Set ℕ) ∧
      ∀ N ≤ K, bound N ≤ (Set.Icc 1 N ∩ (B : Set ℕ)).ncard) :
    ∃ A : Set ℕ, IsSidon A ∧ ∀ N, bound N ≤ (Set.Icc 1 N ∩ A).ncard := by
  classical
  have hclosed := isClosed_goodSidonPrefix bound
  have hnonempty : ∀ K, (goodSidonPrefix bound K).Nonempty := by
    intro K
    obtain ⟨B, hB, hcount⟩ := h K
    let f : ℕ → Bool := fun n => decide (n ∈ B)
    have hf : {n | f n = true} = (B : Set ℕ) := by
      ext n
      simp [f]
    refine ⟨f, ?_, ?_⟩
    · exact Set.IsSidon.subset hB fun n hn => by
        rw [← hf]
        exact hn.2
    · intro N hNK
      rw [interval_inter_sidonPrefix f hNK, hf]
      exact hcount N hNK
  have hdecreasing : ∀ K, goodSidonPrefix bound (K + 1) ⊆ goodSidonPrefix bound K := by
    intro K f hf
    refine ⟨Set.IsSidon.subset hf.1
      (fun n hn => ⟨Nat.le_trans hn.1 (by omega), hn.2⟩), ?_⟩
    intro N hNK
    have hNK' : N ≤ K + 1 := by omega
    have hc := hf.2 N hNK'
    rw [interval_inter_sidonPrefix f hNK'] at hc
    rw [interval_inter_sidonPrefix f hNK]
    exact hc
  obtain ⟨f, hf⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (goodSidonPrefix bound) hdecreasing hnonempty (hclosed 0).isCompact hclosed
  have hgood : ∀ K, f ∈ goodSidonPrefix bound K := Set.mem_iInter.mp hf
  refine ⟨{n | f n = true}, ?_, ?_⟩
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
    let K := i₁ + j₁ + i₂ + j₂
    exact (hgood K).1 i₁ ⟨by omega, hi₁⟩ j₁ ⟨by omega, hj₁⟩
      i₂ ⟨by omega, hi₂⟩ j₂ ⟨by omega, hj₂⟩ hsum
  · intro N
    have hc := (hgood N).2 N le_rfl
    rwa [interval_inter_sidonPrefix f le_rfl] at hc

#print axioms finite_prefix_compactness

end Erdos39
