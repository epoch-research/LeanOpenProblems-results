import Submission.ResidueBlockLevels
import Submission.ValuationBaselines

/-!
# Finite residue nodes and their sums

A node is a prime in `S`, a bounded level, and a residue below the level's
prime-power modulus.  Only occupied nonself pairs survive in `Node`.
The owner is the prime coordinate.  The uniform cutoff `sumCutoff` is a
simple finite sum bounding every valuation of a labelled pair sum.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos126Aux.ResidueBlocks

variable {ι : Type*} [Fintype ι]

def RawNode (S : Finset ℕ) (M : ℕ) :=
  Σ p : ↥S, Σ k : Fin (M + 1), Fin ((p : ℕ) ^ (k : ℕ))

instance rawNodeFintype (S : Finset ℕ) (M : ℕ) : Fintype (RawNode S M) :=
  inferInstanceAs (Fintype (Σ p : ↥S, Σ k : Fin (M + 1), Fin ((p : ℕ) ^ (k : ℕ))))

def Node (a : ι → ℕ) (S : Finset ℕ) (M : ℕ) :=
  {t : RawNode S M // Active a (t.1 : ℕ) (t.2.1 : ℕ) (t.2.2 : ℕ)}

noncomputable instance nodeFintype (a : ι → ℕ) (S : Finset ℕ) (M : ℕ) :
    Fintype (Node a S M) := by
  classical
  exact inferInstanceAs (Fintype {t : RawNode S M // Active a (t.1 : ℕ) (t.2.1 : ℕ) (t.2.2 : ℕ)})

noncomputable def nodeBlock (a : ι → ℕ) (S : Finset ℕ) (M : ℕ)
    (t : Node a S M) : Paired.Block ι :=
  block a (t.val.1 : ℕ) (t.val.2.1 : ℕ) (t.val.2.2 : ℕ)

def owner (a : ι → ℕ) (S : Finset ℕ) (M : ℕ) (t : Node a S M) : ↥S := t.val.1

theorem nodeBlock_valid (a : ι → ℕ) (S : Finset ℕ) (M : ℕ) (t : Node a S M) :
    (nodeBlock a S M t).Valid := block_valid a _ _ _ t.property

/-- Each owner's entire family has strong oriented laminarity. -/
theorem nodeBlock_coherent (a : ι → ℕ) (S : Finset ℕ) (M : ℕ) (p : ↥S) :
    Paired.Coherent (nodeBlock a S M)
      (Finset.univ.filter (fun t => owner a S M t = p)) := by
  intro t ht v hv
  have ht' : (t.val.1 : ℕ) = (p : ℕ) :=
    congrArg Subtype.val (Finset.mem_filter.1 ht).2
  have hv' : (v.val.1 : ℕ) = (p : ℕ) :=
    congrArg Subtype.val (Finset.mem_filter.1 hv).2
  simpa only [nodeBlock, ht', hv'] using
    block_compatible a (p : ℕ) (t.val.2.1 : ℕ) (t.val.2.2 : ℕ)
      (v.val.2.1 : ℕ) (v.val.2.2 : ℕ)

open Classical in
private theorem sum_nodes (a : ι → ℕ) (S : Finset ℕ) (M : ℕ)
    (f : RawNode S M → ℝ) :
    (∑ t : Node a S M, f t.val) =
      ∑ p : ↥S, ∑ k : Fin (M + 1), ∑ r : Fin ((p : ℕ) ^ (k : ℕ)),
        if Active a (p : ℕ) (k : ℕ) (r : ℕ) then f ⟨p, k, r⟩ else 0 := by
  let A : Finset (RawNode S M) :=
    Finset.univ.filter (fun t => Active a (t.1 : ℕ) (t.2.1 : ℕ) (t.2.2 : ℕ))
  have hA : ∀ t : RawNode S M, t ∈ A ↔
      Active a (t.1 : ℕ) (t.2.1 : ℕ) (t.2.2 : ℕ) := by
    intro t
    simp [A]
  have he : (∑ t : Node a S M, f t.val) = ∑ t ∈ A, f t :=
    (Finset.sum_subtype A hA f).symm
  rw [he]
  unfold A
  rw [Finset.sum_filter]
  change (∑ t : (Σ p : ↥S, Σ k : Fin (M + 1), Fin ((p : ℕ) ^ (k : ℕ))),
      if Active a (t.1 : ℕ) (t.2.1 : ℕ) (t.2.2 : ℕ) then f t else 0) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Fintype.sum_sigma]

/-- The cross sum is exactly the sum of the individual level kernels. -/
theorem crossSum_eq_levels (a : ι → ℕ) (S : Finset ℕ) (M : ℕ) (i j : ι) :
    Paired.crossSum (nodeBlock a S M) i j =
      ∑ p : ↥S, ∑ k : Fin (M + 1), crossLevel a (p : ℕ) (k : ℕ) i j := by
  unfold Paired.crossSum nodeBlock
  exact sum_nodes a S M (fun t => (block a (t.1 : ℕ) (t.2.1 : ℕ) (t.2.2 : ℕ)).cross i j)

/-- The same-side sum is exactly the sum of the retained level kernels. -/
theorem diagSum_eq_levels (a : ι → ℕ) (S : Finset ℕ) (M : ℕ) (i j : ι) :
    Paired.diagSum (nodeBlock a S M) i j =
      ∑ p : ↥S, ∑ k : Fin (M + 1), diagLevel a (p : ℕ) (k : ℕ) i j := by
  unfold Paired.diagSum nodeBlock
  exact sum_nodes a S M (fun t => (block a (t.1 : ℕ) (t.2.1 : ℕ) (t.2.2 : ℕ)).diag i j)

noncomputable def sumCutoff (a : ι → ℕ) (S : Finset ℕ) : ℕ :=
  ∑ p ∈ S, ∑ i, ∑ j, (a i + a j).factorization p

theorem factorization_add_le_sumCutoff (a : ι → ℕ) (S : Finset ℕ)
    (p : ℕ) (hp : p ∈ S) (i j : ι) :
    (a i + a j).factorization p ≤ sumCutoff a S := by
  calc
    _ ≤ ∑ j', (a i + a j').factorization p :=
      Finset.single_le_sum (f := fun j' => (a i + a j').factorization p)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', (a i' + a j').factorization p :=
      Finset.single_le_sum (f := fun i' => ∑ j', (a i' + a j').factorization p)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ ≤ sumCutoff a S := by
      unfold sumCutoff
      exact Finset.single_le_sum (f := fun p' => ∑ i', ∑ j', (a i' + a j').factorization p')
        (fun _ _ => Nat.zero_le _) hp

end Erdos126Aux.ResidueBlocks
