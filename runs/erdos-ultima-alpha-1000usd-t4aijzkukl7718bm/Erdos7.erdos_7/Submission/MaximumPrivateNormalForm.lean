import Submission.PrivateRefinementIsolation

/-!
# Minimum-cardinality, maximum-modulus private normal form

At a fixed nonzero common period one may minimize cardinality and then
maximize the total modulus. Every strict private refinement in this normal
form is an existing label, isolated in its coarse residue. Divisor closure
from a DIFFERENT minimum-sum normalization is not asserted here.
-/

namespace Erdos7MaximumPrivateNormalForm
open Erdos7PrivateReplacement
open Erdos7PrivateRefinementIsolation
open Erdos7ExchangePrivateTransfer (LabelMinimal)
open scoped BigOperators

variable {I J : Type*}

lemma reindex_cover (N : ℕ) (m : I → ℕ) (a : I → ℤ)
    (h : OddCover N m a) (e : J ≃ I) :
    OddCover N (m ∘ e) (a ∘ e) := by
  refine ⟨h.1.comp e.injective, fun j => h.2.1 (e j), ?_⟩
  intro x
  obtain ⟨i,hi⟩ := h.2.2 x
  exact ⟨e.symm i,by simpa using hi⟩

/-- Minimum cardinality at the supplied period implies minimality for every
residue assignment on the same labels, not just irredundance of the old one. -/
theorem label_minimal_of_minimum_cardinality (N r : ℕ)
    (m : Fin r → ℕ) (a : Fin r → ℤ) (hc : OddCover N m a)
    (hmin : ∀ s (n : Fin s → ℕ) (b : Fin s → ℤ), OddCover N n b → r ≤ s) :
    LabelMinimal m := by
  classical
  change ∀ (b : Fin r → ℤ) (j : Fin r), ∃ x : ℤ, ∀ k, k ≠ j → ¬ (m k : ℤ) ∣ x-b k
  intro b j
  by_contra h
  have hcov : ∀ x : ℤ, ∃ k, k ≠ j ∧ (m k : ℤ) ∣ x-b k := by
    intro x
    by_contra hx
    exact h ⟨x,fun k hkj hk => hx ⟨k,hkj,hk⟩⟩
  let K := {k : Fin r // k ≠ j}
  have hk : OddCover N (fun k : K => m k) (fun k : K => b k) := by
    refine ⟨hc.1.comp Subtype.val_injective, fun k => hc.2.1 k, ?_⟩
    intro x
    obtain ⟨k,hkj,hk⟩ := hcov x
    exact ⟨⟨k,hkj⟩,hk⟩
  have hf := reindex_cover N _ _ hk (Fintype.equivFin K).symm
  have hle := hmin (Fintype.card K) _ _ hf
  have hlt : Fintype.card K < r := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_subtype_lt (p := fun k : Fin r => k ≠ j) (x := j) (by simp))
  omega

/-- The refinement-isolation conclusion applies to every larger compatible
private modulus, whether or not its presence was known beforehand. -/
theorem private_refinement_isolated [Fintype I] [DecidableEq I]
    (N : ℕ) (m : I → ℕ) (a : I → ℤ) (hc : OddCover N m a)
    (hminimal : LabelMinimal m)
    (hmax : ∀ (n : I → ℕ) (c : I → ℤ), OddCover N n c →
      (∑ j, n j) ≤ ∑ j, m j)
    (i : I) (d : ℕ) (hd : 1 < d ∧ Odd d ∧ d ∣ N)
    (hlt : m i < d) (hdiv : m i ∣ d) (b : ℤ)
    (hp : ∀ x, Private m a i x → (d : ℤ) ∣ x-b) :
    ∃ j, j ≠ i ∧ m j = d ∧
      ∀ k, k ≠ i → k ≠ j → m i ∣ m k → ¬ (m i : ℤ) ∣ a k-a j := by
  obtain ⟨j,hj⟩ := private_refinement_label_exists N m a hc hmax i d hd hlt b hp
  have hji : j ≠ i := by
    intro h
    subst j
    omega
  refine ⟨j,hji,hj,?_⟩
  apply refinement_forces_isolation m a hminimal hc.2.2 i j hji
    (by simpa only [hj] using hdiv) b
  simpa only [hj] using hp

/-- A genuine existence theorem for the new normal form. It preserves the
supplied period and does not increase class count. It does NOT claim divisor
closure, which comes from minimizing rather than maximizing the modulus sum. -/
theorem exists_minimum_maximum_cover [Fintype I]
    (N : ℕ) (hN : N ≠ 0) (m : I → ℕ) (a : I → ℤ) (hc : OddCover N m a) :
    ∃ r ≤ Fintype.card I, ∃ (n : Fin r → ℕ) (c : Fin r → ℤ),
      OddCover N n c ∧ LabelMinimal n ∧
      (∀ s (l : Fin s → ℕ) (b : Fin s → ℤ), OddCover N l b → r ≤ s) ∧
      (∀ (l : Fin r → ℕ) (b : Fin r → ℤ), OddCover N l b →
        (∑ i, l i) ≤ ∑ i, n i) := by
  classical
  let P (r : ℕ) := ∃ (n : Fin r → ℕ) (c : Fin r → ℤ), OddCover N n c
  have hex : ∃ r, P r := ⟨Fintype.card I, _, _,
    reindex_cover N m a hc (Fintype.equivFin I).symm⟩
  obtain ⟨n₀,c₀,hn₀⟩ := Nat.find_spec hex
  obtain ⟨n,c,hn,_,hmax⟩ := exists_maximum_sum_cover N hN n₀ c₀ hn₀
  have hmin : ∀ s (l : Fin s → ℕ) (b : Fin s → ℤ),
      OddCover N l b → Nat.find hex ≤ s := by
    intro s l b hl
    exact Nat.find_min' hex ⟨l,b,hl⟩
  refine ⟨Nat.find hex, hmin _ _ _
    (reindex_cover N m a hc (Fintype.equivFin I).symm), n,c,hn,?_,hmin,hmax⟩
  exact label_minimal_of_minimum_cardinality N (Nat.find hex) n c hn hmin

#print axioms reindex_cover
#print axioms label_minimal_of_minimum_cardinality
#print axioms private_refinement_isolated
#print axioms exists_minimum_maximum_cover

end Erdos7MaximumPrivateNormalForm
