import Submission.ComponentEight

/-! A concrete obstruction to reducing large prime steps by subdivision.
This is not a disproof of the Gaussian moat conjecture. -/
namespace Erdos952Investigation
namespace PrimeStepSubdivisionCounterexample
set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma prime_of_prime_norm {z : GaussianInt} (hz : Prime z.norm) : Prime z := by
  apply irreducible_iff_prime.mp
  refine ⟨fun h => hz.not_unit ((Zsqrtd.isUnit_iff_norm_isUnit z).mp h),?_⟩
  intro a b hab
  have hh : z.norm = a.norm*b.norm := by rw [hab,Zsqrtd.norm_mul]
  exact (hz.irreducible.isUnit_or_isUnit hh).imp
    (Zsqrtd.isUnit_iff_norm_isUnit a).mpr (Zsqrtd.isUnit_iff_norm_isUnit b).mpr

lemma prime_seventeen_two : Prime (⟨17,2⟩ : GaussianInt) := by
  apply prime_of_prime_norm
  norm_num [gaussian_norm_sq]

lemma prime_nineteen : Prime (19 : GaussianInt) := by
  letI : Fact (Nat.Prime 19) := ⟨by decide⟩
  exact (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime 19).mpr rfl

lemma component8_of_reachable {z w : GaussianInt} (hz : InComponent8 z)
    (h : (primeGraph 8).Reachable z w) : InComponent8 w := by
  obtain ⟨p⟩ := h
  revert hz
  induction p with
  | nil => exact id
  | cons hzw p ih =>
    intro hz
    exact ih (inComponent8_closed hz hzw.2.1 hzw.2.2.2)

lemma seventeen_two_not_reachable_nineteen :
    ¬ (primeGraph 8).Reachable (⟨17,2⟩ : GaussianInt) (19 : GaussianInt) := by
  intro h
  have hz : InComponent8 (⟨17,2⟩ : GaussianInt) := by decide +kernel
  have hw : ¬ InComponent8 (19 : GaussianInt) := by decide +kernel
  exact hw (component8_of_reachable hz h)

lemma seventeen_two_adj_nineteen :
    (primeGraph 10).Adj (⟨17,2⟩ : GaussianInt) (19 : GaussianInt) := by
  refine ⟨prime_seventeen_two,prime_nineteen,by decide,?_⟩
  norm_num [gaussian_norm_sq]

/-- Some bound-ten prime edges cannot be subdivided into bound-eight prime
walks, even allowing arbitrarily many intermediate prime vertices. -/
theorem subdivision_counterexample :
    ∃ z w : GaussianInt, (primeGraph 10).Adj z w ∧
      ¬ (primeGraph 8).Reachable z w :=
  ⟨⟨17,2⟩,19,seventeen_two_adj_nineteen,seventeen_two_not_reachable_nineteen⟩

theorem not_every_edge_subdivides :
    ¬ ∀ z w : GaussianInt, (primeGraph 10).Adj z w →
      (primeGraph 8).Reachable z w := by
  intro h
  exact seventeen_two_not_reachable_nineteen (h _ _ seventeen_two_adj_nineteen)

#print axioms subdivision_counterexample
#print axioms not_every_edge_subdivides
end PrimeStepSubdivisionCounterexample
end Erdos952Investigation
