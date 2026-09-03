import Submission.CriticalCommonDensity

/-!
Schwartz–Zippel restrictions on maximal-common-neighbor tuples at critical
density. Polynomial coordinate hypotheses are explicit: this is not a
universal obstruction to arbitrary graphs or a resolution of Erdős714.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714PolynomialExceptionalDensity
open Erdos714Packing Erdos714CriticalCommonDensity
variable {F : Type*} [Field F] [Fintype F]

/-- A nonzero polynomial in a positive number of variables vanishes at
at most its total degree times q^(n-1) points of a finite field. -/
theorem zero_card (n : ℕ) (hn : 0 < n) (p : MvPolynomial (Fin n) F)
    (hp : p ≠ 0) :
    (univ.filter (fun x : Fin n → F => MvPolynomial.eval x p = 0)).card ≤
      p.totalDegree * Fintype.card F^(n-1) := by
  have h := MvPolynomial.schwartz_zippel_totalDegree hp (univ : Finset F)
  simp only [Fintype.piFinset_univ, card_univ] at h
  have hq : (0 : ℚ≥0) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have h' := (div_le_div_iff₀ (pow_pos hq n) hq).mp h
  have h'' :
      (univ.filter (fun x : Fin n → F => MvPolynomial.eval x p = 0)).card *
        Fintype.card F ≤ p.totalDegree * Fintype.card F^n := by
    exact_mod_cast h'
  have hn' : n = (n-1)+1 := by omega
  have hpw : Fintype.card F^n = Fintype.card F^(n-1)*Fintype.card F := by
    conv_lhs => rw [hn', pow_succ]
  rw [hpw, ← mul_assoc] at h''
  exact Nat.le_of_mul_le_mul_right h'' Fintype.card_pos

/-- Restricting the zero set to any injectively encoded finite family can
only decrease its size. -/
theorem encoded_zero_card {T : Type*} [Fintype T]
    (n : ℕ) (hn : 0 < n) (enc : T ↪ (Fin n → F))
    (p : MvPolynomial (Fin n) F) (hp : p ≠ 0) :
    (univ.filter (fun t => MvPolynomial.eval (enc t) p = 0)).card ≤
      p.totalDegree * Fintype.card F^(n-1) := by
  have hsub :
      (univ.filter (fun t => MvPolynomial.eval (enc t) p = 0)).map enc ⊆
      univ.filter (fun x => MvPolynomial.eval x p = 0) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := mem_map.mp hx
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ht).2⟩
  have hc := card_le_card hsub
  rw [card_map] at hc
  exact hc.trans (zero_card n hn p hp)

variable {A B : Type*} [Fintype A] [Fintype B]

/-- At critical density, the maximal common-neighbor tuples cannot all
lie on a hypersurface of degree D once q exceeds an explicit constant
multiple of D. The tuple encoding is required to be injective. -/
theorem polynomial_budget (S : A → Finset B) (r C : ℕ) (hr : 2 ≤ r)
    (hC : 0 < C) (hq : 2*(r-1)*(2*C)^(r-1) ≤ Fintype.card F)
    (hA : Fintype.card A ≤ Fintype.card F^r)
    (hB : Fintype.card B ≤ Fintype.card F^r)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free (incidence S))
    (he : Fintype.card F^(2*r-1) ≤ C*(∑ a, (S a).card))
    (enc : (Fin r ↪ A) ↪ (Fin (r^2) → F))
    (p : MvPolynomial (Fin (r^2)) F) (hp : p ≠ 0)
    (hvanish : ∀ f ∈ maximalCommon S r, MvPolynomial.eval (enc f) p = 0) :
    Fintype.card F ≤ (2*(2*C)^(r-1))^r*(r-1).factorial*p.totalDegree := by
  apply exceptional_budget S r (Fintype.card F) C p.totalDegree hr hC hq
    hA hB hfree he (univ.filter (fun f => MvPolynomial.eval (enc f) p = 0))
    (encoded_zero_card (r^2) (by positivity) enc p hp)
  intro f hf
  have hb := (free_iff_common_card S (by omega : 0 < r)).mp hfree f
  have hn : (common S f).card ≠ r-1 := by
    intro hc
    apply hf
    exact mem_filter.mpr ⟨mem_univ _, hvanish f (mem_filter.mpr ⟨mem_univ _, hc⟩)⟩
  omega

/-- Encode an ordered tuple of rows by listing all their field coordinates. -/
def tupleEncoding (m n : ℕ) (e : A ↪ (Fin n → F)) :
    (Fin m ↪ A) ↪ (Fin (m*n) → F) where
  toFun f j := e (f (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2
  inj' := by
    intro f g h
    apply DFunLike.ext
    intro i
    apply e.injective
    funext j
    have h' := congrFun h (finProdFinEquiv (i,j))
    simpa only [Equiv.symm_apply_apply] using h'

def squareTupleEncoding (r : ℕ) (e : A ↪ (Fin r → F)) :
    (Fin r ↪ A) ↪ (Fin (r^2) → F) := by
  simpa only [pow_two] using tupleEncoding r r e

/-- Row coordinates automatically supply the tuple encoding and row count. -/
theorem coordinate_polynomial_budget (S : A → Finset B) (r C : ℕ) (hr : 2 ≤ r)
    (hC : 0 < C) (hq : 2*(r-1)*(2*C)^(r-1) ≤ Fintype.card F)
    (e : A ↪ (Fin r → F)) (hB : Fintype.card B ≤ Fintype.card F^r)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free (incidence S))
    (he : Fintype.card F^(2*r-1) ≤ C*(∑ a, (S a).card))
    (p : MvPolynomial (Fin (r^2)) F) (hp : p ≠ 0)
    (hvanish : ∀ f ∈ maximalCommon S r,
      MvPolynomial.eval (squareTupleEncoding r e f) p = 0) :
    Fintype.card F ≤ (2*(2*C)^(r-1))^r*(r-1).factorial*p.totalDegree := by
  have hA : Fintype.card A ≤ Fintype.card F^r := by
    simpa only [Fintype.card_fun, Fintype.card_fin] using Fintype.card_le_of_injective _ e.injective
  exact polynomial_budget S r C hr hC hq hA hB hfree he
    (squareTupleEncoding r e) p hp hvanish

/-- An exact degree-r separable all-root model outside one nonzero
polynomial's zero set is incompatible with unbounded critical families.
Equality with the count of ALL roots, not a root injection, is required. -/
theorem polynomial_separable_model_budget (S : A → Finset B) (r C : ℕ) (hr : 2 ≤ r)
    (hC : 0 < C) (hq : 2*(r-1)*(2*C)^(r-1) ≤ Fintype.card F)
    (e : A ↪ (Fin r → F)) (hB : Fintype.card B ≤ Fintype.card F^r)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free (incidence S))
    (he : Fintype.card F^(2*r-1) ≤ C*(∑ a, (S a).card))
    (P : MvPolynomial (Fin (r^2)) F) (hP : P ≠ 0)
    (p : (Fin r ↪ A) → Polynomial F)
    (hmodel : ∀ f, MvPolynomial.eval (squareTupleEncoding r e f) P ≠ 0 →
      (p f).natDegree = r ∧ (p f).Separable ∧
      (common S f).card = (p f).roots.toFinset.card) :
    Fintype.card F ≤ (2*(2*C)^(r-1))^r*(r-1).factorial*P.totalDegree := by
  apply coordinate_polynomial_budget S r C hr hC hq e hB hfree he P hP
  intro f hf
  by_contra hn
  obtain ⟨hd, hs, hc⟩ := hmodel f hn
  have hf' := (mem_filter.mp hf).2
  exact separable_not_degree_sub_one (p f) r (by omega) hd hs (hc.symm.trans hf')

#print axioms tupleEncoding
#print axioms coordinate_polynomial_budget
#print axioms polynomial_separable_model_budget
#print axioms zero_card
#print axioms encoded_zero_card
#print axioms polynomial_budget
end Erdos714PolynomialExceptionalDensity
