import Submission.ProfileThinning

/-!
Arbitrary edge thinnings of translated level-set graphs. In particular, shifting
quadratic-norm curves by an arbitrary function does not avoid a complete-block
cover. This is a construction obstruction, not a solution of Erdős 714.
-/
noncomputable section
open Finset SimpleGraph Classical
set_option maxHeartbeats 2000000
namespace Erdos714TranslatedFibers

variable {G T : Type*} [AddCommGroup G] [Fintype G] [Fintype T]

/-- A translated level set in each second-coordinate slice. -/
def graph (ν : G → T) (f : G → G) (g : G → T) :
    SimpleGraph ((G × G) ⊕ (G × G)) :=
  Erdos714Tensor.incidence fun x y => ν (x.1+y.1-f (x.2+y.2)) = g (x.2+y.2)

/-- Only the number and sizes of the level sets matter; f and g are arbitrary.
The bound applies to every edge subgraph, not only induced vertex restrictions. -/
theorem thinning_fourth_power (ν : G → T) (f : G → G) (g : G → T)
    (q : ℕ) (hq : 0 < q) (hG : Fintype.card G ≤ q^2) (hT : Fintype.card T ≤ q)
    (hν : ∀ r, (univ.filter (fun x => ν x = r)).card ≤ q+1)
    (H : SimpleGraph ((G × G) ⊕ (G × G))) (hH : H ≤ graph ν f g)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 21233664*q^27 := by
  let J := Erdos714ProfileChunks.Index g (q+1)
  let I := G × G × J
  let L (p : I) : Finset ((G × G) ⊕ (G × G)) :=
    (univ.filter (fun z => ν z = p.2.2.1)).map
      ⟨fun z => Sum.inl (p.2.1+z,p.1), by
        intro z w h
        exact add_left_cancel (congrArg Prod.fst (Sum.inl.inj h))⟩
  let R (p : I) : Finset ((G × G) ⊕ (G × G)) :=
    (Erdos714ProfileChunks.block g (q+1) p.2.2).map
      ⟨fun t => Sum.inr (f t-p.2.1,t-p.1), by
        intro t u h
        exact sub_left_injective (congrArg Prod.snd (Sum.inr.inj h))⟩
  have hsize (p : I) : (L p ∪ R p).card ≤ 2*(q+1) := by
    have hl : (L p).card ≤ q+1 := by simpa only [L, card_map] using hν p.2.2.1
    have hr : (R p).card ≤ q+1 := by
      simpa only [R, card_map] using Erdos714ProfileChunks.block_size g (q+1) (by omega) p.2.2
    have hh := card_union_le (L p) (R p)
    omega
  have hforward (x y : G × G)
      (h : ν (x.1+y.1-f (x.2+y.2)) = g (x.2+y.2)) :
      ∃ p : I, Sum.inl x ∈ L p ∪ R p ∧ Sum.inr y ∈ L p ∪ R p := by
    let t := x.2+y.2
    let w := f t-y.1
    obtain ⟨j,hj⟩ := Erdos714ProfileChunks.block_cover g (q+1) t
    have hp := Erdos714ProfileChunks.block_profile g (q+1) j hj
    refine ⟨(x.2,w,j), mem_union_left _ (mem_map.mpr ⟨x.1-w, ?_, ?_⟩),
      mem_union_right _ (mem_map.mpr ⟨t,hj,?_⟩)⟩
    · apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      change ν (x.1-w) = j.1
      rw [show x.1-w = x.1+y.1-f (x.2+y.2) by dsimp [w,t]; abel]
      exact h.trans hp
    · change Sum.inl (w+(x.1-w),x.2) = Sum.inl x
      apply congrArg Sum.inl
      apply Prod.ext
      · dsimp; abel
      · rfl
    · change Sum.inr (f t-w,t-x.2) = Sum.inr y
      simp [w,t, add_sub_cancel_left]
  have hcover : ∀ v w, H.Adj v w → ∃ p : I, v ∈ L p ∪ R p ∧ w ∈ L p ∪ R p := by
    intro v w hvw
    have h := hH hvw
    cases v with
    | inl x =>
      cases w with
      | inl z => exact False.elim h
      | inr y => exact hforward x y h
    | inr y =>
      cases w with
      | inr z => exact False.elim h
      | inl x =>
        obtain ⟨p,hx,hy⟩ := hforward x y h
        exact ⟨p,hy,hx⟩
  have hj : Fintype.card J ≤ 2*q := by
    have h := Erdos714ProfileChunks.cardinality_budget g (q+1)
    have hh : (q+1)*Fintype.card J ≤ (q+1)*(2*q) := by
      calc
        _ ≤ Fintype.card G+(q+1)*Fintype.card T := h
        _ ≤ q^2+(q+1)*q := Nat.add_le_add hG (Nat.mul_le_mul_left _ hT)
        _ ≤ _ := by nlinarith
    exact Nat.le_of_mul_le_mul_left hh (by omega)
  have hi : Fintype.card I ≤ 2*q^5 := by
    calc
      _ = Fintype.card G*(Fintype.card G*Fintype.card J) := by simp [I]
      _ ≤ q^2*(q^2*(2*q)) := by gcongr
      _ = _ := by ring
  have hh := Erdos714BlockThinning.fourth_power_of_block_cover H hfree
    (fun p : I => L p ∪ R p) (q+1) hsize hcover
  calc
    _ ≤ 10368*Fintype.card I^4*(q+1)^7 := hh
    _ ≤ 10368*(2*q^5)^4*(2*q)^7 := by gcongr; omega
    _ = _ := by ring

/-- A fixed critical edge constant is possible only at bounded q. -/
theorem critical_size_bound (ν : G → T) (f : G → G) (g : G → T)
    (q K : ℕ) (hq : 0 < q) (hG : Fintype.card G ≤ q^2) (hT : Fintype.card T ≤ q)
    (hν : ∀ r, (univ.filter (fun x => ν x = r)).card ≤ q+1)
    (H : SimpleGraph ((G × G) ⊕ (G × G))) (hH : H ≤ graph ν f g)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hdense : q^7 ≤ K*H.edgeFinset.card) : q ≤ 21233664*K^4 := by
  have he := thinning_fourth_power ν f g q hq hG hT hν H hH hfree
  have hh : q^27*q ≤ q^27*(21233664*K^4) := by
    calc
      q^27*q = (q^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left hdense 4
      _ = K^4*H.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(21233664*q^27) := Nat.mul_le_mul_left _ he
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (pow_pos hq 27)

end Erdos714TranslatedFibers

namespace Erdos714TranslatedNorm
open Polynomial
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]

/-- The finite-field norm in a quadratic extension is the (q+1)-st power. -/
lemma quadratic_norm_power (hE : Fintype.card E = Fintype.card F^2) (x : E) :
    algebraMap F E (Algebra.norm F x) = x^(Fintype.card F+1) := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hd : (Fintype.card F^2-1)/(Fintype.card F-1) = Fintype.card F+1 := by
    have hh : Fintype.card F^2-1 = (Fintype.card F-1)*(Fintype.card F+1) := by
      have h₁ : Fintype.card F-1+1 = Fintype.card F := by omega
      have h₂ : 1 ≤ Fintype.card F^2 := by nlinarith
      have h₃ := Nat.sub_add_cancel h₂
      nlinarith
    rw [hh, Nat.mul_div_cancel_left _ (by omega)]
  simpa only [Nat.card_eq_fintype_card, hE, hd] using
    (FiniteField.algebraMap_norm_eq_pow (K := F) (x := x))

/-- Zero norm causes no exception to the uniform upper bound on fiber sizes. -/
lemma norm_fiber_bound (hE : Fintype.card E = Fintype.card F^2) (r : F) :
    (univ.filter (fun x : E => Algebra.norm F x = r)).card ≤ Fintype.card F+1 := by
  let P : E[X] := X^(Fintype.card F+1)-C (algebraMap F E r)
  have hp : P ≠ 0 := X_pow_sub_C_ne_zero (by omega) _
  have hs : (univ.filter (fun x : E => Algebra.norm F x = r)).val ⊆ P.roots := by
    intro x hx
    apply (Polynomial.mem_roots hp).mpr
    have hx' := (mem_filter.mp hx).2
    have hh := quadratic_norm_power hE x
    rw [hx'] at hh
    simpa only [IsRoot.def, P, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hh.symm
  simpa only [P, natDegree_X_pow_sub_C] using card_le_degree_of_subset_roots hs

/-- Actual quadratic-norm specialization, for arbitrary shifts and arbitrary
level functions on the extension. Every free edge thinning is o(q^7). -/
theorem arbitrary_thinning (hE : Fintype.card E = Fintype.card F^2)
    (f : E → E) (g : E → F)
    (H : SimpleGraph ((E × E) ⊕ (E × E)))
    (hH : H ≤ Erdos714TranslatedFibers.graph (Algebra.norm F) f g)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 21233664*Fintype.card F^27 :=
  Erdos714TranslatedFibers.thinning_fourth_power (Algebra.norm F) f g
    (Fintype.card F) Fintype.card_pos hE.le le_rfl (norm_fiber_bound hE) H hH hfree

/-- A fixed constant times the selected edge count cannot dominate q^7 for
unbounded quadratic-extension field orders. -/
theorem critical_size_bound (hE : Fintype.card E = Fintype.card F^2)
    (f : E → E) (g : E → F) (K : ℕ)
    (H : SimpleGraph ((E × E) ⊕ (E × E)))
    (hH : H ≤ Erdos714TranslatedFibers.graph (Algebra.norm F) f g)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hdense : Fintype.card F^7 ≤ K*H.edgeFinset.card) : Fintype.card F ≤ 21233664*K^4 :=
  Erdos714TranslatedFibers.critical_size_bound (Algebra.norm F) f g
    (Fintype.card F) K Fintype.card_pos hE.le le_rfl (norm_fiber_bound hE) H hH hfree hdense

#print axioms Erdos714TranslatedFibers.thinning_fourth_power
#print axioms Erdos714TranslatedFibers.critical_size_bound
#print axioms quadratic_norm_power
#print axioms norm_fiber_bound
#print axioms arbitrary_thinning
#print axioms critical_size_bound
end Erdos714TranslatedNorm
