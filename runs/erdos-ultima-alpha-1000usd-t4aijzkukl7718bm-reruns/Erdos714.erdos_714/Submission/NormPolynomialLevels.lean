import Submission.TranslatedNormFibers

/-!
Boundedly many translated norm levels cannot retain the critical density.
This includes polynomial laws of bounded degree in the first norm value,
with arbitrary dependence on the second coordinate. The result concerns
arbitrary edge thinnings of these hosts, not all extremal graphs.
-/
noncomputable section
open Classical Finset SimpleGraph Polynomial
set_option maxHeartbeats 4000000
namespace Erdos714NormLevels

/-- A finite set of size at most d can be covered by d indexed values.
Empty sets and d=0 are included, with no surjectivity assumption. -/
lemma enumerate_sets {A T : Type*} [Fintype T] [Inhabited T]
    (S : A → Finset T) (d : ℕ) (hS : ∀ a, (S a).card ≤ d) :
    ∃ g : Fin d → A → T, ∀ a t, t ∈ S a → ∃ i, g i a=t := by
  let g (i : Fin d) (a : A) : T :=
    if hi : i.val < Fintype.card (S a) then
      ((Fintype.equivFin (S a)).symm ⟨i.val,hi⟩).val else default
  refine ⟨g,?_⟩
  intro a t ht
  let x : S a := ⟨t,ht⟩
  let j := Fintype.equivFin (S a) x
  have hj : j.val < d := by
    exact lt_of_lt_of_le j.isLt (by simpa only [Fintype.card_coe] using hS a)
  refine ⟨⟨j.val,hj⟩,?_⟩
  dsimp [g]
  simp only [j.isLt,if_true]
  change ((Fintype.equivFin (S a)).symm ((Fintype.equivFin (S a)) x)).val=t
  simp [x]

/-- Fourth powers of edge bounds are stable under a finite cover. The selected
subgraphs need not be disjoint, regular, or copies of one another. -/
lemma cover_fourth_power {V I : Type*} [Fintype V] [Fintype I]
    (H : SimpleGraph V) (J : I → SimpleGraph V) (C : ℕ)
    (hcover : ∀ x y, H.Adj x y → ∃ i, (J i).Adj x y)
    (hJ : ∀ i, (J i).edgeFinset.card^4 ≤ C) :
    H.edgeFinset.card^4 ≤ Fintype.card I^4*C := by
  have hsub : H.edgeFinset ⊆ univ.biUnion (fun i => (J i).edgeFinset) := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨i,hi⟩ := hcover x y (mem_edgeFinset.mp he)
      exact mem_biUnion.mpr ⟨i,mem_univ _,mem_edgeFinset.mpr hi⟩
  have he : H.edgeFinset.card ≤ ∑ i : I, (J i).edgeFinset.card :=
    (card_le_card hsub).trans card_biUnion_le
  have hp := pow_sum_le_card_mul_sum_pow (s := (univ : Finset I))
    (f := fun i => (J i).edgeFinset.card) (by intros; omega) 3
  calc
    _ ≤ (∑ i : I, (J i).edgeFinset.card)^4 := Nat.pow_le_pow_left he 4
    _ ≤ Fintype.card I^3*∑ i : I, (J i).edgeFinset.card^4 := by simpa using hp
    _ ≤ Fintype.card I^3*∑ _i : I, C := by
      gcongr with i _
      exact hJ i
    _ = _ := by simp; ring

section General
variable {G T : Type*} [AddCommGroup G] [Fintype G] [Fintype T] [Inhabited T]

/-- A boundedly multivalued version of a translated-fiber graph. -/
def graph (ν : G → T) (f : G → G) (S : G → Finset T) :
    SimpleGraph ((G × G) ⊕ (G × G)) :=
  Erdos714Tensor.incidence fun x y => ν (x.1+y.1-f (x.2+y.2)) ∈ S (x.2+y.2)

/-- Only the number of levels per slice is bounded. Their values, the shift
function, and all edge selections may depend arbitrarily on the slice. -/
theorem fourth_power (ν : G → T) (f : G → G) (S : G → Finset T)
    (q d : ℕ) (hq : 0 < q) (hG : Fintype.card G ≤ q^2) (hT : Fintype.card T ≤ q)
    (hν : ∀ r, (univ.filter (fun x => ν x=r)).card ≤ q+1)
    (hS : ∀ t, (S t).card ≤ d)
    (H : SimpleGraph ((G × G) ⊕ (G × G))) (hH : H ≤ graph ν f S)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 21233664*d^4*q^27 := by
  obtain ⟨g,hg⟩ := enumerate_sets S d hS
  let J (i : Fin d) := H ⊓ Erdos714TranslatedFibers.graph ν f (g i)
  have hcover : ∀ x y, H.Adj x y → ∃ i, (J i).Adj x y := by
    intro u v huv
    have h := hH huv
    cases u with
    | inl x =>
      cases v with
      | inl y => exact False.elim h
      | inr y =>
        obtain ⟨i,hi⟩ := hg _ _ h
        exact ⟨i,huv,hi.symm⟩
    | inr y =>
      cases v with
      | inr x => exact False.elim h
      | inl x =>
        obtain ⟨i,hi⟩ := hg _ _ h
        exact ⟨i,huv,hi.symm⟩
  have hJ (i : Fin d) : Nat.card (J i).edgeSet^4 ≤ 21233664*q^27 := by
    have hJfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (J i) := by
      intro hc
      exact hfree (hc.mono_right inf_le_left)
    have hb := Erdos714TranslatedFibers.thinning_fourth_power ν f (g i) q hq hG hT hν
      (J i) inf_le_right hJfree
    simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using hb
  have hb := cover_fourth_power H J (21233664*q^27) hcover (fun i => by
    simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using hJ i)
  simpa only [Fintype.card_fin,mul_assoc,mul_left_comm,mul_comm] using hb

end General

section Norm
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]

/-- Each slice is cut out by its own nonzero univariate polynomial in the norm.
There is no polynomial assumption on the slice parameter. -/
def polynomialGraph (f : E → E) (P : E → F[X]) :
    SimpleGraph ((E × E) ⊕ (E × E)) :=
  Erdos714Tensor.incidence fun x y =>
    (P (x.2+y.2)).eval (Algebra.norm F (x.1+y.1-f (x.2+y.2)))=0

lemma polynomial_roots_bound {p : F[X]} (hp : p ≠ 0) :
    (univ.filter (fun x : F => p.eval x=0)).card ≤ p.natDegree := by
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  exact (Polynomial.mem_roots hp).mpr ((mem_filter.mp hx).2)

/-- A uniform degree bound yields a uniform loss of critical density, including
for arbitrary edge subgraphs and arbitrary vertex deletions. -/
theorem polynomial_fourth_power (hE : Fintype.card E=Fintype.card F^2)
    (f : E → E) (P : E → F[X]) (d : ℕ)
    (hP : ∀ t, P t ≠ 0) (hdeg : ∀ t, (P t).natDegree ≤ d)
    (H : SimpleGraph ((E × E) ⊕ (E × E))) (hH : H ≤ polynomialGraph f P)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 21233664*d^4*Fintype.card F^27 := by
  letI : Inhabited F := ⟨0⟩
  let S (t : E) := univ.filter (fun z : F => (P t).eval z=0)
  have hs (t : E) : (S t).card ≤ d :=
    (polynomial_roots_bound (hP t)).trans (hdeg t)
  apply fourth_power (Algebra.norm F) f S (Fintype.card F) d Fintype.card_pos
    hE.le le_rfl (Erdos714TranslatedNorm.norm_fiber_bound hE) hs H _ hfree
  intro x y hxy
  have h := hH hxy
  cases x <;> cases y <;> simp_all [graph,polynomialGraph,Erdos714Tensor.incidence,S]

/-- Consequently a fixed positive critical edge constant can occur only at
bounded field orders for a fixed degree bound. -/
theorem polynomial_size_budget (hE : Fintype.card E=Fintype.card F^2)
    (f : E → E) (P : E → F[X]) (d K : ℕ)
    (hP : ∀ t, P t ≠ 0) (hdeg : ∀ t, (P t).natDegree ≤ d)
    (H : SimpleGraph ((E × E) ⊕ (E × E))) (hH : H ≤ polynomialGraph f P)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hdense : Fintype.card F^7 ≤ K*H.edgeFinset.card) :
    Fintype.card F ≤ 21233664*d^4*K^4 := by
  have he := polynomial_fourth_power hE f P d hP hdeg H hH hfree
  have hh : Fintype.card F^27*Fintype.card F ≤
      Fintype.card F^27*(21233664*d^4*K^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left hdense 4
      _ = K^4*H.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(21233664*d^4*Fintype.card F^27) := Nat.mul_le_mul_left _ he
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (pow_pos Fintype.card_pos 27)

/-- In particular, every law N(x)^k = h(y), k positive and fixed, is covered.
The function h is arbitrary, not assumed polynomial, additive, or bijective. -/
theorem power_level_bound (hE : Fintype.card E=Fintype.card F^2)
    (f : E → E) (h : E → F) (k : ℕ) (hk : 0 < k)
    (H : SimpleGraph ((E × E) ⊕ (E × E)))
    (hH : H ≤ Erdos714Tensor.incidence (fun x y : E × E =>
      Algebra.norm F (x.1+y.1-f (x.2+y.2))^k=h (x.2+y.2)))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 21233664*k^4*Fintype.card F^27 := by
  apply polynomial_fourth_power hE f (fun t => X^k-C (h t)) k
    (fun _ => X_pow_sub_C_ne_zero hk _) (fun _ => by simp) H _ hfree
  intro x y hxy
  have h := hH hxy
  cases x <;> cases y
  all_goals first | exact h | simpa only [polynomialGraph,Erdos714Tensor.incidence,
    eval_sub,eval_pow,eval_X,eval_C,sub_eq_zero] using h

end Norm
end Erdos714NormLevels
#print axioms Erdos714NormLevels.enumerate_sets
#print axioms Erdos714NormLevels.cover_fourth_power
#print axioms Erdos714NormLevels.fourth_power
#print axioms Erdos714NormLevels.polynomial_fourth_power
#print axioms Erdos714NormLevels.polynomial_size_budget
#print axioms Erdos714NormLevels.power_level_bound
