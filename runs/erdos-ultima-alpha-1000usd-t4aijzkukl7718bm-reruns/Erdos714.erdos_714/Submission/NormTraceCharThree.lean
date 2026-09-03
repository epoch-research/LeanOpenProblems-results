import Submission.NormTraceLine
import Submission.LinearBlockCounts

/-!
A uniform obstruction to the norm-times-trace lift in characteristic three,
even after deleting every edge whose trace is zero. Not a disproof of Erdős 714.
-/
noncomputable section
open Polynomial Module Finset SimpleGraph Classical
open Erdos714NormTraceLine
namespace Erdos714NormTraceCharThree
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

lemma cubic_norm_shift (hdim : finrank F E = 3) (x : E) (t : F) :
    Algebra.norm F (x+algebraMap F E t) =
      t^3 + Algebra.trace F E x*t^2 + (shiftPoly (F := F) x).coeff 1*t + Algebra.norm F x := by
  let P := shiftPoly (F := F) x
  have hd : P.natDegree = 3 := (shiftPoly_degree x).trans hdim
  have h0 : P.coeff 0 = Algebra.norm F x := by
    simpa only [Polynomial.eval_zero, Polynomial.coeff_zero_eq_eval_zero, map_zero,
      add_zero, P] using shiftPoly_eval (F := F) x 0
  have h2 : P.coeff 2 = Algebra.trace F E x := by
    simpa only [hdim, Nat.reduceSub] using shiftPoly_next (F := F) x
  have h3 : P.coeff 3 = 1 := by
    rw [← hd]
    exact (shiftPoly_monic x).coeff_natDegree
  rw [← shiftPoly_eval]
  change P.eval t = _
  rw [Polynomial.eval_eq_sum_range' (show P.natDegree < 4 by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    h0, h2, h3, pow_zero, mul_one, pow_one, one_mul]
  ring

section CharThree
variable [CharP F 3]

lemma trace_one_shift (hdim : finrank F E = 3) (x : E)
    (hx : Algebra.trace F E x = 1) (t : F) :
    Algebra.trace F E (x+algebraMap F E t) = 1 := by
  rw [(Algebra.trace F E).map_add, hx, Algebra.trace_algebraMap, hdim, nsmul_eq_mul]
  simp only [CharP.cast_eq_zero F 3, zero_mul, add_zero]

lemma trace_one_profile (hdim : finrank F E = 3) (x : E)
    (hx : Algebra.trace F E x = 1) (t : F) :
    value (F := F) (x+algebraMap F E t) =
      t^3+t^2+(shiftPoly (F := F) x).coeff 1*t+Algebra.norm F x := by
  rw [value, trace_one_shift hdim x hx t, mul_one, cubic_norm_shift hdim, hx, one_mul]

/-- The actual additive norm-times-trace graph with all zero-trace edges deleted. -/
def graph : SimpleGraph ((E × F) ⊕ (E × F)) where
  Adj u v := match u,v with
    | .inl a, .inr b => Algebra.trace F E (a.1+b.1) ≠ 0 ∧
        a.2+b.2 = value (F := F) (a.1+b.1)
    | .inr b, .inl a => Algebra.trace F E (a.1+b.1) ≠ 0 ∧
        a.2+b.2 = value (F := F) (a.1+b.1)
    | _,_ => False
  symm := by intro u v; cases u <;> cases v <;> simp_all
  loopless := by intro u; cases u <;> simp

/-- Any four points with trace one and the same next norm coefficient give
an actual biclique, with four arbitrary distinct scalar row coordinates. -/
def profileCopy (hdim : finrank F E = 3) (t : Fin 4 ↪ F) (x : Fin 4 ↪ E)
    (s : F) (hx : ∀ j, Algebra.trace F E (x j) = 1)
    (hs : ∀ j, (shiftPoly (F := F) (x j)).coeff 1 = s) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy (graph (F := F) (E := E)) := by
  let L : Fin 4 ↪ E × F :=
    ⟨fun i => (algebraMap F E (t i), (t i)^3+(t i)^2+s*t i), by
      intro i j hij
      exact t.injective ((algebraMap F E).injective (congrArg Prod.fst hij))⟩
  let R : Fin 4 ↪ E × F :=
    ⟨fun j => (x j, Algebra.norm F (x j)), by
      intro i j hij
      exact x.injective (congrArg Prod.fst hij)⟩
  have hedge (i j : Fin 4) :
      (graph (F := F) (E := E)).Adj (.inl (L i)) (.inr (R j)) := by
    change Algebra.trace F E (algebraMap F E (t i)+x j) ≠ 0 ∧ _
    rw [add_comm (algebraMap F E (t i)) (x j), trace_one_shift hdim _ (hx j)]
    constructor
    · exact one_ne_zero
    · change (t i)^3+(t i)^2+s*t i+Algebra.norm F (x j) = _
      change (t i)^3+(t i)^2+s*t i+Algebra.norm F (x j) =
        value (F := F) (algebraMap F E (t i)+x j)
      rw [add_comm (algebraMap F E (t i)) (x j), trace_one_profile hdim _ (hx j), hs j]
  refine ⟨⟨L.sumMap R, ?_⟩, (L.sumMap R).injective⟩
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j => simp at hab
    | inr j => exact hedge i j
  | inr j =>
    cases b with
    | inl i => exact (hedge i j).symm
    | inr i => simp at hab

variable [Fintype F] [Fintype E]

omit [CharP F 3] in
/-- Counting in the trace-one affine plane supplies the repeated coefficient
in every sufficiently large finite base field, not just one tested field. -/
theorem exists_trace_one_profile (hdim : finrank F E = 3) (hq : 4 ≤ Fintype.card F) :
    ∃ s : F, ∃ x : Fin 4 ↪ E, ∀ j,
      Algebra.trace F E (x j) = 1 ∧ (shiftPoly (F := F) (x j)).coeff 1 = s := by
  let T := (univ : Finset E).filter (fun x => Algebra.trace F E x = 1)
  have hT : T.card = Fintype.card F^2 := by
    have h := Erdos714LinearBlocks.fiber_card (Algebra.trace F E)
      (Algebra.trace_surjective F E) (1 : F)
    simpa only [T, hdim, Module.finrank_self, Nat.reduceSub] using h
  have hcard : (univ : Finset F).card * 3 < T.card := by
    rw [card_univ, hT, pow_two]
    exact Nat.mul_lt_mul_of_pos_left (by omega) Fintype.card_pos
  obtain ⟨s, _, hs⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := T) (t := (univ : Finset F))
    (f := fun x => (shiftPoly (F := F) x).coeff 1)
    (fun _ _ => mem_univ _) hcard
  let U := T.filter (fun x => (shiftPoly (F := F) x).coeff 1 = s)
  have hU : 4 ≤ U.card := by dsimp only [U]; omega
  obtain ⟨x, hx⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 4) (s := U) (by simpa using hU)
  refine ⟨s, x, ?_⟩
  intro j
  have hj := Finset.mem_filter.mp (hx ⟨j, rfl⟩)
  exact ⟨(Finset.mem_filter.mp hj.1).2, hj.2⟩

/-- Uniform nonfreeness, even though every exhibited edge has trace exactly one. -/
theorem graph_not_free (hdim : finrank F E = 3) (hq : 4 ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) (E := E)) := by
  obtain ⟨s,x,hx⟩ := exists_trace_one_profile hdim hq
  obtain ⟨t⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin 4) (β := F) (by simpa using hq)
  exact fun h => h ⟨profileCopy hdim t x s (fun j => (hx j).1) (fun j => (hx j).2)⟩

/-- The version with an arbitrary nonzero linear functional instead of trace. -/
def functionalGraph (L : E →ₗ[F] F) : SimpleGraph ((E × F) ⊕ (E × F)) where
  Adj u v := match u,v with
    | .inl a, .inr b => L (a.1+b.1) ≠ 0 ∧
        a.2+b.2 = Algebra.norm F (a.1+b.1) * L (a.1+b.1)
    | .inr b, .inl a => L (a.1+b.1) ≠ 0 ∧
        a.2+b.2 = Algebra.norm F (a.1+b.1) * L (a.1+b.1)
    | _,_ => False
  symm := by intro u v; cases u <;> cases v <;> simp_all
  loopless := by intro u; cases u <;> simp

omit [Fintype F] [Fintype E] in
/-- Scaling by the inverse trace-pairing coefficient transfers every edge,
including its nonzero-functional restriction. -/
def functionalScaleCopy (L : E →ₗ[F] F) (δ : E) (hδ : δ ≠ 0)
    (hL : ∀ z, L z = Algebra.trace F E (δ*z)) :
    (graph (F := F) (E := E)).Copy (functionalGraph L) := by
  let a := δ⁻¹
  let k := Algebra.norm F a
  have ha : a ≠ 0 := inv_ne_zero hδ
  have hk : k ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
  have hscale (z : E) : L (a*z) = Algebra.trace F E z := by
    rw [hL]
    congr 1
    dsimp only [a]
    rw [← mul_assoc, mul_inv_cancel₀ hδ, one_mul]
  let e : E × F ↪ E × F := ⟨fun z => (a*z.1,k*z.2), by
    intro z w he
    exact Prod.ext (mul_left_cancel₀ ha (congrArg Prod.fst he))
      (mul_left_cancel₀ hk (congrArg Prod.snd he))⟩
  have he (z w : E × F)
      (h : Algebra.trace F E (z.1+w.1) ≠ 0 ∧ z.2+w.2 = value (F := F) (z.1+w.1)) :
      (functionalGraph L).Adj (.inl (e z)) (.inr (e w)) := by
    change L (a*z.1+a*w.1) ≠ 0 ∧
      k*z.2+k*w.2 = Algebra.norm F (a*z.1+a*w.1)*L (a*z.1+a*w.1)
    rw [← mul_add, hscale, map_mul]
    refine ⟨h.1, ?_⟩
    change k*z.2+k*w.2 = k*Algebra.norm F (z.1+w.1)*Algebra.trace F E (z.1+w.1)
    rw [← mul_add, h.2, value]
    ring
  refine ⟨⟨e.sumMap e, ?_⟩, (e.sumMap e).injective⟩
  intro z w h
  cases z with
  | inl z =>
    cases w with
    | inl w => simp [graph] at h
    | inr w => exact he z w h
  | inr z =>
    cases w with
    | inl w => exact (he w z h).symm
    | inr w => simp [graph] at h

/-- Every nonzero linear functional gives a nonfree host, even after all its
zero-functional edges are deleted. The trace-pairing representation is proved. -/
theorem functional_graph_not_free (hdim : finrank F E = 3) (hq : 4 ≤ Fintype.card F)
    (L : E →ₗ[F] F) (hL : L ≠ 0) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (functionalGraph L) := by
  let e := (Algebra.traceForm F E).toDual (traceForm_nondegenerate F E)
  obtain ⟨δ, hδ⟩ := e.surjective L
  have hrep (z : E) : L z = Algebra.trace F E (δ*z) := by
    have h := congrArg (fun f : E →ₗ[F] F => f z) hδ
    exact h.symm
  have hδ0 : δ ≠ 0 := by
    intro hz
    apply hL
    ext z
    simp [hrep, hz]
  intro hfree
  apply graph_not_free hdim hq
  rintro ⟨c⟩
  exact hfree ⟨(functionalScaleCopy L δ hδ0 hrep).comp c⟩

end CharThree
#print axioms cubic_norm_shift
#print axioms trace_one_profile
#print axioms exists_trace_one_profile
#print axioms graph_not_free
#print axioms functionalScaleCopy
#print axioms functional_graph_not_free
end Erdos714NormTraceCharThree
