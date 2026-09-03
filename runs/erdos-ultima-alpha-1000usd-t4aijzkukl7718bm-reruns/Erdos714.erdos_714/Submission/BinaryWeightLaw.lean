import Submission.BinaryLift
import Submission.Packing

/-!
An obstruction to arbitrary full weight laws on a binary additive point group.
This is not a proof or disproof of Erdős 714.
-/

noncomputable section
open Classical SimpleGraph Finset
open scoped CharTwo

namespace Erdos714BinaryWeightLaw

variable {G A B C : Type*} [Ring G] [CharP G 2]
variable [Fintype G] [Fintype A] [Fintype B]

/-- No algebraic assumptions are imposed on the value type or the weight law. -/
def graph (f : G → C) (H : A → B → C) : SimpleGraph ((G × A) ⊕ (G × B)) :=
  Erdos714Packing.incidence (fun p => univ.filter (fun q => f (p.1+q.1) = H p.2 q.2))

/-- A fixed pair of weights embeds the full Cayley graph of its value fiber. -/
def fiberCopy (f : G → C) (H : A → B → C) (a : A) (b : B) :
    Copy (Erdos714BinaryLift.cayley {x | f x = H a b}) (graph f H) where
  toHom := {
    toFun := fun p => if p.1 then Sum.inr (p.2,b) else Sum.inl (p.2,a)
    map_rel' := by
      rintro ⟨bx,x⟩ ⟨cy,y⟩ h
      cases bx <;> cases cy <;>
        simp_all [Erdos714BinaryLift.cayley, graph, Erdos714Packing.incidence, add_comm] }
  injective' := by
    rintro ⟨bx,x⟩ ⟨cy,y⟩ h
    cases bx <;> cases cy <;> simp_all

omit [Fintype A] in
/-- Every fiber used by a free graph is small, regardless of multiplicities
or algebraic properties of the weight law. -/
theorem fiber_bound (f : G → C) (H : A → B → C)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph f H))
    (a : A) (b : B) :
    let m := (univ.filter (fun x => f x = H a b)).card
    m*(m-1) ≤ 2*Fintype.card G := by
  apply Erdos714BinaryLift.cayley_card_bound
  have hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714BinaryLift.cayley {x | f x = H a b}) := by
    rintro ⟨g⟩
    exact hfree ⟨(fiberCopy f H a b).comp g⟩
  simpa only [coe_filter, coe_univ, Set.setOf_mem_eq, Set.mem_univ, mem_univ, true_and] using hf

omit [Fintype A] in
lemma fiber_square_bound (f : G → C) (H : A → B → C)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph f H))
    (a : A) (b : B) :
    (univ.filter (fun x => f x = H a b)).card ^ 2 ≤ 3*Fintype.card G := by
  let m := (univ.filter (fun x => f x = H a b)).card
  have hm : m ≤ Fintype.card G := card_filter_le _ _
  have h := fiber_bound f H hfree a b
  change m*(m-1) ≤ 2*Fintype.card G at h
  change m^2 ≤ 3*Fintype.card G
  by_cases hz : m = 0
  · simp [hz]
  · have hs : m-1+1=m := Nat.sub_add_cancel (by omega)
    nlinarith

lemma fiber_translate_card (f : G → C) (t : C) (x : G) :
    (univ.filter (fun y => f (x+y) = t)).card =
      (univ.filter (fun y => f y = t)).card := by
  apply card_bij (fun y _ => x+y)
  · intro y hy
    simpa using hy
  · intro y hy z hz he
    exact add_left_cancel he
  · intro z hz
    refine ⟨x+z, ?_, ?_⟩
    · simpa only [mem_filter, mem_univ, true_and, ← add_assoc, CharTwo.add_self_eq_zero,
        zero_add] using hz
    · simp

omit [Fintype A] in
lemma neighbor_card (f : G → C) (H : A → B → C) (x : G) (a : A) :
    (univ.filter (fun q : G × B => f (x+q.1) = H a q.2)).card =
      ∑ b : B, (univ.filter (fun y => f y = H a b)).card := by
  calc
    _ = ∑ b : B, (univ.filter (fun y => f (x+y) = H a b)).card := by
      simp only [card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
      rw [sum_comm]
    _ = _ := sum_congr rfl (fun b _ => fiber_translate_card f (H a b) x)

/-- Exact edge count, including arbitrary repetitions of weight-pair values. -/
theorem edges (f : G → C) (H : A → B → C) :
    (graph f H).edgeFinset.card = Fintype.card G *
      ∑ p : A × B, (univ.filter (fun y => f y = H p.1 p.2)).card := by
  rw [graph, Erdos714Packing.incidence_edges]
  simp_rw [Fintype.sum_prod_type, neighbor_card]
  rw [sum_const, card_univ, smul_eq_mul]

/-- Every full graph in this model obeys a uniform squared-edge bound. -/
theorem edge_square_bound (f : G → C) (H : A → B → C)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph f H)) :
    (graph f H).edgeFinset.card ^ 2 ≤
      3 * Fintype.card G ^ 3 * Fintype.card A ^ 2 * Fintype.card B ^ 2 := by
  let m (p : A × B) := (univ.filter (fun y => f y = H p.1 p.2)).card
  have hm : (∑ p, m p)^2 ≤ Fintype.card (A × B) * ∑ p, m p^2 := by
    simpa only [one_mul, one_pow, sum_const, card_univ, smul_eq_mul, mul_one] using
      (sum_mul_sq_le_sq_mul_sq (R := ℕ) (univ : Finset (A × B)) (fun _ => 1) m)
  have hs : ∑ p, m p^2 ≤ Fintype.card (A × B) * (3*Fintype.card G) := by
    calc
      _ ≤ ∑ _p : A × B, 3*Fintype.card G :=
        sum_le_sum (fun p _ => fiber_square_bound f H hfree p.1 p.2)
      _ = _ := by simp
  rw [edges, mul_pow]
  calc
    Fintype.card G ^ 2 * (∑ p, m p)^2 ≤
        Fintype.card G ^ 2 * (Fintype.card (A × B) *
          (Fintype.card (A × B) * (3*Fintype.card G))) :=
      Nat.mul_le_mul_left _ (hm.trans (Nat.mul_le_mul_left _ hs))
    _ = _ := by simp only [Fintype.card_prod]; ring

/-- At the intended fourth-case size, changing the full weight law still loses
half a power of q in the edge count. -/
theorem cubic_scale_bound (f : G → C) (H : A → B → C)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph f H))
    (q : ℕ) (hG : Fintype.card G ≤ q^3)
    (hA : Fintype.card A ≤ q) (hB : Fintype.card B ≤ q) :
    (graph f H).edgeFinset.card ^ 2 ≤ 3*q^13 := by
  calc
    _ ≤ 3 * Fintype.card G ^ 3 * Fintype.card A ^ 2 * Fintype.card B ^ 2 :=
      edge_square_bound f H hfree
    _ ≤ 3 * (q^3)^3 * q^2 * q^2 := by gcongr
    _ = _ := by ring

/-- Fixed-size auxiliary weight labels do not change the deficient exponent. -/
theorem labeled_scale_bound (f : G → C) (H : A → B → C)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph f H))
    (q L R : ℕ) (hG : Fintype.card G ≤ q^3)
    (hA : Fintype.card A ≤ L*q) (hB : Fintype.card B ≤ R*q) :
    (graph f H).edgeFinset.card ^ 2 ≤ 3*L^2*R^2*q^13 := by
  calc
    _ ≤ 3 * Fintype.card G ^ 3 * Fintype.card A ^ 2 * Fintype.card B ^ 2 :=
      edge_square_bound f H hfree
    _ ≤ 3 * (q^3)^3 * (L*q)^2 * (R*q)^2 := by gcongr
    _ = _ := by ring


/-- A fixed critical-scale edge constant forces q to remain bounded. -/
theorem cubic_scale_budget (f : G → C) (H : A → B → C)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph f H))
    (q K : ℕ) (hq : 0 < q) (hG : Fintype.card G ≤ q^3)
    (hA : Fintype.card A ≤ q) (hB : Fintype.card B ≤ q)
    (he : q^7 ≤ K*(graph f H).edgeFinset.card) : q ≤ 3*K^2 := by
  have h := cubic_scale_bound f H hfree q hG hA hB
  have he2 := Nat.pow_le_pow_left he 2
  have hq13 : 0 < q^13 := pow_pos hq 13
  apply Nat.le_of_mul_le_mul_right (c := q^13) ?_ hq13
  calc
    q*q^13 = (q^7)^2 := by ring
    _ ≤ (K*(graph f H).edgeFinset.card)^2 := he2
    _ = K^2 * (graph f H).edgeFinset.card^2 := by ring
    _ ≤ K^2 * (3*q^13) := Nat.mul_le_mul_left _ h
    _ = (3*K^2)*q^13 := by ring

end Erdos714BinaryWeightLaw

#print axioms Erdos714BinaryWeightLaw.fiber_bound
#print axioms Erdos714BinaryWeightLaw.fiber_square_bound
#print axioms Erdos714BinaryWeightLaw.edges
#print axioms Erdos714BinaryWeightLaw.edge_square_bound
#print axioms Erdos714BinaryWeightLaw.cubic_scale_bound
#print axioms Erdos714BinaryWeightLaw.cubic_scale_budget
#print axioms Erdos714BinaryWeightLaw.labeled_scale_bound
