import Submission.TranslatedNormFibers

/-!
Exact host sizes and a relative edge-thinning bound for translated quadratic
norm fibers. These graphs have the desired edge scale before thinning, but
cannot retain a fixed positive fraction of edges while being K44-free.
-/
noncomputable section
open Finset SimpleGraph Classical
set_option maxHeartbeats 2000000
namespace Erdos714TranslatedFibers
variable {G T : Type*} [AddCommGroup G] [Fintype G] [Fintype T]

/-- A change of variables in one complete neighborhood, with no hypothesis on
how the shift and level functions depend on the second coordinate. -/
def neighborEquiv (ν : G → T) (f : G → G) (g : G → T) (x : G × G) :
    {y : G × G // ν (x.1+y.1-f (x.2+y.2)) = g (x.2+y.2)} ≃
      (Σ t : G, {z : G // ν z = g t}) where
  toFun y := ⟨x.2+y.1.2, ⟨x.1+y.1.1-f (x.2+y.1.2),y.property⟩⟩
  invFun p := ⟨(p.2.1+f p.1-x.1,p.1-x.2), by
    have hs : x.2+(p.1-x.2) = p.1 := by abel
    rw [hs, show x.1+(p.2.1+f p.1-x.1)-f p.1 = p.2.1 by abel]
    exact p.2.property⟩
  left_inv y := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> abel
  right_inv p := by
    rcases p with ⟨t,z,hz⟩
    have hs : x.2+(t-x.2) = t := by abel
    have hz' : x.1+(z+f t-x.1)-f t = z := by abel
    dsimp
    simp only [hs, hz']
    apply Sigma.ext hs
    exact (Subtype.heq_iff_coe_eq (fun a => by
      change ν a = g (x.2+(t-x.2)) ↔ ν a = g t
      rw [hs])).mpr rfl

omit [Fintype T] in
/-- Each edge is counted once, using the bipartite set-system identity. -/
theorem edge_count (ν : G → T) (f : G → G) (g : G → T) :
    (graph ν f g).edgeFinset.card =
      Fintype.card G^2 * ∑ t : G, Fintype.card {z : G // ν z = g t} := by
  let S (x : G × G) := univ.filter (fun y : G × G => ν (x.1+y.1-f (x.2+y.2)) = g (x.2+y.2))
  have hg : graph ν f g = Erdos714Packing.incidence S := by
    ext v w
    cases v <;> cases w <;> simp [graph, Erdos714Tensor.incidence, Erdos714Packing.incidence, S]
  rw [hg, Erdos714Packing.incidence_edges]
  have hs (x : G × G) : (S x).card = ∑ t : G, Fintype.card {z : G // ν z = g t} := by
    have h := Fintype.card_congr (neighborEquiv ν f g x)
    simpa only [Fintype.card_subtype, Fintype.card_sigma] using h
  simp_rw [hs]
  simp [Fintype.card_prod, pow_two]
end Erdos714TranslatedFibers

namespace Erdos714TranslatedNorm
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]

/-- The upper bound on every fiber, together with the total cardinality, forces
all nonzero quadratic-norm fibers to attain q+1. -/
lemma norm_fiber_card (hE : Fintype.card E = Fintype.card F^2) {r : F} (hr : r ≠ 0) :
    Fintype.card {x : E // Algebra.norm F x = r} = Fintype.card F+1 := by
  let c (r : F) := Fintype.card {x : E // Algebra.norm F x = r}
  have hc (r : F) : c r ≤ Fintype.card F+1 := by
    simpa only [c, Fintype.card_subtype] using norm_fiber_bound hE r
  have hc0 : c 0 = 1 := by
    simp only [c, Algebra.norm_eq_zero_iff, Fintype.card_subtype_eq]
  have htotal : ∑ r : F, c r = Fintype.card E := by
    simpa only [Fintype.card_sigma, c] using Fintype.card_congr (Equiv.sigmaFiberEquiv (Algebra.norm F (S := E)))
  have hsum := sum_erase_add (univ : Finset F) c (mem_univ (0 : F))
  rw [hc0, htotal, hE] at hsum
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hsub : Fintype.card F-1+1 = Fintype.card F := by omega
  have heq : ∑ a ∈ (univ : Finset F).erase 0, c a =
      ∑ _a ∈ (univ : Finset F).erase 0, (Fintype.card F+1) := by
    simp only [sum_const, nsmul_eq_mul, card_erase_of_mem (mem_univ (0 : F)), card_univ]
    nlinarith
  exact (sum_eq_sum_iff_of_le (fun a _ => hc a)).mp heq r (by simp [hr])

omit [Field F] [Field E] [Algebra F E] in
/-- The host has exactly 2q^4 vertices. -/
lemma vertex_count (hE : Fintype.card E = Fintype.card F^2) :
    Fintype.card ((E × E) ⊕ (E × E)) = 2*Fintype.card F^4 := by
  simp only [Fintype.card_sum, Fintype.card_prod, hE]
  ring

/-- If the level function avoids zero, the host has q^6(q+1) edges. Thus the
negative thinning result is not caused by a deficient original edge count. -/
lemma nonzero_level_edges (hE : Fintype.card E = Fintype.card F^2)
    (f : E → E) (g : E → F) (hg : ∀ t, g t ≠ 0) :
    (Erdos714TranslatedFibers.graph (Algebra.norm F) f g).edgeFinset.card =
      Fintype.card F^6*(Fintype.card F+1) := by
  rw [Erdos714TranslatedFibers.edge_count]
  simp_rw [norm_fiber_card hE (hg _)]
  simp only [sum_const, card_univ, nsmul_eq_mul, hE, Nat.cast_id]
  ring

/-- A relative density estimate for arbitrary selected edges in the actual
quadratic-norm host. The fourth power of the retained fraction is O(1/q). -/
theorem relative_thinning_bound (hE : Fintype.card E = Fintype.card F^2)
    (f : E → E) (g : E → F) (hg : ∀ t, g t ≠ 0)
    (H : SimpleGraph ((E × E) ⊕ (E × E)))
    (hH : H ≤ Erdos714TranslatedFibers.graph (Algebra.norm F) f g)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    Fintype.card F*H.edgeFinset.card^4 ≤
      21233664*(Erdos714TranslatedFibers.graph (Algebra.norm F) f g).edgeFinset.card^4 := by
  have h := arbitrary_thinning hE f g H hH hfree
  rw [nonzero_level_edges hE f g hg]
  calc
    _ ≤ Fintype.card F*(21233664*Fintype.card F^27) := Nat.mul_le_mul_left _ h
    _ = 21233664*(Fintype.card F^7)^4 := by ring
    _ ≤ _ := by
      gcongr
      rw [show Fintype.card F^7 = Fintype.card F^6*Fintype.card F by ring]
      exact Nat.mul_le_mul_left _ (by omega)

#print axioms Erdos714TranslatedFibers.neighborEquiv
#print axioms Erdos714TranslatedFibers.edge_count
#print axioms norm_fiber_card
#print axioms vertex_count
#print axioms nonzero_level_edges
#print axioms relative_thinning_bound
end Erdos714TranslatedNorm
