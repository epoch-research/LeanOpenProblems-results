import Submission.RestrictedTupleCover

/-!
Countable unions of finite-pattern pieces, and relations on countable tuples
whose adjacency is locally determined by a finite prefix. This is an auxiliary
covering theorem, not a solution of Erdős 595.
-/

open SimpleGraph Set
namespace Erdos595LocalTuple
open Erdos595Work Erdos595TupleType Erdos595RestrictedTuple

variable {V A I : Type*}

/-- Flatten a countable union of countable triangle-free edge covers. -/
theorem cover_iSup (G : ℕ → SimpleGraph V)
    (hG : ∀ n, IsCountableUnionOfTriangleFree (G n)) :
    IsCountableUnionOfTriangleFree (⨆ n, G n) := by
  classical
  choose H hH hcov using hG
  refine ⟨fun k => H (Nat.unpair k).1 (Nat.unpair k).2,
    fun k => hH _ _, ?_⟩
  ext a b
  simp only [SimpleGraph.iSup_adj]
  constructor
  · rintro ⟨n, hn⟩
    rw [hcov n, SimpleGraph.iSup_adj] at hn
    obtain ⟨m, hm⟩ := hn
    exact ⟨Nat.pair n m, by simpa only [Nat.unpair_pair] using hm⟩
  · rintro ⟨k, hk⟩
    refine ⟨(Nat.unpair k).1, ?_⟩
    rw [hcov _, SimpleGraph.iSup_adj]
    exact ⟨(Nat.unpair k).2, hk⟩

/-- Countably many coverable induced fibers can be combined without requiring
any compatibility among their chosen covers. -/
theorem cover_of_countable_fibers {C : Type*} [Countable C]
    (G : SimpleGraph V) (f : V → C)
    (hf : ∀ c, IsCountableUnionOfTriangleFree (G.induce {a | f a = c})) :
    IsCountableUnionOfTriangleFree G := by
  classical
  obtain ⟨enc, henc⟩ := exists_injective_nat C
  let e : C → ℕ → Fin 2 := fun c n => if enc c = n then 1 else 0
  have he : Function.Injective e := by
    intro c d h
    apply henc
    have hh := congrFun h (enc c)
    have hd : enc d = enc c := by simpa [e] using hh
    exact hd.symm
  apply countable_union_of_vertex_pieces G (e ∘ f)
  intro i
  by_cases hi : ∃ a, e (f a) = i
  · obtain ⟨a, ha⟩ := hi
    let r : V → {b : V // f b = f a} := fun b =>
      if h : f b = f a then ⟨b, h⟩ else ⟨a, rfl⟩
    let F : vertexPiece G (e ∘ f) i →g G.induce {b | f b = f a} :=
      { toFun := r
        map_rel' := by
          intro b c hbc
          have hb : f b = f a := he (hbc.2.1.trans ha.symm)
          have hc : f c = f a := he (hbc.2.2.trans ha.symm)
          simpa only [r, dif_pos hb, dif_pos hc, SimpleGraph.induce_adj] using hbc.1 }
    exact countable_union_of_hom F (hf (f a))
  · have hz : vertexPiece G (e ∘ f) i = ⊥ := by
      ext a b
      constructor
      · intro h
        exact (hi ⟨a, h.2.1⟩).elim
      · exact False.elim
    exact ⟨fun _ => ⊥, fun _ => SimpleGraph.cliqueFree_bot (by omega), by simpa using hz⟩


section Order
variable [LinearOrder A]

lemma pairType_swap {x y z w : I → A}
    (h : pairType x y = pairType z w) : pairType y x = pairType w z := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := pairType_eq_iff.mp h
  exact pairType_eq_iff.mpr ⟨h₃,h₂,h₁,h₀⟩

/-- The largest subgraph of G whose ordered adjacency is forced by the
comparison type of the chosen tuple labels. -/
def forced (G : SimpleGraph V) (v : V → I → A) : SimpleGraph V where
  Adj a b := ∀ c d, pairType (v a) (v b) = pairType (v c) (v d) → G.Adj c d
  symm := by
    intro a b h c d ht
    exact (h d c (pairType_swap ht)).symm
  loopless := by
    intro a h
    exact G.loopless a (h a a rfl)

lemma forced_le (G : SimpleGraph V) (v : V → I → A) : forced G v ≤ G :=
  fun a b h => h a b rfl

lemma forced_invariant (G : SimpleGraph V) (v : V → I → A) :
    RelativeInvariant (forced G v) v := by
  intro a b c d ht h e f hef
  exact h e f (ht.trans hef)

/-- Countably many finite tuple descriptions suffice when every edge is
forced by one of them. The descriptions need not be nested. -/
theorem cover_of_finite_descriptions (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (I : ℕ → Type*) [∀ n, Finite (I n)] (v : ∀ n, V → I n → A)
    (hlocal : ∀ a b, G.Adj a b → ∃ n,
      ∀ c d, pairType (v n a) (v n b) = pairType (v n c) (v n d) → G.Adj c d) :
    IsCountableUnionOfTriangleFree G := by
  have he : G = ⨆ n, forced G (v n) := by
    ext a b
    rw [SimpleGraph.iSup_adj]
    exact ⟨fun h => hlocal a b h, fun ⟨n, hn⟩ => forced_le G (v n) hn⟩
  rw [he]
  apply cover_iSup
  intro n
  exact countable_cover (forced G (v n)) ((hG.anti (forced_le G (v n))))
    (v n) (forced_invariant G (v n))

/-- An adjacency relation on countable tuple labels is finitely local if
at every actual edge, some finite prefix comparison type forces adjacency
for every other actual pair with that prefix type. -/
def FinitelyLocal (G : SimpleGraph V) (v : V → ℕ → A) : Prop :=
  ∀ a b, G.Adj a b → ∃ n, ∀ c d,
    pairType (fun i : Fin n => v a i) (fun i : Fin n => v b i) =
      pairType (fun i : Fin n => v c i) (fun i : Fin n => v d i) → G.Adj c d

/-- Every K4-free finitely local graph on an arbitrary family of countable
tuples has a countable triangle-free edge cover. -/
theorem cover_of_finitelyLocal (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (v : V → ℕ → A) (hlocal : FinitelyLocal G v) :
    IsCountableUnionOfTriangleFree G :=
  cover_of_finite_descriptions G hG (fun n => Fin n)
    (fun _ a i => v a i) hlocal

/-- A countable collection of finite-arity tuple shapes, with arbitrary
cross-shape edges, cannot be a witness. Only each same-shape induced graph
is required to have relatively order-type-invariant adjacency. -/
theorem cover_of_finite_shapes {C : Type*} [Countable C]
    (G : SimpleGraph V) (hG : G.CliqueFree 4) (shape : V → C)
    (I : C → Type*) [∀ c, Finite (I c)]
    (v : ∀ c, {a : V // shape a = c} → I c → A)
    (hInv : ∀ c, RelativeInvariant (G.induce {a | shape a = c}) (v c)) :
    IsCountableUnionOfTriangleFree G := by
  apply cover_of_countable_fibers G shape
  intro c
  apply countable_cover _ _ (v c) (hInv c)
  exact hG.comap (SimpleGraph.Embedding.induce _)

end Order

#print axioms cover_of_countable_fibers
#print axioms cover_of_finite_shapes
#print axioms cover_iSup
#print axioms forced_invariant
#print axioms cover_of_finite_descriptions
#print axioms cover_of_finitelyLocal
end Erdos595LocalTuple
