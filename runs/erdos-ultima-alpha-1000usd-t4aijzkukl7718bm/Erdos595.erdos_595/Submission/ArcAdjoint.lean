import Submission.Work

/-!
The symmetrized arc construction and its biclique right adjoint.
These provide a precise clique test for a powerset-based candidate family.
They do not by themselves prove or disprove Erdős Problem 595.
-/

set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595ArcAdjoint

variable {V W : Type*}

/-- Directed edges of an undirected simple graph. -/
abbrev Arc (G : SimpleGraph V) := {p : V × V // G.Adj p.1 p.2}

/-- Two directed edges are adjacent if they concatenate in either order. -/
def arcGraph (G : SimpleGraph V) : SimpleGraph (Arc G) where
  Adj p q := p.1.2 = q.1.1 ∨ q.1.2 = p.1.1
  symm := fun _ _ h => h.symm
  loopless := fun p h => h.elim (fun h => p.2.ne h.symm) (fun h => p.2.ne h.symm)

/-- Complete ordered bicliques. Empty sides are allowed and give isolated
vertices when they cannot meet the adjacency requirements. -/
abbrev Biclique (H : SimpleGraph W) :=
  {p : Set W × Set W // ∀ a ∈ p.1, ∀ b ∈ p.2, H.Adj a b}

/-- The mutual-intersection right adjoint. -/
def right (H : SimpleGraph W) : SimpleGraph (Biclique H) where
  Adj p q := (p.1.2 ∩ q.1.1).Nonempty ∧ (q.1.2 ∩ p.1.1).Nonempty
  symm := fun _ _ h => h.symm
  loopless := by
    intro p h
    obtain ⟨x, hxB, hxA⟩ := h.1
    exact H.loopless x (p.2 x hxA x hxB)

/-- Currying an arc-graph map gives a map to the biclique graph. -/
def toRight {G : SimpleGraph V} {H : SimpleGraph W} (f : arcGraph G →g H) :
    G →g right H where
  toFun v :=
    ⟨({w | ∃ e : Arc G, e.1.2 = v ∧ f e = w},
      {w | ∃ e : Arc G, e.1.1 = v ∧ f e = w}), by
      rintro a ⟨e, he, rfl⟩ b ⟨d, hd, rfl⟩
      exact f.map_adj (Or.inl (he.trans hd.symm))⟩
  map_rel' := by
    intro u v huv
    let e : Arc G := ⟨(u,v), huv⟩
    let d : Arc G := ⟨(v,u), huv.symm⟩
    exact ⟨⟨f e, ⟨e, rfl, rfl⟩, ⟨e, rfl, rfl⟩⟩,
      ⟨f d, ⟨d, rfl, rfl⟩, ⟨d, rfl, rfl⟩⟩⟩

/-- Uncurrying chooses a point in the required nonempty intersection. -/
noncomputable def fromRight {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g right H) : arcGraph G →g H where
  toFun e := (f.map_adj e.2).1.choose
  map_rel' := by
    intro e d hed
    have he := (f.map_adj e.2).1.choose_spec
    have hd := (f.map_adj d.2).1.choose_spec
    rcases hed with h | h
    · have ha : (f.map_adj e.2).1.choose ∈ (f d.1.1).1.1 := h ▸ he.2
      exact (f d.1.1).2 _ ha _ hd.1
    · have ha : (f.map_adj d.2).1.choose ∈ (f e.1.1).1.1 := h ▸ hd.2
      exact ((f e.1.1).2 _ ha _ he.1).symm

/-- The adjunction is stated as existence of graph homomorphisms. -/
theorem hom_iff (G : SimpleGraph V) (H : SimpleGraph W) :
    Nonempty (arcGraph G →g H) ↔ Nonempty (G →g right H) :=
  ⟨fun ⟨f⟩ => ⟨toRight f⟩, fun ⟨f⟩ => ⟨fromRight f⟩⟩

def unit (G : SimpleGraph V) : G →g right (arcGraph G) :=
  toRight (SimpleGraph.Hom.id)

private def topHomEmbedding {A : Type*} {H : SimpleGraph W}
    (f : (⊤ : SimpleGraph A) →g H) : (⊤ : SimpleGraph A) ↪g H where
  toFun := f
  inj' := f.injective_of_top_hom
  map_rel_iff' := by
    intro a b
    exact ⟨fun h he => h.ne (congrArg f he), fun h => f.map_adj h⟩

/-- An exact finite clique criterion for the right adjoint. In particular,
its K4 exclusion is a homomorphism exclusion involving a fixed 12-vertex graph. -/
theorem right_not_cliqueFree_iff (H : SimpleGraph W) (n : ℕ) :
    ¬(right H).CliqueFree n ↔
      Nonempty (arcGraph (⊤ : SimpleGraph (Fin n)) →g H) := by
  constructor
  · intro h
    exact ⟨fromRight (SimpleGraph.topEmbeddingOfNotCliqueFree h).toHom⟩
  · rintro ⟨f⟩
    exact SimpleGraph.not_cliqueFree_of_top_embedding (topHomEmbedding (toRight f))

/-- Every triangle of the arc graph is a directed three-cycle. -/
theorem arc_triangle {G : SimpleGraph V} {p q r : Arc G}
    (hpq : (arcGraph G).Adj p q) (hpr : (arcGraph G).Adj p r)
    (hqr : (arcGraph G).Adj q r) :
    (p.1.2 = q.1.1 ∧ q.1.2 = r.1.1 ∧ r.1.2 = p.1.1) ∨
    (q.1.2 = p.1.1 ∧ p.1.2 = r.1.1 ∧ r.1.2 = q.1.1) := by
  have hp := p.2.ne
  have hq := q.2.ne
  have hr := r.2.ne
  rcases hpq with hpq | hpq <;> rcases hpr with hpr | hpr <;>
    rcases hqr with hqr | hqr <;> aesop

private theorem different_tails {G : SimpleGraph V} {p q : Arc G}
    (h : (arcGraph G).Adj p q) : p.1.1 ≠ q.1.1 := by
  intro he
  rcases h with h | h
  · exact p.2.ne (he.trans h.symm)
  · exact q.2.ne (he.symm.trans h.symm)

private theorem different_heads {G : SimpleGraph V} {p q : Arc G}
    (h : (arcGraph G).Adj p q) : p.1.2 ≠ q.1.2 := by
  intro he
  rcases h with h | h
  · exact q.2.ne (h.symm.trans he)
  · exact p.2.ne (h.symm.trans he.symm)

/-- Arc graphs are always K4-free: every neighbourhood is bipartite. -/
theorem arc_cliqueFree_four (G : SimpleGraph V) : (arcGraph G).CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have hadj : ∀ i j : Fin 4, i ≠ j → (arcGraph G).Adj (e i) (e j) :=
    fun _ _ h => e.map_rel_iff.mpr h
  have h12 := hadj 1 2 (by decide)
  have h13 := hadj 1 3 (by decide)
  have h23 := hadj 2 3 (by decide)
  rcases hadj 0 1 (by decide) with h01 | h10 <;>
    rcases hadj 0 2 (by decide) with h02 | h20
  · exact different_tails h12 (h01.symm.trans h02)
  · rcases hadj 0 3 (by decide) with h03 | h30
    · exact different_tails h13 (h01.symm.trans h03)
    · exact different_heads h23 (h20.trans h30.symm)
  · rcases hadj 0 3 (by decide) with h03 | h30
    · exact different_tails h23 (h02.symm.trans h03)
    · exact different_heads h13 (h10.trans h30.symm)
  · exact different_heads h12 (h10.trans h20.symm)

/-- In contrast, the right adjoint does not preserve K4-freeness in general. -/
theorem right_can_create_four :
    ∃ (A : Type) (G : SimpleGraph A), G.CliqueFree 4 ∧ ¬(right G).CliqueFree 4 := by
  let G := arcGraph (⊤ : SimpleGraph (Fin 4))
  exact ⟨_, G, arc_cliqueFree_four _,
    (right_not_cliqueFree_iff G 4).mpr ⟨SimpleGraph.Hom.id⟩⟩

/-- A useful sufficient covering criterion for the right adjoint. The base
colouring must make each triangle RAINBOW, not merely non-monochromatic. -/
theorem right_cover_of_rainbow {C : Type*} [Countable C]
    (H : SimpleGraph W) (c : W → C)
    (hc : ∀ a b d, H.Adj a b → H.Adj a d → H.Adj b d →
      c a ≠ c b ∧ c a ≠ c d ∧ c b ≠ c d) :
    Erdos595Work.IsCountableUnionOfTriangleFree (right H) := by
  classical
  obtain ⟨enc, henc⟩ := exists_injective_nat (Sym2 C)
  let col : Sym2 (Biclique H) → ℕ := Sym2.lift
    ⟨fun p q => if h : (right H).Adj p q then
        enc s(c h.1.choose, c h.2.choose) else 0, by
      intro p q
      dsimp only
      by_cases h : (right H).Adj p q
      · rw [dif_pos h, dif_pos h.symm]
        exact congrArg enc (Sym2.eq_swap)
      · rw [dif_neg h, dif_neg (fun h' => h h'.symm)]⟩
  have hcol : ∀ p q (h : (right H).Adj p q),
      col s(p,q) = enc s(c h.1.choose, c h.2.choose) := by
    intro p q h
    simp only [col, Sym2.lift_mk, dif_pos h]
  apply (Erdos595Work.countable_union_iff_edge_coloring (right H)).mpr
  refine ⟨col, ?_⟩
  intro p q r hpq hpr hqr he
  have he1 : s(c hpq.1.choose, c hpq.2.choose) =
      s(c hpr.1.choose, c hpr.2.choose) := by
    apply henc
    simpa only [hcol p q hpq, hcol p r hpr] using he.1
  have he2 : s(c hpq.1.choose, c hpq.2.choose) =
      s(c hqr.1.choose, c hqr.2.choose) := by
    apply henc
    simpa only [hcol p q hpq, hcol q r hqr] using he.2
  have hpq' := hpq.1.choose_spec
  have hqr' := hqr.1.choose_spec
  have hrp' := hpr.2.choose_spec
  have hxy : H.Adj hpq.1.choose hqr.1.choose :=
    q.2 _ hpq'.2 _ hqr'.1
  have hxz : H.Adj hpq.1.choose hpr.2.choose :=
    (p.2 _ hrp'.2 _ hpq'.1).symm
  have hyz : H.Adj hqr.1.choose hpr.2.choose :=
    r.2 _ hqr'.2 _ hrp'.1
  have hrain := hc _ _ _ hxy hxz hyz
  have hy : c hqr.1.choose ∈ s(c hpq.1.choose, c hpq.2.choose) :=
    he2.symm ▸ Sym2.mem_mk_left _ _
  have hz : c hpr.2.choose ∈ s(c hpq.1.choose, c hpq.2.choose) :=
    he1.symm ▸ Sym2.mem_mk_right _ _
  rcases Sym2.mem_iff.mp hy with hy | hy
  · exact hrain.1 hy.symm
  rcases Sym2.mem_iff.mp hz with hz | hz
  · exact hrain.2.1 hz.symm
  exact hrain.2.2 (hy.trans hz.symm)

#print axioms right_cover_of_rainbow
#print axioms hom_iff
#print axioms right_not_cliqueFree_iff
#print axioms arc_cliqueFree_four
#print axioms right_can_create_four
end Erdos595ArcAdjoint
