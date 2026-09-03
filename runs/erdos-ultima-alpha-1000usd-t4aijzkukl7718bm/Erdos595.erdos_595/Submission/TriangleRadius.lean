import Submission.Work

/-!
A normalization obstruction for local recoloring arguments. This file does not
settle Erdős Problem 595. Every graph embeds inducedly in a graph whose edges
are at triangle-sharing distance at most four from a distinguished edge, and
this enlargement preserves K₄-freeness.
-/

open SimpleGraph Set
namespace Erdos595TriangleRadius

universe u
inductive Vertex (V : Type u)
  | a | b | port (v : V) | pair (e : Sym2 V) | orig (v : V)

variable {V : Type u}

def Rel (G : SimpleGraph V) : Vertex V → Vertex V → Prop
  | .a, .b | .b, .a => True
  | .a, .port _ | .port _, .a => True
  | .b, .port _ | .port _, .b => True
  | .a, .pair _ | .pair _, .a => True
  | .port v, .pair e | .pair e, .port v => v ∈ e
  | .orig v, .pair e | .pair e, .orig v => v ∈ e
  | .orig v, .port w | .port w, .orig v => v = w
  | .orig v, .orig w => G.Adj v w
  | _, _ => False

def graph (G : SimpleGraph V) : SimpleGraph (Vertex V) where
  Adj := Rel G
  symm := by intro x y h; cases x <;> cases y <;> simp_all [Rel, G.adj_comm]
  loopless := by intro x; cases x <;> simp [Rel]

lemma adj_iff (G : SimpleGraph V) (x y : Vertex V) :
    (graph G).Adj x y ↔ Rel G x y := Iff.rfl

lemma triangle_free_a (G : SimpleGraph V) (x y z : Vertex V)
    (hx : (graph G).Adj .a x) (hy : (graph G).Adj .a y)
    (hz : (graph G).Adj .a z) (hxy : (graph G).Adj x y)
    (hxz : (graph G).Adj x z) (hyz : (graph G).Adj y z) : False := by
  cases x <;> cases y <;> cases z <;> simp_all [adj_iff, Rel]

lemma triangle_free_b (G : SimpleGraph V) (x y z : Vertex V)
    (hx : (graph G).Adj .b x) (hy : (graph G).Adj .b y)
    (hz : (graph G).Adj .b z) (hxy : (graph G).Adj x y)
    (hxz : (graph G).Adj x z) (hyz : (graph G).Adj y z) : False := by
  cases x <;> cases y <;> cases z <;> simp_all [adj_iff, Rel]

lemma triangle_free_port (G : SimpleGraph V) (v : V) (x y z : Vertex V)
    (hx : (graph G).Adj (.port v) x) (hy : (graph G).Adj (.port v) y)
    (hz : (graph G).Adj (.port v) z) (hxy : (graph G).Adj x y)
    (hxz : (graph G).Adj x z) (hyz : (graph G).Adj y z) : False := by
  cases x <;> cases y <;> cases z <;> simp_all [adj_iff, Rel]

lemma triangle_free_pair (G : SimpleGraph V) (e : Sym2 V) (x y z : Vertex V)
    (hx : (graph G).Adj (.pair e) x) (hy : (graph G).Adj (.pair e) y)
    (hz : (graph G).Adj (.pair e) z) (hxy : (graph G).Adj x y)
    (hxz : (graph G).Adj x z) (hyz : (graph G).Adj y z) : False := by
  induction e using Sym2.inductionOn with
  | _ v w =>
    cases x <;> cases y <;> cases z <;>
      simp_all [adj_iff, Rel, Sym2.mem_iff] <;> aesop

lemma orig_of_four (G : SimpleGraph V) (q x y z : Vertex V)
    (hqx : (graph G).Adj q x) (hqy : (graph G).Adj q y)
    (hqz : (graph G).Adj q z) (hxy : (graph G).Adj x y)
    (hxz : (graph G).Adj x z) (hyz : (graph G).Adj y z) :
    ∃ v, q = .orig v := by
  cases q with
  | a => exact (triangle_free_a G x y z hqx hqy hqz hxy hxz hyz).elim
  | b => exact (triangle_free_b G x y z hqx hqy hqz hxy hxz hyz).elim
  | port v => exact (triangle_free_port G v x y z hqx hqy hqz hxy hxz hyz).elim
  | pair e => exact (triangle_free_pair G e x y z hqx hqy hqz hxy hxz hyz).elim
  | orig v => exact ⟨v, rfl⟩

lemma no_four (G : SimpleGraph V) (hG : G.CliqueFree 4) (q x y z : Vertex V)
    (hqx : (graph G).Adj q x) (hqy : (graph G).Adj q y)
    (hqz : (graph G).Adj q z) (hxy : (graph G).Adj x y)
    (hxz : (graph G).Adj x z) (hyz : (graph G).Adj y z) : False := by
  obtain ⟨q', rfl⟩ := orig_of_four G q x y z hqx hqy hqz hxy hxz hyz
  obtain ⟨x', rfl⟩ := orig_of_four G x (.orig q') y z hqx.symm hxy hxz hqy hqz hyz
  obtain ⟨y', rfl⟩ := orig_of_four G y (.orig q') (.orig x') z
    hqy.symm hxy.symm hyz hqx hqz hxz
  obtain ⟨z', rfl⟩ := orig_of_four G z (.orig q') (.orig x') (.orig y')
    hqz.symm hxz.symm hyz.symm hqx hqy hxy
  exact Erdos595Work.no_adj_common_neighbors hG hqx hqy hxy hqz hxz hyz

theorem cliqueFree (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    (graph G).CliqueFree 4 := by
  classical
  by_contra hn
  let f : (⊤ : SimpleGraph (Fin 4)) ↪g graph G :=
    SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have hadj : ∀ i j : Fin 4, i ≠ j → (graph G).Adj (f i) (f j) := by
    intro i j hij
    exact f.map_rel_iff.mpr (by simpa only [SimpleGraph.top_adj] using hij)
  exact no_four G hG (f 0) (f 1) (f 2) (f 3)
    (hadj 0 1 (by decide)) (hadj 0 2 (by decide)) (hadj 0 3 (by decide))
    (hadj 1 2 (by decide)) (hadj 1 3 (by decide)) (hadj 2 3 (by decide))

def embedding (G : SimpleGraph V) : G ↪g graph G where
  toFun := Vertex.orig
  inj' := by intro v w h; exact Vertex.orig.inj h
  map_rel_iff' := Iff.rfl

/-- An edge reached from `a--b` in at most `n` triangle-sharing steps. -/
inductive Within (G : SimpleGraph V) : ℕ → Sym2 (Vertex V) → Prop
  | base : Within G 0 s(.a, .b)
  | wait {n e} : Within G n e → Within G (n + 1) e
  | step {n x y z e} : Within G n s(x, y) →
      (graph G).Adj x y → (graph G).Adj x z → (graph G).Adj y z →
      (e = s(x, z) ∨ e = s(y, z)) → Within G (n + 1) e

lemma ports_one (G : SimpleGraph V) (v : V) :
    Within G 1 s(.a, .port v) ∧ Within G 1 s(.b, .port v) := by
  constructor
  · exact .step (z := .port v) .base trivial trivial trivial (Or.inl rfl)
  · exact .step (z := .port v) .base trivial trivial trivial (Or.inr rfl)

lemma pairs_two (G : SimpleGraph V) (v : V) (e : Sym2 V) (hv : v ∈ e) :
    Within G 2 s(.a, .pair e) ∧ Within G 2 s(.port v, .pair e) := by
  constructor
  · exact .step (z := .pair e) (ports_one G v).1 trivial trivial hv (Or.inl rfl)
  · exact .step (z := .pair e) (ports_one G v).1 trivial trivial hv (Or.inr rfl)

lemma originals_three (G : SimpleGraph V) (v : V) (e : Sym2 V) (hv : v ∈ e) :
    Within G 3 s(.port v, .orig v) ∧ Within G 3 s(.pair e, .orig v) := by
  constructor
  · exact .step (z := .orig v) (pairs_two G v e hv).2 hv rfl hv (Or.inl rfl)
  · exact .step (z := .orig v) (pairs_two G v e hv).2 hv rfl hv (Or.inr rfl)

lemma original_edges_four (G : SimpleGraph V) (v w : V) (hvw : G.Adj v w) :
    Within G 4 s(.orig v, .orig w) := by
  have hv := Sym2.mem_mk_left v w
  have hw := Sym2.mem_mk_right v w
  exact .step (z := .orig w) (originals_three G v s(v, w) hv).2 hv hw hvw (Or.inr rfl)

/-- No triangle-sharing radius bound can exclude a bad graph: the enlargement
has radius at most four, regardless of the original graph. -/
theorem all_edges_within_four (G : SimpleGraph V) (x y : Vertex V)
    (hxy : (graph G).Adj x y) : Within G 4 s(x, y) := by
  cases x with
  | a =>
    cases y with
    | a => exact hxy.elim
    | b => exact .wait (.wait (.wait (.wait .base)))
    | port v => exact .wait (.wait (.wait (ports_one G v).1))
    | pair e =>
      induction e using Sym2.inductionOn with
      | _ v w => exact .wait (.wait (pairs_two G v s(v, w) (Sym2.mem_mk_left v w)).1)
    | orig v => exact hxy.elim
  | b =>
    cases y with
    | a => simpa only [Sym2.eq_swap] using (Within.wait (Within.wait (Within.wait
        (Within.wait (Within.base (G := G))))))
    | b => exact hxy.elim
    | port v => exact .wait (.wait (.wait (ports_one G v).2))
    | pair e => exact hxy.elim
    | orig v => exact hxy.elim
  | port v =>
    cases y with
    | a => simpa only [Sym2.eq_swap] using
        (Within.wait (Within.wait (Within.wait (ports_one G v).1)))
    | b => simpa only [Sym2.eq_swap] using
        (Within.wait (Within.wait (Within.wait (ports_one G v).2)))
    | port w => exact hxy.elim
    | pair e => exact .wait (.wait (pairs_two G v e hxy).2)
    | orig w =>
      have hw : w = v := hxy
      subst w
      exact .wait (originals_three G v s(v, v) (Sym2.mem_mk_left v v)).1
  | pair e =>
    cases y with
    | a =>
      induction e using Sym2.inductionOn with
      | _ v w => simpa only [Sym2.eq_swap] using
          (Within.wait (Within.wait (pairs_two G v s(v, w) (Sym2.mem_mk_left v w)).1))
    | b => exact hxy.elim
    | port v => simpa only [Sym2.eq_swap] using
        (Within.wait (Within.wait (pairs_two G v e hxy).2))
    | pair f => exact hxy.elim
    | orig v => exact .wait (originals_three G v e hxy).2
  | orig v =>
    cases y with
    | a => exact hxy.elim
    | b => exact hxy.elim
    | port w =>
      have hv : v = w := hxy
      subst w
      simpa only [Sym2.eq_swap] using
        (Within.wait (originals_three G v s(v, v) (Sym2.mem_mk_left v v)).1)
    | pair e => simpa only [Sym2.eq_swap] using
        (Within.wait (originals_three G v e hxy).2)
    | orig w => exact original_edges_four G v w hxy

theorem no_cover_preserved (G : SimpleGraph V)
    (hG : ¬Erdos595Work.IsCountableUnionOfTriangleFree G) :
    ¬Erdos595Work.IsCountableUnionOfTriangleFree (graph G) := by
  intro h
  exact hG (Erdos595Work.countable_union_of_hom (embedding G).toHom h)

#print axioms cliqueFree
#print axioms all_edges_within_four
#print axioms no_cover_preserved
end Erdos595TriangleRadius
