import Submission.ArcAdjoint
import Submission.MiddleCornerObstruction

/-!
Finite-palette compactness for triangle-free edge coverings, and finite
witness reflection for the biclique right adjoint. These do NOT supply a
uniform finite bound and do not settle Erdős 595.
-/

set_option autoImplicit false
open Set Filter SimpleGraph
open Erdos595Work Erdos595ArcAdjoint
namespace Erdos595FinitePalette

variable {V W C : Type*}

def HasColoring (G : SimpleGraph V) (C : Type*) : Prop :=
  ∃ c : Sym2 V → C, ∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
    ¬(c s(x,y) = c s(x,z) ∧ c s(x,y) = c s(y,z))

theorem HasColoring.comap {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (h : HasColoring H C) : HasColoring G C := by
  obtain ⟨c,hc⟩ := h
  refine ⟨fun e => c (e.map f), ?_⟩
  intro x y z hxy hxz hyz hm
  exact hc (f x) (f y) (f z) (f.map_adj hxy) (f.map_adj hxz) (f.map_adj hyz) hm

theorem HasColoring.countable_cover [Countable C] {G : SimpleGraph V}
    (h : HasColoring G C) : IsCountableUnionOfTriangleFree G := by
  obtain ⟨c,hc⟩ := h
  obtain ⟨enc,he⟩ := exists_injective_nat C
  apply countable_union_iff_edge_coloring G |>.mpr
  refine ⟨enc ∘ c, ?_⟩
  intro x y z hxy hxz hyz hm
  exact hc x y z hxy hxz hyz ⟨he hm.1,he hm.2⟩

/-- Finite palettes, unlike countable palettes, obey compactness. -/
theorem compactness [Finite C] [Nonempty C] (G : SimpleGraph V)
    (h : ∀ S : Finset V, HasColoring (G.induce (S : Set V)) C) :
    HasColoring G C := by
  classical
  choose c hc using h
  let col : Finset V → Sym2 V → C := fun S => Sym2.lift
    ⟨fun x y => if hxy : x ∈ S ∧ y ∈ S then c S s(⟨x,hxy.1⟩,⟨y,hxy.2⟩)
      else Classical.arbitrary C, by
      intro x y
      by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
        simp [hx,hy,Sym2.eq_swap]⟩
  let U : Ultrafilter (Finset V) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset V)) ≤ atTop := Ultrafilter.of_le _
  have hmem (v : V) : ∀ᶠ S in (U : Filter (Finset V)), v ∈ S := by
    apply hU
    exact Filter.eventually_atTop.mpr ⟨{v},fun S hS => hS (by simp)⟩
  have hex (e : Sym2 V) : ∃ k : C, ∀ᶠ S in (U : Filter (Finset V)), col S e = k := by
    apply Ultrafilter.eventually_exists_iff.mp
    exact Filter.Eventually.of_forall fun S => ⟨col S e,rfl⟩
  choose d hd using hex
  refine ⟨d, ?_⟩
  intro x y z hxy hxz hyz hm
  have he := (hd s(x,y)).and ((hd s(x,z)).and (hd s(y,z)))
  obtain ⟨S,hS,hcol⟩ := ((hmem x).and ((hmem y).and (hmem z)) |>.and he).exists
  have hx : x ∈ S := hS.1
  have hy : y ∈ S := hS.2.1
  have hz : z ∈ S := hS.2.2
  have h₁ : c S s(⟨x,hx⟩,⟨y,hy⟩) = d s(x,y) := by
    simpa only [col,Sym2.lift_mk,hx,hy,and_self,dif_pos] using hcol.1
  have h₂ : c S s(⟨x,hx⟩,⟨z,hz⟩) = d s(x,z) := by
    simpa only [col,Sym2.lift_mk,hx,hz,and_self,dif_pos] using hcol.2.1
  have h₃ : c S s(⟨y,hy⟩,⟨z,hz⟩) = d s(y,z) := by
    simpa only [col,Sym2.lift_mk,hy,hz,and_self,dif_pos] using hcol.2.2
  exact hc S ⟨x,hx⟩ ⟨y,hy⟩ ⟨z,hz⟩ hxy hxz hyz
    ⟨h₁.trans (hm.1.trans h₂.symm), h₁.trans (hm.2.trans h₃.symm)⟩

theorem compactness_iff [Finite C] [Nonempty C] (G : SimpleGraph V) :
    HasColoring G C ↔ ∀ S : Finset V, HasColoring (G.induce (S : Set V)) C := by
  refine ⟨?_,compactness G⟩
  intro h S
  exact h.comap (SimpleGraph.Embedding.comap (Function.Embedding.subtype _) G).toHom

/-- Any finite graph mapping to a full right adjoint already maps to the
right adjoint of a finite induced subgraph of its base. -/
theorem right_finite_witness {I : Type*} [Finite I]
    (F : SimpleGraph I) (H : SimpleGraph V) (f : F →g right H) :
    ∃ S : Finset V, Nonempty (F →g right (H.induce (S : Set V))) := by
  classical
  letI := Fintype.ofFinite I
  let T (i j : I) : Finset V := if h : F.Adj i j then {(f.map_adj h).1.choose} else ∅
  let S : Finset V := Finset.univ.biUnion fun i => Finset.univ.biUnion (T i)
  have hmem (i j : I) (hij : F.Adj i j) : (f.map_adj hij).1.choose ∈ S := by
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,?_⟩⟩
    simp only [T,dif_pos hij,Finset.mem_singleton]
  let p (i : I) : Biclique (H.induce (S : Set V)) :=
    ⟨({x | x.1 ∈ (f i).1.1},{x | x.1 ∈ (f i).1.2}), by
      intro x hx y hy
      exact (f i).2 x hx y hy⟩
  refine ⟨S,⟨{ toFun := p, map_rel' := ?_ }⟩⟩
  intro i j hij
  have h₁ := (f.map_adj hij).1.choose_spec
  have h₂ := (f.map_adj hij.symm).1.choose_spec
  exact ⟨⟨⟨(f.map_adj hij).1.choose,hmem i j hij⟩,h₁.1,h₁.2⟩,
    ⟨⟨(f.map_adj hij.symm).1.choose,hmem j i hij.symm⟩,h₂.1,h₂.2⟩⟩

/-- Functoriality of the right adjoint. -/
def rightMap {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H) :
    right G →g right H where
  toFun p := ⟨(f '' p.1.1,f '' p.1.2),by
    rintro a ⟨x,hx,rfl⟩ b ⟨y,hy,rfl⟩
    exact f.map_adj (p.2 x hx y hy)⟩
  map_rel' := by
    intro p q hpq
    obtain ⟨a,hap,haq⟩ := hpq.1
    obtain ⟨b,hbq,hbp⟩ := hpq.2
    exact ⟨⟨f a,⟨a,hap,rfl⟩,⟨a,haq,rfl⟩⟩,
      ⟨f b,⟨b,hbq,rfl⟩,⟨b,hbp,rfl⟩⟩⟩

/-- A UNIFORM finite palette on all finite bases extends to the full
right-adjoint graph. The palette must be fixed independently of S. -/
theorem right_compactness_iff [Finite C] [Nonempty C] (H : SimpleGraph V) :
    HasColoring (right H) C ↔
      ∀ S : Finset V, HasColoring (right (H.induce (S : Set V))) C := by
  constructor
  · intro h S
    exact h.comap (rightMap (SimpleGraph.Embedding.comap
      (Function.Embedding.subtype _) H).toHom)
  · intro h
    apply compactness (right H)
    intro T
    let F := (right H).induce (T : Set (Biclique H))
    let f : F →g right H :=
      (SimpleGraph.Embedding.comap (Function.Embedding.subtype _) (right H)).toHom
    obtain ⟨S,⟨g⟩⟩ := right_finite_witness F H f
    exact (h S).comap g

/-- Finite witnesses reflect through two successive right adjoints as well. -/
theorem right_twice_finite_witness {I : Type*} [Finite I]
    (F : SimpleGraph I) (H : SimpleGraph V) (f : F →g right (right H)) :
    ∃ S : Finset V, Nonempty (F →g right (right (H.induce (S : Set V)))) := by
  classical
  obtain ⟨T,⟨g⟩⟩ := right_finite_witness F (right H) f
  let J := (right H).induce (T : Set (Biclique H))
  let j : J →g right H :=
    (SimpleGraph.Embedding.comap (Function.Embedding.subtype _) (right H)).toHom
  obtain ⟨S,⟨k⟩⟩ := right_finite_witness J H j
  exact ⟨S,⟨(rightMap k).comp g⟩⟩

theorem right_twice_compactness_iff [Finite C] [Nonempty C] (H : SimpleGraph V) :
    HasColoring (right (right H)) C ↔
      ∀ S : Finset V, HasColoring (right (right (H.induce (S : Set V)))) C := by
  constructor
  · intro h S
    exact h.comap (rightMap (rightMap (SimpleGraph.Embedding.comap
      (Function.Embedding.subtype _) H).toHom))
  · intro h
    apply compactness (right (right H))
    intro T
    let F := (right (right H)).induce (T : Set (Biclique (right H)))
    let f : F →g right (right H) :=
      (SimpleGraph.Embedding.comap (Function.Embedding.subtype _) (right (right H))).toHom
    obtain ⟨S,⟨g⟩⟩ := right_twice_finite_witness F H f
    exact (h S).comap g

open Erdos595MiddleCorner

/-- A finite graph mapping to an arbitrary shift-square graph already maps
to a shift-square graph over a finite linear order. -/
theorem shift_finite_order_witness {I A : Type*} [Finite I] [LinearOrder A]
    (F : SimpleGraph I) (f : F →g graph A) :
    ∃ n : ℕ, Nonempty (F →g graph (Fin n)) := by
  classical
  letI := Fintype.ofFinite I
  let T : Finset A := Finset.univ.biUnion fun i => {(f i).a,(f i).b,(f i).c}
  have ha (i : I) : (f i).a ∈ T := by
    simp only [T,Finset.mem_biUnion,Finset.mem_univ,true_and]
    exact ⟨i,by simp⟩
  have hb (i : I) : (f i).b ∈ T := by
    simp only [T,Finset.mem_biUnion,Finset.mem_univ,true_and]
    exact ⟨i,by simp⟩
  have hc (i : I) : (f i).c ∈ T := by
    simp only [T,Finset.mem_biUnion,Finset.mem_univ,true_and]
    exact ⟨i,by simp⟩
  let e : T ≃o Fin T.card := (T.orderIsoOfFin rfl).symm
  let t (i : I) : Triple (Fin T.card) :=
    ⟨e ⟨(f i).a,ha i⟩,e ⟨(f i).b,hb i⟩,e ⟨(f i).c,hc i⟩,
      e.strictMono (f i).ab,e.strictMono (f i).bc⟩
  refine ⟨T.card,⟨{ toFun := t, map_rel' := ?_ }⟩⟩
  intro i j hij
  have h := f.map_adj hij
  rcases h with (⟨h₁,h₂⟩ | h₁) | (⟨h₁,h₂⟩ | h₁)
  · exact Or.inl (Or.inl ⟨congrArg e (Subtype.ext h₁),congrArg e (Subtype.ext h₂)⟩)
  · exact Or.inl (Or.inr (congrArg e (Subtype.ext h₁)))
  · exact Or.inr (Or.inl ⟨congrArg e (Subtype.ext h₁),congrArg e (Subtype.ext h₂)⟩)
  · exact Or.inr (Or.inr (congrArg e (Subtype.ext h₁)))

/-- A uniform finite palette on ALL finite twice-right-shift graphs is
sufficient at every cardinality. This theorem does not assert such a bound. -/
theorem right_twice_shift_of_uniform_finite [Finite C] [Nonempty C]
    (h : ∀ n : ℕ, HasColoring (right (right (graph (Fin n)))) C)
    (A : Type*) [LinearOrder A] : HasColoring (right (right (graph A))) C := by
  apply (right_twice_compactness_iff (graph A)).mpr
  intro S
  let F := (graph A).induce (S : Set (Triple A))
  let f : F →g graph A :=
    (SimpleGraph.Embedding.comap (Function.Embedding.subtype _) (graph A)).toHom
  obtain ⟨n,⟨g⟩⟩ := shift_finite_order_witness F f
  exact (h n).comap (rightMap (rightMap g))

/-- Consequently a non-coverable twice-right-shift graph would require
unbounded finite palette obstructions among the finite-order instances. -/
theorem right_twice_shift_finite_obstructions (A : Type*) [LinearOrder A]
    (h : ¬IsCountableUnionOfTriangleFree (right (right (graph A))))
    (r : ℕ) (hr : 0 < r) :
    ∃ n : ℕ, ¬HasColoring (right (right (graph (Fin n)))) (Fin r) := by
  classical
  letI : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  by_contra! hn
  exact h (right_twice_shift_of_uniform_finite hn A).countable_cover

#print axioms right_twice_finite_witness
#print axioms right_twice_compactness_iff
#print axioms shift_finite_order_witness
#print axioms right_twice_shift_of_uniform_finite
#print axioms right_twice_shift_finite_obstructions

/-- A non-coverable right adjoint requires arbitrarily large finite
palette obstructions already in right adjoints of finite base graphs. -/
theorem finite_obstructions_of_right_no_cover (H : SimpleGraph V)
    (h : ¬IsCountableUnionOfTriangleFree (right H)) (r : ℕ) (hr : 0 < r) :
    ∃ S : Finset V, ¬HasColoring (right (H.induce (S : Set V))) (Fin r) := by
  classical
  letI : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  by_contra! hn
  exact h ((right_compactness_iff H).mpr hn).countable_cover

#print axioms compactness
#print axioms right_finite_witness
#print axioms right_compactness_iff
#print axioms finite_obstructions_of_right_no_cover

end Erdos595FinitePalette
