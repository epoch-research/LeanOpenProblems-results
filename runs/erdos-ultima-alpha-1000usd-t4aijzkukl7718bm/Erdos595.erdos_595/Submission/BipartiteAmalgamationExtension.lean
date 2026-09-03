import Submission.FiniteFolkmanAmalgamation
import Submission.FiniteAdaptedExtension

/-!
A prescribed countable triangle-avoiding edge coloring on one distinguished
copy extends unchanged across a free amalgamation with a countably
vertex-colored triangle-free base. In particular this holds for all the
bipartite bases used in the partite Ramsey steps. No finiteness of the
attaching subgraph or the family of copies is needed.
This is a limitation of that construction, not a solution of Erdős 595.
-/

set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595BipartiteAmalgamationExtension
open Erdos595FiniteFolkmanAmalgamation Erdos595FiniteAdapted

variable {A B I : Type*} (H : SimpleGraph A) (K : SimpleGraph B)
    (D : Set A) (e : I → H.induce D ↪g K) (i₀ : I)
    (side : B → ℕ) (c : Sym2 A → ℕ)

/-- Even side colors and odd private colors use disjoint countable palettes. -/
def fallback : Sym2 (Vertex D (B := B) (I := I)) → ℕ :=
  Sym2.lift ⟨fun x y => match x,y with
    | .inl _, .inl _ => 0
    | .inl b, .inr _ => 2 * side b
    | .inr _, .inl b => 2 * side b
    | .inr a, .inr b => 2 * c s(a.2.val,b.2.val) + 1,
    by intro x y; cases x <;> cases y <;> simp only [Sym2.eq_swap]⟩

/-- Override the fallback on all unordered pairs of the distinguished copy. -/
noncomputable def color : Sym2 (Vertex D (B := B) (I := I)) → ℕ :=
  Function.extend (Sym2.map (copy H K D e i₀)) c (fallback D side c)

lemma color_copy (a b : A) :
    color H K D e i₀ side c s(copy H K D e i₀ a,copy H K D e i₀ b) = c s(a,b) := by
  exact (Sym2.map.injective (copy_injective H K D e i₀)).extend_apply c
    (fallback D side c) s(a,b)

lemma private_not_in_copy {i : I} (hi : i ≠ i₀) (a : Outside D) :
    ¬∃ b : A, copy H K D e i₀ b = Sum.inr (i,a) := by
  classical
  rintro ⟨b,hb⟩
  by_cases hd : b ∈ D
  · rw [copy_of_mem _ _ _ _ _ _ hd] at hb
    simp only [Sum.inl_ne_inr] at hb
  · rw [copy_of_not_mem _ _ _ _ _ _ hd] at hb
    exact hi (congrArg Prod.fst (Sum.inr.inj hb)).symm

lemma color_other_private {i : I} (hi : i ≠ i₀) (a : Outside D)
    (z : Vertex D (B := B) (I := I)) :
    color H K D e i₀ side c s(Sum.inr (i,a),z) =
      fallback D side c s(Sum.inr (i,a),z) := by
  apply Function.extend_apply'
  rintro ⟨s,hs⟩
  have hm : Sum.inr (i,a) ∈ s.map (copy H K D e i₀) := by rw [hs]; simp
  obtain ⟨b,_,hb⟩ := Sym2.mem_map.mp hm
  exact private_not_in_copy H K D e i₀ hi a ⟨b,hb⟩

lemma valid_at_distinguished (hc : Valid H c) (a : Outside D)
    (x y : Vertex D (B := B) (I := I))
    (hax : (graph H K D e).Adj (Sum.inr (i₀,a)) x)
    (hay : (graph H K D e).Adj (Sum.inr (i₀,a)) y)
    (hxy : (graph H K D e).Adj x y) :
    ¬(color H K D e i₀ side c s(Sum.inr (i₀,a),x) =
        color H K D e i₀ side c s(Sum.inr (i₀,a),y) ∧
      color H K D e i₀ side c s(Sum.inr (i₀,a),x) =
        color H K D e i₀ side c s(x,y)) := by
  obtain ⟨b,rfl⟩ := neighbor_private H K D e hax
  obtain ⟨d,rfl⟩ := neighbor_private H K D e hay
  have ha : Sum.inr (i₀,a) = copy H K D e i₀ a.val :=
    (copy_of_not_mem H K D e i₀ a.val a.property).symm
  rw [ha] at hax hay ⊢
  simp only [color_copy]
  exact hc a.val b d ((copy_rel H K D e i₀ _ _).mp hax)
    ((copy_rel H K D e i₀ _ _).mp hay) ((copy_rel H K D e i₀ _ _).mp hxy)

/-- The chosen coloring is preserved literally, not merely up to recoloring. -/
theorem color_valid (hK : K.CliqueFree 3)
    (hs : ∀ a b, K.Adj a b → side a ≠ side b) (hc : Valid H c) :
    Valid (graph H K D e) (color H K D e i₀ side c) := by
  classical
  intro x y z hxy hxz hyz he
  have hfirst := valid_at_distinguished H K D e i₀ side c hc
  have hpriv (w : Vertex D (B := B) (I := I)) :
      (∃ a : Outside D, w = Sum.inr (i₀,a)) ∨
        ∀ (i : I) (a : Outside D), w = Sum.inr (i,a) → i ≠ i₀ := by
    classical
    by_cases h : ∃ a : Outside D, w = Sum.inr (i₀,a)
    · exact Or.inl h
    · refine Or.inr fun i a hw hi => h ⟨a,?_⟩
      simpa only [hi] using hw
  rcases hpriv x with ⟨a,rfl⟩ | hx
  · exact hfirst a y z hxy hxz hyz he
  rcases hpriv y with ⟨a,rfl⟩ | hy
  · apply hfirst a x z hxy.symm hyz hxz
    constructor
    · simpa only [Sym2.eq_swap] using he.2
    · simpa only [Sym2.eq_swap] using he.1
  rcases hpriv z with ⟨a,rfl⟩ | hz
  · apply hfirst a x y hxz.symm hyz.symm hxy
    constructor
    · simpa only [Sym2.eq_swap] using he.1.symm.trans he.2
    · simpa only [Sym2.eq_swap] using he.1.symm
  have hnew (i : I) (a : Outside D) (hi : i ≠ i₀)
      (v : Vertex D (B := B) (I := I)) :=
    color_other_private H K D e i₀ side c hi a v
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      cases z with
      | inl z => exact hK _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy,hxz,hyz⟩)
      | inr t =>
        have ht := hz t.1 t.2 rfl
        have he' := he.1.symm.trans he.2
        rw [Sym2.eq_swap (a := Sum.inl x), Sym2.eq_swap (a := Sum.inl y),
          hnew _ _ ht, hnew _ _ ht] at he'
        exact hs x y hxy (by change 2 * side _ = 2 * side _ at he'; omega)
    | inr t =>
      have ht := hy t.1 t.2 rfl
      cases z with
      | inl z =>
        have he' := he.2
        rw [Sym2.eq_swap (a := Sum.inl x),hnew _ _ ht,hnew _ _ ht] at he'
        exact hs x z hxz (by change 2 * side _ = 2 * side _ at he'; omega)
      | inr u =>
        have hu := hz u.1 u.2 rfl
        have he' := he.2
        rw [Sym2.eq_swap (a := Sum.inl x),hnew _ _ ht,hnew _ _ ht] at he'
        change 2 * side x = 2 * c s(t.2.val,u.2.val) + 1 at he'
        omega
  | inr t =>
    have ht := hx t.1 t.2 rfl
    cases y with
    | inl y =>
      cases z with
      | inl z =>
        have he' := he.1
        rw [hnew _ _ ht,hnew _ _ ht] at he'
        exact hs y z hyz (by change 2 * side _ = 2 * side _ at he'; omega)
      | inr u =>
        have he' := he.1
        rw [hnew _ _ ht,hnew _ _ ht] at he'
        change 2 * side y = 2 * c s(t.2.val,u.2.val) + 1 at he'
        omega
    | inr u =>
      have hu := hy u.1 u.2 rfl
      cases z with
      | inl z =>
        have he' := he.1
        rw [hnew _ _ ht,hnew _ _ ht] at he'
        change 2 * c s(t.2.val,u.2.val) + 1 = 2 * side z at he'
        omega
      | inr v =>
        rw [hnew _ _ ht,hnew _ _ ht,hnew _ _ hu] at he
        change 2 * c s(t.2.val,u.2.val) + 1 = 2 * c s(t.2.val,v.2.val) + 1 ∧
          2 * c s(t.2.val,u.2.val) + 1 = 2 * c s(u.2.val,v.2.val) + 1 at he
        exact hc _ _ _ hxy.2 hxz.2 hyz.2
          ⟨by omega,by omega⟩

theorem exists_extension (hK : K.CliqueFree 3)
    (hs : ∀ a b, K.Adj a b → side a ≠ side b) (hc : Valid H c) :
    ∃ d : Sym2 (Vertex D (B := B) (I := I)) → ℕ,
      Valid (graph H K D e) d ∧
      ∀ a b, d s(copy H K D e i₀ a,copy H K D e i₀ b) = c s(a,b) :=
  ⟨color H K D e i₀ side c,color_valid H K D e i₀ side c hK hs hc,
    color_copy H K D e i₀ side c⟩

#print axioms exists_extension
end Erdos595BipartiteAmalgamationExtension
