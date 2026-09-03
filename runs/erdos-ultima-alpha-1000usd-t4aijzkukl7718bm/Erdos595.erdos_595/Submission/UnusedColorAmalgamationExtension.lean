import Submission.BipartiteAmalgamationExtension

/-!
Literal color extension over a triangle-free base when a color is absent
from the attaching subgraph. In particular, this applies to every finite
attachment, without a vertex-chromatic bound on the base. This does not
settle Erdős 595.
-/

set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595UnusedColorAmalgamationExtension
open Erdos595FiniteFolkmanAmalgamation Erdos595FiniteAdapted

variable {A B I : Type*} (H : SimpleGraph A) (K : SimpleGraph B)
    (D : Set A) (e : I → H.induce D ↪g K) (i₀ : I)
    (c : Sym2 A → ℕ) (k : ℕ)

/-- The missing color is reserved for cross edges. -/
def fallback : Sym2 (Vertex D (B := B) (I := I)) → ℕ :=
  Sym2.lift ⟨fun x y => match x,y with
    | .inl _, .inl _ => k + 1
    | .inl _, .inr _ => k
    | .inr _, .inl _ => k
    | .inr a, .inr b => c s(a.2.val,b.2.val) + k + 1,
    by intro x y; cases x <;> cases y <;> simp only [Sym2.eq_swap]⟩

/-- Override the fallback on all unordered pairs of the distinguished copy. -/
noncomputable def color : Sym2 (Vertex D (B := B) (I := I)) → ℕ :=
  Function.extend (Sym2.map (copy H K D e i₀)) c (fallback D c k)

lemma color_copy (a b : A) :
    color H K D e i₀ c k s(copy H K D e i₀ a,copy H K D e i₀ b) = c s(a,b) := by
  exact (Sym2.map.injective (copy_injective H K D e i₀)).extend_apply c
    (fallback D c k) s(a,b)

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
    color H K D e i₀ c k s(Sum.inr (i,a),z) =
      fallback D c k s(Sum.inr (i,a),z) := by
  apply Function.extend_apply'
  rintro ⟨s,hs⟩
  have hm : Sum.inr (i,a) ∈ s.map (copy H K D e i₀) := by rw [hs]; simp
  obtain ⟨b,_,hb⟩ := Sym2.mem_map.mp hm
  exact private_not_in_copy H K D e i₀ hi a ⟨b,hb⟩

lemma copy_base_mem {a : A} {b : B} (h : copy H K D e i₀ a = Sum.inl b) : a ∈ D := by
  classical
  by_contra ha
  rw [copy_of_not_mem _ _ _ _ _ _ ha] at h
  simp only [Sum.inr_ne_inl] at h

lemma base_color_ne (hu : ∀ a ∈ D, ∀ b ∈ D, H.Adj a b → c s(a,b) ≠ k)
    {x y : B} (hxy : K.Adj x y) : color H K D e i₀ c k s(Sum.inl x,Sum.inl y) ≠ k := by
  classical
  by_cases him : ∃ q : Sym2 A, q.map (copy H K D e i₀) = s(Sum.inl x,Sum.inl y)
  · obtain ⟨q,hq⟩ := him
    have hx : Sum.inl x ∈ q.map (copy H K D e i₀) := by rw [hq]; simp
    have hy : Sum.inl y ∈ q.map (copy H K D e i₀) := by rw [hq]; simp
    obtain ⟨a,_,ha⟩ := Sym2.mem_map.mp hx
    obtain ⟨b,_,hb⟩ := Sym2.mem_map.mp hy
    rw [← ha,← hb,color_copy]
    apply hu a (copy_base_mem H K D e i₀ ha) b (copy_base_mem H K D e i₀ hb)
    apply (copy_rel H K D e i₀ a b).mp
    rw [ha,hb]
    exact hxy
  · rw [show color H K D e i₀ c k s(Sum.inl x,Sum.inl y) =
        fallback D c k s(Sum.inl x,Sum.inl y) from Function.extend_apply' _ _ _ him]
    change k + 1 ≠ k
    omega

lemma valid_at_distinguished (hc : Valid H c) (a : Outside D)
    (x y : Vertex D (B := B) (I := I))
    (hax : (graph H K D e).Adj (Sum.inr (i₀,a)) x)
    (hay : (graph H K D e).Adj (Sum.inr (i₀,a)) y)
    (hxy : (graph H K D e).Adj x y) :
    ¬(color H K D e i₀ c k s(Sum.inr (i₀,a),x) =
        color H K D e i₀ c k s(Sum.inr (i₀,a),y) ∧
      color H K D e i₀ c k s(Sum.inr (i₀,a),x) =
        color H K D e i₀ c k s(x,y)) := by
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
    (hc : Valid H c)
    (hu : ∀ a ∈ D, ∀ b ∈ D, H.Adj a b → c s(a,b) ≠ k) :
    Valid (graph H K D e) (color H K D e i₀ c k) := by
  classical
  intro x y z hxy hxz hyz he
  have hfirst := valid_at_distinguished H K D e i₀ c k hc
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
  have hnew : ∀ {i : I}, i ≠ i₀ → ∀ (a : Outside D) (v : Vertex D (B := B) (I := I)),
      color H K D e i₀ c k s(Sum.inr (i,a),v) = fallback D c k s(Sum.inr (i,a),v) :=
    fun {_} hi => color_other_private H K D e i₀ c k hi
  have hbase : ∀ {a b : B}, K.Adj a b → color H K D e i₀ c k s(Sum.inl a,Sum.inl b) ≠ k :=
    fun {_ _} h => base_color_ne H K D e i₀ c k hu h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      cases z with
      | inl z => exact hK _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy,hxz,hyz⟩)
      | inr t =>
        apply hbase hxy
        exact he.1.trans (by rw [Sym2.eq_swap, hnew (hz _ _ rfl)]; rfl)
    | inr t =>
      cases z with
      | inl z =>
        apply hbase hxz
        exact he.1.symm.trans (by rw [Sym2.eq_swap, hnew (hy _ _ rfl)]; rfl)
      | inr u =>
        have he' := he.2
        rw [Sym2.eq_swap (a := Sum.inl x),hnew (hy _ _ rfl),hnew (hy _ _ rfl)] at he'
        change k = c s(t.2.val,u.2.val) + k + 1 at he'
        omega
  | inr t =>
    cases y with
    | inl y =>
      cases z with
      | inl z =>
        apply hbase hyz
        exact he.2.symm.trans (by rw [hnew (hx _ _ rfl)]; rfl)
      | inr u =>
        have he' := he.1
        rw [hnew (hx _ _ rfl),hnew (hx _ _ rfl)] at he'
        change k = c s(t.2.val,u.2.val) + k + 1 at he'
        omega
    | inr u =>
      cases z with
      | inl z =>
        have he' := he.1
        rw [hnew (hx _ _ rfl),hnew (hx _ _ rfl)] at he'
        change c s(t.2.val,u.2.val) + k + 1 = k at he'
        omega
      | inr v =>
        rw [hnew (hx _ _ rfl),hnew (hx _ _ rfl),hnew (hy _ _ rfl)] at he
        change c s(t.2.val,u.2.val) + k + 1 = c s(t.2.val,v.2.val) + k + 1 ∧
          c s(t.2.val,u.2.val) + k + 1 = c s(u.2.val,v.2.val) + k + 1 at he
        exact hc _ _ _ hxy.2 hxz.2 hyz.2 ⟨by omega,by omega⟩

theorem exists_extension (hK : K.CliqueFree 3)
    (hc : Valid H c)
    (hu : ∀ a ∈ D, ∀ b ∈ D, H.Adj a b → c s(a,b) ≠ k) :
    ∃ d : Sym2 (Vertex D (B := B) (I := I)) → ℕ,
      Valid (graph H K D e) d ∧
      ∀ a b, d s(copy H K D e i₀ a,copy H K D e i₀ b) = c s(a,b) :=
  ⟨color H K D e i₀ c k,color_valid H K D e i₀ c k hK hc hu,
    color_copy H K D e i₀ c k⟩

theorem exists_extension_finite (hK : K.CliqueFree 3) (hc : Valid H c) (hD : D.Finite) :
    ∃ d : Sym2 (Vertex D (B := B) (I := I)) → ℕ,
      Valid (graph H K D e) d ∧
      ∀ a b, d s(copy H K D e i₀ a,copy H K D e i₀ b) = c s(a,b) := by
  classical
  have hf : ((fun p : A × A => c s(p.1,p.2)) '' (D ×ˢ D)).Finite :=
    (hD.prod hD).image _
  obtain ⟨k,hk⟩ := hf.exists_notMem
  apply exists_extension H K D e i₀ c k hK hc
  intro a ha b hb _ he
  exact hk ⟨(a,b),⟨ha,hb⟩,he⟩

#print axioms exists_extension
#print axioms exists_extension_finite
end Erdos595UnusedColorAmalgamationExtension
