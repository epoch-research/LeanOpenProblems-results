import Submission.InfiniteBipartiteRamsey
import Submission.FiniteBipartiteInfinitePalette

/-!
Infinite point-interval incidence graphs have induced, side-preserving bipartite
Ramsey hosts for arbitrary palettes. In particular this supplies a Ramsey host
for an entire one-way infinite path. Only two ordered coordinates are used.
This does not give hosts for arbitrary infinite bipartite graphs or coherent
choices at infinitely many partite stages, and does not settle Erdos 595.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595IntervalBipartite
open Erdos595InfiniteBipartite
universe u

variable {L R A B D : Type u} [LinearOrder A] [LinearOrder B] [LinearOrder D]
    (lo hi : L → A) (point : R → A)

abbrev target : SimpleGraph (L ⊕ R) :=
  Erdos595FiniteBipartiteInfinitePalette.graph (fun l r => lo l < point r ∧ point r < hi l)

def embedMap (f : A ↪o B) (g : A ↪o D) : L ⊕ R → (B × D) ⊕ (B × D)
  | .inl l => .inl (f (lo l),g (hi l))
  | .inr r => .inr (f (point r),g (point r))

lemma embedMap_injective (hl : Function.Injective (fun l => (lo l,hi l)))
    (hr : Function.Injective point) (f : A ↪o B) (g : A ↪o D) :
    Function.Injective (embedMap lo hi point f g) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have he := Sum.inl_injective h
      have h₀ := f.injective (congrArg Prod.fst he)
      have h₁ := g.injective (congrArg Prod.snd he)
      exact congrArg Sum.inl (hl (Prod.ext h₀ h₁))
    | inr y => cases h
  | inr x =>
    cases y with
    | inl y => cases h
    | inr y =>
      exact congrArg Sum.inr (hr (f.injective (congrArg Prod.fst (Sum.inr_injective h))))

lemma embedMap_adj (f : A ↪o B) (g : A ↪o D) (x y : L ⊕ R) :
    (intervalGraph B D).Adj (embedMap lo hi point f g x) (embedMap lo hi point f g y) ↔
      (target lo hi point).Adj x y := by
  cases x <;> cases y <;>
    simp only [embedMap,intervalGraph,target,Erdos595FiniteBipartiteInfinitePalette.graph,
      OrderEmbedding.lt_iff_lt]

def embedding (hl : Function.Injective (fun l => (lo l,hi l)))
    (hr : Function.Injective point) (f : A ↪o B) (g : A ↪o D) :
    target lo hi point ↪g intervalGraph B D where
  toFun := embedMap lo hi point f g
  inj' := embedMap_injective lo hi point hl hr f g
  map_rel_iff' := embedMap_adj lo hi point f g _ _

/-- Entire infinite targets are allowed. Well-foundedness is required of the
coordinate order, not any preassigned ordering of the target vertices. -/
theorem ramsey [WellFoundedLT A] (hl : Function.Injective (fun l => (lo l,hi l)))
    (hr : Function.Injective point) (C : Type u) :
    ∃ (V : Type u) (K : SimpleGraph (V ⊕ V)), K.CliqueFree 3 ∧
      ∀ c : Sym2 (V ⊕ V) → C, ∃ (e : target lo hi point ↪g K) (k : C),
        (∀ l, ∃ v, e (.inl l) = .inl v) ∧
        (∀ r, ∃ v, e (.inr r) = .inr v) ∧
        ∀ x y, (target lo hi point).Adj x y → c s(e x,e y) = k := by
  obtain ⟨B,D,oB,oD,h⟩ := pair_box A C
  letI : LinearOrder B := oB
  letI : LinearOrder D := oD
  refine ⟨B × D,intervalGraph B D,intervalGraph_triangleFree B D,?_⟩
  intro c
  obtain ⟨f,g,k,hfg⟩ := h (fun a b s t => c s(Sum.inl (a,t),Sum.inr (b,s)))
  let e := embedding lo hi point hl hr f g
  have he (l : L) (r : R) (hlr : lo l < point r ∧ point r < hi l) :
      c s(e (.inl l),e (.inr r)) = k :=
    hfg (lo l) (point r) (point r) (hi l) hlr.1 hlr.2
  refine ⟨e,k,fun _ => ⟨_,rfl⟩,fun _ => ⟨_,rfl⟩,?_⟩
  intro x y hxy
  cases x with
  | inl l =>
    cases y with
    | inl l' => exact hxy.elim
    | inr r => exact he l r hxy
  | inr r =>
    cases y with
    | inl l => simpa only [Sym2.eq_swap] using he l r hxy
    | inr r' => exact hxy.elim

/-- Free amalgamation homogenizes an entire designated point-interval target
while preserving K4-freeness. It supplies one step, not an infinite iteration. -/
theorem step [WellFoundedLT A] (hl : Function.Injective (fun l => (lo l,hi l)))
    (hr : Function.Injective point) {V C : Type u}
    (H : SimpleGraph V) (hH : H.CliqueFree 4) (S : Set V)
    (e : target lo hi point ≃g H.induce S) :
    ∃ (U : Type u) (G : SimpleGraph U), G.CliqueFree 4 ∧
      ∀ c : Sym2 U → C, ∃ (f : H ↪g G) (k : C),
        ∀ x y : S, H.Adj x.val y.val → c s(f x.val,f y.val) = k := by
  obtain ⟨B,K,hK,hRam⟩ := ramsey lo hi point hl hr C
  apply step_of_ramsey (target lo hi point) K (hK.mono (by decide)) ?_ H hH S e
  intro c
  obtain ⟨f,k,_,_,hf⟩ := hRam c
  exact ⟨f,k,hf⟩

/-- The one-way infinite path, in the order R0--L0--R1--L1--R2--L2--... . -/
def ray : SimpleGraph (ℕ ⊕ ℕ) :=
  Erdos595FiniteBipartiteInfinitePalette.graph (fun i j => j = i ∨ j = i + 1)

private lemma interval_ray_eq :
    target (fun i : ℕ => 4*i) (fun i => 4*i+7) (fun j => 4*j+2) = ray := by
  ext x y
  cases x <;> cases y <;>
    simp only [target,ray,Erdos595FiniteBipartiteInfinitePalette.graph]
  all_goals omega

/-- This forces a monochromatic induced copy of the WHOLE infinite ray, not
merely paths of every finite length. The palette may be infinite. -/
theorem ray_ramsey (C : Type) :
    ∃ (V : Type) (K : SimpleGraph (V ⊕ V)), K.CliqueFree 3 ∧
      ∀ c : Sym2 (V ⊕ V) → C, ∃ (e : ray ↪g K) (k : C),
        (∀ i, ∃ v, e (.inl i) = .inl v) ∧
        (∀ i, ∃ v, e (.inr i) = .inr v) ∧
        ∀ x y, ray.Adj x y → c s(e x,e y) = k := by
  have hl : Function.Injective (fun i : ℕ => (4*i,4*i+7)) := by
    intro i j h
    have he : 4*i = 4*j := congrArg Prod.fst h
    omega
  have hr : Function.Injective (fun j : ℕ => 4*j+2) := by
    intro i j h
    change 4*i+2 = 4*j+2 at h
    omega
  obtain ⟨V,K,hK,hRam⟩ :=
    ramsey (fun i : ℕ => 4*i) (fun i => 4*i+7) (fun j => 4*j+2) hl hr C
  refine ⟨V,K,hK,?_⟩
  intro c
  obtain ⟨e,k,heL,heR,he⟩ := hRam c
  let e' : ray ↪g K :=
    { toFun := e
      inj' := e.injective
      map_rel_iff' := by
        intro x y
        exact e.map_rel_iff.trans (by rw [interval_ray_eq]) }
  refine ⟨e',k,heL,heR,fun x y hxy => he x y ?_⟩
  simpa only [interval_ray_eq] using hxy

/-- A designated induced infinite ray can be homogenized in a K4-free extension. -/
theorem ray_step {V C : Type} (H : SimpleGraph V) (hH : H.CliqueFree 4)
    (S : Set V) (e : ray ≃g H.induce S) :
    ∃ (U : Type) (G : SimpleGraph U), G.CliqueFree 4 ∧
      ∀ c : Sym2 U → C, ∃ (f : H ↪g G) (k : C),
        ∀ x y : S, H.Adj x.val y.val → c s(f x.val,f y.val) = k := by
  obtain ⟨B,K,hK,hRam⟩ := ray_ramsey C
  apply step_of_ramsey ray K (hK.mono (by decide)) ?_ H hH S e
  intro c
  obtain ⟨f,k,_,_,hf⟩ := hRam c
  exact ⟨f,k,hf⟩

#print axioms ramsey
#print axioms step
#print axioms ray_ramsey
#print axioms ray_step
end Erdos595IntervalBipartite
