import Submission.LocallyFiniteFolkmanTarget
import Submission.FiniteExceptionUltrafilterTarget

/-!
The simultaneous absence of a finite triangle-edge palette and of a countable
K4-free homomorphism target does not force non-coverability at ANY finite
mutual-ultrafilter stage. The example is initially countably vertex-colorable.
This blocks a proposed compression implication; it does not settle Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set Filter
namespace Erdos595FiniteTowerCompression
open Erdos595Work Erdos595GenericUltrafilterUniversality
open Erdos595FiniteExceptionUltrafilterTarget

variable {A V : Type*}

/-- A triangle-free component and a complementary component mapping into H. -/
structure Split (G : SimpleGraph V) (H : SimpleGraph A) where
  part : Set V
  closed : ∀ {a b}, G.Adj a b → (a ∈ part ↔ b ∈ part)
  triangleFree : (G.induce part).CliqueFree 3
  code : V → A
  map_adj : ∀ {a b}, a ∉ part → b ∉ part → G.Adj a b → H.Adj (code a) (code b)

namespace Split
variable {G : SimpleGraph V} {H : SimpleGraph A} (s : Split G H)

def nextPart : Set (Ultrafilter V) := {p | s.part ∈ p}

lemma next_closed (hG : G.CliqueFree 4) {p q : Ultrafilter V}
    (hpq : (ultrafilterGraph G hG).Adj p q) :
    p ∈ s.nextPart ↔ q ∈ s.nextPart := by
  have hf (p q : Ultrafilter V) (hpq : fubiniAdj G p q) (hp : s.part ∈ p) :
      s.part ∈ q := by
    obtain ⟨a,ha,hN⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem hp hpq)
    exact Filter.mem_of_superset hN (fun b hab => (s.closed hab).mp ha)
  exact ⟨hf p q hpq.1,hf q p hpq.2⟩

lemma map_fubini {p q : Ultrafilter V} (hp : p ∉ s.nextPart) (hq : q ∉ s.nextPart)
    (hpq : fubiniAdj G p q) : fubiniAdj H (p.map s.code) (q.map s.code) := by
  have hp' : s.partᶜ ∈ p := Ultrafilter.compl_mem_iff_notMem.mpr hp
  have hq' : s.partᶜ ∈ q := Ultrafilter.compl_mem_iff_notMem.mpr hq
  change {a | {b | H.Adj (s.code a) (s.code b)} ∈ q} ∈ p
  apply Filter.mem_of_superset (Filter.inter_mem hp' hpq)
  intro a ha
  exact Filter.mem_of_superset (Filter.inter_mem hq' ha.2)
    (fun b hb => s.map_adj ha.1 hb.1 hb.2)

noncomputable def next [H.LocallyFinite] (d : A) (hG : G.CliqueFree 4) :
    Split (ultrafilterGraph G hG) H where
  part := s.nextPart
  closed := s.next_closed hG
  triangleFree := ultrafilterGraph_support_cliqueFree G hG s.part s.triangleFree
  code p := collapse d (p.map s.code)
  map_adj := by
    intro p q hp hq hpq
    exact collapse_adj H ∅ (Set.finite_empty) (fun a _ => Set.toFinite _)
      d (fun _ h => h.elim) _ _ (s.map_fubini hp hq hpq.1)
      (s.map_fubini hq hp hpq.2)

noncomputable def iterate [H.LocallyFinite] (d : A) (hG : G.CliqueFree 4) :
    (n : ℕ) → Split (tower G hG n).val H
  | 0 => s
  | n+1 => (iterate d hG n).next d (tower G hG n).property

include s in
lemma cover [Countable A] : IsCountableUnionOfTriangleFree G := by
  classical
  let f : V → Option A := fun a => if a ∈ s.part then none else some (s.code a)
  have hf : ∀ k, (G.induce {a | f a = k}).CliqueFree 3 := by
    intro k t ht
    obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp ht
    cases k with
    | none =>
      have hm {x : V} (h : f x = none) : x ∈ s.part := by
        by_contra hn
        simp [f,hn] at h
      exact s.triangleFree _ (SimpleGraph.is3Clique_triple_iff.mpr
        (show (G.induce s.part).Adj ⟨a.val,hm a.property⟩ ⟨b.val,hm b.property⟩ ∧
          (G.induce s.part).Adj ⟨a.val,hm a.property⟩ ⟨c.val,hm c.property⟩ ∧
          (G.induce s.part).Adj ⟨b.val,hm b.property⟩ ⟨c.val,hm c.property⟩ from
          ⟨hab,hac,hbc⟩))
    | some k =>
      have hm {x : V} (h : f x = some k) : x ∉ s.part ∧ s.code x = k := by
        by_cases hx : x ∈ s.part
        · simp [f,hx] at h
        · exact ⟨hx,Option.some.inj (by simpa [f,hx] using h)⟩
      have ha := hm a.property
      have hb := hm b.property
      exact (s.map_adj ha.1 hb.1 hab).ne (ha.2.trans hb.2.symm)
  obtain ⟨enc,henc⟩ := exists_injective_nat (Option A)
  let code : Option A → ℕ → Fin 2 := fun a n => if enc a = n then 1 else 0
  have hc : Function.Injective code := by
    intro a b h
    apply henc
    have hh := congrFun h (enc a)
    by_contra he
    simp [code,Ne.symm he] at hh
  apply countable_union_of_triangle_free_fibers G (code ∘ f)
  intro a b c hab hac hbc hm
  have he₁ : f b = f a := (hc hm.1).symm
  have he₂ : f c = f a := (hc hm.2).symm
  exact hf (f a) _ (SimpleGraph.is3Clique_triple_iff.mpr
    (show (G.induce {x | f x = f a}).Adj ⟨a,rfl⟩ ⟨b,he₁⟩ ∧
      (G.induce {x | f x = f a}).Adj ⟨a,rfl⟩ ⟨c,he₂⟩ ∧
      (G.induce {x | f x = f a}).Adj ⟨b,he₁⟩ ⟨c,he₂⟩ from
      ⟨hab,hac,hbc⟩))

include s in
lemma every_tower_cover [Countable A] [H.LocallyFinite] (d : A)
    (hG : G.CliqueFree 4) (n : ℕ) : IsCountableUnionOfTriangleFree (tower G hG n).val :=
  (s.iterate d hG n).cover
end Split

variable {B : Type*}

def sumGraph (H : SimpleGraph A) (K : SimpleGraph B) : SimpleGraph (A ⊕ B) where
  Adj
    | .inl a,.inl b => H.Adj a b
    | .inr a,.inr b => K.Adj a b
    | _,_ => False
  symm := by intro a b h; cases a <;> cases b <;> first | exact h.symm | exact h
  loopless := by intro a h; cases a <;> exact SimpleGraph.irrefl _ h

def leftHom (H : SimpleGraph A) (K : SimpleGraph B) : H →g sumGraph H K :=
  ⟨Sum.inl,fun h => h⟩
def rightHom (H : SimpleGraph A) (K : SimpleGraph B) : K →g sumGraph H K :=
  ⟨Sum.inr,fun h => h⟩

lemma sum_cliqueFree (H : SimpleGraph A) (K : SimpleGraph B)
    (hH : H.CliqueFree 4) (hK : K.CliqueFree 4) : (sumGraph H K).CliqueFree 4 := by
  have hn : ∀ a b c d, (sumGraph H K).Adj a b → (sumGraph H K).Adj a c →
      (sumGraph H K).Adj b c → (sumGraph H K).Adj a d →
      (sumGraph H K).Adj b d → (sumGraph H K).Adj c d → False := by
    intro a b c d hab hac hbc had hbd hcd
    cases a <;> cases b <;> cases c <;> cases d <;>
      first | exact hab | exact hac | exact had |
        exact no_adj_common_neighbors hH hab hac hbc had hbd hcd |
        exact no_adj_common_neighbors hK hab hac hbc had hbd hcd
  classical
  by_contra hh
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hh
  exact hn (e 0) (e 1) (e 2) (e 3) (e.map_rel_iff.mpr (by decide))
    (e.map_rel_iff.mpr (by decide)) (e.map_rel_iff.mpr (by decide))
    (e.map_rel_iff.mpr (by decide)) (e.map_rel_iff.mpr (by decide))
    (e.map_rel_iff.mpr (by decide))

def sumSplit (H : SimpleGraph A) (K : SimpleGraph B) (hK : K.CliqueFree 3) (d : A) :
    Split (sumGraph H K) H where
  part := {x | x.isRight}
  closed := by
    intro a b h
    cases a <;> cases b <;> first | exact Iff.rfl | exact h.elim
  triangleFree := by
    classical
    intro t ht
    obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp ht
    rcases a with ⟨a,ha⟩; rcases b with ⟨b,hb⟩; rcases c with ⟨c,hc⟩
    cases a with
    | inl a => exact (Bool.false_ne_true ha).elim
    | inr a =>
      cases b with
      | inl b => exact hab
      | inr b =>
        cases c with
        | inl c => exact hac
        | inr c => exact hK _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)
  code := Sum.elim id (fun _ => d)
  map_adj := by
    intro a b ha hb hab
    cases a <;> cases b
    · exact hab
    · exact hab.elim
    · exact hab.elim
    · exact (ha rfl).elim

/-- Both suggested obstructions can coexist with coverability at EVERY finite
stage, even when the original graph has a countable proper vertex coloring. -/
theorem simultaneous_obstructions :
    ∃ (V : Type) (G : SimpleGraph V) (hG : G.CliqueFree 4),
      Nonempty (G.Coloring ℕ) ∧
      (∀ (C : Type) [Finite C], ¬Erdos595FinitePalette.HasColoring G C) ∧
      (∀ (W : Type) [Countable W] (K : SimpleGraph W), K.CliqueFree 4 → IsEmpty (G →g K)) ∧
      (∀ n, IsCountableUnionOfTriangleFree (tower G hG n).val) := by
  classical
  obtain ⟨B,K,hK,hcol,hbad⟩ := exists_countably_colorable_no_countable_cliqueFree_target
  let H := Erdos595LocallyFiniteFolkmanTarget.H
  have hH := Erdos595LocallyFiniteFolkmanTarget.cliqueFree
  let G := sumGraph H K
  have hG := sum_cliqueFree H K hH (hK.mono (by omega))
  have hd : Nonempty Erdos595LocallyFiniteFolkmanTarget.Carrier := by
    by_contra hh
    haveI : IsEmpty Erdos595LocallyFiniteFolkmanTarget.Carrier := not_nonempty_iff.mp hh
    have hc : Erdos595FinitePalette.HasColoring H Bool := by
      refine ⟨fun _ => false,?_⟩
      intro a
      exact isEmptyElim a
    exact Erdos595LocallyFiniteFolkmanTarget.no_finite_palette Bool hc
  let d := Classical.choice hd
  refine ⟨_,G,hG,?_,?_,?_,?_⟩
  · obtain ⟨c⟩ := hcol
    obtain ⟨enc,henc⟩ := exists_injective_nat Erdos595LocallyFiniteFolkmanTarget.Carrier
    let f : Erdos595LocallyFiniteFolkmanTarget.Carrier ⊕ B → ℕ := Sum.elim enc c
    exact ⟨SimpleGraph.Coloring.mk f (by
      intro a b hab he
      cases a <;> cases b
      · exact (show H.Adj _ _ from hab).ne (henc he)
      · exact hab.elim
      · exact hab.elim
      · exact c.valid hab he)⟩
  · intro C hC hc
    exact Erdos595LocallyFiniteFolkmanTarget.no_finite_palette C
      (hc.comap (leftHom H K))
  · intro W hW T hT
    exact ⟨fun f => (hbad W hW T hT).false (f.comp (rightHom H K))⟩
  · intro n
    exact (sumSplit H K hK d).every_tower_cover d hG n

#print axioms Split.every_tower_cover
#print axioms simultaneous_obstructions
end Erdos595FiniteTowerCompression
