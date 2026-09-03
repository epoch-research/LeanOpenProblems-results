import Submission.CountableGenericUniversality
import Submission.ThirdBadTriangle

/-!
A single explicit countable base contains every other countable K4-free
base, and its mutual ultrafilter towers inherit this universality.
Its unsupported third-stage part receives homomorphisms from every
countable K4-free graph. Countability is essential to the claim here;
no non-coverability conclusion is asserted.
-/

open SimpleGraph Set Filter
open Erdos595Work Erdos595CountableExtension Erdos595CountableGenericUniversality
namespace Erdos595GenericUltrafilterUniversality

lemma fubini_map_iff {A B : Type*} {H : SimpleGraph A} {K : SimpleGraph B}
    (f : H ↪g K) (p q : Ultrafilter A) :
    fubiniAdj K (Ultrafilter.map f p) (Ultrafilter.map f q) ↔ fubiniAdj H p q := by
  change {a | {b | K.Adj (f a) (f b)} ∈ q} ∈ p ↔ _
  simp only [f.map_rel_iff]
  rfl

def ultrafilterEmbedding {A B : Type*} {H : SimpleGraph A} {K : SimpleGraph B}
    (hH : H.CliqueFree 4) (hK : K.CliqueFree 4) (f : H ↪g K) :
    ultrafilterGraph H hH ↪g ultrafilterGraph K hK where
  toFun := Ultrafilter.map f
  inj' := by
    intro p q he
    apply Ultrafilter.coe_injective
    exact Filter.map_injective f.injective (congrArg Ultrafilter.toFilter he)
  map_rel_iff' := by
    intro p q
    change (fubiniAdj K (Ultrafilter.map f p) (Ultrafilter.map f q) ∧
      fubiniAdj K (Ultrafilter.map f q) (Ultrafilter.map f p)) ↔ _
    rw [fubini_map_iff,fubini_map_iff]
    rfl

def Carrier (A : Type*) : ℕ → Type _
  | 0 => A
  | n+1 => Ultrafilter (Carrier A n)

def tower {A : Type*} (H : SimpleGraph A) (hH : H.CliqueFree 4) :
    (n : ℕ) → {K : SimpleGraph (Carrier A n) // K.CliqueFree 4}
  | 0 => ⟨H,hH⟩
  | n+1 => ⟨ultrafilterGraph (tower H hH n).val (tower H hH n).property,
    ultrafilterGraph_cliqueFree _ _⟩

def towerEmbedding {A B : Type*} {H : SimpleGraph A} {K : SimpleGraph B}
    (hH : H.CliqueFree 4) (hK : K.CliqueFree 4) (f : H ↪g K) :
    (n : ℕ) → (tower H hH n).val ↪g (tower K hK n).val
  | 0 => f
  | n+1 => ultrafilterEmbedding (tower H hH n).property (tower K hK n).property
    (towerEmbedding hH hK f n)

/-- Any finite mutual tower over a countable base embeds into the tower
at the same stage over the one fixed explicit base. -/
theorem tower_universal_countable {A : Type*} [Countable A]
    (H : SimpleGraph A) (hH : H.CliqueFree 4) (n : ℕ) :
    Nonempty ((tower H hH n).val ↪g (tower G G_cliqueFree n).val) := by
  obtain ⟨f⟩ := universal_countable H hH
  exact ⟨towerEmbedding hH G_cliqueFree f n⟩

def support {A : Type*} (S : Set A) : (n : ℕ) → Set (Carrier A n)
  | 0 => S
  | n+1 => {p : Ultrafilter (Carrier A n) | support S n ∈ p}

lemma support_map_iff {A B : Type*} {H : SimpleGraph A} {K : SimpleGraph B}
    (hH : H.CliqueFree 4) (hK : K.CliqueFree 4) (f : H ↪g K)
    (S : Set B) (n : ℕ) (p : Carrier A n) :
    towerEmbedding hH hK f n p ∈ support S n ↔ p ∈ support (f ⁻¹' S) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change support S n ∈ Ultrafilter.map (towerEmbedding hH hK f n) p ↔ _
    rw [Ultrafilter.mem_map]
    have he : (towerEmbedding hH hK f n) ⁻¹' support S n = support (f ⁻¹' S) n := by
      ext q
      exact ih q
    rw [he]
    rfl

lemma preimage_triangleFree {A B : Type*} {H : SimpleGraph A} {K : SimpleGraph B}
    (f : H ↪g K) (S : Set B) (hS : (K.induce S).CliqueFree 3) :
    (H.induce (f ⁻¹' S)).CliqueFree 3 := by
  let g : H.induce (f ⁻¹' S) ↪g K.induce S :=
    { toFun := fun x => ⟨f x.val,x.property⟩
      inj' := fun x y h => Subtype.ext (f.injective (congrArg Subtype.val h))
      map_rel_iff' := by intro x y; exact f.map_rel_iff }
  exact hS.comap g

def Bad {A : Type*} (H : SimpleGraph A) (n : ℕ) : Set (Carrier A n) :=
  {p | ∀ S, (H.induce S).CliqueFree 3 → p ∉ support S n}

/-- Unsupported vertices remain unsupported under induced embeddings of bases. -/
lemma bad_map {A B : Type*} {H : SimpleGraph A} {K : SimpleGraph B}
    (hH : H.CliqueFree 4) (hK : K.CliqueFree 4) (f : H ↪g K)
    (n : ℕ) {p : Carrier A n} (hp : p ∈ Bad H n) :
    towerEmbedding hH hK f n p ∈ Bad K n := by
  intro S hS hm
  exact hp (f ⁻¹' S) (preimage_triangleFree f S hS)
    ((support_map_iff hH hK f S n p).mp hm)

/-- Every countable K4-free graph maps into the unsupported third-stage
part of the tower over the SAME countable explicit base. -/
theorem third_bad_universal_countable {A : Type*} [Countable A]
    (B : SimpleGraph A) (hB : B.CliqueFree 4) :
    Nonempty (B →g (tower G G_cliqueFree 3).val.induce (Bad G 3)) := by
  let H := Erdos595ThirdBadTriangle.H B
  have hH := Erdos595ThirdBadTriangle.H_cliqueFree B hB
  obtain ⟨f⟩ := universal_countable H hH
  let e := towerEmbedding hH G_cliqueFree f 3
  have hb : ∀ v : A, Erdos595ThirdBadTriangle.X v ∈ Bad H 3 := by
    intro v S hS hm
    exact Erdos595ThirdBadTriangle.no_original_support B v S hS hm
  refine ⟨{
    toFun := fun v => ⟨e (Erdos595ThirdBadTriangle.X v),bad_map hH G_cliqueFree f 3 (hb v)⟩
    map_rel' := ?_ }⟩
  intro v w hvw
  exact e.map_rel_iff.mpr (Erdos595ThirdBadTriangle.third_cross B hB hvw)

#print axioms ultrafilterEmbedding
#print axioms tower_universal_countable
#print axioms bad_map
#print axioms third_bad_universal_countable
end Erdos595GenericUltrafilterUniversality
