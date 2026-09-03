import Submission.IndependentPairAdjoint
import Submission.PairAnchorPattern
import Submission.NegativeInner

/-! A countable-cover theorem for the independent-pair right-adjoint family.
This is an auxiliary candidate exclusion, not a settlement of Erdős 595. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open Set SimpleGraph
namespace Erdos595IndependentPairCover
open Erdos595ArcAdjoint Erdos595IndependentPair Erdos595Work
variable {V : Type*} (B : SimpleGraph V)

abbrev RP := right (graph B)
abbrev RV := Biclique (graph B)

def side (p : RV B) (s : Bool) : Set (Vertex B) := if s then p.val.2 else p.val.1

def Present (p : RV B) (s k : Bool) : Prop := ∃ x ∈ side B p s, x.2 = k

def Full (p : RV B) : Prop := ∀ s k, Present B p s k

noncomputable def anchor (p : RV B) (hp : Full B p) (s k : Bool) : Vertex B :=
  (hp s k).choose

lemma anchor_mem (p : RV B) (hp : Full B p) (s k : Bool) :
    anchor B p hp s k ∈ side B p s := (hp s k).choose_spec.1

lemma anchor_bit (p : RV B) (hp : Full B p) (s k : Bool) :
    (anchor B p hp s k).2 = k := (hp s k).choose_spec.2

noncomputable def back (p q : RV B) (h : (RP B).Adj p q) : Vertex B := h.2.choose

lemma back_left (p q : RV B) (h : (RP B).Adj p q) : back B p q h ∈ p.val.1 :=
  h.2.choose_spec.2
lemma back_right (p q : RV B) (h : (RP B).Adj p q) : back B p q h ∈ q.val.2 :=
  h.2.choose_spec.1

lemma overlap {p q : Pair B} (h : (support B p ∩ support B q).Nonempty) :
    p.val.1 = q.val.1 ∨ p.val.1 = q.val.2 ∨
      p.val.2 = q.val.1 ∨ p.val.2 = q.val.2 := by
  obtain ⟨x,hx,hy⟩ := h
  simp only [Erdos595IndependentPair.support,Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with hy | hy <;> tauto

lemma overlap_of_bits {x y : Vertex B} (h : (graph B).Adj x y) (hb : x.2 ≠ y.2) :
    x.1.val.1 = y.1.val.1 ∨ x.1.val.1 = y.1.val.2 ∨
      x.1.val.2 = y.1.val.1 ∨ x.1.val.2 = y.1.val.2 :=
  overlap B (by simpa only [graph,if_neg hb] using h)

lemma near_of_bits {x y : Vertex B} (h : (graph B).Adj x y) (hb : x.2 = y.2) :
    Near B x.1 y.1 := by simpa only [graph,if_pos hb] using h

lemma near_columns {p q : Pair B} (h : Near B p q) :
    (B.Adj p.val.1 q.val.1 ∨ B.Adj p.val.2 q.val.1) ∧
    (B.Adj p.val.1 q.val.1 ∨ B.Adj p.val.1 q.val.2) ∧
    (B.Adj p.val.1 q.val.2 ∨ B.Adj p.val.2 q.val.2) := by
  obtain ⟨a,ha,hap⟩ := h.1
  obtain ⟨b,hb,hbq⟩ := h.2
  have h₁ := hap q.val.1 (by simp [Erdos595IndependentPair.support])
  have h₂ := hap q.val.2 (by simp [Erdos595IndependentPair.support])
  have h₃ := (hbq p.val.1 (by simp [Erdos595IndependentPair.support])).symm
  simp only [Erdos595IndependentPair.support,Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> tauto

/-- An all-one-bit triangle in P(B) gives a triangle in B. -/
lemma near_triangle (hB : B.CliqueFree 3) {p q r : Pair B}
    (hpq : Near B p q) (hpr : Near B p r) (hqr : Near B q r) : False := by
  classical
  obtain ⟨a,ha,haq⟩ := hpq.1
  obtain ⟨b,hb,hbr⟩ := hqr.1
  obtain ⟨c,hc,hcp⟩ := hpr.2
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr
    ⟨haq b hb,(hcp a ha).symm,hbr c hc⟩)

lemma same_bit_triangle (hB : B.CliqueFree 3) {p q r : Vertex B}
    (hpq : (graph B).Adj p q) (hpr : (graph B).Adj p r) (hqr : (graph B).Adj q r)
    (he : p.2 = q.2 ∧ p.2 = r.2) : False :=
  near_triangle B hB (near_of_bits B hpq he.1) (near_of_bits B hpr he.2)
    (near_of_bits B hqr (he.1.symm.trans he.2))

abbrev Diagram := (Fin 10 → Fin 10 → Prop) × (Fin 10 → Fin 10 → Prop)

def diagram (x : Fin 10 → V) : Diagram :=
  (fun i j => x i = x j,fun i j => B.Adj (x i) (x j))

noncomputable def edgeTuple (p q : RV B) (hp : Full B p) (hq : Full B q)
    (h : (RP B).Adj p q) : Fin 10 → V :=
  let k := !(back B p q h).2
  let a := (anchor B p hp false k).1.val
  let b := (anchor B p hp true k).1.val
  let c := (anchor B q hq false k).1.val
  let d := (anchor B q hq true k).1.val
  let w := (back B p q h).1.val
  ![a.1,a.2,b.1,b.2,c.1,c.2,d.1,d.2,w.1,w.2]

noncomputable def key (p q : RV B) (hp : Full B p) (hq : Full B q)
    (h : (RP B).Adj p q) : Bool × Diagram :=
  ((back B p q h).2,diagram B (edgeTuple B p q hp hq h))

lemma key_valid (hB : B.CliqueFree 3) (p q r : RV B)
    (hp : Full B p) (hq : Full B q) (hr : Full B r)
    (hpq : (RP B).Adj p q) (hpr : (RP B).Adj p r) (hqr : (RP B).Adj q r)
    (he₁ : key B p q hp hq hpq = key B p r hp hr hpr)
    (he₂ : key B p q hp hq hpq = key B q r hq hr hqr) : False := by
  let w₀ := back B p q hpq
  let w₁ := back B p r hpr
  let w₂ := back B q r hqr
  have hb₁ : w₀.2 = w₁.2 := congrArg Prod.fst he₁
  have hb₂ : w₀.2 = w₂.2 := congrArg Prod.fst he₂
  let k := !w₀.2
  let a₀ := anchor B p hp false k
  let b₀ := anchor B p hp true k
  let a₁ := anchor B q hq false k
  let b₁ := anchor B q hq true k
  let a₂ := anchor B r hr false k
  let b₂ := anchor B r hr true k
  let z : Fin 18 → V :=
    ![a₀.1.val.1,a₀.1.val.2,b₀.1.val.1,b₀.1.val.2,
      a₁.1.val.1,a₁.1.val.2,b₁.1.val.1,b₁.1.val.2,
      a₂.1.val.1,a₂.1.val.2,b₂.1.val.1,b₂.1.val.2,
      w₀.1.val.1,w₀.1.val.2,w₁.1.val.1,w₁.1.val.2,w₂.1.val.1,w₂.1.val.2]
  let ts : Fin 3 → Fin 10 → V :=
    ![edgeTuple B p q hp hq hpq,edgeTuple B p r hp hr hpr,edgeTuple B q r hq hr hqr]
  have hts : ∀ i j, z (Erdos595PairAnchorPattern.edgeCoords i j) = ts i j := by
    intro i j
    fin_cases i
    · fin_cases j
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · fin_cases j
      · change ((anchor B p hp false (!w₀.2)).1.val).1 =
          ((anchor B p hp false (!w₁.2)).1.val).1
        rw [← hb₁]
      · change ((anchor B p hp false (!w₀.2)).1.val).2 =
          ((anchor B p hp false (!w₁.2)).1.val).2
        rw [← hb₁]
      · change ((anchor B p hp true (!w₀.2)).1.val).1 =
          ((anchor B p hp true (!w₁.2)).1.val).1
        rw [← hb₁]
      · change ((anchor B p hp true (!w₀.2)).1.val).2 =
          ((anchor B p hp true (!w₁.2)).1.val).2
        rw [← hb₁]
      · change ((anchor B r hr false (!w₀.2)).1.val).1 =
          ((anchor B r hr false (!w₁.2)).1.val).1
        rw [← hb₁]
      · change ((anchor B r hr false (!w₀.2)).1.val).2 =
          ((anchor B r hr false (!w₁.2)).1.val).2
        rw [← hb₁]
      · change ((anchor B r hr true (!w₀.2)).1.val).1 =
          ((anchor B r hr true (!w₁.2)).1.val).1
        rw [← hb₁]
      · change ((anchor B r hr true (!w₀.2)).1.val).2 =
          ((anchor B r hr true (!w₁.2)).1.val).2
        rw [← hb₁]
      · rfl
      · rfl
    · fin_cases j
      · change ((anchor B q hq false (!w₀.2)).1.val).1 =
          ((anchor B q hq false (!w₂.2)).1.val).1
        rw [← hb₂]
      · change ((anchor B q hq false (!w₀.2)).1.val).2 =
          ((anchor B q hq false (!w₂.2)).1.val).2
        rw [← hb₂]
      · change ((anchor B q hq true (!w₀.2)).1.val).1 =
          ((anchor B q hq true (!w₂.2)).1.val).1
        rw [← hb₂]
      · change ((anchor B q hq true (!w₀.2)).1.val).2 =
          ((anchor B q hq true (!w₂.2)).1.val).2
        rw [← hb₂]
      · change ((anchor B r hr false (!w₀.2)).1.val).1 =
          ((anchor B r hr false (!w₂.2)).1.val).1
        rw [← hb₂]
      · change ((anchor B r hr false (!w₀.2)).1.val).2 =
          ((anchor B r hr false (!w₂.2)).1.val).2
        rw [← hb₂]
      · change ((anchor B r hr true (!w₀.2)).1.val).1 =
          ((anchor B r hr true (!w₂.2)).1.val).1
        rw [← hb₂]
      · change ((anchor B r hr true (!w₀.2)).1.val).2 =
          ((anchor B r hr true (!w₂.2)).1.val).2
        rw [← hb₂]
      · rfl
      · rfl
  have hD : ∀ i : Fin 3, diagram B (ts i) = diagram B (ts 0) := by
    intro i
    fin_cases i
    · rfl
    · exact (congrArg Prod.snd he₁).symm
    · exact (congrArg Prod.snd he₂).symm
  have hb (x : RV B) (hx : Full B x) (s : Bool) :
      (anchor B x hx s k).2 ≠ w₀.2 := by
    rw [anchor_bit]
    intro he
    have he' : (!w₀.2) = w₀.2 := he
    cases hw : w₀.2 <;> simp only [hw,Bool.not_false,Bool.not_true] at he' <;> cases he'
  have m₀ := overlap_of_bits B
    (p.property _ (back_left B p q hpq) _ (anchor_mem B p hp true k)).symm (hb p hp true)
  have m₁ := overlap_of_bits B
    (p.property _ (back_left B p r hpr) _ (anchor_mem B p hp true k)).symm
    (fun he => hb p hp true (he.trans hb₁.symm))
  have m₂ := overlap_of_bits B
    (q.property _ (anchor_mem B q hq false k) _ (back_right B p q hpq)) (hb q hq false)
  have m₃ := overlap_of_bits B
    (q.property _ (back_left B q r hqr) _ (anchor_mem B q hq true k)).symm
    (fun he => hb q hq true (he.trans hb₂.symm))
  have m₄ := overlap_of_bits B
    (r.property _ (anchor_mem B r hr false k) _ (back_right B p r hpr))
    (fun he => hb r hr false (he.trans hb₁.symm))
  have m₅ := overlap_of_bits B
    (r.property _ (anchor_mem B r hr false k) _ (back_right B q r hqr))
    (fun he => hb r hr false (he.trans hb₂.symm))
  have hn := near_columns B (near_of_bits B
    (q.property _ (back_left B q r hqr) _ (back_right B p q hpq)).symm hb₂)
  apply Erdos595PairAnchorPattern.no_pattern B z hB
  refine ⟨w₀.1.property,w₁.1.property,w₂.1.property,
    m₀,m₁,m₂,m₃,m₄,m₅,hn.1,hn.2.1,hn.2.2,?_,?_⟩
  · intro i j a b
    simp only [hts]
    exact Iff.of_eq (congrFun (congrFun (congrArg Prod.fst ((hD i).trans (hD j).symm)) a) b)
  · intro i j a b
    simp only [hts]
    exact Iff.of_eq (congrFun (congrFun (congrArg Prod.snd ((hD i).trans (hD j).symm)) a) b)


abbrev Profile := Bool → Bool → Bool

noncomputable def profile (p : RV B) : Profile := fun s k => by
  classical
  exact decide (Present B p s k)

lemma present_iff {p q : RV B} (h : profile B p = profile B q) (s k : Bool) :
    Present B p s k ↔ Present B q s k := by
  classical
  exact decide_eq_decide.mp (congrFun (congrFun h s) k)

lemma full_of_profile {p q : RV B} (h : profile B p = profile B q) (hp : Full B p) :
    Full B q := fun s k => (present_iff B h s k).mp (hp s k)

private lemma bool_same {a b k : Bool} (ha : a ≠ k) (hb : b ≠ k) : a = b := by
  cases a <;> cases b <;> cases k <;> simp_all

lemma full_of_triangle_profile (hB : B.CliqueFree 3) (p q r : RV B)
    (hpq : (RP B).Adj p q) (hpr : (RP B).Adj p r) (hqr : (RP B).Adj q r)
    (he₁ : profile B p = profile B q) (he₂ : profile B p = profile B r) : Full B p := by
  classical
  intro s k
  by_contra hn
  have hnq : ¬Present B q s k := fun hh => hn ((present_iff B he₁ s k).mpr hh)
  have hnr : ¬Present B r s k := fun hh => hn ((present_iff B he₂ s k).mpr hh)
  obtain ⟨x,hxp,hxq⟩ := hpq.1
  obtain ⟨y,hyq,hyr⟩ := hqr.1
  obtain ⟨z,hzr,hzp⟩ := hpr.2
  have hxy := q.property x hxq y hyq
  have hxz := (p.property z hzp x hxp).symm
  have hyz := r.property y hyr z hzr
  have avoid : x.2 ≠ k ∧ y.2 ≠ k ∧ z.2 ≠ k := by
    cases s
    · exact ⟨fun he => hnq ⟨x,hxq,he⟩,fun he => hnr ⟨y,hyr,he⟩,
        fun he => hn ⟨z,hzp,he⟩⟩
    · exact ⟨fun he => hn ⟨x,hxp,he⟩,fun he => hnq ⟨y,hyq,he⟩,
        fun he => hnr ⟨z,hzr,he⟩⟩
  exact same_bit_triangle B hB hxy hxz hyz
    ⟨bool_same avoid.1 avoid.2.1,bool_same avoid.1 avoid.2.2⟩

noncomputable def color (p q : RV B) : (Profile × Profile) × Option (Bool × Diagram) := by
  classical
  exact ((profile B p,profile B q),
    if hp : Full B p then if hq : Full B q then
      if h : (RP B).Adj p q then some (key B p q hp hq h) else none
    else none else none)

lemma color_key (p q : RV B) (hp : Full B p) (hq : Full B q) (h : (RP B).Adj p q) :
    (color B p q).2 = some (key B p q hp hq h) := by
  classical
  simp only [color,dif_pos hp,dif_pos hq,dif_pos h]

/-- Every member of the independent-pair right-adjoint family is covered.
No cardinality bound on B, or proper coloring of B, is assumed. -/
theorem countable_cover (hB : B.CliqueFree 3) : IsCountableUnionOfTriangleFree (RP B) := by
  classical
  letI : LinearOrder (RV B) := IsWellOrder.linearOrder WellOrderingRel
  apply Erdos595NegativeInner.cover_of_ordered_patterns (RP B) (color B)
  intro p q r _ _ hpq hpr hqr he
  have hpq' : profile B p = profile B q :=
    congrArg Prod.fst (congrArg Prod.fst he.2)
  have hqr' : profile B q = profile B r :=
    congrArg Prod.snd (congrArg Prod.fst he.1)
  have hpr' := hpq'.trans hqr'
  have hp := full_of_triangle_profile B hB p q r hpq hpr hqr hpq' hpr'
  have hq := full_of_profile B hpq' hp
  have hr := full_of_profile B hpr' hp
  have hk₁ := congrArg Prod.snd he.1
  have hk₂ := congrArg Prod.snd he.2
  rw [color_key B p q hp hq hpq,color_key B p r hp hr hpr] at hk₁
  rw [color_key B p q hp hq hpq,color_key B q r hq hr hqr] at hk₂
  exact key_valid B hB p q r hp hq hr hpq hpr hqr
    (Option.some.inj hk₁) (Option.some.inj hk₂)

#print axioms key_valid
#print axioms countable_cover
end Erdos595IndependentPairCover
