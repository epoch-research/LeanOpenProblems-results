import FormalConjecturesUtil
import Submission.Verified

open Filter SimpleGraph Asymptotics

namespace Erdos713GeneralDRC
open Finset Erdos713C6

open scoped Classical in
noncomputable def common {I V : Type*} [Fintype V] (G : SimpleGraph V) (f : I → V) : Finset V :=
  univ.filter (fun v => ∀ i, G.Adj (f i) v)

@[simp] theorem mem_common {I V : Type*} [Fintype V] {G : SimpleGraph V} {f : I → V} {v : V} :
    v ∈ common G f ↔ ∀ i, G.Adj (f i) v := by classical simp [common]

open scoped Classical in
set_option maxHeartbeats 2000000 in
theorem clean_set {V : Type*} [Fintype V] (G : SimpleGraph V) {r : ℕ} (hr : 1 ≤ r)
    (U : Finset V) (k : ℕ) :
    ∃ S : Finset V, S ⊆ U ∧
      U.card ≤ S.card + ((Fintype.piFinset fun _ : Fin r => U).filter
        (fun q => (common G q).card < k)).card ∧
      ∀ q : Fin r → V, (∀ i, q i ∈ S) → k ≤ (common G q).card := by
  classical
  let i0 : Fin r := ⟨0, by omega⟩
  let B := (Fintype.piFinset fun _ : Fin r => U).filter (fun q => (common G q).card < k)
  let S := U \ B.image (fun q => q i0)
  refine ⟨S, sdiff_subset, ?_, ?_⟩
  · exact (card_le_card_sdiff_add_card (s := U) (t := B.image (fun q => q i0))).trans
      (Nat.add_le_add_left (card_image_le (s := B) (f := fun q => q i0)) S.card)
  · intro q hq
    by_contra hh
    have hB : q ∈ B := mem_filter.mpr
      ⟨Fintype.mem_piFinset.mpr (fun i => (mem_sdiff.mp (hq i)).1), lt_of_not_ge hh⟩
    exact (mem_sdiff.mp (hq i0)).2 (mem_image_of_mem (fun q => q i0) hB)

open scoped Classical in
theorem sum_common_eq_sum_descFactorial {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : ℕ) :
    ∑ z : Fin r ↪ V, (common G z).card = ∑ v, (G.degree v).descFactorial r := by
  classical
  let rel : V → (Fin r ↪ V) → Prop := fun v z => ∀ i, G.Adj v (z i)
  have hAbove (v : V) : ((univ : Finset (Fin r ↪ V)).bipartiteAbove rel v).card =
      (G.degree v).descFactorial r := by
    let e : ↥((univ : Finset (Fin r ↪ V)).bipartiteAbove rel v) ≃
        (Fin r ↪ G.neighborSet v) :=
      { toFun := fun f =>
          ⟨fun i => ⟨f.val i, ((mem_bipartiteAbove rel).mp f.prop).2 i⟩,
            fun i j hij => f.val.injective (congrArg Subtype.val hij)⟩
        invFun := fun f =>
          ⟨f.trans (Function.Embedding.subtype _),
            (mem_bipartiteAbove rel).mpr ⟨mem_univ _, fun i => (f i).prop⟩⟩
        left_inv := by intro f; rfl
        right_inv := by intro f; rfl }
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_embedding_eq,
      Fintype.card_fin, card_neighborSet_eq_degree]
  have hBelow (z : Fin r ↪ V) : (univ : Finset V).bipartiteBelow rel z = common G z := by
    ext v
    simp [bipartiteBelow, rel, adj_comm]
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := rel) (s := (univ : Finset V)) (t := (univ : Finset (Fin r ↪ V)))
  simpa only [hAbove, hBelow] using hsum.symm

open scoped Classical in
theorem sum_bad_tuples_le {V : Type*} [Fintype V] (G : SimpleGraph V) (r k : ℕ) :
    ∑ z : Fin r ↪ V, ((Fintype.piFinset fun _ : Fin r => common G z).filter
      (fun q => (common G q).card < k)).card ≤ k ^ r * Fintype.card V ^ r := by
  classical
  let rel : (Fin r ↪ V) → (Fin r → V) → Prop := fun z q =>
    (∀ j i, G.Adj (z i) (q j)) ∧ (common G q).card < k
  have hAbove (z : Fin r ↪ V) : (univ : Finset (Fin r → V)).bipartiteAbove rel z =
      (Fintype.piFinset fun _ : Fin r => common G z).filter (fun q => (common G q).card < k) := by
    ext q
    simp [bipartiteAbove, rel]
  have hBelow (q : Fin r → V) : ((univ : Finset (Fin r ↪ V)).bipartiteBelow rel q).card ≤ k ^ r := by
    by_cases hq : (common G q).card < k
    · let C := (univ : Finset (Fin r ↪ V)).bipartiteBelow rel q
      have hinj : Function.Injective (fun z : Fin r ↪ V => (z : Fin r → V)) := by
        intro z z' he
        exact Function.Embedding.ext (congrFun he)
      have hsub : C.image (fun z : Fin r ↪ V => (z : Fin r → V)) ⊆
          Fintype.piFinset (fun _ : Fin r => common G q) := by
        intro z hz
        obtain ⟨f, hf, rfl⟩ := mem_image.mp hz
        apply Fintype.mem_piFinset.mpr
        intro i
        apply mem_common.mpr
        intro j
        exact (((mem_bipartiteBelow rel).mp hf).2.1 j i).symm
      have hh := card_le_card hsub
      rw [card_image_of_injective _ hinj, Fintype.card_piFinset_const] at hh
      exact hh.trans (Nat.pow_le_pow_left hq.le r)
    · have he : (univ : Finset (Fin r ↪ V)).bipartiteBelow rel q = ∅ := by
        ext z
        simp only [mem_bipartiteBelow, mem_univ, rel, hq, and_false, notMem_empty]
      simp [he]
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := rel) (s := (univ : Finset (Fin r ↪ V))) (t := (univ : Finset (Fin r → V)))
  simp_rw [hAbove] at hsum
  rw [hsum]
  calc
    _ ≤ ∑ _ : Fin r → V, k ^ r := sum_le_sum fun q _ => hBelow q
    _ = _ := by simp [Fintype.card_fun, mul_comm]

def augmented {A B : Type*} (r : ℕ) (R : A → B → Prop) (a : A) : Fin r ⊕ B → Prop :=
  Sum.elim (fun _ => True) (R a)

open scoped Classical in
theorem contained_of_anchored_heavy_set {A B V : Type*} [Fintype A] [Fintype B] [Fintype V]
    (R : A → B → Prop) (G : SimpleGraph V) {r : ℕ}
    (hR : ∀ b, ∃ w : Fin r → A, ∀ a, R a b → a ∈ Set.range w)
    (z : Fin r ↪ V) (S : Finset V) (hS : Fintype.card A ≤ S.card)
    (hSz : ∀ a ∈ S, ∀ i, G.Adj a (z i))
    (hgood : ∀ q : Fin r → V, (∀ i, q i ∈ S) →
      Fintype.card A + Fintype.card B + r ≤ (common G q).card) :
    bipGraph (augmented r R) ⊑ G := by
  classical
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset hS
  choose w hw using hR
  let L := (univ : Finset A).image f ∪ (univ : Finset (Fin r)).image z
  let t : B → Finset V := fun b => common G (fun i => f (w b i)) \ L
  have hL : L.card ≤ Fintype.card A + r := by
    apply (card_union_le _ _).trans
    exact Nat.add_le_add ((card_image_le).trans (by simp)) ((card_image_le).trans (by simp))
  have ht (b : B) : Fintype.card B ≤ (t b).card := by
    have hg := hgood (fun i => f (w b i)) (fun i => hf ⟨w b i, rfl⟩)
    have hh := card_le_card_sdiff_add_card (s := common G (fun i => f (w b i))) (t := L)
    dsimp only [t]
    omega
  have hHall (U : Finset B) : U.card ≤ (U.biUnion t).card := by
    rcases U.eq_empty_or_nonempty with rfl | hU
    · simp
    obtain ⟨b, hb⟩ := hU
    exact (card_le_univ U).trans ((ht b).trans (card_le_card (subset_biUnion_of_mem t hb)))
  obtain ⟨g, hginj, hg⟩ := (all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  have hdis (a : A) (b : B) : f a ≠ g b := by
    intro hab
    exact (mem_sdiff.mp (hg b)).2
      (hab ▸ mem_union_left _ (mem_image_of_mem f (mem_univ a)))
  have hdisz (i : Fin r) (b : B) : z i ≠ g b := by
    intro hab
    exact (mem_sdiff.mp (hg b)).2
      (hab ▸ mem_union_right _ (mem_image_of_mem z (mem_univ i)))
  have hAdj (a : A) (b : B) (hab : R a b) : G.Adj (f a) (g b) := by
    obtain ⟨i, rfl⟩ := hw b a hab
    exact (mem_common.mp (mem_sdiff.mp (hg b)).1) i
  apply Erdos713Anchors.bipGraph_contained_of_maps (augmented r R) G f (Sum.elim z g) f.injective
  · intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (z.injective hxy)
      | inr b => exact (hdisz i b hxy).elim
    | inr b =>
      cases y with
      | inl i => exact (hdisz i b hxy.symm).elim
      | inr b' => exact congrArg Sum.inr (hginj hxy)
  · intro a b
    cases b with
    | inl i => exact (hSz (f a) (hf ⟨a, rfl⟩) i).ne
    | inr b => exact hdis a b
  · intro a b hab
    cases b with
    | inl i => exact hSz (f a) (hf ⟨a, rfl⟩) i
    | inr b => exact hAdj a b hab

open scoped Classical in
theorem sum_descFactorial_le {A B V : Type*} [Fintype A] [Fintype B] [Fintype V]
    (R : A → B → Prop) (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ} (hr : 1 ≤ r)
    (hR : ∀ b, ∃ w : Fin r → A, ∀ a, R a b → a ∈ Set.range w)
    (hfree : (bipGraph (augmented r R)).Free G) :
    ∑ v, (G.degree v).descFactorial r ≤
      (Fintype.card A + (Fintype.card A + Fintype.card B + r) ^ r) * Fintype.card V ^ r := by
  classical
  let k := Fintype.card A + Fintype.card B + r
  have hrow (z : Fin r ↪ V) : (common G z).card ≤
      Fintype.card A + ((Fintype.piFinset fun _ : Fin r => common G z).filter
        (fun q => (common G q).card < k)).card := by
    obtain ⟨S, hS, hcard, hgood⟩ := clean_set G hr (common G z) k
    have hsmall : S.card ≤ Fintype.card A := by
      by_contra hh
      apply hfree
      apply contained_of_anchored_heavy_set R G hR z S (by omega) ?_ hgood
      intro a ha i
      exact (mem_common.mp (hS ha) i).symm
    exact hcard.trans (Nat.add_le_add_right hsmall _)
  rw [← sum_common_eq_sum_descFactorial]
  calc
    _ ≤ ∑ z : Fin r ↪ V, (Fintype.card A + ((Fintype.piFinset fun _ : Fin r => common G z).filter
        (fun q => (common G q).card < k)).card) := sum_le_sum fun z _ => hrow z
    _ ≤ Fintype.card A * Fintype.card V ^ r + k ^ r * Fintype.card V ^ r := by
      rw [sum_add_distrib]
      apply Nat.add_le_add _ (sum_bad_tuples_le G r k)
      simp only [sum_const, card_univ, Nat.nsmul_eq_mul, Fintype.card_embedding_eq, Fintype.card_fin]
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)
    _ = _ := by dsimp only [k]; ring

open scoped Classical in
theorem sum_degree_pow_le {A B V : Type*} [Fintype A] [Fintype B] [Fintype V]
    (R : A → B → Prop) (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ} (hr : 1 ≤ r)
    (hR : ∀ b, ∃ w : Fin r → A, ∀ a, R a b → a ∈ Set.range w)
    (hfree : (bipGraph (augmented r R)).Free G) :
    ∑ v, G.degree v ^ r ≤ (r + 1) ^ r *
      (Fintype.card A + (Fintype.card A + Fintype.card B + r) ^ r + 1) * Fintype.card V ^ r := by
  calc
    _ ≤ ∑ v, (r + 1) ^ r * ((G.degree v).descFactorial r + 1) :=
      sum_le_sum fun v _ => Erdos713KST.pow_le_descFactorial _ _
    _ = (r + 1) ^ r * ((∑ v, (G.degree v).descFactorial r) + Fintype.card V) := by
      simp [sum_add_distrib, ← mul_sum]
    _ ≤ (r + 1) ^ r * ((Fintype.card A + (Fintype.card A + Fintype.card B + r) ^ r) *
        Fintype.card V ^ r + Fintype.card V ^ r) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add (sum_descFactorial_le R G hr hR hfree)
        (Nat.le_self_pow (by omega) _))
    _ = _ := by ring

open scoped Classical in
theorem edge_pow_le {A B V : Type*} [Fintype A] [Fintype B] [Fintype V]
    (R : A → B → Prop) (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ} (hr : 1 ≤ r)
    (hR : ∀ b, ∃ w : Fin r → A, ∀ a, R a b → a ∈ Set.range w)
    (hfree : (bipGraph (augmented r R)).Free G) :
    G.edgeFinset.card ^ r ≤ (r + 1) ^ r *
      (Fintype.card A + (Fintype.card A + Fintype.card B + r) ^ r + 1) * Fintype.card V ^ (r - 1 + r) := by
  have hJ := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg univ
    (f := fun v => (G.degree v : ℝ)) (show (1 : ℝ) ≤ r by exact_mod_cast hr)
    (fun v _ => Nat.cast_nonneg _)
  have he : (r : ℝ) - 1 = ((r - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hr, Nat.cast_one]
  rw [he] at hJ
  simp only [Real.rpow_natCast, card_univ] at hJ
  have hJN : (∑ v, G.degree v) ^ r ≤
      Fintype.card V ^ (r - 1) * ∑ v, G.degree v ^ r := by exact_mod_cast hJ
  rw [sum_degrees_eq_twice_card_edges] at hJN
  calc
    _ ≤ (2 * G.edgeFinset.card) ^ r := Nat.pow_le_pow_left (by omega) _
    _ ≤ Fintype.card V ^ (r - 1) * ∑ v, G.degree v ^ r := hJN
    _ ≤ Fintype.card V ^ (r - 1) * ((r + 1) ^ r *
        (Fintype.card A + (Fintype.card A + Fintype.card B + r) ^ r + 1) * Fintype.card V ^ r) :=
      Nat.mul_le_mul_left _ (sum_degree_pow_le R G hr hR hfree)
    _ = _ := by rw [pow_add]; ring

end Erdos713GeneralDRC

#print axioms Erdos713GeneralDRC.edge_pow_le

namespace Erdos713GeneralDRC
open Finset Erdos713C6

theorem extremal_pow_le {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) {r : ℕ} (hr : 1 ≤ r)
    (hR : ∀ b, ∃ w : Fin r → A, ∀ a, R a b → a ∈ Set.range w) (n : ℕ) :
    (extremalNumber n (bipGraph (augmented r R))) ^ r ≤ (r + 1) ^ r *
      (Fintype.card A + (Fintype.card A + Fintype.card B + r) ^ r + 1) * n ^ (r - 1 + r) := by
  classical
  let S : Finset (SimpleGraph (Fin n)) := {G | (bipGraph (augmented r R)).Free G}
  change (S.sup (fun G => G.edgeFinset.card)) ^ r ≤ _
  by_cases hS : S.Nonempty
  · obtain ⟨G, hG, he⟩ := exists_mem_eq_sup S hS (fun G => G.edgeFinset.card)
    rw [he]
    have hfree : (bipGraph (augmented r R)).Free G := by simpa [S] using hG
    simpa only [Fintype.card_fin] using edge_pow_le R G hr hR hfree
  · rw [not_nonempty_iff_eq_empty.mp hS]
    simp [Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hr)]

theorem exponent_upper_of_containment {A B W : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) {r : ℕ} (hr : 1 ≤ r)
    (hR : ∀ b, ∃ w : Fin r → A, ∀ a, R a b → a ∈ Set.range w)
    {H : SimpleGraph W} (hH : H ⊑ bipGraph (augmented r R)) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ≤ 2 - 1 / (r : ℝ) := by
  have hO : (fun n : ℕ => (n : ℝ) ^ a) =O[atTop]
      (fun n : ℕ => (extremalNumber n H : ℝ)) :=
    (isBigO_const_mul_left_iff hc).mp h.isBigO_symm
  have hP : (fun n : ℕ => (n : ℝ) ^ (a * (r : ℝ))) =O[atTop]
      (fun n : ℕ => (extremalNumber n H : ℝ) ^ r) := by
    simpa only [Real.rpow_mul_natCast (Nat.cast_nonneg _)] using hO.pow r
  have hB : (fun n : ℕ => (extremalNumber n H : ℝ) ^ r) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((r - 1 + r : ℕ) : ℝ)) := by
    apply IsBigO.of_bound (((r + 1) ^ r *
      (Fintype.card A + (Fintype.card A + Fintype.card B + r) ^ r + 1) : ℕ) : ℝ)
    filter_upwards with n
    rw [Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _),
      Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
    exact_mod_cast (Nat.pow_le_pow_left (hH.extremalNumber_le (n := n)) r).trans
      (extremal_pow_le R hr hR n)
  have hExp := Erdos713Forest.exponent_le_of_isBigO (hP.trans hB)
  have hr' : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have he : ((r - 1 + r : ℕ) : ℝ) = 2 * (r : ℝ) - 1 := by
    rw [Nat.cast_add, Nat.cast_sub hr, Nat.cast_one]
    ring
  rw [he] at hExp
  calc
    a ≤ (2 * (r : ℝ) - 1) / (r : ℝ) := (le_div_iff₀ hr').mpr hExp
    _ = 2 - 1 / (r : ℝ) := by field_simp

theorem cover_of_card_le {A : Type*} [Fintype A] [Nonempty A] (U : Set A)
    {r : ℕ} (hU : Nat.card U ≤ r) : ∃ w : Fin r → A, U ⊆ Set.range w := by
  classical
  let e : U ↪ Fin r := Classical.choice (Function.Embedding.nonempty_of_card_le
    (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hU))
  let w := Function.extend e Subtype.val (fun _ => Classical.arbitrary A)
  refine ⟨w, ?_⟩
  intro a ha
  exact ⟨e ⟨a, ha⟩, e.injective.extend_apply _ _ _⟩

open scoped Classical in
theorem contained_in_augmented {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) {r : ℕ} (E : Set B) (hE : Nat.card E ≤ r) :
    bipGraph R ⊑ bipGraph (augmented r (fun a (b : ↥(Eᶜ)) => R a b.val)) := by
  classical
  let e : E ↪ Fin r := Classical.choice (Function.Embedding.nonempty_of_card_le
    (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hE))
  let g : B ↪ Fin r ⊕ ↥(Eᶜ) := (Equiv.Set.sumCompl E).symm.toEmbedding.trans
    (e.sumMap (Function.Embedding.refl _))
  apply Erdos713Anchors.bipGraph_contained_of_maps R _ Sum.inl (fun b => Sum.inr (g b)) Sum.inl_injective
    (Sum.inr_injective.comp g.injective) (by simp)
  intro a b hab
  by_cases hb : b ∈ E
  · simp [g, Equiv.Set.sumCompl_symm_apply_of_mem hb, bipGraph, augmented]
  · simpa [g, Equiv.Set.sumCompl_symm_apply_of_notMem hb, bipGraph, augmented] using hab

theorem exponent_upper_of_exceptional_columns {A B W : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (R : A → B → Prop) {r : ℕ} (hr : 1 ≤ r) (E : Set B) (hE : Nat.card E ≤ r)
    (hR : ∀ b ∉ E, Nat.card {a // R a b} ≤ r)
    {H : SimpleGraph W} (hhi : H ⊑ bipGraph R) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ≤ 2 - 1 / (r : ℝ) := by
  classical
  let R' : A → ↥(Eᶜ) → Prop := fun a b => R a b.val
  have hR' (b : ↥(Eᶜ)) : ∃ w : Fin r → A, ∀ a, R' a b → a ∈ Set.range w := by
    obtain ⟨w, hw⟩ := cover_of_card_le {a | R a b.val} (hR b.val b.prop)
    exact ⟨w, fun a ha => hw ha⟩
  exact exponent_upper_of_containment R' hr hR'
    (hhi.trans (contained_in_augmented R E hE)) hc h

theorem exponent_eq_of_three_exceptions {A B W : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (R : A → B → Prop) (E : Set B) (hE : Nat.card E ≤ 3)
    (hR : ∀ b ∉ E, Nat.card {a // R a b} ≤ 3)
    {H : SimpleGraph W} (hlo : Erdos713Norm.K33 ⊑ H) (hhi : H ⊑ bipGraph R)
    {a c : ℝ} (ha : 0 ≤ a) (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = (5 : ℝ) / 3 := by
  have hu : a ≤ (5 : ℝ) / 3 := by
    have hh := exponent_upper_of_exceptional_columns R (by decide : 1 ≤ 3) E hE hR hhi hc h
    norm_num at hh
    exact hh
  have hO : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) := (isBigO_const_mul_right_iff hc).mp h.isBigO
  apply le_antisymm hu
  apply Erdos713Norm.lower_exponent_of_prime_bound ha hO
  intro p hp
  exact (Erdos713Norm.extremal_lower_prime p hp).trans
    (Nat.mul_le_mul_left 4 hlo.extremalNumber_le)

theorem rational_of_three_exceptions {A B W : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (R : A → B → Prop) (E : Set B) (hE : Nat.card E ≤ 3)
    (hR : ∀ b ∉ E, Nat.card {a // R a b} ≤ 3)
    {H : SimpleGraph W} (hlo : Erdos713Norm.K33 ⊑ H) (hhi : H ⊑ bipGraph R)
    {a c : ℝ} (ha : 0 ≤ a) (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨5 / 3, ?_⟩
  simpa using (exponent_eq_of_three_exceptions R E hE hR hlo hhi ha hc h).symm

end Erdos713GeneralDRC

#print axioms Erdos713GeneralDRC.exponent_upper_of_exceptional_columns
#print axioms Erdos713GeneralDRC.rational_of_three_exceptions

namespace Erdos713GeneralDRC
open Finset Erdos713C6

theorem rational_of_bipartition {W : Type*} [Fintype W] (H : SimpleGraph W)
    (S E : Set W) (hB : H.IsBipartiteWith S Sᶜ) (hE : Nat.card E ≤ 3)
    (hdeg : ∀ v ∈ Sᶜ, v ∉ E → Nat.card (H.neighborSet v) ≤ 3)
    (hlo : Erdos713Norm.K33 ⊑ H) {a c : ℝ} (ha : 0 ≤ a) (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  haveI : Nonempty S := by
    obtain ⟨f⟩ := hlo
    have he : H.Adj (f (Sum.inl 0)) (f (Sum.inr 0)) :=
      f.toHom.map_adj (by simp [Erdos713Norm.K33, completeBipartiteGraph])
    rcases hB.2 he with ⟨hu, _⟩ | ⟨_, hv⟩
    · exact ⟨⟨_, hu⟩⟩
    · exact ⟨⟨_, hv⟩⟩
  let R : S → ↥(Sᶜ) → Prop := fun u v => H.Adj u.val v.val
  let E' : Set ↥(Sᶜ) := {b | b.val ∈ E}
  have hE' : Nat.card E' ≤ 3 := by
    let f : E' ↪ E := ⟨fun b => ⟨b.val.val, b.prop⟩, by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : E => z.val) hxy⟩
    have hh := Fintype.card_le_of_embedding f
    simp only [Fintype.card_eq_nat_card] at hh
    exact hh.trans hE
  have hR (b : ↥(Sᶜ)) (hb : b ∉ E') : Nat.card {a : S // R a b} ≤ 3 := by
    let f : {a : S // R a b} ↪ H.neighborSet b.val :=
      ⟨fun a => ⟨a.val.val, a.prop.symm⟩, by
          intro x y hxy
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun z : H.neighborSet b.val => z.val) hxy⟩
    have hh := Fintype.card_le_of_embedding f
    simp only [Fintype.card_eq_nat_card] at hh
    exact hh.trans (hdeg b.val b.prop hb)
  have hhi : H ⊑ bipGraph R := by
    let e := (Equiv.Set.sumCompl S).symm
    refine ⟨⟨⟨e, ?_⟩, e.injective⟩⟩
    intro u v huv
    rcases hB.2 huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · have hv' : v ∉ S := hv
      simpa [e, Equiv.Set.sumCompl_symm_apply_of_mem hu,
        Equiv.Set.sumCompl_symm_apply_of_notMem hv', bipGraph, R] using huv
    · have hu' : u ∉ S := hu
      simpa [e, Equiv.Set.sumCompl_symm_apply_of_mem hv,
        Equiv.Set.sumCompl_symm_apply_of_notMem hu', bipGraph, R] using huv.symm
  exact rational_of_three_exceptions R E' hE' hR hlo hhi ha hc h

end Erdos713GeneralDRC

#print axioms Erdos713GeneralDRC.rational_of_bipartition

namespace Erdos713Minus44
open Finset Erdos713C6

def D44 : SimpleGraph (Fin 4 ⊕ Fin 4) := bipGraph (fun i j => i ≠ 3 ∨ j ≠ 3)

theorem contains_K33 : Erdos713Norm.K33 ⊑ D44 := by
  let f : Fin 3 ↪ Fin 4 := Fin.castLEEmb (by decide)
  have hn (i : Fin 3) : f i ≠ 3 := by
    intro he
    have hv := congrArg Fin.val he
    simp only [f, Fin.castLEEmb_apply, Fin.val_castLE] at hv
    omega
  have he : Erdos713Norm.K33 = bipGraph (fun (_ _ : Fin 3) => True) := by
    ext u v
    cases u <;> cases v <;> simp [Erdos713Norm.K33, completeBipartiteGraph, bipGraph]
  rw [he]
  apply Erdos713Anchors.bipGraph_contained_of_maps _ D44 (fun i => Sum.inl (f i))
    (fun j => Sum.inr (f j)) (Sum.inl_injective.comp f.injective)
    (Sum.inr_injective.comp f.injective) (by simp)
  intro i j _
  exact Or.inl (hn i)

theorem exponent_eq_of_containment {W : Type*} {H : SimpleGraph W}
    (hlo : Erdos713Norm.K33 ⊑ H) (hhi : H ⊑ D44) {a c : ℝ} (ha : 0 ≤ a) (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = (5 : ℝ) / 3 := by
  classical
  have hn : Nat.card {i : Fin 4 // i ≠ 3} ≤ 3 := by
    simpa only [Fintype.card_eq_nat_card, Nat.card_fin] using (Set.card_ne_eq (3 : Fin 4)).le
  apply Erdos713GeneralDRC.exponent_eq_of_three_exceptions (fun i j : Fin 4 => i ≠ 3 ∨ j ≠ 3)
    {j | j ≠ 3} hn ?_ hlo hhi ha hc h
  intro b hb
  have hb3 : b = 3 := by simpa using hb
  subst b
  simpa only [ne_eq, not_true_eq_false, or_false] using hn

theorem rational_of_containment {W : Type*} {H : SimpleGraph W}
    (hlo : Erdos713Norm.K33 ⊑ H) (hhi : H ⊑ D44) {a c : ℝ} (ha : 0 ≤ a) (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨5 / 3, ?_⟩
  simpa using (exponent_eq_of_containment hlo hhi ha hc h).symm

theorem rational_exponent {a c : ℝ} (ha : 0 ≤ a) (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n D44 : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) :=
  rational_of_containment contains_K33 (.refl _) ha hc h

end Erdos713Minus44

#print axioms Erdos713Minus44.rational_exponent
