import Submission.TensorObstruction
import Submission.EdgeAveraging
import Submission.UpperBounds
import Submission.Packing

/-!
An edge-thinning obstruction for unions of matched tensor layers.
This is not a resolution of Erdős 714.
-/

set_option maxHeartbeats 2000000

noncomputable section
open Finset SimpleGraph Classical

namespace Erdos714BlockThinning

variable {V I : Type*} [Fintype V] [Fintype I]

/-- A convenient integral consequence of the Kővári–Sós–Turán bound. -/
lemma fourth_power_bound (H : SimpleGraph V)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card ^ 4 ≤ 81 * Fintype.card V ^ 7 := by
  have hp := Erdos714Upper.edge_power_bound (by decide : 1 ≤ 4) H hfree
  norm_num only at hp
  by_cases he : H.edgeFinset.card ≤ 3 * Fintype.card V
  · have hn : Fintype.card V ^ 4 ≤ Fintype.card V ^ 7 := by
      by_cases hn : Fintype.card V = 0
      · simp [hn]
      · exact pow_le_pow_right' (Nat.one_le_iff_ne_zero.mpr hn) (by decide)
    calc
      H.edgeFinset.card ^ 4 ≤ (3 * Fintype.card V) ^ 4 := Nat.pow_le_pow_left he 4
      _ = 81 * Fintype.card V ^ 4 := by ring
      _ ≤ 81 * Fintype.card V ^ 7 := Nat.mul_le_mul_left _ hn
  · have he' : H.edgeFinset.card ≤ 2 * H.edgeFinset.card - 3 * Fintype.card V := by
      omega
    exact (Nat.pow_le_pow_left he' 4).trans (hp.trans (by omega))

/-- A vertex-block cover bounds the number of edges, without assuming that the
selected subgraph retains every edge of any block. -/
lemma edge_count_le_blocks (H : SimpleGraph V) (B : I → Finset V)
    (hcover : ∀ v w, H.Adj v w → ∃ i, v ∈ B i ∧ w ∈ B i) :
    H.edgeFinset.card ≤ ∑ i, (H.comap (Subtype.val : B i → V)).edgeFinset.card := by
  let E (i : I) : Finset (Sym2 V) :=
    (H.comap (Subtype.val : B i → V)).edgeFinset.image (Sym2.map Subtype.val)
  have hsub : H.edgeFinset ⊆ univ.biUnion E := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf v w =>
      have hvw : H.Adj v w := by simpa using he
      obtain ⟨i, hv, hw⟩ := hcover v w hvw
      apply mem_biUnion.mpr
      refine ⟨i, mem_univ _, ?_⟩
      apply mem_image.mpr
      refine ⟨s((⟨v,hv⟩ : B i), (⟨w,hw⟩ : B i)), ?_, rfl⟩
      simpa using hvw
  calc
    H.edgeFinset.card ≤ (univ.biUnion E).card := card_le_card hsub
    _ ≤ ∑ i, (E i).card := card_biUnion_le
    _ ≤ ∑ i, (H.comap (Subtype.val : B i → V)).edgeFinset.card :=
      sum_le_sum (fun i _ => card_image_le)

/-- The exact extremal-number version works for any forbidden graph without
isolated vertices, not just K44. -/
theorem extremal_bound_of_block_cover {W : Type*} (F : SimpleGraph W)
    (hF : ∀ v, ∃ w, F.Adj v w) (H : SimpleGraph V) (hfree : F.Free H)
    (B : I → Finset V) (n : ℕ) (hsize : ∀ i, (B i).card ≤ n)
    (hcover : ∀ v w, H.Adj v w → ∃ i, v ∈ B i ∧ w ∈ B i) :
    H.edgeFinset.card ≤ Fintype.card I * extremalNumber n F := by
  calc
    H.edgeFinset.card ≤ ∑ i, (H.comap (Subtype.val : B i → V)).edgeFinset.card :=
      edge_count_le_blocks H B hcover
    _ ≤ ∑ _i : I, extremalNumber n F := by
      apply sum_le_sum
      intro i _
      have hf := Erdos714GraphAveraging.free_comap F H
        (⟨Subtype.val, Subtype.val_injective⟩ : B i ↪ V) hfree
      have he := card_edgeFinset_le_extremalNumber hf
      simp only [Fintype.card_coe] at he
      exact he.trans (Erdos714Reduction.extremalNumber_monotone_of_no_isolated F hF (hsize i))
    _ = _ := by simp

/-- If all edges lie in blocks of at most `2*q` vertices, every K44-free
subgraph obeys a fourth-moment bound in terms of the number of blocks. -/
theorem fourth_power_of_block_cover (H : SimpleGraph V)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (B : I → Finset V) (q : ℕ) (hsize : ∀ i, (B i).card ≤ 2*q)
    (hcover : ∀ v w, H.Adj v w → ∃ i, v ∈ B i ∧ w ∈ B i) :
    H.edgeFinset.card ^ 4 ≤ 10368 * Fintype.card I ^ 4 * q ^ 7 := by
  let w (i : I) := (H.comap (Subtype.val : B i → V)).edgeFinset.card
  have hlocal (i : I) : w i ^ 4 ≤ 10368 * q ^ 7 := by
    have hf := Erdos714GraphAveraging.free_comap
      (completeBipartiteGraph (Fin 4) (Fin 4)) H
      (⟨Subtype.val, Subtype.val_injective⟩ : B i ↪ V) hfree
    have hp := fourth_power_bound (H.comap (Subtype.val : B i → V)) hf
    simp only [Fintype.card_coe] at hp
    calc
      w i ^ 4 ≤ 81 * (B i).card ^ 7 := hp
      _ ≤ 81 * (2*q)^7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hsize i) 7)
      _ = 10368 * q^7 := by ring
  have hm : (∑ i, w i)^4 ≤ Fintype.card I ^ 3 * ∑ i, w i ^ 4 := by
    simpa only [Nat.reduceAdd, card_univ] using
      (pow_sum_le_card_mul_sum_pow (s := (univ : Finset I)) (f := w)
        (by intros; omega) 3)
  calc
    H.edgeFinset.card ^ 4 ≤ (∑ i, w i)^4 :=
      Nat.pow_le_pow_left (edge_count_le_blocks H B hcover) 4
    _ ≤ Fintype.card I ^ 3 * ∑ i, w i ^ 4 := hm
    _ ≤ Fintype.card I ^ 3 * ∑ _i : I, (10368 * q^7) := by
      exact Nat.mul_le_mul_left _ (sum_le_sum (fun i _ => hlocal i))
    _ = 10368 * Fintype.card I ^ 4 * q^7 := by simp; ring

end Erdos714BlockThinning

namespace Erdos714ColoredTensor

variable {A B C D I : Type*}

/-- The color need not be unique: a union of matched tensor layers. -/
def host (R : I → A → B → Prop) (S : I → C → D → Prop) :
    SimpleGraph ((A × C) ⊕ (B × D)) :=
  Erdos714Tensor.incidence (fun x y => ∃ i, R i x.1 y.1 ∧ S i x.2 y.2)

/-- A single layer already supplies the standard oppositely oriented star copy. -/
def copy_of_stars (R : I → A → B → Prop) (S : I → C → D → Prop)
    (i : I) {s t : ℕ} (a : A) (d : D) (f : Fin s ↪ C) (g : Fin t ↪ B)
    (hf : ∀ j, S i (f j) d) (hg : ∀ j, R i a (g j)) :
    (completeBipartiteGraph (Fin s) (Fin t)).Copy (host R S) :=
  { Erdos714Tensor.copy_of_stars (R i) (S i) a d f g hf hg with
    toHom := {
      toFun := Sum.elim (fun j => Sum.inl (a, f j)) (fun j => Sum.inr (g j, d))
      map_rel' := by
        intro x y h
        cases x with
        | inl j =>
          cases y with
          | inl k => simp at h
          | inr k => exact ⟨i, hg k, hf j⟩
        | inr j =>
          cases y with
          | inl k => exact ⟨i, hg j, hf k⟩
          | inr k => simp at h } }

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I]

/-- Arbitrary edge deletion cannot evade the complete-bipartite block cover.
Only one row-degree bound and one column-degree bound per layer are needed. -/
theorem thinning_fourth_power (R : I → A → B → Prop) (S : I → C → D → Prop)
    (H : SimpleGraph ((A × C) ⊕ (B × D))) (hH : H ≤ host R S)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (q : ℕ)
    (hR : ∀ i a, (univ.filter (R i a)).card ≤ q)
    (hS : ∀ i d, (univ.filter (fun c => S i c d)).card ≤ q) :
    H.edgeFinset.card ^ 4 ≤
      10368 * (Fintype.card A * Fintype.card D * Fintype.card I)^4 * q^7 := by
  let L (p : A × D × I) : Finset ((A × C) ⊕ (B × D)) :=
    (univ.filter (fun c => S p.2.2 c p.2.1)).map
      ⟨fun c => Sum.inl (p.1,c), fun _ _ h => congrArg Prod.snd (Sum.inl.inj h)⟩
  let T (p : A × D × I) : Finset ((A × C) ⊕ (B × D)) :=
    (univ.filter (R p.2.2 p.1)).map
      ⟨fun b => Sum.inr (b,p.2.1), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩
  have hsize (p : A × D × I) : (L p ∪ T p).card ≤ 2*q := by
    have hL : (L p).card ≤ q := by simpa [L] using hS p.2.2 p.2.1
    have hT : (T p).card ≤ q := by simpa [T] using hR p.2.2 p.1
    have hh := card_union_le (L p) (T p)
    omega
  have hcover : ∀ v w, H.Adj v w → ∃ p : A × D × I,
      v ∈ L p ∪ T p ∧ w ∈ L p ∪ T p := by
    intro v w hvw
    have hvw' := hH hvw
    cases v with
    | inl x =>
      cases w with
      | inl y => exact False.elim hvw'
      | inr y =>
        obtain ⟨i, hi, hj⟩ := hvw'
        refine ⟨(x.1,y.2,i), ?_, ?_⟩
        · apply mem_union_left
          exact mem_map.mpr ⟨x.2, mem_filter.mpr ⟨mem_univ _, hj⟩, by simp⟩
        · apply mem_union_right
          exact mem_map.mpr ⟨y.1, mem_filter.mpr ⟨mem_univ _, hi⟩, by simp⟩
    | inr x =>
      cases w with
      | inl y =>
        obtain ⟨i, hi, hj⟩ := hvw'
        refine ⟨(y.1,x.2,i), ?_, ?_⟩
        · apply mem_union_right
          exact mem_map.mpr ⟨x.1, mem_filter.mpr ⟨mem_univ _, hi⟩, by simp⟩
        · apply mem_union_left
          exact mem_map.mpr ⟨y.2, mem_filter.mpr ⟨mem_univ _, hj⟩, by simp⟩
      | inr y => exact False.elim hvw'
  have hp := Erdos714BlockThinning.fourth_power_of_block_cover H hfree
    (fun p => L p ∪ T p) q hsize hcover
  simpa only [Fintype.card_prod, mul_assoc] using hp

/-- At the proposed q^4-vertex/q^3-degree scale, the fourth power of the
number of retained edges has exponent at most 27, rather than 28. -/
theorem critical_scale_bound (R : I → A → B → Prop) (S : I → C → D → Prop)
    (H : SimpleGraph ((A × C) ⊕ (B × D))) (hH : H ≤ host R S)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (q : ℕ) (hA : Fintype.card A ≤ q^2) (hD : Fintype.card D ≤ q^2)
    (hI : Fintype.card I ≤ q)
    (hR : ∀ i a, (univ.filter (R i a)).card ≤ 2*q)
    (hS : ∀ i d, (univ.filter (fun c => S i c d)).card ≤ 2*q) :
    H.edgeFinset.card ^ 4 ≤ 1327104 * q^27 := by
  have hp := thinning_fourth_power R S H hH hfree (2*q) hR hS
  have hc : Fintype.card A * Fintype.card D * Fintype.card I ≤ q^5 := by
    calc
      _ ≤ (q^2)*(q^2)*q := Nat.mul_le_mul (Nat.mul_le_mul hA hD) hI
      _ = q^5 := by ring
  calc
    H.edgeFinset.card^4 ≤
        10368 * (Fintype.card A * Fintype.card D * Fintype.card I)^4 * (2*q)^7 := hp
    _ ≤ 10368 * (q^5)^4 * (2*q)^7 := by gcongr
    _ = 1327104 * q^27 := by ring

/-- A q^7 lower bound with fixed multiplicative constant is possible in these
hosts only for bounded q. This is an obstruction to the hosts, not to arbitrary graphs. -/
theorem critical_scale_size_budget (R : I → A → B → Prop) (S : I → C → D → Prop)
    (H : SimpleGraph ((A × C) ⊕ (B × D))) (hH : H ≤ host R S)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (q K : ℕ) (hq : 0 < q)
    (hA : Fintype.card A ≤ q^2) (hD : Fintype.card D ≤ q^2)
    (hI : Fintype.card I ≤ q)
    (hR : ∀ i a, (univ.filter (R i a)).card ≤ 2*q)
    (hS : ∀ i d, (univ.filter (fun c => S i c d)).card ≤ 2*q)
    (hdense : q^7 ≤ K * H.edgeFinset.card) :
    q ≤ 1327104 * K^4 := by
  have he := critical_scale_bound R S H hH hfree q hA hD hI hR hS
  have h : q^27 * q ≤ q^27 * (1327104 * K^4) := by
    calc
      q^27 * q = (q^7)^4 := by ring
      _ ≤ (K * H.edgeFinset.card)^4 := Nat.pow_le_pow_left hdense 4
      _ = K^4 * H.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4 * (1327104 * q^27) := Nat.mul_le_mul_left _ he
      _ = q^27 * (1327104 * K^4) := by ring
  exact Nat.le_of_mul_le_mul_left h (pow_pos hq 27)

end Erdos714ColoredTensor

#print axioms Erdos714BlockThinning.fourth_power_of_block_cover
#print axioms Erdos714ColoredTensor.copy_of_stars
#print axioms Erdos714ColoredTensor.thinning_fourth_power
#print axioms Erdos714ColoredTensor.critical_scale_bound

#print axioms Erdos714BlockThinning.extremal_bound_of_block_cover
#print axioms Erdos714ColoredTensor.critical_scale_size_budget
