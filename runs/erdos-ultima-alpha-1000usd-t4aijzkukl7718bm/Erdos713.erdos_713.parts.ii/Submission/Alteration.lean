import FormalConjecturesUtil
import Submission.Verified

open Filter SimpleGraph Asymptotics

namespace Erdos713Alteration
open Finset

open scoped Classical in
theorem card_fixed_coordinates {I K : Type*} [Fintype I] [Fintype K]
    (S : Set I) (c : K) :
    Fintype.card {f : I → K // ∀ i ∈ S, f i = c} =
      Fintype.card K ^ (Fintype.card I - Nat.card S) := by
  classical
  let e : {f : I → K // ∀ i ∈ S, f i = c} ≃ (↥(Sᶜ) → K) :=
    { toFun := fun f i => f.val i.val
      invFun := fun f => ⟨fun i => if h : i ∈ S then c else f ⟨i, h⟩, by
        intro i hi
        simp only [dif_pos hi]⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ S
        · simpa only [dif_pos hi] using (f.prop i hi).symm
        · simp only [dif_neg hi]
      right_inv := by
        intro f
        funext i
        simp only [dif_neg i.prop] }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_compl_set]
  simp only [Nat.card_eq_fintype_card]

lemma mem_label_edges {V K : Type*} {G : SimpleGraph V} (C : G.EdgeLabeling K) (c : K)
    (e : Sym2 V) : e ∈ (C.labelGraph c).edgeSet ↔ ∃ he : e ∈ G.edgeSet, C ⟨e, he⟩ = c := by
  induction e using Sym2.inductionOn with
  | hf u v => exact EdgeLabeling.labelGraph_adj u v

lemma mem_label_edges_subtype {V K : Type*} {G : SimpleGraph V} (C : G.EdgeLabeling K) (c : K)
    (e : G.edgeSet) : e.val ∈ (C.labelGraph c).edgeSet ↔ C e = c := by
  rw [mem_label_edges]
  exact ⟨fun ⟨_, hh⟩ => hh, fun hh => ⟨e.prop, hh⟩⟩

open scoped Classical in
theorem label_edges_card {V K : Type*} [Fintype V] (G : SimpleGraph V)
    (C : G.EdgeLabeling K) (c : K) :
    Nat.card (C.labelGraph c).edgeSet = Nat.card {e : G.edgeSet // C e = c} := by
  classical
  let e : (C.labelGraph c).edgeSet ≃ {e : G.edgeSet // C e = c} :=
    { toFun := fun x =>
        ⟨⟨x.val, edgeSet_mono C.labelGraph_le x.prop⟩,
          (mem_label_edges_subtype C c _).mp x.prop⟩
      invFun := fun x => ⟨x.val.val, (mem_label_edges_subtype C c x.val).mpr x.prop⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  exact Nat.card_congr e

open scoped Classical in
theorem sum_label_edges {V K : Type*} [Fintype V] [Fintype K] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : K) :
    ∑ C : G.EdgeLabeling K, (C.labelGraph c).edgeFinset.card =
      G.edgeFinset.card * Fintype.card K ^ (G.edgeFinset.card - 1) := by
  classical
  let rel : G.EdgeLabeling K → G.edgeSet → Prop := fun C e => C e = c
  have hAbove (C : G.EdgeLabeling K) : ((univ : Finset G.edgeSet).bipartiteAbove rel C).card =
      (C.labelGraph c).edgeFinset.card := by
    rw [edgeFinset_card, ← Nat.card_eq_fintype_card, label_edges_card]
    simp only [bipartiteAbove, Nat.card_eq_fintype_card, Fintype.card_subtype, rel]
  have hBelow (e : G.edgeSet) : ((univ : Finset (G.EdgeLabeling K)).bipartiteBelow rel e).card =
      Fintype.card K ^ (G.edgeFinset.card - 1) := by
    have hh := card_fixed_coordinates ({e} : Set G.edgeSet) c
    rw [card_edgeSet] at hh
    simp only [Nat.card_unique, Fintype.card_subtype, Set.mem_singleton_iff, forall_eq] at hh
    exact hh
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := rel) (s := (univ : Finset (G.EdgeLabeling K))) (t := (univ : Finset G.edgeSet))
  simpa only [hAbove, hBelow, sum_const, card_univ, Nat.nsmul_eq_mul, card_edgeSet] using hsum

open scoped Classical in
def copyEquiv {V W K : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (C : G.EdgeLabeling K) (c : K) :
    H.Copy (C.labelGraph c) ≃ {f : H.Copy G // ∀ e, C (f.mapEdgeSet e) = c} where
  toFun f :=
    ⟨(Copy.ofLE _ _ C.labelGraph_le).comp f, fun e =>
      (mem_label_edges_subtype C c _).mp (f.mapEdgeSet e).prop⟩
  invFun f := ⟨⟨f.val, by
    intro u v huv
    apply (EdgeLabeling.labelGraph_adj (f.val u) (f.val v)).mpr
    exact ⟨f.val.toHom.map_adj huv, f.prop ⟨s(u,v), huv⟩⟩⟩, f.val.injective⟩
  left_inv f := by ext v; rfl
  right_inv f := by apply Subtype.ext; ext v; rfl

open scoped Classical in
set_option maxHeartbeats 2000000 in
theorem sum_labelled_copies {V W K : Type*} [Fintype V] [Fintype W] [Fintype K]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] (c : K) :
    ∑ C : G.EdgeLabeling K, Nat.card (H.Copy (C.labelGraph c)) =
      Nat.card (H.Copy G) * Fintype.card K ^ (G.edgeFinset.card - H.edgeFinset.card) := by
  classical
  let rel : G.EdgeLabeling K → H.Copy G → Prop := fun C f => ∀ e, C (f.mapEdgeSet e) = c
  have hAbove (C : G.EdgeLabeling K) : ((univ : Finset (H.Copy G)).bipartiteAbove rel C).card =
      Nat.card (H.Copy (C.labelGraph c)) := by
    rw [Nat.card_congr (copyEquiv G H C c)]
    simp only [bipartiteAbove, Nat.card_eq_fintype_card, Fintype.card_subtype, rel]
  have hBelow (f : H.Copy G) : ((univ : Finset (G.EdgeLabeling K)).bipartiteBelow rel f).card =
      Fintype.card K ^ (G.edgeFinset.card - H.edgeFinset.card) := by
    have hcard : Nat.card (Set.range f.mapEdgeSet) = H.edgeFinset.card := by
      rw [Nat.card_congr (Equiv.ofInjective _ f.mapEdgeSet.injective).symm]
      simp only [Nat.card_eq_fintype_card, card_edgeSet]
    have hh := card_fixed_coordinates (Set.range f.mapEdgeSet) c
    rw [hcard, card_edgeSet] at hh
    simp only [Fintype.card_subtype, Set.forall_mem_range] at hh
    exact hh
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := rel) (s := (univ : Finset (G.EdgeLabeling K))) (t := (univ : Finset (H.Copy G)))
  simpa only [hAbove, hBelow, sum_const, card_univ, Nat.nsmul_eq_mul, Fintype.card_eq_nat_card] using hsum

end Erdos713Alteration

#print axioms Erdos713Alteration.sum_labelled_copies

namespace Erdos713Alteration
open Finset

open scoped Classical in
theorem edges_le_extremal_add_copies {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] (hH : H ≠ ⊥) :
    G.edgeFinset.card ≤ extremalNumber (Fintype.card V) H + Nat.card (H.Copy G) := by
  classical
  have hk := le_card_edgeFinset_killCopies_add_copyCount (G := G) (H := H)
  have he := card_edgeFinset_le_extremalNumber (G := G.killCopies H) (free_killCopies hH)
  have hc := copyCount_le_labelledCopyCount (G := G) (H := H)
  rw [labelledCopyCount, Fintype.card_eq_nat_card] at hc
  simp only [edgeFinset_card, Fintype.card_eq_nat_card] at hk he ⊢
  omega

open scoped Classical in
theorem sampled_alteration {V W K : Type*} [Fintype V] [Fintype W] [Fintype K]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (c : K) (hH : H ≠ ⊥) (he : 1 ≤ H.edgeFinset.card) (heG : H.edgeFinset.card ≤ G.edgeFinset.card) :
    G.edgeFinset.card * Fintype.card K ^ (H.edgeFinset.card - 1) ≤
      Fintype.card K ^ H.edgeFinset.card * extremalNumber (Fintype.card V) H + Nat.card (H.Copy G) := by
  classical
  have hs := sum_le_sum (s := (univ : Finset (G.EdgeLabeling K)))
    (fun C _ => edges_le_extremal_add_copies (C.labelGraph c) H hH)
  have hC : Fintype.card (G.EdgeLabeling K) = Fintype.card K ^ G.edgeFinset.card := by
    change Fintype.card (G.edgeSet → K) = _
    rw [Fintype.card_fun, card_edgeSet]
  rw [sum_label_edges, sum_add_distrib, sum_const, card_univ, hC, Nat.nsmul_eq_mul,
    sum_labelled_copies] at hs
  have hp1 : Fintype.card K ^ (G.edgeFinset.card - 1) =
      Fintype.card K ^ (H.edgeFinset.card - 1) * Fintype.card K ^ (G.edgeFinset.card - H.edgeFinset.card) := by
    rw [← pow_add]
    congr 1
    omega
  have hp2 : Fintype.card K ^ G.edgeFinset.card =
      Fintype.card K ^ H.edgeFinset.card * Fintype.card K ^ (G.edgeFinset.card - H.edgeFinset.card) := by
    rw [← pow_add, Nat.add_sub_of_le heG]
  rw [hp1, hp2] at hs
  have ht : (G.edgeFinset.card * Fintype.card K ^ (H.edgeFinset.card - 1)) *
      Fintype.card K ^ (G.edgeFinset.card - H.edgeFinset.card) ≤
      (Fintype.card K ^ H.edgeFinset.card * extremalNumber (Fintype.card V) H + Nat.card (H.Copy G)) *
        Fintype.card K ^ (G.edgeFinset.card - H.edgeFinset.card) := by
    convert hs using 1 <;> ring
  have hk : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨c⟩
  exact Nat.le_of_mul_le_mul_right ht (Nat.pow_pos hk)

open scoped Classical in
theorem alteration_bound {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (he : 1 ≤ H.edgeFinset.card) (n k : ℕ) (hk : 1 ≤ k) :
    n.choose 2 * k ^ (H.edgeFinset.card - 1) ≤
      k ^ H.edgeFinset.card * extremalNumber n H + n ^ Fintype.card W := by
  classical
  have hH : H ≠ ⊥ := by
    intro hh
    subst H
    simpa using he
  by_cases hen : H.edgeFinset.card ≤ n.choose 2
  · have hs := sampled_alteration (⊤ : SimpleGraph (Fin n)) H (⟨0, by omega⟩ : Fin k) hH he
      (by simpa only [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin] using hen)
    simp only [Fintype.card_fin, card_edgeFinset_top_eq_card_choose_two] at hs
    have hc : Nat.card (H.Copy (⊤ : SimpleGraph (Fin n))) ≤ n ^ Fintype.card W := by
      have hf : Function.Injective (fun f : H.Copy (⊤ : SimpleGraph (Fin n)) => (f : W → Fin n)) := by
        intro f g he
        exact Copy.ext (congrFun he)
      have hh := Fintype.card_le_of_injective _ hf
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_eq_nat_card] at hh
      exact hh
    exact hs.trans (Nat.add_le_add_left hc _)
  · have hfree : H.Free (⊤ : SimpleGraph (Fin n)) := by
      rintro ⟨f⟩
      have hh := Fintype.card_le_of_embedding f.mapEdgeSet
      simp only [card_edgeSet, card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin] at hh
      exact hen hh
    have hn : n.choose 2 ≤ extremalNumber n H := by
      simpa only [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin] using
        card_edgeFinset_le_extremalNumber hfree
    have hp : k ^ (H.edgeFinset.card - 1) ≤ k ^ H.edgeFinset.card :=
      Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
    calc
      _ ≤ extremalNumber n H * k ^ H.edgeFinset.card := Nat.mul_le_mul hn hp
      _ ≤ _ := by rw [mul_comm]; omega

end Erdos713Alteration

#print axioms Erdos713Alteration.alteration_bound

namespace Erdos713Alteration
open Finset

theorem sq_le_four_choose_two (n : ℕ) (hn : 2 ≤ n) : n ^ 2 ≤ 4 * n.choose 2 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hh : (n : ℝ) ^ 2 ≤ 4 * (n.choose 2 : ℝ) := by
    rw [Nat.cast_choose_two]
    nlinarith
  exact_mod_cast hh

open scoped Classical in
set_option maxHeartbeats 2000000 in
theorem power_sequence_lower {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (he : 2 ≤ H.edgeFinset.card) (hq : 2 ≤ Fintype.card W)
    (hqe : Fintype.card W ≤ 2 * H.edgeFinset.card) (t : ℕ) (ht : 2 ≤ t) :
    t ^ (2 * H.edgeFinset.card - Fintype.card W) ≤
      64 * extremalNumber (t ^ (H.edgeFinset.card - 1)) H := by
  classical
  let e := H.edgeFinset.card
  let q := Fintype.card W
  let n := t ^ (e - 1)
  let k := 8 * t ^ (q - 2)
  have ht0 : 0 < t := by omega
  have hk0 : 0 < k := by dsimp [k]; positivity
  have hn2 : 2 ≤ n := ht.trans (Nat.le_self_pow (by dsimp [e]; omega) t)
  have hs := alteration_bound H (by omega) n k (by omega)
  change n.choose 2 * k ^ (e - 1) ≤ k ^ e * extremalNumber n H + n ^ q at hs
  have hquad := sq_le_four_choose_two n hn2
  have hbase : k ^ (e - 1) * n ^ 2 ≤ 4 * k ^ e * extremalNumber n H + 4 * n ^ q := by
    have hm := Nat.mul_le_mul_left (k ^ (e - 1)) hquad
    nlinarith only [hs, hm]
  have hpow : k ^ (e - 1) * n ^ 2 = 8 ^ (e - 1) * n ^ q := by
    dsimp only [k, n]
    simp only [mul_pow, ← pow_mul]
    rw [mul_assoc, ← pow_add]
    congr 2
    calc
      (q - 2) * (e - 1) + (e - 1) * 2 = (e - 1) * (q - 2 + 2) := by ring
      _ = (e - 1) * q := by rw [Nat.sub_add_cancel hq]
  have h8 : 8 ≤ 8 ^ (e - 1) := Nat.le_self_pow (by dsimp [e]; omega) 8
  have hsmall : 8 * n ^ q ≤ k ^ (e - 1) * n ^ 2 := by
    rw [hpow]
    exact Nat.mul_le_mul_right _ h8
  have hke : k ^ e = k ^ (e - 1) * k := by
    rw [← pow_succ]
    congr 1
    dsimp [e]
    omega
  rw [hke] at hbase
  have hmain : k ^ (e - 1) * n ^ 2 ≤ k ^ (e - 1) * (8 * k * extremalNumber n H) := by
    nlinarith only [hbase, hsmall]
  have hnmain := Nat.le_of_mul_le_mul_left hmain (Nat.pow_pos hk0)
  have hnexp : n ^ 2 = t ^ (q - 2) * t ^ (2 * e - q) := by
    dsimp only [n]
    rw [← pow_mul, ← pow_add]
    congr 1
    dsimp only [e, q]
    omega
  rw [hnexp] at hnmain
  have hlast : t ^ (q - 2) * t ^ (2 * e - q) ≤ t ^ (q - 2) * (64 * extremalNumber n H) := by
    convert hnmain using 1
    dsimp only [k]
    ring
  exact Nat.le_of_mul_le_mul_left hlast (Nat.pow_pos ht0)

theorem exponent_lower_of_power_sequence {f : ℕ → ℕ} {m s C : ℕ} (hs : 1 ≤ s)
    (hlow : ∀ t : ℕ, 2 ≤ t → t ^ m ≤ C * f (t ^ s)) {a : ℝ}
    (hO : (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ a)) :
    (m : ℝ) / s ≤ a := by
  have ht : Tendsto (fun t : ℕ => t ^ s) atTop atTop := tendsto_pow_atTop (by omega)
  have hS := hO.comp_tendsto ht
  have hP (t : ℕ) : ((t ^ s : ℕ) : ℝ) ^ a = (t : ℝ) ^ ((s : ℝ) * a) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg t)]
  change (fun t : ℕ => (f (t ^ s) : ℝ)) =O[atTop] (fun t : ℕ => ((t ^ s : ℕ) : ℝ) ^ a) at hS
  simp only [hP] at hS
  have hL : (fun t : ℕ => (t : ℝ) ^ (m : ℝ)) =O[atTop]
      (fun t : ℕ => (f (t ^ s) : ℝ)) := by
    apply IsBigO.of_bound (C : ℝ)
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with t ht
    rw [Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _), Real.norm_natCast]
    exact_mod_cast hlow t ht
  have hh := Erdos713Forest.exponent_le_of_isBigO (hL.trans hS)
  have hs' : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  exact (div_le_iff₀ hs').mpr (by nlinarith only [hh])

open scoped Classical in
set_option maxHeartbeats 2000000 in
theorem exponent_lower {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (he : 2 ≤ H.edgeFinset.card) (hq : 2 ≤ Fintype.card W)
    (hqe : Fintype.card W ≤ 2 * H.edgeFinset.card) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) :
    ((2 * H.edgeFinset.card - Fintype.card W : ℕ) : ℝ) / (H.edgeFinset.card - 1 : ℕ) ≤ a := by
  have hO : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) := (isBigO_const_mul_right_iff hc).mp h.isBigO
  exact exponent_lower_of_power_sequence (f := fun n => extremalNumber n H)
    (s := H.edgeFinset.card - 1) (m := 2 * H.edgeFinset.card - Fintype.card W) (C := 64)
    (by omega) (fun t ht => power_sequence_lower H he hq hqe t ht) hO

end Erdos713Alteration

#print axioms Erdos713Alteration.exponent_lower

namespace Erdos713Alteration
open Finset

open scoped Classical in
theorem exponent_lower_formula {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (he : 2 ≤ H.edgeFinset.card) (hq : 2 ≤ Fintype.card W)
    (hqe : Fintype.card W ≤ 2 * H.edgeFinset.card) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) :
    2 - ((Fintype.card W : ℝ) - 2) / ((H.edgeFinset.card : ℝ) - 1) ≤ a := by
  have he1 : 1 ≤ H.edgeFinset.card := by omega
  have hp : (0 : ℝ) < (H.edgeFinset.card : ℝ) - 1 := by
    have hh : (2 : ℝ) ≤ H.edgeFinset.card := by exact_mod_cast he
    linarith
  have hh := exponent_lower H he hq hqe hc h
  rw [Nat.cast_sub hqe, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub he1, Nat.cast_one] at hh
  have heq : 2 - ((Fintype.card W : ℝ) - 2) / ((H.edgeFinset.card : ℝ) - 1) =
      (2 * (H.edgeFinset.card : ℝ) - (Fintype.card W : ℝ)) / ((H.edgeFinset.card : ℝ) - 1) := by
    field_simp
    <;> ring
  rwa [heq]

open scoped Classical in
theorem card_le_edges_of_degree_two {W : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hd : ∀ v, 2 ≤ Nat.card (H.neighborSet v)) :
    Fintype.card W ≤ H.edgeFinset.card := by
  have hd' (v : W) : 2 ≤ H.degree v := by
    simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hd v
  have hs := sum_le_sum (s := (univ : Finset W)) (fun v _ => hd' v)
  simp only [sum_const, card_univ, Nat.nsmul_eq_mul, sum_degrees_eq_twice_card_edges] at hs
  omega

end Erdos713Alteration

#print axioms Erdos713Alteration.exponent_lower_formula
