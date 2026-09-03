import FormalConjecturesUtil
import Submission.UpToRegularization

/-! Regular witnesses below an ordinary extremal power threshold, without a tightness assumption. -/

open Filter SimpleGraph Asymptotics Finset

namespace Erdos713RateRegularization
universe u
open Erdos713Regularization
set_option maxHeartbeats 2000000

open scoped Classical in
lemma small_set_deletion_local {W V : Type*} [Fintype V] (H : SimpleGraph W)
    (G : SimpleGraph V) (hfree : H.Free G) {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hUpper : ∀ n : ℕ, n ≤ Fintype.card V → (extremalNumber n H : ℝ) ≤ C * (n : ℝ)^r)
    (L : ℕ) (hL : 0 < L) (hn : L ≤ Fintype.card V)
    (S : Finset V) (hS : (S.card : ℝ) ≤ (Fintype.card V : ℝ) / L) :
    (G.edgeFinset.card : ℝ) ≤ ((G.induce (S : Set V)ᶜ).spanningCoe).edgeFinset.card +
      (L : ℝ) * C * (3 * (Fintype.card V : ℝ) / L)^r := by
  classical
  obtain ⟨P,hP,hPL⟩ := Finpartition.exists_equipartition_card_eq (univ : Finset V)
    hL.ne' (by simpa using hn)
  have hPart (T : Finset V) (hT : T ∈ P.parts) :
      (((G.induce ((S ∪ T : Finset V) : Set V)).spanningCoe).edgeFinset.card : ℝ) ≤
        C * (3 * (Fintype.card V : ℝ) / L)^r := by
    have hmap := card_edgeFinset_map
      (Function.Embedding.subtype (fun v => v ∈ ((S ∪ T : Finset V) : Set V)))
      (G.induce ((S ∪ T : Finset V) : Set V))
    simp only [edgeFinset_card, Fintype.card_eq_nat_card] at hmap ⊢
    rw [hmap]
    have hf : H.Free (G.induce ((S ∪ T : Finset V) : Set V)) :=
      fun h => hfree (h.trans ⟨Copy.induce G _⟩)
    have he := card_edgeFinset_le_extremalNumber hf
    simp only [edgeFinset_card, Fintype.card_eq_nat_card] at he
    apply (Nat.cast_le.mpr he).trans
    apply (hUpper _ (by
      simpa only [Nat.card_eq_fintype_card] using
        Fintype.card_subtype_le (fun v => v ∈ ((S ∪ T : Finset V) : Set V)))).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hr
    simp only [Nat.card_eq_fintype_card]
    rw [Fintype.card_of_finset' (p := ((S ∪ T : Finset V) : Set V)) (S ∪ T) (fun _ => Iff.rfl)]
    have hc : (T.card : ℝ) ≤ (Fintype.card V : ℝ) / L + 1 := by
      have hh := hP.card_part_le_average_add_one hT
      rw [hPL,card_univ] at hh
      have hh' : (T.card : ℝ) ≤ (Fintype.card V / L : ℕ) + 1 := by exact_mod_cast hh
      exact hh'.trans (add_le_add_left (Nat.cast_div_le (α := ℝ)) _)
    have hone : (1 : ℝ) ≤ (Fintype.card V : ℝ) / L :=
      (le_div_iff₀ (by exact_mod_cast hL)).mpr (by simpa using (Nat.cast_le.mpr hn : (L : ℝ) ≤ Fintype.card V))
    have hu : ((S ∪ T).card : ℝ) ≤ S.card + T.card := by exact_mod_cast card_union_le S T
    rw [mul_div_assoc]
    linarith
  have hh : (G.edgeFinset.card : ℝ) ≤ ((G.induce (S : Set V)ᶜ).spanningCoe).edgeFinset.card +
      ∑ T ∈ P.parts, (((G.induce ((S ∪ T : Finset V) : Set V)).spanningCoe).edgeFinset.card : ℝ) := by
    exact_mod_cast edges_delete_partition G S P
  apply hh.trans
  apply add_le_add_right
  apply (sum_le_sum hPart).trans
  simp only [sum_const, nsmul_eq_mul, hPL]
  exact le_of_eq (by ring)

open scoped Classical in
lemma trim_high_degrees_local {W V : Type*} [Fintype V] (H : SimpleGraph W)
    (G : SimpleGraph V) (hfree : H.Free G) {C r d : ℝ}
    (hC : 0 < C) (hr : 0 ≤ r)
    (hUpper : ∀ n : ℕ, n ≤ Fintype.card V → (extremalNumber n H : ℝ) ≤ C * (n : ℝ)^r)
    (L : ℕ) (hL : 0 < L) (hn : L ≤ Fintype.card V)
    (hSmall : (L : ℝ) * C * (3 / (L : ℝ))^r ≤ d / 8) :
    ∃ K : SimpleGraph V, K ≤ G ∧
      (G.edgeFinset.card : ℝ) ≤ K.edgeFinset.card + d / 8 * (Fintype.card V : ℝ)^r ∧
      (∀ v, (K.degree v : ℝ) ≤ 2 * C * L * (Fintype.card V : ℝ)^(r-1)) := by
  classical
  let S := (univ : Finset V).filter (fun v =>
    2 * C * L * (Fintype.card V : ℝ)^(r-1) < (G.degree v : ℝ))
  let K := (G.induce (S : Set V)ᶜ).spanningCoe
  have hKG : K ≤ G := spanningCoe_induce_le G _
  have hS : (S.card : ℝ) ≤ (Fintype.card V : ℝ) / L := high_degree_card_bound G hC
    (hL.trans_le hn) ((Nat.cast_le.mpr (card_edgeFinset_le_extremalNumber hfree)).trans (hUpper _ le_rfl)) L hL
  refine ⟨K,hKG,?_,?_⟩
  · have hh := small_set_deletion_local H G hfree hC.le hr hUpper L hL hn S hS
    have hmul : (L : ℝ) * C * (3 * (Fintype.card V : ℝ) / L)^r =
        ((L : ℝ) * C * (3 / (L : ℝ))^r) * (Fintype.card V : ℝ)^r := by
      rw [show 3 * (Fintype.card V : ℝ) / L = (3 / (L : ℝ)) * Fintype.card V by ring,
        Real.mul_rpow (by positivity) (Nat.cast_nonneg _)]
      ring
    rw [hmul] at hh
    simp only [edgeFinset_card, Fintype.card_eq_nat_card] at hh ⊢
    exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_right hSmall
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) _)
  · intro v
    simp only [← card_neighborSet_eq_degree, Fintype.card_eq_nat_card]
    by_cases hz : K.degree v = 0
    · simp only [← card_neighborSet_eq_degree, Fintype.card_eq_nat_card] at hz
      rw [hz, Nat.cast_zero]
      positivity
    obtain ⟨w,hw⟩ := (K.degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero hz)
    have hv : v ∉ S := ((restrict_adj G (S : Set V)ᶜ v w).mp hw).2.1
    have hvg : (G.degree v : ℝ) ≤ 2 * C * L * (Fintype.card V : ℝ)^(r-1) := by
      simpa only [S, mem_filter, mem_univ, true_and, not_lt] using hv
    have hdeg : K.degree v ≤ G.degree v := degree_le_of_le hKG
    simp only [← card_neighborSet_eq_degree, Fintype.card_eq_nat_card] at hdeg hvg
    exact (Nat.cast_le.mpr hdeg).trans hvg


lemma extremal_sq_bound {W : Type*} (H : SimpleGraph W) (n : ℕ) :
    extremalNumber n H ≤ n^2 := by
  classical
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ _
  exact card_edgeFinset_le_card_choose_two.trans (Nat.choose_le_pow _ _)

lemma exists_record {W : Type*} (H : SimpleGraph W) {r : ℝ} (hr : 0 < r)
    (hLarge : ∀ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      C * (n : ℝ)^r < (extremalNumber n H : ℝ))
    (M : ℕ) (A : ℝ) (hA : 0 < A) :
    ∃ n : ℕ, M ≤ n ∧ 0 < n ∧ ∃ C : ℝ, A < C ∧
      (extremalNumber n H : ℝ) = C * (n : ℝ)^r ∧
      (∀ j : ℕ, j ≤ n → (extremalNumber j H : ℝ) ≤ C * (j : ℝ)^r) := by
  classical
  obtain ⟨n,hn,hDense⟩ := hLarge (A + (M : ℝ)^2) 1
  let f : ℕ → ℝ := fun j => (extremalNumber j H : ℝ) / (j : ℝ)^r
  obtain ⟨m,hm,hMax⟩ := exists_max_image (range (n+1)) f ⟨n,by simp⟩
  have hnreal : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hBig : A + (M : ℝ)^2 < f m := by
    have hh : A + (M : ℝ)^2 < f n :=
      (lt_div_iff₀ (Real.rpow_pos_of_pos hnreal r)).mpr hDense
    exact hh.trans_le (hMax n (by simp))
  have hmpos : 0 < m := by
    by_contra hz
    have hm0 : m = 0 := by omega
    have : f m = 0 := by simp [f,hm0,Real.zero_rpow hr.ne']
    rw [this] at hBig
    nlinarith [sq_nonneg (M : ℝ)]
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hpow : 1 ≤ (m : ℝ)^r :=
    Real.one_le_rpow (by exact_mod_cast hmpos) hr.le
  have hSquare : f m ≤ (m : ℝ)^2 := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hmreal r)).mpr
    have he : (extremalNumber m H : ℝ) ≤ (m : ℝ)^2 := by exact_mod_cast extremal_sq_bound H m
    exact he.trans (le_mul_of_one_le_right (by positivity) hpow)
  have hM : M ≤ m := by
    by_contra hlt
    have hh : (m : ℝ) ≤ M := by exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge hlt)
    have hh2 := pow_le_pow_left₀ (Nat.cast_nonneg m) hh 2
    linarith
  refine ⟨m,hM,hmpos,f m,by nlinarith [sq_nonneg (M : ℝ)],?_,?_⟩
  · exact (div_mul_cancel₀ _ (Real.rpow_pos_of_pos hmreal r).ne').symm
  · intro j hj
    by_cases hj0 : j = 0
    · subst j
      have he : extremalNumber 0 H = 0 := by have := extremal_sq_bound H 0; norm_num at this ⊢; exact this
      simp [he,Real.zero_rpow hr.ne']
    have hjreal : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj0
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hjreal r)).mp
    apply hMax j
    have hmN := mem_range.mp hm
    simp only [mem_range]
    omega

lemma local_regularization {W : Type*} (H : SimpleGraph W) {r C : ℝ} (hr : 1 < r)
    (hC : 32 ≤ C) (n L : ℕ) (hL : 0 < L) (hnL : L ≤ n)
    (hSmall : (L : ℝ) * (3 / (L : ℝ))^r ≤ 1 / 8)
    (hLow : C / 2 * (n : ℝ)^r < (extremalNumber n H : ℝ))
    (hUpper : ∀ j : ℕ, j ≤ n → (extremalNumber j H : ℝ) ≤ C * (j : ℝ)^r) :
    ∃ G : SimpleGraph (Fin n), H.Free G ∧ G.IsBipartite ∧
      C / 32 * (n : ℝ)^r ≤ (Nat.card G.edgeSet : ℝ) ∧
      (∀ v, Nat.card (G.neighborSet v) = 0 ∨
        C / 32 * (n : ℝ)^(r-1) ≤ (Nat.card (G.neighborSet v) : ℝ)) ∧
      (∀ v, (Nat.card (G.neighborSet v) : ℝ) ≤ 2 * C * L * (n : ℝ)^(r-1)) := by
  classical
  have hCpos : 0 < C := by linarith
  have hnpos : 0 < n := hL.trans_le hnL
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hPow : (n : ℝ)^r = (n : ℝ)^(r-1) * n := by
    calc
      _ = (n : ℝ)^((r-1)+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hnr, Real.rpow_one]
  obtain ⟨G,instG,hGfree,hGe⟩ :=
    (lt_extremalNumber_iff_of_nonneg (V := Fin n) H
      (show 0 ≤ C / 2 * (n : ℝ)^r by positivity)).mp (by simpa only [Fintype.card_fin] using hLow)
  obtain ⟨B,hBG,hBip,hHalf⟩ := Erdos713Cut.exists_bipartite_half G
  have hBfree : H.Free B := fun hc => hGfree (hc.trans ⟨Copy.ofLE _ _ hBG⟩)
  have hSmall' : (L : ℝ) * C * (3 / (L : ℝ))^r ≤ C / 8 := by
    nlinarith [mul_le_mul_of_nonneg_left hSmall hCpos.le]
  obtain ⟨K,hKB,hKE,hKD⟩ := trim_high_degrees_local H B hBfree hCpos (le_trans zero_le_one hr.le)
    (by simpa only [Fintype.card_fin] using hUpper) L hL (by simpa only [Fintype.card_fin] using hnL) hSmall'
  let t : ℕ := ⌊C / 16 * (n : ℝ)^(r-1)⌋₊
  obtain ⟨Q,hQK,hQD,hQE⟩ := Erdos713Leaf.exists_pruned K t
  have hQG : Q ≤ G := hQK.trans (hKB.trans hBG)
  have hQfree : H.Free Q := fun hc => hGfree (hc.trans ⟨Copy.ofLE _ _ hQG⟩)
  have hQBip : Q.IsBipartite := hBip.of_hom (Copy.ofLE _ _ (hQK.trans hKB)).toHom
  have ht : (t : ℝ) ≤ C / 16 * (n : ℝ)^(r-1) := Nat.floor_le (by positivity)
  have htLower : C / 32 * (n : ℝ)^(r-1) ≤ (t : ℝ) := by
    have h1 := Nat.lt_floor_add_one (C / 16 * (n : ℝ)^(r-1))
    have hp : 1 ≤ (n : ℝ)^(r-1) := Real.one_le_rpow (by exact_mod_cast hnpos) (sub_nonneg.mpr hr.le)
    have h2 : 2 ≤ C / 16 * (n : ℝ)^(r-1) := by
      nlinarith [mul_le_mul_of_nonneg_left hp hCpos.le]
    change C / 16 * (n : ℝ)^(r-1) < (t : ℝ) + 1 at h1
    nlinarith
  refine ⟨Q,hQfree,hQBip,?_,?_,?_⟩
  · simp only [edgeFinset_card, Fintype.card_eq_nat_card] at hGe hHalf hKE
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hKE
    have heG : C / 2 * (n : ℝ)^r < (Nat.card G.edgeSet : ℝ) := by
      simpa only [Nat.card_eq_fintype_card] using hGe
    have heHalf : (Nat.card G.edgeSet : ℝ) ≤ 2 * (Nat.card B.edgeSet : ℝ) := by exact_mod_cast hHalf
    have heK : (Nat.card B.edgeSet : ℝ) ≤ (Nat.card K.edgeSet : ℝ) + C / 8 * (n : ℝ)^r := by
      simpa only [Nat.card_eq_fintype_card] using hKE
    have heQ : (Nat.card K.edgeSet : ℝ) ≤ (Nat.card Q.edgeSet : ℝ) + (t : ℝ) * n := by
      simp only [Fintype.card_fin] at hQE
      exact_mod_cast hQE
    have hCost : (t : ℝ) * n ≤ C / 16 * (n : ℝ)^r := by
      rw [hPow]
      nlinarith [mul_le_mul_of_nonneg_right ht hnr.le]
    nlinarith [Real.rpow_nonneg hnr.le r]
  · intro v
    rcases hQD v with hz | hq
    · exact Or.inl hz
    · exact Or.inr (htLower.trans (Nat.cast_le.mpr hq))
  · intro v
    have hh : Q.degree v ≤ K.degree v := degree_le_of_le hQK
    have hk := hKD v
    simp only [← card_neighborSet_eq_degree, Fintype.card_eq_nat_card] at hh hk
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using (Nat.cast_le.mpr hh).trans hk

lemma exists_almost_regular_below {W : Type*} (H : SimpleGraph W) {r : ℝ} (hr : 1 < r)
    (hLarge : ∀ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      C * (n : ℝ)^r < (extremalNumber n H : ℝ)) :
    ∃ R : ℝ, 0 < R ∧ ∀ A : ℝ, 0 < A → ∀ N : ℕ,
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (d : ℝ),
        N ≤ Fintype.card V ∧ 0 < Fintype.card V ∧ H.Free G ∧ G.IsBipartite ∧
        A * (Fintype.card V : ℝ)^r ≤ (Nat.card G.edgeSet : ℝ) ∧
        0 < d ∧ A * (Fintype.card V : ℝ)^(r-1) ≤ d ∧
        (∀ v, d ≤ (Nat.card (G.neighborSet v) : ℝ) ∧
          (Nat.card (G.neighborSet v) : ℝ) ≤ R*d) := by
  classical
  obtain ⟨L,hL,hSmall⟩ := exists_partition_size (r := r) (d := 1) (C := 1) hr (by norm_num) (by norm_num)
  simp only [mul_one] at hSmall
  refine ⟨64*L,by positivity,?_⟩
  intro A hA N
  obtain ⟨n,hn,hnpos,C,hC,hRecord,hUpper⟩ := exists_record H (lt_trans zero_lt_one hr) hLarge
    ((32*L)*max N 1) (32*(A+1)) (by positivity)
  have hC32 : 32 ≤ C := by linarith
  have hCpos : 0 < C := by linarith
  have hCA : A ≤ C/32 := by linarith
  have hnL : L ≤ n := by
    have h1 : 1 ≤ max N 1 := le_max_right _ _
    have h2 : L ≤ 32*L := by omega
    exact (h2.trans (Nat.le_mul_of_pos_right _ (by omega))).trans hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hLow : C / 2 * (n : ℝ)^r < (extremalNumber n H : ℝ) := by
    rw [hRecord]
    exact mul_lt_mul_of_pos_right (by linarith) (Real.rpow_pos_of_pos hnr r)
  obtain ⟨G,hFree,hBip,hE,hMin,hMax⟩ := local_regularization H hr hC32 n L hL hnL hSmall hLow hUpper
  let V := G.support
  let J := G.induce G.support
  have hcard : Fintype.card V ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (· ∈ G.support)
  have hJE : Nat.card J.edgeSet = Nat.card G.edgeSet := by
    have hh := card_edgeFinset_induce_of_support_subset (G := G) (s := G.support) Set.Subset.rfl
    simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using hh
  have hJD (v : V) : Nat.card (J.neighborSet v) = Nat.card (G.neighborSet v.val) := by
    have hh := degree_induce_support (G := G) v
    simpa only [← card_neighborSet_eq_degree, Fintype.card_eq_nat_card] using hh
  have hsum : 2 * (Nat.card J.edgeSet : ℝ) ≤
      (Fintype.card V : ℝ) * (2*C*L * (n : ℝ)^(r-1)) := by
    have hh : (∑ v : V, (J.degree v : ℝ)) ≤ ∑ v : V, 2*C*L * (n : ℝ)^(r-1) := by
      apply sum_le_sum
      intro v _
      simpa only [← card_neighborSet_eq_degree, Fintype.card_eq_nat_card, hJD] using hMax v.val
    simpa only [← Nat.cast_sum, sum_degrees_eq_twice_card_edges, edgeFinset_card,
      Fintype.card_eq_nat_card, Nat.cast_mul, Nat.cast_ofNat, sum_const, card_univ, nsmul_eq_mul] using hh
  have hPow : (n : ℝ)^r = (n : ℝ)^(r-1) * n := by
    calc
      _ = (n : ℝ)^((r-1)+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hnr, Real.rpow_one]
  have hnScale : (n : ℝ) ≤ (32*L : ℕ) * Fintype.card V := by
    have hp : 0 < C * (n : ℝ)^(r-1) := mul_pos hCpos (Real.rpow_pos_of_pos hnr _)
    rw [hJE] at hsum
    rw [hPow] at hE
    have hh : (C * (n : ℝ)^(r-1)) * n ≤
        (C * (n : ℝ)^(r-1)) * ((32*L : ℕ) * (Fintype.card V : ℝ)) := by
      push_cast
      nlinarith
    exact (mul_le_mul_iff_right₀ hp).mp hh
  have hsize : max N 1 ≤ Fintype.card V := by
    have hlower : (32*L : ℕ) * (max N 1 : ℕ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hh := hlower.trans hnScale
    exact_mod_cast (mul_le_mul_iff_right₀ (show (0 : ℝ) < (32*L : ℕ) by positivity)).mp hh
  have hJFree : H.Free J := fun hc => hFree (hc.trans ⟨Copy.induce G _⟩)
  have hJBip : J.IsBipartite := hBip.of_hom (Copy.induce G _).toHom
  refine ⟨V,inferInstance,J,C/32*(n : ℝ)^(r-1),(le_max_left _ _).trans hsize,
    lt_of_lt_of_le Nat.zero_lt_one ((le_max_right _ _).trans hsize),hJFree,hJBip,?_,by positivity,?_,?_⟩
  · rw [hJE]
    apply le_trans _ hE
    exact mul_le_mul hCA
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hcard) (le_trans zero_le_one hr.le))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
  · exact mul_le_mul hCA
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hcard) (sub_nonneg.mpr hr.le))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
  · intro v
    rw [hJD]
    constructor
    · have hpos : 0 < Nat.card (G.neighborSet v.val) := by
        have hh := (G.degree_pos_iff_mem_support v.val).mpr v.prop
        simpa only [← card_neighborSet_eq_degree, Fintype.card_eq_nat_card] using hh
      exact (hMin v.val).resolve_left (Nat.ne_of_gt hpos)
    · apply (hMax v.val).trans
      exact le_of_eq (by ring)

lemma of_rate {W : Type*} (H : SimpleGraph W) {α r : ℝ}
    (h : Erdos713Rate.HasRate H α) (hr : 1 < r) (hrα : r < α) :
    ∃ R : ℝ, 0 < R ∧ ∀ A : ℝ, 0 < A → ∀ N : ℕ,
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (d : ℝ),
        N ≤ Fintype.card V ∧ 0 < Fintype.card V ∧ H.Free G ∧ G.IsBipartite ∧
        A * (Fintype.card V : ℝ)^r ≤ (Nat.card G.edgeSet : ℝ) ∧
        0 < d ∧ A * (Fintype.card V : ℝ)^(r-1) ≤ d ∧
        (∀ v, d ≤ (Nat.card (G.neighborSet v) : ℝ) ∧
          (Nat.card (G.neighborSet v) : ℝ) ≤ R*d) :=
  exists_almost_regular_below H hr
    (Erdos713PowerCritical.exists_lower_above_smaller_power h hr.le hrα)

lemma uniform_proper_constant {W : Type u} [Fintype W] (H : SimpleGraph W) {β : ℝ}
    (hβ : 0 < β) (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (hProper : ∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H →
      ¬ Nonempty (J ≃g H) →
      (fun n : ℕ => (extremalNumber n J : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^β)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H →
      ¬ Nonempty (J ≃g H) → ∀ n : ℕ,
      (extremalNumber n J : ℝ) ≤ C * (n : ℝ)^β := by
  classical
  have hEach (J : SimpleGraph W) : ∃ C : ℝ, 0 < C ∧
      (J < H → ∀ n : ℕ, (extremalNumber n J : ℝ) ≤ C * (n : ℝ)^β) := by
    by_cases hJ : J < H
    · have hNoEq : ¬ Nonempty (J ≃g H) := by
        rintro ⟨e⟩
        exact hJ.ne (edgeFinset_inj.mp (Finset.eq_of_subset_of_card_le (edgeFinset_mono hJ.le)
          e.card_edgeFinset_eq.ge))
      obtain ⟨C,hC,hU⟩ := global_upper hβ (hProper W J ⟨Copy.ofLE _ _ hJ.le⟩ hNoEq)
      exact ⟨C,hC,fun _ => hU⟩
    · exact ⟨1,by norm_num,fun hh => (hJ hh).elim⟩
  choose C hC hU using hEach
  obtain ⟨J₀,_,hMax⟩ := exists_max_image (univ : Finset (SimpleGraph W)) C ⟨⊥,mem_univ _⟩
  refine ⟨C J₀,hC J₀,?_⟩
  intro T _ J hJH hNoEq n
  obtain ⟨f⟩ := hJH
  have hle : J.map f.toEmbedding ≤ H :=
    (map_le_iff_le_comap f.toEmbedding J H).mpr (fun _ _ h => f.toHom.map_adj h)
  have hlt : J.map f.toEmbedding < H := lt_of_le_of_ne hle
    (fun hh => hNoEq (Erdos713PowerCritical.iso_of_map_eq_of_no_isolates hNoIso f hh))
  have hm : (extremalNumber n J : ℝ) ≤ (extremalNumber n (J.map f.toEmbedding) : ℝ) :=
    Nat.cast_le.mpr ((show J ⊑ J.map f.toEmbedding from ⟨(Embedding.map f.toEmbedding J).toCopy⟩).extremalNumber_le)
  exact (hm.trans (hU _ hlt n)).trans (mul_le_mul_of_nonneg_right (hMax _ (mem_univ _))
    (Real.rpow_nonneg (Nat.cast_nonneg n) β))

lemma robust_of_rate {W : Type u} [Fintype W] (H : SimpleGraph W) {α β γ : ℝ}
    (hRate : Erdos713Rate.HasRate H α) (hβ : 1 ≤ β) (hβγ : β < γ) (hγα : γ < α)
    (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (hProper : ∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H →
      ¬ Nonempty (J ≃g H) →
      (fun n : ℕ => (extremalNumber n J : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^β)) :
    ∃ R : ℝ, 0 < R ∧ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (d : ℝ),
        N ≤ Fintype.card V ∧ 0 < Fintype.card V ∧ H.Free G ∧ G.IsBipartite ∧
        (Fintype.card V : ℝ)^γ ≤ (Nat.card G.edgeSet : ℝ) ∧
        0 < d ∧ (Fintype.card V : ℝ)^(γ-1) ≤ d ∧
        (∀ v, d ≤ (Nat.card (G.neighborSet v) : ℝ) ∧
          (Nat.card (G.neighborSet v) : ℝ) ≤ R*d) ∧
        (∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → ¬ Nonempty (J ≃g H) →
          ∀ F : SimpleGraph V, ε * (Nat.card G.edgeSet : ℝ) ≤ (Nat.card F.edgeSet : ℝ) → J ⊑ F) := by
  classical
  obtain ⟨C,hC,hUpper⟩ := uniform_proper_constant H (lt_of_lt_of_le zero_lt_one hβ) hNoIso hProper
  obtain ⟨R,hR,hReg⟩ := of_rate H hRate (lt_of_le_of_lt hβ hβγ) hγα
  refine ⟨R,hR,?_⟩
  intro ε hε N
  let A : ℝ := 1 + (C+1)/ε
  have hA : 0 < A := by dsimp [A]; positivity
  have hAone : 1 ≤ A := by
    have hp : 0 ≤ (C+1)/ε := by positivity
    dsimp only [A]
    linarith
  have hAε : C < ε*A := by
    dsimp only [A]
    have heq : ε*(1+(C+1)/ε) = ε+C+1 := by field_simp; ring
    rw [heq]
    linarith
  obtain ⟨V,instV,G,d,hN,hpos,hFree,hBip,hE,hd,hD,hDeg⟩ := hReg A hA N
  have hnr : (0 : ℝ) < Fintype.card V := by exact_mod_cast hpos
  have hnone : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hpos
  have hpow : (Fintype.card V : ℝ)^β ≤ (Fintype.card V : ℝ)^γ :=
    Real.rpow_le_rpow_of_exponent_le hnone hβγ.le
  refine ⟨V,instV,G,d,hN,hpos,hFree,hBip,?_,hd,?_,hDeg,?_⟩
  · exact (le_mul_of_one_le_left (Real.rpow_nonneg hnr.le _) hAone).trans hE
  · exact (le_mul_of_one_le_left (Real.rpow_nonneg hnr.le _) hAone).trans hD
  · intro T _ J hJH hNoEq F hF
    have hu : (extremalNumber (Fintype.card V) J : ℝ) ≤ C * (Fintype.card V : ℝ)^γ :=
      (hUpper T J hJH hNoEq _).trans (mul_le_mul_of_nonneg_left hpow hC.le)
    have hl : ε * (A * (Fintype.card V : ℝ)^γ) ≤ (Nat.card F.edgeSet : ℝ) :=
      (mul_le_mul_of_nonneg_left hE hε.le).trans hF
    have hlt : (extremalNumber (Fintype.card V) J : ℝ) < (Nat.card F.edgeSet : ℝ) := by
      have hh := mul_lt_mul_of_pos_right hAε (Real.rpow_pos_of_pos hnr γ)
      rw [mul_assoc] at hh
      exact (hu.trans_lt hh).trans_le hl
    apply IsContained.of_extremalNumber_lt_card_edgeFinset
    simp only [edgeFinset_card, Fintype.card_eq_nat_card]
    simp only [Fintype.card_eq_nat_card] at hlt
    exact_mod_cast hlt

end Erdos713RateRegularization
