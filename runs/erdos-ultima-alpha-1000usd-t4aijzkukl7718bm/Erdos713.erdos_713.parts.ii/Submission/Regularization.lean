import FormalConjecturesUtil
import Submission.UpToPowerCritical

/-! Almost-regular witnesses for a tight superlinear extremal rate. -/

open Filter SimpleGraph Asymptotics Finset

set_option maxHeartbeats 2000000

namespace Erdos713Regularization
universe u

lemma global_upper {W : Type*} {H : SimpleGraph W} {r : ℝ}
    (hr : 0 < r)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^r)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (extremalNumber n H : ℝ) ≤ C * (n : ℝ)^r := by
  classical
  obtain ⟨C,hC,hB⟩ := h.exists_pos
  obtain ⟨N,hN⟩ := eventually_atTop.mp hB.bound
  refine ⟨C + (N : ℝ)^2 + 1, by positivity, ?_⟩
  intro n
  have htriv : extremalNumber n H ≤ n^2 := by
    rw [← Fintype.card_fin n, extremalNumber_le_iff]
    intro G _ _
    exact card_edgeFinset_le_card_choose_two.trans (Nat.choose_le_pow _ _)
  by_cases hn : N ≤ n
  · have hh := hN n hn
    rw [Real.norm_natCast, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) r)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (N : ℝ)]) (Real.rpow_nonneg (Nat.cast_nonneg n) r))
  · by_cases hn0 : n = 0
    · subst n
      simp only [Nat.zero_pow (by decide : 0 < 2), Nat.le_zero] at htriv
      simp [htriv, Real.zero_rpow hr.ne']
    have hp : 1 ≤ (n : ℝ)^r := Real.one_le_rpow (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0) hr.le
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge hn)
    have hnn : (n : ℝ)^2 ≤ (N : ℝ)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnN 2
    have ht : (extremalNumber n H : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast htriv
    have hh := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ N^2 by positivity)
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg n) r]

open scoped Classical in
lemma restrict_adj {V : Type*} (G : SimpleGraph V) (S : Set V) (u v : V) :
    (G.induce S).spanningCoe.Adj u v ↔ G.Adj u v ∧ u ∈ S ∧ v ∈ S := by
  constructor
  · rintro ⟨a,b,hab,rfl,rfl⟩
    exact ⟨hab,a.prop,b.prop⟩
  · rintro ⟨hab,hu,hv⟩
    exact ⟨⟨u,hu⟩,⟨v,hv⟩,hab,rfl,rfl⟩

open scoped Classical in
lemma edges_delete_partition {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) (P : Finpartition (univ : Finset V)) :
    G.edgeFinset.card ≤ ((G.induce (S : Set V)ᶜ).spanningCoe).edgeFinset.card +
      ∑ T ∈ P.parts, ((G.induce ((S ∪ T : Finset V) : Set V)).spanningCoe).edgeFinset.card := by
  classical
  let K := (G.induce (S : Set V)ᶜ).spanningCoe
  let E (T : Finset V) := ((G.induce ((S ∪ T : Finset V) : Set V)).spanningCoe).edgeFinset
  have hsub : G.edgeFinset ⊆ K.edgeFinset ∪ P.parts.biUnion E := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : G.Adj u v := by simpa only [mem_edgeFinset] using he
      by_cases hu : u ∈ S
      · obtain ⟨T,⟨hT,hvT⟩,_⟩ := P.existsUnique_mem (mem_univ v)
        apply mem_union_right
        apply mem_biUnion.mpr ⟨T,hT,?_⟩
        exact (mem_edgeFinset).mpr ((restrict_adj _ _ _ _).mpr
          ⟨huv,mem_union_left _ hu,mem_union_right _ hvT⟩)
      · by_cases hv : v ∈ S
        · obtain ⟨T,⟨hT,huT⟩,_⟩ := P.existsUnique_mem (mem_univ u)
          apply mem_union_right
          apply mem_biUnion.mpr ⟨T,hT,?_⟩
          exact (mem_edgeFinset).mpr ((restrict_adj _ _ _ _).mpr
            ⟨huv,mem_union_right _ huT,mem_union_left _ hv⟩)
        · apply mem_union_left
          exact (mem_edgeFinset).mpr ((restrict_adj _ _ _ _).mpr ⟨huv,hu,hv⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left (card_biUnion_le) _))

open scoped Classical in
lemma small_set_deletion_bound {W V : Type*} [Fintype V] (H : SimpleGraph W)
    (G : SimpleGraph V) (hfree : H.Free G) {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hUpper : ∀ n : ℕ, (extremalNumber n H : ℝ) ≤ C * (n : ℝ)^r)
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
    apply (hUpper _).trans
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
lemma high_degree_card_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    {C r : ℝ} (hC : 0 < C) (hn : 0 < Fintype.card V)
    (he : (G.edgeFinset.card : ℝ) ≤ C * (Fintype.card V : ℝ)^r)
    (L : ℕ) (hL : 0 < L) :
    (((univ : Finset V).filter (fun v =>
      2 * C * L * (Fintype.card V : ℝ)^(r-1) < (G.degree v : ℝ))).card : ℝ) ≤
      (Fintype.card V : ℝ) / L := by
  classical
  let S := (univ : Finset V).filter (fun v =>
    2 * C * L * (Fintype.card V : ℝ)^(r-1) < (G.degree v : ℝ))
  change (S.card : ℝ) ≤ _
  have hsum : (S.card : ℝ) * (2 * C * L * (Fintype.card V : ℝ)^(r-1)) ≤
      ∑ v ∈ S, (G.degree v : ℝ) := by
    simpa only [sum_const, nsmul_eq_mul] using
      (sum_le_sum (s := S) (fun v hv => ((mem_filter.mp hv).2).le))
  have hall : (∑ v ∈ S, (G.degree v : ℝ)) ≤ 2 * (G.edgeFinset.card : ℝ) := by
    have hs : (∑ v ∈ S, (G.degree v : ℝ)) ≤ ∑ v : V, (G.degree v : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ S) (by intros; positivity)
    simpa only [← Nat.cast_sum, sum_degrees_eq_twice_card_edges, Nat.cast_mul, Nat.cast_ofNat] using hs
  have hp : (Fintype.card V : ℝ)^r = (Fintype.card V : ℝ)^(r-1) * Fintype.card V := by
    calc
      _ = (Fintype.card V : ℝ)^((r-1)+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add (by exact_mod_cast hn), Real.rpow_one]
  have hprod : (2 * C * (Fintype.card V : ℝ)^(r-1)) * (S.card * (L : ℝ)) ≤
      (2 * C * (Fintype.card V : ℝ)^(r-1)) * Fintype.card V := by
    rw [hp] at he
    nlinarith [hsum.trans hall]
  have hpos : 0 < 2 * C * (Fintype.card V : ℝ)^(r-1) := by
    exact mul_pos (mul_pos (by norm_num) hC) (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)
  apply (le_div_iff₀ (by exact_mod_cast hL)).mpr
  exact (mul_le_mul_iff_right₀ hpos).mp hprod

lemma exists_partition_size {r d C : ℝ} (hr : 1 < r) (hd : 0 < d) (hC : 0 < C) :
    ∃ L : ℕ, 0 < L ∧ (L : ℝ) * C * (3 / (L : ℝ))^r ≤ d / 8 := by
  have hε : 0 < d / (8 * C * (3 : ℝ)^r) := by positivity
  have he := (Erdos713Leaf.rpow_isLittleO_nat hr).bound hε
  obtain ⟨L,hL,hB⟩ := ((eventually_gt_atTop (0 : ℕ)).and he).exists
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg L) 1), Real.rpow_one,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg L) r)] at hB
  refine ⟨L,hL,?_⟩
  rw [Real.div_rpow (by norm_num) hLreal.le]
  have hp : 0 < (L : ℝ)^r := Real.rpow_pos_of_pos hLreal r
  have h3 : 0 < (3 : ℝ)^r := by positivity
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
  have hh := mul_le_mul_of_nonneg_right hB (show 0 ≤ C * (3 : ℝ)^r / (L : ℝ)^r * 8 by positivity)
  convert hh using 1 <;> field_simp [hC.ne',hp.ne',h3.ne']

open scoped Classical in
lemma trim_high_degrees {W V : Type*} [Fintype V] (H : SimpleGraph W)
    (G : SimpleGraph V) (hfree : H.Free G) {C r d : ℝ}
    (hC : 0 < C) (hr : 0 ≤ r)
    (hUpper : ∀ n : ℕ, (extremalNumber n H : ℝ) ≤ C * (n : ℝ)^r)
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
    (hL.trans_le hn) ((Nat.cast_le.mpr (card_edgeFinset_le_extremalNumber hfree)).trans (hUpper _)) L hL
  refine ⟨K,hKG,?_,?_⟩
  · have hh := small_set_deletion_bound H G hfree hC.le hr hUpper L hL hn S hS
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

lemma exists_almost_regular_witnesses {W : Type*} (H : SimpleGraph W) {r : ℝ}
    (hr : 1 < r) (h : Erdos713Tight.HasTightRate H r) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧
      ∃ G : SimpleGraph (Fin n), H.Free G ∧ G.IsBipartite ∧
        a * (n : ℝ)^r ≤ (Nat.card G.edgeSet : ℝ) ∧
        (∀ v, Nat.card (G.neighborSet v) = 0 ∨
          a * (n : ℝ)^(r-1) ≤ (Nat.card (G.neighborSet v) : ℝ)) ∧
        (∀ v, (Nat.card (G.neighborSet v) : ℝ) ≤ b * (n : ℝ)^(r-1)) := by
  classical
  obtain ⟨d,hd,hLower⟩ := Erdos713Tight.exists_positive_lower_constant h
  obtain ⟨C,hC,hUpper⟩ := global_upper (lt_trans zero_lt_one hr) h.upper
  obtain ⟨L,hL,hSmall⟩ := exists_partition_size hr hd hC
  have hlim : Tendsto (fun n : ℕ => d / 16 * (n : ℝ)^(r-1)) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity)
      ((tendsto_rpow_atTop (sub_pos.mpr hr)).comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (hlim.eventually (eventually_ge_atTop (2 : ℝ)))
  refine ⟨d/32,2*C*L,by positivity,by positivity,?_⟩
  intro N
  obtain ⟨n,hn,hLow⟩ := hLower (max N (max L N₀))
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnL : L ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₀ : N₀ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnpos : 0 < n := hL.trans_le hnL
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hPow : (n : ℝ)^r = (n : ℝ)^(r-1) * n := by
    calc
      _ = (n : ℝ)^((r-1)+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hnr, Real.rpow_one]
  obtain ⟨G,instG,hGfree,hGe⟩ :=
    (lt_extremalNumber_iff_of_nonneg (V := Fin n) H
      (show 0 ≤ d * (n : ℝ)^r by positivity)).mp (by simpa only [Fintype.card_fin] using hLow)
  obtain ⟨B,hBG,hBip,hHalf⟩ := Erdos713Cut.exists_bipartite_half G
  have hBfree : H.Free B := fun hc => hGfree (hc.trans ⟨Copy.ofLE _ _ hBG⟩)
  obtain ⟨K,hKB,hKE,hKD⟩ := trim_high_degrees H B hBfree hC (le_trans zero_le_one hr.le)
    hUpper L hL (by simpa only [Fintype.card_fin] using hnL) hSmall
  let t : ℕ := ⌊d / 16 * (n : ℝ)^(r-1)⌋₊
  obtain ⟨Q,hQK,hQD,hQE⟩ := Erdos713Leaf.exists_pruned K t
  have hQG : Q ≤ G := hQK.trans (hKB.trans hBG)
  have hQfree : H.Free Q := fun hc => hGfree (hc.trans ⟨Copy.ofLE _ _ hQG⟩)
  have hQBip : Q.IsBipartite := hBip.of_hom (Copy.ofLE _ _ (hQK.trans hKB)).toHom
  have ht : (t : ℝ) ≤ d / 16 * (n : ℝ)^(r-1) := Nat.floor_le (by positivity)
  have htLower : d / 32 * (n : ℝ)^(r-1) ≤ (t : ℝ) := by
    have h1 := Nat.lt_floor_add_one (d / 16 * (n : ℝ)^(r-1))
    have h2 := hN₀ n hn₀
    change d / 16 * (n : ℝ)^(r-1) < (t : ℝ) + 1 at h1
    nlinarith
  refine ⟨n,hnN,hnpos,Q,hQfree,hQBip,?_,?_,?_⟩
  · simp only [edgeFinset_card, Fintype.card_eq_nat_card] at hGe hHalf hKE
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hKE
    have heG : d * (n : ℝ)^r < (Nat.card G.edgeSet : ℝ) := by
      simpa only [Nat.card_eq_fintype_card] using hGe
    have heHalf : (Nat.card G.edgeSet : ℝ) ≤ 2 * (Nat.card B.edgeSet : ℝ) := by exact_mod_cast hHalf
    have heK : (Nat.card B.edgeSet : ℝ) ≤ (Nat.card K.edgeSet : ℝ) + d / 8 * (n : ℝ)^r := by
      simpa only [Nat.card_eq_fintype_card] using hKE
    have heQ : (Nat.card K.edgeSet : ℝ) ≤ (Nat.card Q.edgeSet : ℝ) + (t : ℝ) * n := by
      simp only [Fintype.card_fin] at hQE
      exact_mod_cast hQE
    have hCost : (t : ℝ) * n ≤ d / 16 * (n : ℝ)^r := by
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

lemma exists_almost_regular_graphs {W : Type*} (H : SimpleGraph W) {r : ℝ}
    (hr : 1 < r) (h : Erdos713Tight.HasTightRate H r) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ N : ℕ,
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
        N ≤ Fintype.card V ∧ 0 < Fintype.card V ∧ H.Free G ∧ G.IsBipartite ∧
        a * (Fintype.card V : ℝ)^r ≤ (Nat.card G.edgeSet : ℝ) ∧
        (∀ v, a * (Fintype.card V : ℝ)^(r-1) ≤ (Nat.card (G.neighborSet v) : ℝ) ∧
          (Nat.card (G.neighborSet v) : ℝ) ≤ b * (Fintype.card V : ℝ)^(r-1)) := by
  classical
  obtain ⟨a,b,ha,hb,hW⟩ := exists_almost_regular_witnesses H hr h
  let k : ℝ := b / (2*a)
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨a,b*k^(r-1),ha,mul_pos hb (Real.rpow_pos_of_pos hk _),?_⟩
  intro N
  obtain ⟨n,hn,hnpos,G,hFree,hBip,hE,hMin,hMax⟩ := hW ⌈k * (max N 1 : ℕ)⌉₊
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
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
      (Fintype.card V : ℝ) * (b * (n : ℝ)^(r-1)) := by
    have hh : (∑ v : V, (J.degree v : ℝ)) ≤ ∑ v : V, b * (n : ℝ)^(r-1) := by
      apply sum_le_sum
      intro v _
      simpa only [← card_neighborSet_eq_degree, Fintype.card_eq_nat_card, hJD] using hMax v.val
    simpa only [← Nat.cast_sum, sum_degrees_eq_twice_card_edges, edgeFinset_card,
      Fintype.card_eq_nat_card, Nat.cast_mul, Nat.cast_ofNat, sum_const, card_univ, nsmul_eq_mul] using hh
  have hPow : (n : ℝ)^r = (n : ℝ)^(r-1) * n := by
    calc
      _ = (n : ℝ)^((r-1)+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hnr, Real.rpow_one]
  have hnScale : (n : ℝ) ≤ k * Fintype.card V := by
    have hp : 0 < (n : ℝ)^(r-1) := Real.rpow_pos_of_pos hnr _
    rw [hJE] at hsum
    rw [hPow] at hE
    have hh : (n : ℝ)^(r-1) * (2*a*n) ≤ (n : ℝ)^(r-1) * (b * Fintype.card V) := by
      nlinarith
    have hcoeff := (mul_le_mul_iff_right₀ hp).mp hh
    dsimp only [k]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (show 0 < 2*a by positivity)).mpr
    nlinarith
  have hsize : max N 1 ≤ Fintype.card V := by
    have hlower : k * (max N 1 : ℕ) ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
    exact_mod_cast (mul_le_mul_iff_right₀ hk).mp (hlower.trans hnScale)
  have hJFree : H.Free J := fun hc => hFree (hc.trans ⟨Copy.induce G _⟩)
  have hJBip : J.IsBipartite := hBip.of_hom (Copy.induce G _).toHom
  refine ⟨V,inferInstance,J,(le_max_left _ _).trans hsize,
    lt_of_lt_of_le Nat.zero_lt_one ((le_max_right _ _).trans hsize),hJFree,hJBip,?_,?_⟩
  · rw [hJE]
    apply le_trans _ hE
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hcard) (le_trans zero_le_one hr.le)) ha.le
  · intro v
    rw [hJD]
    constructor
    · have hpos : 0 < Nat.card (G.neighborSet v.val) := by
        have hh := (G.degree_pos_iff_mem_support v.val).mpr v.prop
        simpa only [← card_neighborSet_eq_degree, Fintype.card_eq_nat_card] using hh
      have hd : a * (n : ℝ)^(r-1) ≤ (Nat.card (G.neighborSet v.val) : ℝ) :=
        (hMin v.val).resolve_left (Nat.ne_of_gt hpos)
      exact (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hcard) (sub_nonneg.mpr hr.le)) ha.le).trans hd
    · apply (hMax v.val).trans
      have hh := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg n) hnScale (sub_nonneg.mpr hr.le)) hb.le
      rw [Real.mul_rpow hk.le (Nat.cast_nonneg _)] at hh
      simpa only [mul_assoc] using hh

end Erdos713Regularization
