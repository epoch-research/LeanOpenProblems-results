import FormalConjecturesUtil
import Submission.ExpanderPruning

/-! Almost-regular bipartite expanders below an extremal power threshold. -/
open Filter SimpleGraph Asymptotics Finset
namespace Erdos713ExpandingRegularization
universe u
open Erdos713SwitchGluing Erdos713Expansion Erdos713ExpanderPruning
set_option maxHeartbeats 1000000

lemma cross_singleton_card {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) :
    Nat.card (cross G {v}).edgeSet = Nat.card (G.neighborSet v) := by
  classical
  have he : (cross G {v}).edgeFinset = G.incidenceFinset v := by
    ext e
    induction e using Sym2.inductionOn with
    | hf a b =>
      simp only [mem_edgeFinset,mem_incidenceFinset,mk'_mem_incidenceSet_iff,cross,Set.mem_singleton_iff]
      constructor
      · rintro ⟨hab,⟨ha,_⟩ | ⟨hb,_⟩⟩
        · exact ⟨hab,Or.inl ha.symm⟩
        · exact ⟨hab,Or.inr hb.symm⟩
      · rintro ⟨hab,ha | hb⟩
        · subst a
          exact ⟨hab,Or.inl ⟨rfl,hab.ne.symm⟩⟩
        · subst b
          exact ⟨hab,Or.inr ⟨rfl,hab.ne⟩⟩
  have hh := congrArg Finset.card he
  rw [card_incidenceFinset_eq_degree] at hh
  simpa only [edgeFinset_card,← card_neighborSet_eq_degree,Fintype.card_eq_nat_card] using hh

open scoped Classical in
lemma cut_induce_image {V : Type*} [Fintype V] (G : SimpleGraph V) (U : Finset V)
    (S : Finset U) :
    Nat.card (cross (G.induce (U : Set V)) (S : Set U)).edgeSet =
      Nat.card (cross (inside G (U : Set V)) ((S.image Subtype.val : Finset V) : Set V)).edgeSet := by
  classical
  let f : U ↪ V := Function.Embedding.subtype (fun v => v ∈ U)
  have hm (a : U) : a.val ∈ S.image Subtype.val ↔ a ∈ S := by
    simp only [mem_image,Subtype.val_inj,exists_eq_right]
  have he : (cross (G.induce (U : Set V)) (S : Set U)).map f =
      cross (inside G (U : Set V)) ((S.image Subtype.val : Finset V) : Set V) := by
    ext u v
    rw [map_adj]
    constructor
    · rintro ⟨a,b,hab,rfl,rfl⟩
      change G.Adj a.val b.val ∧ ((a ∈ S ∧ b ∉ S) ∨ (b ∈ S ∧ a ∉ S)) at hab
      change (G.Adj a.val b.val ∧ a.val ∈ U ∧ b.val ∈ U) ∧
        ((a.val ∈ S.image Subtype.val ∧ b.val ∉ S.image Subtype.val) ∨
          (b.val ∈ S.image Subtype.val ∧ a.val ∉ S.image Subtype.val))
      simpa only [hm] using And.intro ⟨hab.1,a.prop,b.prop⟩ hab.2
    · rintro ⟨⟨huv,hu,hv⟩,hab⟩
      let a : U := ⟨u,hu⟩
      let b : U := ⟨v,hv⟩
      refine ⟨a,b,?_,rfl,rfl⟩
      change G.Adj u v ∧ ((a ∈ S ∧ b ∉ S) ∨ (b ∈ S ∧ a ∉ S))
      exact ⟨huv,by simpa only [← hm a,← hm b] using hab⟩
  have hc := card_edgeFinset_map f (cross (G.induce (U : Set V)) (S : Set U))
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hc
  rw [he] at hc
  exact hc.symm

lemma degree_induce_le {V : Type*} [Fintype V] (G : SimpleGraph V) (U : Finset V) (v : U) :
    Nat.card ((G.induce (U : Set V)).neighborSet v) ≤ Nat.card (G.neighborSet v.val) := by
  let f := (Copy.induce G (U : Set V)).mapNeighborSet v
  exact Nat.card_le_card_of_injective f f.injective


lemma local_regular_expander {W : Type*} (H : SimpleGraph W) {r C : ℝ} (hr : 1 < r) (hC : 0 < C)
    (n L : ℕ) (hn : 4 ≤ n) (hL : 0 < L) (hnL : L ≤ n)
    (hSmall : (L : ℝ)*(3/(L : ℝ))^r ≤ expansionConstant r/32)
    (hRecord : (extremalNumber n H : ℝ) = C*(n : ℝ)^r)
    (hUpper : ∀ j : ℕ, j ≤ n → (extremalNumber j H : ℝ) ≤ C*(j : ℝ)^r) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      n ≤ 2*Fintype.card V ∧ Fintype.card V ≤ n ∧ 2 ≤ Fintype.card V ∧ H.Free G ∧ G.IsBipartite ∧
      (∀ v, expansionConstant r*C/8*(n : ℝ)^(r-1) ≤ (Nat.card (G.neighborSet v) : ℝ) ∧
        (Nat.card (G.neighborSet v) : ℝ) ≤ 2*C*L*(n : ℝ)^(r-1)) ∧
      (∀ S : Finset V, 2*S.card ≤ Fintype.card V →
        expansionConstant r*C/8*(n : ℝ)^(r-1)*S.card ≤
          (Nat.card (cross G (S : Set V)).edgeSet : ℝ)) := by
  classical
  have hk := expansionConstant_pos hr
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hPow : (n : ℝ)^r = (n : ℝ)^(r-1)*n := by
    rw [rpow_factor hnr.le hr]; ring
  have hepos : 0 < extremalNumber n H := by
    have hh : (0 : ℝ) < extremalNumber n H := by rw [hRecord]; positivity
    exact_mod_cast hh
  obtain ⟨X,hXFree,hXE⟩ := Erdos713SharpDegree.exists_extremal_of_pos H n hepos
  obtain ⟨B,hBX,hBip,_,hBCuts⟩ := exists_bipartite_all_cuts X
  have hBFree : H.Free B := fun hc => hXFree (hc.trans ⟨Copy.ofLE _ _ hBX⟩)
  let h : ℝ := expansionConstant r*C/2*(n : ℝ)^(r-1)
  have hh : 0 < h := by dsimp [h]; positivity
  have hBExp (S : Finset (Fin n)) (hS : 2*S.card ≤ n) :
      h*S.card ≤ (Nat.card (cross B (S : Set (Fin n))).edgeSet : ℝ) := by
    have hOrig := record_cut_bound H X hXFree hr hC.le
      (by simpa only [Fintype.card_fin,hXE] using hRecord)
      (by simpa only [Fintype.card_fin] using hUpper) S
      (by simpa only [Fintype.card_fin] using hS)
    simp only [Fintype.card_fin] at hOrig
    have hHalf : (Nat.card (cross X (S : Set (Fin n))).edgeSet : ℝ) ≤
        2*(Nat.card (cross B (S : Set (Fin n))).edgeSet : ℝ) := by exact_mod_cast hBCuts S
    dsimp only [h]
    nlinarith
  have hSmallC : (L : ℝ)*C*(3/(L : ℝ))^r ≤ (expansionConstant r*C/4)/8 := by
    nlinarith [mul_le_mul_of_nonneg_left hSmall hC.le]
  obtain ⟨K,hKB,hLoss,hDeg⟩ := Erdos713RateRegularization.trim_high_degrees_local H B hBFree hC
    (by linarith) (by simpa only [Fintype.card_fin] using hUpper) L hL
    (by simpa only [Fintype.card_fin] using hnL) hSmallC
  simp only [Fintype.card_fin] at hLoss hDeg
  have hLoss' : (Nat.card B.edgeSet : ℝ) ≤ Nat.card K.edgeSet +
      expansionConstant r*C/32*(n : ℝ)^r := by
    simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hLoss
    convert hLoss using 1 <;> ring
  have hSmall' : expansionConstant r*C/32*(n : ℝ)^r ≤ h*(Fintype.card (Fin n) : ℝ)/16 := by
    simp only [Fintype.card_fin]
    dsimp only [h]
    rw [hPow]
    exact le_of_eq (by ring)
  obtain ⟨U,hUsmall,hCuts⟩ := exists_pruned_expander B K hKB hh
    (by simpa only [Fintype.card_fin] using hBExp) hLoss' hSmall'
  simp only [Fintype.card_fin] at hUsmall hCuts
  let V := (Uᶜ : Finset (Fin n))
  let J := K.induce (V : Set (Fin n))
  have hCard : Fintype.card V = n-U.card := by
    rw [Fintype.card_coe,card_compl,Fintype.card_fin]
  have hVbig : n ≤ 2*Fintype.card V := by rw [hCard]; omega
  have hVle : Fintype.card V ≤ n := by rw [hCard]; omega
  have hVtwo : 2 ≤ Fintype.card V := by omega
  have hJFree : H.Free J := fun hc => hBFree
    (hc.trans ((show J ⊑ K from ⟨Copy.induce K _⟩).trans ⟨Copy.ofLE _ _ hKB⟩))
  have hJBip : J.IsBipartite := hBip.of_hom
    ((Copy.ofLE _ _ hKB).comp (Copy.induce K _)).toHom
  have hJCuts (S : Finset V) (hS : 2*S.card ≤ Fintype.card V) :
      expansionConstant r*C/8*(n : ℝ)^(r-1)*S.card ≤
        (Nat.card (cross J (S : Set V)).edgeSet : ℝ) := by
    let T : Finset (Fin n) := S.image Subtype.val
    have hTcard : T.card = S.card := card_image_of_injective S Subtype.val_injective
    have hTsub : T ⊆ Uᶜ := by
      intro v hv
      obtain ⟨w,_,rfl⟩ := mem_image.mp hv
      exact w.prop
    have hTsize : 2*T.card ≤ n-U.card := by rw [hTcard,← hCard]; exact hS
    have hc := hCuts T (by simpa only [← coe_subset,coe_compl] using hTsub) hTsize
    dsimp only [J]
    rw [cut_induce_image]
    dsimp only [h] at hc
    rw [hTcard] at hc
    simp only [coe_compl] at hc
    have heq : (V : Set (Fin n)) = (U : Set (Fin n))ᶜ := by simp [V]
    rw [heq]
    dsimp only [T] at hc
    simp only [coe_image] at hc ⊢
    nlinarith
  refine ⟨V,inferInstance,J,hVbig,hVle,hVtwo,hJFree,hJBip,?_,hJCuts⟩
  intro v
  constructor
  · have hs := hJCuts {v} (by simpa using hVtwo)
    simpa only [card_singleton,Nat.cast_one,mul_one,coe_singleton,cross_singleton_card] using hs
  · have hle := degree_induce_le K V v
    have hd := hDeg v.val
    simp only [← card_neighborSet_eq_degree,Fintype.card_eq_nat_card] at hd
    exact (Nat.cast_le.mpr hle).trans hd

lemma exists_regular_expanders {W : Type*} (H : SimpleGraph W) {r : ℝ} (hr : 1 < r)
    (hLarge : ∀ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      C * (n : ℝ)^r < (extremalNumber n H : ℝ)) :
    ∃ R : ℝ, 0 < R ∧ ∀ A : ℝ, 0 < A → ∀ N : ℕ,
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (d : ℝ),
        N ≤ Fintype.card V ∧ 2 ≤ Fintype.card V ∧ H.Free G ∧ G.IsBipartite ∧
        A*(Fintype.card V : ℝ)^r ≤ (Nat.card G.edgeSet : ℝ) ∧
        0 < d ∧ A*(Fintype.card V : ℝ)^(r-1) ≤ d ∧
        (∀ v, d ≤ (Nat.card (G.neighborSet v) : ℝ) ∧ (Nat.card (G.neighborSet v) : ℝ) ≤ R*d) ∧
        (∀ S : Finset V, 2*S.card ≤ Fintype.card V →
          d*S.card ≤ (Nat.card (cross G (S : Set V)).edgeSet : ℝ)) := by
  classical
  have hk := expansionConstant_pos hr
  obtain ⟨L,hL,hSmall⟩ := Erdos713Regularization.exists_partition_size
    (r := r) (d := expansionConstant r/4) (C := 1) hr (by positivity) (by norm_num)
  simp only [mul_one] at hSmall
  have hSmall' : (L : ℝ)*(3/(L : ℝ))^r ≤ expansionConstant r/32 := by convert hSmall using 1 <;> ring
  refine ⟨16*L/expansionConstant r,by positivity,?_⟩
  intro A hA N
  obtain ⟨n,hn,hnpos,C,hC,hRecord,hUpper⟩ := Erdos713RateRegularization.exists_record H (by linarith)
    hLarge (max (max (2*N) 4) L) (16*(A+1)/expansionConstant r) (by positivity)
  have hnN : 2*N ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn4 : 4 ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnL : L ≤ n := (le_max_right _ _).trans hn
  have hCpos : 0 < C := (by positivity : 0 < 16*(A+1)/expansionConstant r).trans hC
  obtain ⟨V,instV,G,hVbig,hVle,hVtwo,hFree,hBip,hDeg,hCuts⟩ :=
    local_regular_expander H hr hCpos n L hn4 hL hnL hSmall' hRecord hUpper
  let d : ℝ := expansionConstant r*C/8*(n : ℝ)^(r-1)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hvr : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hd : 0 < d := by dsimp [d]; positivity
  have hCA : 2*A ≤ expansionConstant r*C/8 := by
    have hh := (div_lt_iff₀ hk).mp hC
    nlinarith
  have hD : 2*A*(Fintype.card V : ℝ)^(r-1) ≤ d := by
    exact mul_le_mul hCA
      (Real.rpow_le_rpow hvr.le (Nat.cast_le.mpr hVle) (by linarith))
      (Real.rpow_nonneg hvr.le _) (by positivity)
  have hEdges : d*(Fintype.card V : ℝ) ≤ 2*(Nat.card G.edgeSet : ℝ) := by
    have he := sum_le_sum (s := (univ : Finset V)) (fun v _ => (hDeg v).1)
    simpa only [← card_neighborSet_eq_degree,Fintype.card_eq_nat_card] using (show
        d*(Fintype.card V : ℝ) ≤ 2*(Nat.card G.edgeSet : ℝ) from by
      simp only [sum_const,card_univ,nsmul_eq_mul] at he
      have hs := G.sum_degrees_eq_twice_card_edges
      have hs' : (∑ v : V, (Nat.card (G.neighborSet v) : ℝ)) = 2*(Nat.card G.edgeSet : ℝ) := by
        exact_mod_cast (by simpa only [← card_neighborSet_eq_degree,edgeFinset_card,
          Fintype.card_eq_nat_card] using hs)
      rw [hs'] at he
      dsimp only [d]
      nlinarith)
  refine ⟨V,instV,G,d,by omega,hVtwo,hFree,hBip,?_,hd,?_,?_,hCuts⟩
  · have hh := mul_le_mul_of_nonneg_right hD hvr.le
    rw [rpow_factor hvr.le hr]
    nlinarith
  · have hp : 0 ≤ A*(Fintype.card V : ℝ)^(r-1) := by positivity
    nlinarith
  · intro v
    refine ⟨(hDeg v).1,((hDeg v).2).trans ?_⟩
    dsimp only [d]
    exact le_of_eq (by field_simp; ring)

lemma of_rate {W : Type*} (H : SimpleGraph W) {α r : ℝ}
    (h : Erdos713Rate.HasRate H α) (hr : 1 < r) (hrα : r < α) :
    ∃ R : ℝ, 0 < R ∧ ∀ A : ℝ, 0 < A → ∀ N : ℕ,
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (d : ℝ),
        N ≤ Fintype.card V ∧ 2 ≤ Fintype.card V ∧ H.Free G ∧ G.IsBipartite ∧
        A*(Fintype.card V : ℝ)^r ≤ (Nat.card G.edgeSet : ℝ) ∧
        0 < d ∧ A*(Fintype.card V : ℝ)^(r-1) ≤ d ∧
        (∀ v, d ≤ (Nat.card (G.neighborSet v) : ℝ) ∧ (Nat.card (G.neighborSet v) : ℝ) ≤ R*d) ∧
        (∀ S : Finset V, 2*S.card ≤ Fintype.card V →
          d*S.card ≤ (Nat.card (cross G (S : Set V)).edgeSet : ℝ)) :=
  exists_regular_expanders H hr
    (Erdos713PowerCritical.exists_lower_above_smaller_power h hr.le hrα)

lemma robust_of_rate {W : Type u} [Fintype W] (H : SimpleGraph W) {α β γ : ℝ}
    (hRate : Erdos713Rate.HasRate H α) (hβ : 1 ≤ β) (hβγ : β < γ) (hγα : γ < α)
    (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (hProper : ∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H →
      ¬ Nonempty (J ≃g H) →
      (fun n : ℕ => (extremalNumber n J : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^β)) :
    ∃ R : ℝ, 0 < R ∧ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (d : ℝ),
        N ≤ Fintype.card V ∧ 2 ≤ Fintype.card V ∧ H.Free G ∧ G.IsBipartite ∧
        (Fintype.card V : ℝ)^γ ≤ (Nat.card G.edgeSet : ℝ) ∧
        0 < d ∧ (Fintype.card V : ℝ)^(γ-1) ≤ d ∧
        (∀ v, d ≤ (Nat.card (G.neighborSet v) : ℝ) ∧
          (Nat.card (G.neighborSet v) : ℝ) ≤ R*d) ∧
        (∀ S : Finset V, 2*S.card ≤ Fintype.card V →
          d*S.card ≤ (Nat.card (cross G (S : Set V)).edgeSet : ℝ)) ∧
        (∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → ¬ Nonempty (J ≃g H) →
          ∀ F : SimpleGraph V, ε * (Nat.card G.edgeSet : ℝ) ≤ (Nat.card F.edgeSet : ℝ) → J ⊑ F) := by
  classical
  obtain ⟨C,hC,hUpper⟩ := Erdos713RateRegularization.uniform_proper_constant H (lt_of_lt_of_le zero_lt_one hβ) hNoIso hProper
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
  obtain ⟨V,instV,G,d,hN,hpos,hFree,hBip,hE,hd,hD,hDeg,hCuts⟩ := hReg A hA N
  have hnr : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hnone : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hpow : (Fintype.card V : ℝ)^β ≤ (Fintype.card V : ℝ)^γ :=
    Real.rpow_le_rpow_of_exponent_le hnone hβγ.le
  refine ⟨V,instV,G,d,hN,hpos,hFree,hBip,?_,hd,?_,hDeg,hCuts,?_⟩
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

#print axioms robust_of_rate

#print axioms of_rate

end Erdos713ExpandingRegularization
