import FormalConjecturesUtil
import Submission.BipartiteExtremal
import Submission.WeakPowerRecords

/-! Joint witnesses extremal among bipartite H-free graphs. They need not be
ordinary exact extremal graphs, and no exact asymptotic for the bipartite
extremal number is inferred. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713BipExtremal
open Erdos713Cloning Erdos713SwitchGluing

lemma mass_bound {W : Type*} (H : SimpleGraph W) {n : ℕ} (G : SimpleGraph (Fin n))
    (hfree : H.Free G) (hB : G.IsBipartite) (he : Nat.card G.edgeSet = number n H)
    {s : ℝ} (hs : 0 ≤ s)
    (hinc : (n : ℝ)*((number (n+1) H : ℝ)-(number n H : ℝ)) ≤
      s*(number n H : ℝ)) :
    ∃ B : Finset (Fin n), (∀ v ∈ B, SingleFold H G v) ∧
      (2-s)*(Nat.card G.edgeSet : ℝ) ≤ ∑ v ∈ B, (Nat.card (G.neighborSet v) : ℝ) := by
  classical
  let D : ℝ := max ((number (n+1) H : ℝ)-(number n H : ℝ)) 0
  have hD : 0 ≤ D := le_max_right _ _
  have hBD : (n : ℝ)*D ≤ s*(Nat.card G.edgeSet : ℝ) := by
    rw [he]
    by_cases hd : 0 ≤ (number (n+1) H : ℝ)-(number n H : ℝ)
    · simpa only [D,max_eq_left hd] using hinc
    · have hd' : (number (n+1) H : ℝ)-(number n H : ℝ) ≤ 0 := le_of_not_ge hd
      simp only [D,max_eq_right hd',mul_zero]
      positivity
  let B : Finset (Fin n) := univ.filter (SingleFold H G)
  refine ⟨B,fun v hv => (mem_filter.mp hv).2,?_⟩
  have hlocal (v : Fin n) : (Nat.card (G.neighborSet v) : ℝ) ≤
      (if SingleFold H G v then (Nat.card (G.neighborSet v) : ℝ) else 0)+D := by
    by_cases hv : SingleFold H G v
    · simp only [if_pos hv]
      linarith
    · have hc : H.Free (clone G v) := fun hh => hv (fold_of_obstructed H G v hfree hh)
      have hh := safe_clone_bound H G hB v hc
      simp only [Fintype.card_fin] at hh
      have hh' : (Nat.card G.edgeSet : ℝ)+(Nat.card (G.neighborSet v) : ℝ) ≤
          (number (n+1) H : ℝ) := by exact_mod_cast hh
      rw [he] at hh'
      have hle : (number (n+1) H : ℝ)-(number n H : ℝ) ≤ D := le_max_left _ _
      simp only [if_neg hv,zero_add]
      linarith
  have hsum := sum_le_sum (fun v (_ : v ∈ (univ : Finset (Fin n))) => hlocal v)
  rw [sum_add_distrib] at hsum
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hsumdeg : (∑ v : Fin n, (Nat.card (G.neighborSet v) : ℝ)) = 2*(Nat.card G.edgeSet : ℝ) := by
    have hh := G.sum_degrees_eq_twice_card_edges
    simp only [← card_neighborSet_eq_degree,edgeFinset_card,Fintype.card_eq_nat_card] at hh
    exact_mod_cast hh
  have hBsum : (∑ v : Fin n, if SingleFold H G v then (Nat.card (G.neighborSet v) : ℝ) else 0) =
      ∑ v ∈ B, (Nat.card (G.neighborSet v) : ℝ) := by simp only [B,sum_filter]
  rw [hsumdeg,hBsum] at hsum
  linarith

open scoped Classical in
lemma inside_edges_le {W V : Type*} [Fintype V] (H : SimpleGraph W)
    (G : SimpleGraph V) (hFree : H.Free G) (hB : G.IsBipartite) (S : Finset V) :
    Nat.card (inside G (S : Set V)).edgeSet ≤ number S.card H := by
  classical
  have heq : inside G (S : Set V) = (G.induce (S : Set V)).spanningCoe := by
    ext u v
    constructor
    · rintro ⟨h,hu,hv⟩
      exact ⟨⟨u,hu⟩,⟨v,hv⟩,h,rfl,rfl⟩
    · rintro ⟨a,b,h,rfl,rfl⟩
      exact ⟨h,a.property,b.property⟩
  rw [heq]
  have hmap := card_edgeFinset_map (Function.Embedding.subtype (fun v => v ∈ (S : Set V)))
    (G.induce (S : Set V))
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hmap
  rw [hmap]
  have hf : H.Free (G.induce (S : Set V)) := fun h => hFree (h.trans ⟨Copy.induce G _⟩)
  have hc : Nat.card (S : Set V) = S.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe S
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card,hc] using
    card_bound H (G.induce (S : Set V)) hf (hB.of_hom (Copy.induce G _).toHom)

lemma edges_le_parts_and_cut {W V : Type*} [Fintype V] (H : SimpleGraph W)
    (G : SimpleGraph V) (hFree : H.Free G) (hB : G.IsBipartite) (S : Finset V) :
    Nat.card G.edgeSet ≤ number S.card H + number (Fintype.card V-S.card) H +
      Nat.card (cross G (S : Set V)).edgeSet := by
  classical
  have hRest : Erdos713Gluing.rest G (S : Set V) = inside G ((Sᶜ : Finset V) : Set V) := by
    ext u v
    simp [Erdos713Gluing.rest,inside]
  have hA := inside_edges_le H G hFree hB S
  have hB := inside_edges_le H G hFree hB Sᶜ
  rw [card_compl] at hB
  have hsplit := edge_split G (S : Set V)
  rw [hRest] at hsplit
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hsplit
  omega

lemma record_cut_bound {W V : Type*} [Fintype V] (H : SimpleGraph W)
    (G : SimpleGraph V) (hFree : H.Free G) (hB : G.IsBipartite) {r C : ℝ} (hr : 1 < r) (hC : 0 ≤ C)
    (hEdges : (Nat.card G.edgeSet : ℝ) = C*(Fintype.card V : ℝ)^r)
    (hUpper : ∀ j : ℕ, j ≤ Fintype.card V → (number j H : ℝ) ≤ C*(j : ℝ)^r)
    (S : Finset V) (hS : 2*S.card ≤ Fintype.card V) :
    expansionConstant r * C * S.card * (Fintype.card V : ℝ)^(r-1) ≤
      (Nat.card (cross G (S : Set V)).edgeSet : ℝ) := by
  classical
  have hs : S.card ≤ Fintype.card V := card_le_univ S
  have he : (Nat.card G.edgeSet : ℝ) ≤ (number S.card H : ℝ) +
      (number (Fintype.card V-S.card) H : ℝ) +
        (Nat.card (cross G (S : Set V)).edgeSet : ℝ) := by
    exact_mod_cast edges_le_parts_and_cut H G hFree hB S
  have hA := hUpper S.card hs
  have hB := hUpper (Fintype.card V-S.card) (Nat.sub_le _ _)
  rw [Nat.cast_sub hs] at hB
  have hp := mul_le_mul_of_nonneg_left
    (power_gap (Nat.cast_nonneg (Fintype.card V)) (Nat.cast_nonneg S.card)
      (by exact_mod_cast hS) hr) hC
  rw [hEdges] at he
  nlinarith


lemma degree_lower_of_record {W : Type*} (H : SimpleGraph W) {n : ℕ}
    (G : SimpleGraph (Fin n)) (hfree : H.Free G) (hB : G.IsBipartite)
    (he : Nat.card G.edgeSet = number n H)
    {r C : ℝ} (hEq : (Nat.card G.edgeSet : ℝ) = C*(n : ℝ)^r)
    (hUpper : ∀ j : ℕ, j ≤ n → (number j H : ℝ) ≤ C*(j : ℝ)^r) (v : Fin n) :
    C*((n : ℝ)^r-((n-1 : ℕ) : ℝ)^r) ≤ (Nat.card (G.neighborSet v) : ℝ) := by
  classical
  have hf : H.Free (G.induce {v}ᶜ) := fun hh => hfree (hh.trans ⟨Copy.induce G _⟩)
  have hb : (G.induce {v}ᶜ).IsBipartite := hB.of_hom (Copy.induce G _).toHom
  have hDel := card_bound H (G.induce {v}ᶜ) hf hb
  have hcard : Fintype.card ({v}ᶜ : Set (Fin n)) = n-1 := by
    change Fintype.card {w : Fin n // ¬ w = v} = n-1
    rw [Fintype.card_subtype_compl]
    simp
  have hi := G.card_edgeFinset_induce_compl_singleton v
  have hd := G.card_edgeFinset_deleteIncidenceSet v
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hi hd
  rw [hi,hd,hcard] at hDel
  have hNat : Nat.card G.edgeSet ≤ number (n-1) H + G.degree v := by
    have hh := G.degree_le_card_edgeFinset v
    simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hh
    omega
  simp only [← card_neighborSet_eq_degree,Fintype.card_eq_nat_card,he] at hNat
  have hReal : (number n H : ℝ) ≤ (number (n-1) H : ℝ) +
      (Nat.card (G.neighborSet v) : ℝ) := by exact_mod_cast hNat
  have hh := hUpper (n-1) (Nat.sub_le _ _)
  rw [he] at hEq
  nlinarith

lemma bipartite_identified_copy {W V : Type*} {H : SimpleGraph W} {G : SimpleGraph V} {v : V}
    (hG : G.IsBipartite) (h : SingleFold H G v) :
    ∃ a b : W, ∃ hab : a ≠ b, ∃ hnab : ¬ H.Adj a b,
      (identified H a b hnab).IsBipartite ∧
      ∃ f : (identified H a b hnab).Copy G, f ⟨b,hab.symm⟩ = v := by
  obtain ⟨a,b,hab,hnab,f,hf⟩ := h.identified_copy
  exact ⟨a,b,hab,hnab,hG.of_hom f.toHom,f,hf⟩

lemma joint_of_asymptotic {W : Type*} (H : SimpleGraph W) {α c r s : ℝ}
    (hr : 1 < r) (hra : r < α) (has : α < s) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ∃ C : ℝ, 0 < C ∧ ∃ G : SimpleGraph (Fin n),
      H.Free G ∧ G.IsBipartite ∧ Nat.card G.edgeSet = number n H ∧
      extremalNumber n H ≤ 2*Nat.card G.edgeSet ∧
      (Nat.card G.edgeSet : ℝ) = C*(n : ℝ)^r ∧
      (∀ j : ℕ, j ≤ n → (number j H : ℝ) ≤ C*(j : ℝ)^r) ∧
      (∀ v, C*((n : ℝ)^r-((n-1 : ℕ) : ℝ)^r) ≤ (Nat.card (G.neighborSet v) : ℝ)) ∧
      (∀ S : Finset (Fin n), 2*S.card ≤ n →
        expansionConstant r*C*S.card*(n : ℝ)^(r-1) ≤
          (Nat.card (cross G (S : Set (Fin n))).edgeSet : ℝ)) ∧
      ∃ B : Finset (Fin n), (∀ v ∈ B, SingleFold H G v) ∧
        (2-s)*(Nat.card G.edgeSet : ℝ) ≤ ∑ v ∈ B, (Nat.card (G.neighborSet v) : ℝ) := by
  obtain ⟨t,hat,hts⟩ := exists_between has
  obtain ⟨n,hn,hnp,hpos,hpast,hinc⟩ :=
    Erdos713FutureRecords.small_increment_with_past_of_limits (hra.trans hat) (by linarith) hts
      (lower_ratio_top H hra hc h) (higher_ratio_zero H hat h) N
  have hnpR : (0 : ℝ) < n := by exact_mod_cast hnp
  have hpos' : 0 < number n H := by exact_mod_cast hpos
  let C : ℝ := (number n H : ℝ)/(n : ℝ)^r
  have hC : 0 < C := div_pos hpos (Real.rpow_pos_of_pos hnpR r)
  have hEq : (number n H : ℝ) = C*(n : ℝ)^r :=
    (div_mul_cancel₀ _ (Real.rpow_pos_of_pos hnpR r).ne').symm
  have hUpper : ∀ j : ℕ, j ≤ n → (number j H : ℝ) ≤ C*(j : ℝ)^r := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp [number_zero,Real.zero_rpow (by linarith : r ≠ 0)]
    · exact (div_le_iff₀ (Real.rpow_pos_of_pos (show (0 : ℝ) < j by exact_mod_cast Nat.pos_of_ne_zero hj0) r)).mp
        (hpast j (Nat.pos_of_ne_zero hj0) hj)
  obtain ⟨G,hfree,hB,he⟩ := exists_extremal_of_pos H n hpos'
  have hEqG : (Nat.card G.edgeSet : ℝ) = C*(n : ℝ)^r := by rwa [he]
  refine ⟨n,hn,hnp,C,hC,G,hfree,hB,he,by simpa only [he] using ordinary_le_two H n,
    hEqG,hUpper,degree_lower_of_record H G hfree hB he hEqG hUpper,?_,
    mass_bound H G hfree hB he (by linarith) hinc⟩
  intro S hS
  simpa only [Fintype.card_fin] using record_cut_bound H G hfree hB hr hC.le
    (by simpa only [Fintype.card_fin] using hEqG)
    (by simpa only [Fintype.card_fin] using hUpper) S
    (by simpa only [Fintype.card_fin] using hS)

#print axioms mass_bound
#print axioms record_cut_bound
#print axioms degree_lower_of_record
#print axioms bipartite_identified_copy
#print axioms joint_of_asymptotic
end Erdos713BipExtremal
