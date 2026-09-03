import Submission.EdgeAveraging

/-!
Positive-density extraction from fractional covers, with an exact converse
for transitive finite group actions. The sets in the cover must ALREADY
satisfy the desired global property. No such cover of norm-graph edges is
constructed here, and this file does not settle Erdős Problem 714.
-/
noncomputable section
open Classical Finset
set_option maxHeartbeats 2000000
namespace Erdos714Fractional

variable {E I : Type*} [Fintype E] [Fintype I]

/-- Weighted incidence counting, with every incidence counted on both sides. -/
lemma weighted_count (B : I → Finset E) (w : I → ℝ) :
    (∑ i, w i*(B i).card) = ∑ e : E, ∑ i : I, if e ∈ B i then w i else 0 := by
  calc
    _ = ∑ i : I, ∑ e : E, if e ∈ B i then w i else 0 := by
      apply sum_congr rfl
      intro i _
      simp [mul_comm]
    _ = _ := sum_comm

/-- A fractional cover of mass at most D contains a block of density at least
1/D. No integrality or equality of the weights is assumed. -/
theorem extract_dense [Nonempty I] (B : I → Finset E) (w : I → ℝ) (D : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hcover : ∀ e : E, 1 ≤ ∑ i, if e ∈ B i then w i else 0)
    (hmass : ∑ i, w i ≤ D) :
    ∃ i, (Fintype.card E : ℝ) ≤ D*(B i).card := by
  obtain ⟨i,_,hi⟩ := exists_max_image (univ : Finset I) (fun i => (B i).card) univ_nonempty
  have hcount : (Fintype.card E : ℝ) ≤ ∑ j, w j*(B j).card := by
    rw [weighted_count]
    calc
      _ = ∑ _e : E, (1 : ℝ) := by simp
      _ ≤ _ := sum_le_sum (fun e _ => hcover e)
  refine ⟨i,?_⟩
  calc
    _ ≤ ∑ j, w j*(B j).card := hcount
    _ ≤ ∑ j, w j*(B i).card := by
      apply sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hi j (mem_univ _))) (hw j)
    _ = (∑ j, w j)*(B i).card := (sum_mul _ _ _).symm
    _ ≤ D*(B i).card := mul_le_mul_of_nonneg_right hmass (by positivity)

/-- The selected block retains whatever global property every block has. -/
theorem extract_property [Nonempty I] (P : Finset E → Prop)
    (B : I → Finset E) (w : I → ℝ) (D : ℝ)
    (hP : ∀ i, P (B i)) (hw : ∀ i, 0 ≤ w i)
    (hcover : ∀ e : E, 1 ≤ ∑ i, if e ∈ B i then w i else 0)
    (hmass : ∑ i, w i ≤ D) :
    ∃ S : Finset E, P S ∧ (Fintype.card E : ℝ) ≤ D*S.card := by
  obtain ⟨i,hi⟩ := extract_dense B w D hw hcover hmass
  exact ⟨B i,hP i,hi⟩

variable {Γ : Type*} [Group Γ] [Fintype Γ]
open Erdos714Averaging

/-- Translates of one nonempty set give an exact positive uniform cover. -/
theorem translated_cover [Nonempty E] (ρ : Γ →* Equiv.Perm E)
    (htrans : ∀ x y : E, ∃ g, ρ g x=y)
    (S : Finset E) (hS : S.Nonempty) :
    ∃ m : ℕ, 0 < m ∧
      (∀ e : E, (univ.filter (fun g => e ∈ translate ρ g S)).card=m) ∧
      Fintype.card Γ*S.card=Fintype.card E*m := by
  let x : E := Classical.choice ‹Nonempty E›
  let m := (univ.filter (fun g => x ∈ translate ρ g S)).card
  have hm : 0 < m := by
    obtain ⟨s,hs⟩ := hS
    obtain ⟨g,hg⟩ := htrans s x
    apply card_pos.mpr
    refine ⟨g,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    rw [mem_translate,← hg,Equiv.symm_apply_apply]
    exact hs
  have he (e : E) : (univ.filter (fun g => e ∈ translate ρ g S)).card=m :=
    coverage_eq ρ S e x (htrans e x)
  refine ⟨m,hm,he,?_⟩
  have h := count_selected (translate ρ · S) (univ : Finset E)
  simpa only [filter_mem_eq_inter,univ_inter,card_translate,he,sum_const,
    card_univ,nsmul_eq_mul] using h

/-- Normalized translates give a fractional cover whose mass is exactly
|E|/|S|, not a claim about the number of colors in an integral coloring. -/
theorem fractional_translates [Nonempty E] (ρ : Γ →* Equiv.Perm E)
    (htrans : ∀ x y : E, ∃ g, ρ g x=y) (S : Finset E) (hS : S.Nonempty) :
    ∃ w : Γ → ℝ, (∀ g, 0 ≤ w g) ∧
      (∀ e : E, (∑ g, if e ∈ translate ρ g S then w g else 0)=1) ∧
      (∑ g, w g)=(Fintype.card E : ℝ)/S.card := by
  obtain ⟨m,hm,hcover,hcount⟩ := translated_cover ρ htrans S hS
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs0 : (0 : ℝ) < S.card := by exact_mod_cast card_pos.mpr hS
  refine ⟨fun _ => 1/(m : ℝ),fun _ => by positivity,?_,?_⟩
  · intro e
    rw [← sum_filter]
    simp only [sum_const,nsmul_eq_mul,hcover]
    field_simp
  · simp only [sum_const,card_univ,nsmul_eq_mul]
    rw [mul_one_div]
    apply (div_eq_div_iff (ne_of_gt hm0) (ne_of_gt hs0)).mpr
    exact_mod_cast hcount

/-- Exact positive-density criterion for any translate-invariant global
property. The fractional-cover side still requires all blocks to satisfy P. -/
theorem dense_iff_fractional_cover [Nonempty E] (ρ : Γ →* Equiv.Perm E)
    (htrans : ∀ x y : E, ∃ g, ρ g x=y) (P : Finset E → Prop)
    (hP : ∀ g S, P S → P (translate ρ g S)) (D : ℝ) :
    (∃ S : Finset E, P S ∧ (Fintype.card E : ℝ) ≤ D*S.card) ↔
    (∃ B : Γ → Finset E, ∃ w : Γ → ℝ,
      (∀ g, P (B g)) ∧ (∀ g, 0 ≤ w g) ∧
      (∀ e : E, 1 ≤ ∑ g, if e ∈ B g then w g else 0) ∧ ∑ g, w g ≤ D) := by
  constructor
  · rintro ⟨S,hPS,hsize⟩
    have hS : S.Nonempty := by
      by_contra h
      have hs : S=∅ := not_nonempty_iff_eq_empty.mp h
      have he : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
      simp only [hs,card_empty,Nat.cast_zero,mul_zero] at hsize
      linarith
    obtain ⟨w,hw,hcover,hmass⟩ := fractional_translates ρ htrans S hS
    refine ⟨(fun g => translate ρ g S),w,fun g => hP g S hPS,hw,fun e => (hcover e).ge,?_⟩
    rw [hmass]
    exact (div_le_iff₀ (by exact_mod_cast card_pos.mpr hS)).mpr hsize
  · rintro ⟨B,w,hBP,hw,hcover,hmass⟩
    exact extract_property P B w D hBP hw hcover hmass


section Graphs
open SimpleGraph Erdos714GraphAveraging
variable {V W : Type*} [Fintype V]

/-- A fractional cover by globally free spanning subgraphs supplies a dense
free spanning subgraph. Local freeness of small blocks would not suffice. -/
theorem graph_extract [Nonempty I] (F : SimpleGraph W) (G : SimpleGraph V)
    (H : I → SimpleGraph V) (w : I → ℝ) (D : ℝ)
    (hHG : ∀ i, H i ≤ G) (hfree : ∀ i, F.Free (H i)) (hw : ∀ i, 0 ≤ w i)
    (hcover : ∀ e : G.edgeSet, 1 ≤ ∑ i, if e.val ∈ (H i).edgeSet then w i else 0)
    (hmass : ∑ i, w i ≤ D) :
    ∃ K : SimpleGraph V, K ≤ G ∧ F.Free K ∧ (G.edgeFinset.card : ℝ) ≤ D*K.edgeFinset.card := by
  let B (i : I) := univ.filter (fun e : G.edgeSet => e.val ∈ (H i).edgeSet)
  obtain ⟨i,hi⟩ := extract_dense B w D hw (by simpa [B] using hcover) hmass
  refine ⟨H i,hHG i,hfree i,?_⟩
  simpa only [B,card_edgeSet,selected_edge_card (H i) G (hHG i)] using hi

local instance automorphismFintype (G : SimpleGraph V) : Fintype (G ≃g G) :=
  Fintype.ofInjective RelIso.toEquiv RelIso.toEquiv_injective

/-- The edge-set translate agrees with pulling the spanning graph back along
the inverse automorphism. -/
lemma translated_edge_membership (G H : SimpleGraph V) (g : G ≃g G) (e : G.edgeSet) :
    e ∈ translate (edgeAction G) g (univ.filter (fun e : G.edgeSet => e.val ∈ H.edgeSet)) ↔
      e.val ∈ (H.comap g.symm).edgeSet := by
  rw [mem_translate]
  simp only [mem_filter,mem_univ,true_and]
  change Sym2.map g.symm e.val ∈ H.edgeSet ↔ e.val ∈ (H.comap g.symm).edgeSet
  rcases e with ⟨e,he⟩
  induction e using Sym2.ind with
  | _ x y => rfl

/-- An edge-transitive host has a dense free spanning subgraph exactly when
it has a fractional cover by free spanning subgraphs of bounded total mass.
This supplies no existence assertion for either side. -/
theorem graph_dense_iff_fractional_cover (F : SimpleGraph W) (G : SimpleGraph V)
    [Nonempty G.edgeSet] (htrans : EdgeTransitive G) (D : ℝ) :
    (∃ H : SimpleGraph V, H ≤ G ∧ F.Free H ∧ (G.edgeFinset.card : ℝ) ≤ D*H.edgeFinset.card) ↔
    (∃ H : (G ≃g G) → SimpleGraph V, ∃ w : (G ≃g G) → ℝ,
      (∀ g, H g ≤ G) ∧ (∀ g, F.Free (H g)) ∧ (∀ g, 0 ≤ w g) ∧
      (∀ e : G.edgeSet, 1 ≤ ∑ g, if e.val ∈ (H g).edgeSet then w g else 0) ∧ ∑ g, w g ≤ D) := by
  constructor
  · rintro ⟨H,hHG,hfree,hsize⟩
    let S := univ.filter (fun e : G.edgeSet => e.val ∈ H.edgeSet)
    have hcard : S.card=H.edgeFinset.card := selected_edge_card H G hHG
    have hS : S.Nonempty := by
      apply card_pos.mp
      rw [hcard]
      by_contra! h
      have hz : H.edgeFinset.card=0 := by omega
      have hg : (0 : ℝ) < G.edgeFinset.card := by
        rw [← card_edgeSet]
        exact_mod_cast Fintype.card_pos
      simp only [hz,Nat.cast_zero,mul_zero] at hsize
      linarith
    obtain ⟨w,hw,hcover,hmass⟩ := fractional_translates (edgeAction G) htrans S hS
    refine ⟨(fun g => H.comap g.symm),w,?_,?_,hw,?_,?_⟩
    · intro g x y hxy
      have h := hHG hxy
      exact (g.symm.map_adj_iff).mp h
    · intro g
      exact free_comap F H g.symm.toEquiv.toEmbedding hfree
    · intro e
      have he := (hcover e).ge
      simpa only [S,translated_edge_membership] using he
    · rw [hmass,card_edgeSet,hcard]
      exact (div_le_iff₀ (by exact_mod_cast (show 0 < H.edgeFinset.card by
        rw [← hcard]; exact card_pos.mpr hS))).mpr hsize
  · rintro ⟨H,w,hHG,hfree,hw,hcover,hmass⟩
    exact graph_extract F G H w D hHG hfree hw hcover hmass

end Graphs

end Erdos714Fractional

#print axioms Erdos714Fractional.weighted_count
#print axioms Erdos714Fractional.extract_dense
#print axioms Erdos714Fractional.extract_property
#print axioms Erdos714Fractional.translated_cover
#print axioms Erdos714Fractional.fractional_translates
#print axioms Erdos714Fractional.dense_iff_fractional_cover

#print axioms Erdos714Fractional.graph_extract
#print axioms Erdos714Fractional.translated_edge_membership
#print axioms Erdos714Fractional.graph_dense_iff_fractional_cover
