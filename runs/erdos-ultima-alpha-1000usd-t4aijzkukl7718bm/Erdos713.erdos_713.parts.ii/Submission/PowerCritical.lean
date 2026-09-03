import FormalConjecturesUtil
import Submission.UpToCritical

/-! Power-critical cores with a uniform rational gap below their power threshold. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713PowerCritical
open Erdos713Rate Erdos713Critical
universe u

open scoped Classical in
lemma exists_power_critical_core {W : Type u} [Fintype W] (G : SimpleGraph W)
    {r : ℝ} (hr : 1 < r) (h : HasRate G r) :
    ∃ (U : Type u) (_ : Fintype U) (H : SimpleGraph U), H ⊑ G ∧ H.Connected ∧
      (∀ v, 2 ≤ Nat.card (H.neighborSet v)) ∧ HasRate H r ∧ Fintype.card U ≤ Fintype.card W ∧
      (∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → HasRate J r →
        Fintype.card U ≤ Fintype.card T) ∧
      (∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → HasRate J r → Nonempty (J ≃g H)) := by
  classical
  let P : ℕ → Prop := fun n => ∃ (U : Type u) (_ : Fintype U) (H : SimpleGraph U),
    H ⊑ G ∧ HasRate H r ∧ Fintype.card U = n
  have hP : ∃ n, P n := ⟨Fintype.card W, W, inferInstance, G, .refl _, h, rfl⟩
  obtain ⟨U₀, inst₀, H₀, hH₀G, hH₀R, hc₀⟩ := Nat.find_spec hP
  let Q : ℕ → Prop := fun m => ∃ (U : Type u) (_ : Fintype U) (H : SimpleGraph U),
    H ⊑ G ∧ HasRate H r ∧ Fintype.card U = Nat.find hP ∧ Nat.card H.edgeSet = m
  have hQ : ∃ m, Q m := ⟨Nat.card H₀.edgeSet, U₀, inst₀, H₀, hH₀G, hH₀R, hc₀, rfl⟩
  obtain ⟨U, instU, H, hHG, hHR, hcard, hecard⟩ := Nat.find_spec hQ
  have hMin (T : Type u) [Fintype T] (J : SimpleGraph T) (hJG : J ⊑ G) (hJR : HasRate J r) :
      Fintype.card U ≤ Fintype.card T := by
    rw [hcard]
    exact Nat.find_min' hP ⟨T, inferInstance, J, hJG, hJR, rfl⟩
  have hEdgeMin (T : Type u) [Fintype T] (J : SimpleGraph T) (hJH : J ⊑ H) (hJR : HasRate J r) :
      Nat.card H.edgeSet ≤ Nat.card J.edgeSet := by
    have hJcard : Fintype.card T = Nat.find hP := by
      exact (le_antisymm (card_le_of_contained hJH) (hMin T J (hJH.trans hHG) hJR)).trans hcard
    rw [hecard]
    exact Nat.find_min' hQ ⟨T, inferInstance, J, hJH.trans hHG, hJR, hJcard, rfl⟩
  have hSmaller (S : Set U) (hS : Nat.card S < Fintype.card U)
      (hR : HasRate (H.induce S) r) : False := by
    have hh := hMin S (H.induce S) ((show H.induce S ⊑ H from ⟨Copy.induce H S⟩).trans hHG) hR
    simp only [Fintype.card_eq_nat_card] at hh hS
    omega
  have hDegree : ∀ v, 2 ≤ Nat.card (H.neighborSet v) := by
    intro x
    by_contra hx
    have hx' : H.degree x < 2 := by
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree, not_le] using hx
    apply hSmaller {x}ᶜ (by
      simpa only [Fintype.card_eq_nat_card] using
        Fintype.card_subtype_lt (p := fun v => v ∈ ({x}ᶜ : Set U)) (x := x) (by simp))
    have hx01 : H.degree x = 0 ∨ H.degree x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · exact isolated_rate_converse H hx0 hHR
    · obtain ⟨y, hxy, _⟩ := degree_eq_one_iff_existsUnique_adj.mp hx1
      exact leaf_rate_converse H hx1 hxy hHR
  letI : Nonempty U := nonempty_of_superlinear_rate hr hHR
  have hConnected : H.Connected := by
    by_contra hC
    let w : U := Classical.arbitrary U
    have hw : ∃ v, ¬H.Reachable w v := by
      by_contra hhh
      push_neg at hhh
      exact hC ((H.connected_iff_exists_forall_reachable).mpr ⟨w, hhh⟩)
    obtain ⟨v, hv⟩ := hw
    let S : Set U := (H.connectedComponentMk w).supp
    have hwS : w ∈ S := rfl
    have hvS : v ∉ S := by
      intro hh
      exact hv (ConnectedComponent.exact hh.symm)
    have hs : Nat.card S < Fintype.card U := by
      simpa only [Fintype.card_eq_nat_card] using Fintype.card_subtype_lt hvS
    have hsc : Nat.card ↥(Sᶜ) < Fintype.card U := by
      simpa only [Fintype.card_eq_nat_card] using
        Fintype.card_subtype_lt (x := w) (by simpa only [Set.mem_compl_iff, not_not] using hwS)
    have hSplit := iso_rate (Erdos713Components.splitIso H S (fun u v huv =>
      ConnectedComponent.mem_supp_congr_adj (H.connectedComponentMk w) huv)) hHR
    rcases rate_sum_or hSplit with hRS | hRSc
    · exact hSmaller S hs hRS
    · exact hSmaller Sᶜ hsc hRSc

  refine ⟨U, instU, H, hHG, hConnected, hDegree, hHR, hMin W G (.refl _) h, ?_, ?_⟩
  · intro T _ J hJH hJR
    exact hMin T J (hJH.trans hHG) hJR
  · intro T _ J hJH hJR
    exact iso_of_contained_card_eq hJH
      (le_antisymm (card_le_of_contained hJH) (hMin T J (hJH.trans hHG) hJR))
      (hEdgeMin T J hJH hJR)

lemma lower_power_of_no_rate {W : Type*} {H : SimpleGraph W} {r : ℝ}
    (hr : 1 ≤ r)
    (hUpper : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^r))
    (hNoRate : ¬ HasRate H r) :
    ∃ b : ℚ, 1 ≤ (b : ℝ) ∧ (b : ℝ) < r ∧
      (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^(b : ℝ)) := by
  classical
  have hn : ¬ ∀ a : ℝ, 1 ≤ a →
      ((fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^a)) → r ≤ a :=
    fun hh => hNoRate ⟨hr,hUpper,hh⟩
  push_neg at hn
  obtain ⟨a, ha, hA, har⟩ := hn
  obtain ⟨b, hab, hbr⟩ := exists_rat_btwn har
  exact ⟨b, ha.trans hab.le, hbr, hA.trans (rpow_mono_bigO hab.le)⟩

lemma proper_rational_upper {U W : Type u} [Fintype U] [Fintype W]
    {H : SimpleGraph W} {r : ℝ} (h : HasRate H r)
    (hCritical : ∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → HasRate J r → Nonempty (J ≃g H))
    (J : SimpleGraph U) (hJH : J ⊑ H) (hNoIso : ¬ Nonempty (J ≃g H)) :
    ∃ b : ℚ, 1 ≤ (b : ℝ) ∧ (b : ℝ) < r ∧
      (fun n : ℕ => (extremalNumber n J : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^(b : ℝ)) :=
  lower_power_of_no_rate h.one_le ((extremal_mono_bigO hJH).trans h.upper)
    (fun hJ => hNoIso (hCritical U J hJH hJ))

lemma uniform_rational_gap {W : Type u} [Fintype W] (H : SimpleGraph W) {r : ℝ}
    (hr : 1 < r) (h : HasRate H r)
    (hCritical : ∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → HasRate J r → Nonempty (J ≃g H)) :
    ∃ b : ℚ, 1 ≤ (b : ℝ) ∧ (b : ℝ) < r ∧ ∀ J : SimpleGraph W, J < H →
      (fun n : ℕ => (extremalNumber n J : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^(b : ℝ)) := by
  classical
  have hEach (J : SimpleGraph W) : ∃ b : ℚ, 1 ≤ (b : ℝ) ∧ (b : ℝ) < r ∧
      (J < H → (fun n : ℕ => (extremalNumber n J : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^(b : ℝ))) := by
    by_cases hJ : J < H
    · obtain ⟨b,hb,hbr,hB⟩ := proper_rational_upper h hCritical J ⟨Copy.ofLE _ _ hJ.le⟩ (by
        rintro ⟨e⟩
        exact hJ.ne (edgeFinset_inj.mp (Finset.eq_of_subset_of_card_le (edgeFinset_mono hJ.le)
          e.card_edgeFinset_eq.ge)))
      exact ⟨b,hb,hbr,fun _ => hB⟩
    · exact ⟨1,by norm_num,by simpa using hr,fun hh => (hJ hh).elim⟩
  choose b hb hbr hB using hEach
  obtain ⟨J₀, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (SimpleGraph W)) b
    ⟨⊥, Finset.mem_univ _⟩
  refine ⟨b J₀, hb J₀, hbr J₀, ?_⟩
  intro J hJ
  apply (hB J hJ).trans (rpow_mono_bigO _)
  exact_mod_cast hmax J (Finset.mem_univ _)


lemma iso_of_map_eq_of_no_isolates {U W : Type*} {J : SimpleGraph U} {H : SimpleGraph W}
    (hNoIso : ∀ a, ∃ b, H.Adj a b) (f : J.Copy H) (hf : J.map f.toEmbedding = H) :
    Nonempty (J ≃g H) := by
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨b,hab⟩ := hNoIso a
    rw [← hf] at hab
    obtain ⟨u,v,_,hu,_⟩ := (map_adj f.toEmbedding J a b).mp hab
    exact ⟨u,hu⟩
  let e : U ≃ W := Equiv.ofBijective f ⟨f.injective,hsurj⟩
  have he : J.map e.toEmbedding = H := hf
  exact ⟨he ▸ Iso.map e J⟩

lemma uniform_rational_gap_all {W : Type u} [Fintype W] (H : SimpleGraph W) {r : ℝ}
    (hr : 1 < r) (h : HasRate H r) (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (hCritical : ∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → HasRate J r → Nonempty (J ≃g H)) :
    ∃ b : ℚ, 1 ≤ (b : ℝ) ∧ (b : ℝ) < r ∧
      ∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → ¬ Nonempty (J ≃g H) →
        (fun n : ℕ => (extremalNumber n J : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^(b : ℝ)) := by
  obtain ⟨b,hb,hbr,hB⟩ := uniform_rational_gap H hr h hCritical
  refine ⟨b,hb,hbr,?_⟩
  intro T _ J hJH hNoEq
  obtain ⟨f⟩ := hJH
  have hle : J.map f.toEmbedding ≤ H :=
    (map_le_iff_le_comap f.toEmbedding J H).mpr (fun _ _ h => f.toHom.map_adj h)
  have hlt : J.map f.toEmbedding < H := lt_of_le_of_ne hle
    (fun hh => hNoEq (iso_of_map_eq_of_no_isolates hNoIso f hh))
  exact (extremal_mono_bigO ⟨(Embedding.map f.toEmbedding J).toCopy⟩).trans (hB _ hlt)

open scoped Classical in
lemma exists_uniform_power_core {W : Type u} [Fintype W] (G : SimpleGraph W)
    {r : ℝ} (hr : 1 < r) (h : HasRate G r) :
    ∃ (U : Type u) (_ : Fintype U) (H : SimpleGraph U), H ⊑ G ∧ H.Connected ∧
      (∀ v, 2 ≤ Nat.card (H.neighborSet v)) ∧ HasRate H r ∧ Fintype.card U ≤ Fintype.card W ∧
      (∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → HasRate J r →
        Fintype.card U ≤ Fintype.card T) ∧
      (∃ b : ℚ, 1 ≤ (b : ℝ) ∧ (b : ℝ) < r ∧
        ∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → ¬ Nonempty (J ≃g H) →
          (fun n : ℕ => (extremalNumber n J : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^(b : ℝ))) := by
  classical
  obtain ⟨U,instU,H,hHG,hConn,hDeg,hR,hCard,hMin,hCrit⟩ := exists_power_critical_core G hr h
  have hNoIso : ∀ a, ∃ b, H.Adj a b := by
    intro a
    apply (H.degree_pos_iff_exists_adj a).mp
    have hh : 2 ≤ H.degree a := by
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hDeg a
    omega
  exact ⟨U,instU,H,hHG,hConn,hDeg,hR,hCard,hMin,uniform_rational_gap_all H hr hR hNoIso hCrit⟩

lemma exists_lower_above_smaller_power {W : Type*} {H : SimpleGraph W} {r b : ℝ}
    (h : HasRate H r) (hb : 1 ≤ b) (hbr : b < r) (C : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ C * (n : ℝ)^b < (extremalNumber n H : ℝ) := by
  classical
  by_contra hn
  push_neg at hn
  have hu : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^b) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop N] with n hnN
    rw [Real.norm_natCast, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) b)]
    exact hn n hnN
  exact not_lt_of_ge (h.lower b hb hu) hbr

#print axioms exists_power_critical_core
#print axioms uniform_rational_gap_all
#print axioms exists_uniform_power_core
#print axioms exists_lower_above_smaller_power
end Erdos713PowerCritical
