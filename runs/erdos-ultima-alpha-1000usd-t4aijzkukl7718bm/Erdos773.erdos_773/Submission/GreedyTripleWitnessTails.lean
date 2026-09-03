import Submission.GreedyWitnessPacking

/-!
A two-stage packing estimate for indexed three-vertex witnesses. Only pair
incidences, not single-vertex incidences, need be small. All probabilities
refer to the stopped greedy process; witness events are not independent.
-/
namespace Erdos773.GreedyTripleWitnessTails
open Finset GreedyWitnessPacking GreedyConfigurationTails StoppedGreedyMoments
set_option maxHeartbeats 2500000
noncomputable section
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- A selected disjoint subfamily of the prescribed size. -/
def packedEvent (T : Finset β) (C : β → Finset α) (k : ℕ) (I : Finset α) : Prop :=
  ∃ U ∈ T.powersetCard (k+1), (U:Set β).PairwiseDisjoint C ∧ U.biUnion C ⊆ I

/-- Packing after selection is valid when the SELECTED incidence counts
    are bounded, even if original incidence counts are large. -/
lemma selected_packing (T : Finset β) (C : β → Finset α) (r M k : ℕ)
    (hne : ∀ i ∈ T, (C i).Nonempty) (hr : ∀ i ∈ T, (C i).card ≤ r)
    (I : Finset α)
    (hinc : ∀ a, ((T.filter (fun i => C i ⊆ I)).filter (fun i => a ∈ C i)).card ≤ M)
    (hlarge : r*M*k < (T.filter (fun i => C i ⊆ I)).card) : packedEvent T C k I := by
  let S := T.filter (fun i => C i ⊆ I)
  have hST : S ⊆ T := filter_subset _ _
  obtain ⟨V,hVS,hd,hcard⟩ := packing_bound S C r M
    (fun i hi => hne i (hST hi)) (fun i hi => hr i (hST hi)) hinc
  have hkV : k+1 ≤ V.card := by
    by_contra! hh
    have hle := Nat.mul_le_mul_left (r*M) (show V.card ≤ k by omega)
    exact (not_lt_of_ge (hcard.trans hle)) hlarge
  obtain ⟨U,hUV,hUk⟩ := exists_subset_card_eq hkV
  refine ⟨U,mem_powersetCard.mpr ⟨hUV.trans (hVS.trans hST),hUk⟩,
    fun i hi j hj hij => hd (hUV hi) (hUV hj) hij,?_⟩
  exact biUnion_subset.mpr (fun i hi => (mem_filter.mp (hVS (hUV hi))).2)

def link (T : Finset β) (C : β → Finset α) (a : α) : Finset β := T.filter (fun i => a ∈ C i)

def linkBad (T : Finset β) (C : β → Finset α) (a : α) (M : ℕ) (I : Finset α) : Prop :=
  M < ((link T C a).filter (fun i => (C i).erase a ⊆ I)).card

lemma selected_heavy_or_packed (T : Finset β) (C : β → Finset α) (r M k : ℕ)
    (hne : ∀ i ∈ T, (C i).Nonempty) (hr : ∀ i ∈ T, (C i).card ≤ r)
    (I : Finset α) (hlarge : r*M*k < (T.filter (fun i => C i ⊆ I)).card) :
    (∃ a, linkBad T C a M I) ∨ packedEvent T C k I := by
  by_cases hb : ∃ a, linkBad T C a M I
  · exact Or.inl hb
  right
  apply selected_packing T C r M k hne hr I _ hlarge
  intro a
  have hle : ((link T C a).filter (fun i => (C i).erase a ⊆ I)).card ≤ M := by
    exact le_of_not_gt (fun h => hb ⟨a,h⟩)
  apply le_trans (card_le_card ?_) hle
  intro i hi
  obtain ⟨hi,ha⟩ := mem_filter.mp hi
  obtain ⟨hi,hsub⟩ := mem_filter.mp hi
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨hi,ha⟩,(erase_subset _ _).trans hsub⟩

variable [Fintype α]

omit [DecidableEq β] in
theorem packed_event_tail (H : Finset (Finset α)) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hn : n ≤ L) (T : Finset β) (C : β → Finset α) (s k : ℕ)
    (hs : ∀ i ∈ T, s ≤ (C i).card) :
    expectation H L n (event (packedEvent T C k)) ≤
      (T.card.choose (k+1):ℝ)*((n:ℝ)/L)^(s*(k+1)) := by
  classical
  let F := (T.powersetCard (k+1)).filter (fun U : Finset β => (U:Set β).PairwiseDisjoint C)
  have hw (I : Finset α) (hI : packedEvent T C k I) : ∃ U ∈ F, U.biUnion C ⊆ I := by
    obtain ⟨U,hU,hd,hUI⟩ := hI
    exact ⟨U,mem_filter.mpr ⟨hU,hd⟩,hUI⟩
  have hc (U : Finset β) (hU : U ∈ F) : s*(k+1) ≤ (U.biUnion C).card := by
    obtain ⟨hU,hd⟩ := mem_filter.mp hU
    obtain ⟨hUT,hUk⟩ := mem_powersetCard.mp hU
    rw [card_biUnion hd]
    calc
      _ = ∑ _i ∈ U, s := by simp [hUk,mul_comm]
      _ ≤ _ := sum_le_sum (fun i hi => hs i (hUT hi))
  have hp0 : (0:ℝ) ≤ (n:ℝ)/L := by positivity
  have hp1 : (n:ℝ)/L ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hL : (0:ℝ) < L)).mpr
    exact_mod_cast hn
  calc
    _ ≤ ∑ U ∈ F, ((n:ℝ)/L)^(U.biUnion C).card := witness_bound H L hL n F _ _ hw
    _ ≤ ∑ _U ∈ F, ((n:ℝ)/L)^(s*(k+1)) :=
      sum_le_sum (fun U hU => pow_le_pow_of_le_one hp0 hp1 (hc U hU))
    _ = (F.card:ℝ)*((n:ℝ)/L)^(s*(k+1)) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hh := card_filter_le (s := T.powersetCard (k+1))
        (p := fun U : Finset β => (U:Set β).PairwiseDisjoint C)
      rw [card_powersetCard] at hh
      exact_mod_cast hh

theorem link_tail (H : Finset (Finset α)) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hn : n ≤ L) (T : Finset β) (C : β → Finset α)
    (hthree : ∀ i ∈ T, (C i).card = 3) (P l : ℕ)
    (hP : ∀ a b : α, a ≠ b → (T.filter (fun i => a ∈ C i ∧ b ∈ C i)).card ≤ P)
    (a : α) :
    expectation H L n (event (linkBad T C a (2*P*l))) ≤
      (T.card.choose (l+1):ℝ)*((n:ℝ)/L)^(2*(l+1)) := by
  have hs (i : β) (hi : i ∈ link T C a) : ((C i).erase a).card = 2 := by
    obtain ⟨hi,ha⟩ := mem_filter.mp hi
    rw [card_erase_of_mem ha,hthree i hi]
  have hinc (b : α) : ((link T C a).filter (fun i => b ∈ (C i).erase a)).card ≤ P := by
    by_cases hab : a = b
    · subst b
      simp
    have he : (link T C a).filter (fun i => b ∈ (C i).erase a) =
        T.filter (fun i => a ∈ C i ∧ b ∈ C i) := by
      ext i
      simp only [link,mem_filter,mem_erase]
      tauto
    rw [he]
    exact hP a b hab
  have hb := packing_tail H L hL n hn (link T C a) (fun i => (C i).erase a) 2 P 2 l
    (fun i hi => card_pos.mp (by rw [hs i hi]; decide))
    (fun i hi => (hs i hi).le) (fun i hi => (hs i hi).ge) hinc
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.choose_le_choose (l+1) (card_filter_le (s := T) (p := fun i => a ∈ C i))

/-- Three-vertex witnesses with bounded pair incidences have a two-stage
    tail. The first term controls selected incidences through links; the
    second controls the disjoint selected subfamily. -/
theorem triple_tail (H : Finset (Finset α)) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hn : n ≤ L) (T : Finset β) (C : β → Finset α)
    (hthree : ∀ i ∈ T, (C i).card = 3) (P l k : ℕ)
    (hP : ∀ a b : α, a ≠ b → (T.filter (fun i => a ∈ C i ∧ b ∈ C i)).card ≤ P) :
    expectation H L n (event (fun I => 6*P*l*k < (T.filter (fun i => C i ⊆ I)).card)) ≤
      (Fintype.card α:ℝ)*(T.card.choose (l+1):ℝ)*((n:ℝ)/L)^(2*(l+1)) +
      (T.card.choose (k+1):ℝ)*((n:ℝ)/L)^(3*(k+1)) := by
  have hdom (I : Finset α) :
      event (fun I => 6*P*l*k < (T.filter (fun i => C i ⊆ I)).card) I ≤
      (∑ a : α, event (linkBad T C a (2*P*l)) I) + event (packedEvent T C k) I := by
    classical
    by_cases hb : 6*P*l*k < (T.filter (fun i => C i ⊆ I)).card
    · have hb' : 3*(2*P*l)*k < (T.filter (fun i => C i ⊆ I)).card := by
        convert hb using 1; ring
      rcases selected_heavy_or_packed T C 3 (2*P*l) k
        (fun i hi => card_pos.mp (by rw [hthree i hi]; decide))
        (fun i hi => (hthree i hi).le) I hb' with ⟨a,ha⟩ | hp
      · have hs := single_le_sum (s := (univ : Finset α)) (a := a)
          (f := fun a => event (linkBad T C a (2*P*l)) I)
          (fun _ _ => event_nonneg _ _) (mem_univ a)
        dsimp only at hs
        have he : event (linkBad T C a (2*P*l)) I = 1 := by simp only [event,if_pos ha]
        rw [he] at hs
        simpa only [event,if_pos hb] using hs.trans (le_add_of_nonneg_right (event_nonneg _ _))
      · have he : event (packedEvent T C k) I = 1 := by simp only [event,if_pos hp]
        rw [he]
        simpa only [event,if_pos hb] using le_add_of_nonneg_left
          (sum_nonneg (fun _ _ => event_nonneg _ _) : (0:ℝ) ≤ ∑ a : α, event (linkBad T C a (2*P*l)) I)
    · simp only [event,if_neg hb]
      exact add_nonneg (sum_nonneg (fun _ _ => event_nonneg _ _)) (event_nonneg _ _)
  calc
    _ ≤ expectation H L n (fun I =>
        (∑ a : α, event (linkBad T C a (2*P*l)) I) + event (packedEvent T C k) I) :=
      expectation_mono H L n hdom
    _ = (∑ a : α, expectation H L n (event (linkBad T C a (2*P*l)))) +
        expectation H L n (event (packedEvent T C k)) := by rw [expectation_add,expectation_sum]
    _ ≤ (∑ _a : α, (T.card.choose (l+1):ℝ)*((n:ℝ)/L)^(2*(l+1))) +
        (T.card.choose (k+1):ℝ)*((n:ℝ)/L)^(3*(k+1)) :=
      add_le_add (sum_le_sum (fun a _ => link_tail H L hL n hn T C hthree P l hP a))
        (packed_event_tail H L hL n hn T C 3 k (fun i hi => (hthree i hi).ge))
    _ = _ := by simp [mul_assoc]

theorem triple_exponential_tail (H : Finset (Finset α)) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hn : n ≤ L) (T : Finset β) (C : β → Finset α)
    (hthree : ∀ i ∈ T, (C i).card = 3) (P l k : ℕ)
    (hP : ∀ a b : α, a ≠ b → (T.filter (fun i => a ∈ C i ∧ b ∈ C i)).card ≤ P) :
    expectation H L n (event (fun I => 6*P*l*k < (T.filter (fun i => C i ⊆ I)).card)) ≤
      (Fintype.card α:ℝ)*(3*T.card*((n:ℝ)/L)^2/(l+1))^(l+1) +
      (3*T.card*((n:ℝ)/L)^3/(k+1))^(k+1) := by
  apply (triple_tail H L hL n hn T C hthree P l k hP).trans
  rw [mul_assoc]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    simpa only [Nat.cast_add,Nat.cast_one] using
      choose_mul_pow_le T.card (l+1) 2 (by omega) ((n:ℝ)/L) (by positivity)
  · simpa only [Nat.cast_add,Nat.cast_one] using
      choose_mul_pow_le T.card (k+1) 3 (by omega) ((n:ℝ)/L) (by positivity)

#print axioms selected_packing
#print axioms selected_heavy_or_packed
#print axioms packed_event_tail
#print axioms link_tail
#print axioms triple_tail
#print axioms triple_exponential_tail
end
end Erdos773.GreedyTripleWitnessTails
