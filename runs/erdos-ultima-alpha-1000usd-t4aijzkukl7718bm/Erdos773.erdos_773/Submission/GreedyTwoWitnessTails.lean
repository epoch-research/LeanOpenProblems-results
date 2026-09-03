import Submission.GreedyTwoWitnessPacking

/-!
Heavy/light tails for indexed two-vertex witnesses with bounded pair
multiplicity. All estimates use the stopped-process inclusion bound, not
independence of selection events.
-/
namespace Erdos773.GreedyTwoWitnessTails
open Finset GreedyTripleWitnessTails GreedyTwoWitnessPacking GreedyWitnessPacking
open GreedyConfigurationTails StoppedGreedyMoments
set_option maxHeartbeats 2500000
noncomputable section
variable {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]

theorem link_one_tail (H : Finset (Finset α)) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hn : n ≤ L) (T : Finset β) (C : β → Finset α)
    (htwo : ∀ i ∈ T, (C i).card = 2) (P l : ℕ)
    (hP : ∀ a b : α, a ≠ b → (T.filter (fun i => a ∈ C i ∧ b ∈ C i)).card ≤ P)
    (a : α) (M : ℕ) (hM : (link T C a).card ≤ M) :
    expectation H L n (event (linkBad T C a (P*l))) ≤
      (3*M*((n:ℝ)/L)/(l+1))^(l+1) := by
  have hs (i : β) (hi : i ∈ link T C a) : ((C i).erase a).card = 1 := by
    obtain ⟨hi,ha⟩ := mem_filter.mp hi
    rw [card_erase_of_mem ha,htwo i hi]
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
  have hb := packing_exponential_tail H L hL n hn (link T C a) (fun i => (C i).erase a) 1 P 1 l
    (fun i hi => card_pos.mp (by rw [hs i hi]; decide))
    (fun i hi => (hs i hi).le) (fun i hi => (hs i hi).ge) hinc
  simp only [one_mul,pow_one] at hb
  apply hb.trans
  have hMR : ((link T C a).card:ℝ) ≤ M := by exact_mod_cast hM
  gcongr

omit [DecidableEq β] in
theorem selected_vertex_tail (H : Finset (Finset α)) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hn : n ≤ L) (A : Finset α) (s : ℕ) :
    expectation H L n (event (fun I => s < (A ∩ I).card)) ≤
      (3*A.card*((n:ℝ)/L)/(s+1))^(s+1) := by
  have hb := packing_exponential_tail H L hL n hn A (fun a => ({a}:Finset α)) 1 1 1 s
    (fun a _ => singleton_nonempty a) (fun a _ => by simp) (fun a _ => by simp)
    (fun a => by
      apply card_le_one.mpr
      intro b hb c hc
      have hab := mem_singleton.mp (mem_filter.mp hb).2
      have hac := mem_singleton.mp (mem_filter.mp hc).2
      exact hab.symm.trans hac)
  have he (I : Finset α) : A.filter (fun a => ({a}:Finset α) ⊆ I) = A ∩ I := by
    ext a
    simp
  simpa only [one_mul,pow_one,he] using hb

def badCost (T : Finset β) (C : β → Finset α) (h P l₀ l₁ s k : ℕ) (I : Finset α) : ℝ :=
  (∑ a : α, event (linkBad T C a (P*l₀)) I) +
  (∑ a ∈ univ \ heavy T C h, event (linkBad T C a (P*l₁)) I) +
  event (fun I => s < (heavy T C h ∩ I).card) I + event (packedEvent T C k) I

lemma badCost_dom (T : Finset β) (C : β → Finset α)
    (htwo : ∀ i ∈ T, (C i).card = 2) (h P l₀ l₁ s k : ℕ) (I : Finset α) :
    event (fun I => s*(P*l₀)+2*(P*l₁)*k < (T.filter (fun i => C i ⊆ I)).card) I ≤
      badCost T C h P l₀ l₁ s k I := by
  classical
  have hn₀ : 0 ≤ ∑ a : α, event (linkBad T C a (P*l₀)) I :=
    sum_nonneg (fun _ _ => event_nonneg _ _)
  have hn₁ : 0 ≤ ∑ a ∈ univ \ heavy T C h, event (linkBad T C a (P*l₁)) I :=
    sum_nonneg (fun _ _ => event_nonneg _ _)
  have hns := event_nonneg (fun I => s < (heavy T C h ∩ I).card) I
  have hnk := event_nonneg (packedEvent T C k) I
  unfold badCost
  by_cases hb : s*(P*l₀)+2*(P*l₁)*k < (T.filter (fun i => C i ⊆ I)).card
  · simp only [event,if_pos hb]
    rcases split_or_packed T C (heavy T C h) I htwo (P*l₀) (P*l₁) s k hb with
      ⟨a,ha⟩ | ⟨a,ha,hb⟩ | hs | hk
    · have hh := single_le_sum (s := (univ:Finset α)) (a := a)
        (f := fun a => event (linkBad T C a (P*l₀)) I)
        (fun _ _ => event_nonneg _ _) (mem_univ a)
      dsimp only at hh
      have he : event (linkBad T C a (P*l₀)) I = 1 := by simp only [event,if_pos ha]
      rw [he] at hh
      change 1 ≤ (∑ a : α, event (linkBad T C a (P*l₀)) I) +
        (∑ a ∈ univ \ heavy T C h, event (linkBad T C a (P*l₁)) I) +
        event (fun I => s < (heavy T C h ∩ I).card) I + event (packedEvent T C k) I
      linarith only [hh,hn₁,hns,hnk]
    · have hh := single_le_sum (s := univ \ heavy T C h) (a := a)
        (f := fun a => event (linkBad T C a (P*l₁)) I)
        (fun _ _ => event_nonneg _ _) (mem_sdiff.mpr ⟨mem_univ a,ha⟩)
      dsimp only at hh
      have he : event (linkBad T C a (P*l₁)) I = 1 := by simp only [event,if_pos hb]
      rw [he] at hh
      change 1 ≤ (∑ a : α, event (linkBad T C a (P*l₀)) I) +
        (∑ a ∈ univ \ heavy T C h, event (linkBad T C a (P*l₁)) I) +
        event (fun I => s < (heavy T C h ∩ I).card) I + event (packedEvent T C k) I
      linarith only [hh,hn₀,hns,hnk]
    · have he : event (fun I => s < (heavy T C h ∩ I).card) I = 1 := by simp only [event,if_pos hs]
      change 1 ≤ (∑ a : α, event (linkBad T C a (P*l₀)) I) +
        (∑ a ∈ univ \ heavy T C h, event (linkBad T C a (P*l₁)) I) +
        event (fun I => s < (heavy T C h ∩ I).card) I + event (packedEvent T C k) I
      linarith only [he,hn₀,hn₁,hnk]
    · have he : event (packedEvent T C k) I = 1 := by simp only [event,if_pos hk]
      change 1 ≤ (∑ a : α, event (linkBad T C a (P*l₀)) I) +
        (∑ a ∈ univ \ heavy T C h, event (linkBad T C a (P*l₁)) I) +
        event (fun I => s < (heavy T C h ∩ I).card) I + event (packedEvent T C k) I
      linarith only [he,hn₀,hn₁,hns]
  · have hz : event (fun I => s*(P*l₀)+2*(P*l₁)*k < (T.filter (fun i => C i ⊆ I)).card) I = 0 := by
      simp only [event,if_neg hb]
    rw [hz]
    linarith only [hn₀,hn₁,hns,hnk]

theorem expectation_badCost (H : Finset (Finset α)) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hn : n ≤ L) (T : Finset β) (C : β → Finset α)
    (htwo : ∀ i ∈ T, (C i).card = 2) (h P l₀ l₁ s k : ℕ)
    (hP : ∀ a b : α, a ≠ b → (T.filter (fun i => a ∈ C i ∧ b ∈ C i)).card ≤ P) :
    expectation H L n (badCost T C h P l₀ l₁ s k) ≤
      (Fintype.card α:ℝ)*(3*T.card*((n:ℝ)/L)/(l₀+1))^(l₀+1) +
      (Fintype.card α:ℝ)*(3*h*((n:ℝ)/L)/(l₁+1))^(l₁+1) +
      (3*(heavy T C h).card*((n:ℝ)/L)/(s+1))^(s+1) +
      (3*T.card*((n:ℝ)/L)^2/(k+1))^(k+1) := by
  unfold badCost
  rw [expectation_add,expectation_add,expectation_add,expectation_sum,expectation_sum]
  have hfull : (∑ a : α, expectation H L n (event (linkBad T C a (P*l₀)))) ≤
      (Fintype.card α:ℝ)*(3*T.card*((n:ℝ)/L)/(l₀+1))^(l₀+1) := by
    calc
      _ ≤ ∑ _a : α, (3*T.card*((n:ℝ)/L)/(l₀+1))^(l₀+1) :=
        sum_le_sum (fun a _ => link_one_tail H L hL n hn T C htwo P l₀ hP a T.card (card_filter_le _ _))
      _ = _ := by simp
  have hlight : (∑ a ∈ univ \ heavy T C h, expectation H L n (event (linkBad T C a (P*l₁)))) ≤
      (Fintype.card α:ℝ)*(3*h*((n:ℝ)/L)/(l₁+1))^(l₁+1) := by
    calc
      _ ≤ ∑ _a ∈ univ \ heavy T C h, (3*h*((n:ℝ)/L)/(l₁+1))^(l₁+1) := by
        apply sum_le_sum
        intro a ha
        exact link_one_tail H L hL n hn T C htwo P l₁ hP a h
          (not_heavy_degree T C h (mem_sdiff.mp ha).2)
      _ = ((univ \ heavy T C h).card:ℝ)*(3*h*((n:ℝ)/L)/(l₁+1))^(l₁+1) := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (card_le_card (sdiff_subset : univ \ heavy T C h ⊆ univ))
  have hpacked := (packed_event_tail H L hL n hn T C 2 k (fun i hi => (htwo i hi).ge)).trans
    (choose_mul_pow_le T.card (k+1) 2 (by omega) ((n:ℝ)/L) (by positivity))
  simp only [Nat.cast_add,Nat.cast_one] at hpacked
  exact add_le_add (add_le_add (add_le_add hfull hlight)
    (selected_vertex_tail H L hL n hn (heavy T C h) s)) hpacked

/-- Heavy/light estimate with an upper bound E on the indexed witness count. -/
theorem two_tail (H : Finset (Finset α)) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hn : n ≤ L) (T : Finset β) (C : β → Finset α)
    (htwo : ∀ i ∈ T, (C i).card = 2) (E h P l₀ l₁ s k : ℕ)
    (hE : T.card ≤ E) (hh : 0 < h)
    (hP : ∀ a b : α, a ≠ b → (T.filter (fun i => a ∈ C i ∧ b ∈ C i)).card ≤ P) :
    expectation H L n (event (fun I => s*(P*l₀)+2*(P*l₁)*k < (T.filter (fun i => C i ⊆ I)).card)) ≤
      (Fintype.card α:ℝ)*(3*E*((n:ℝ)/L)/(l₀+1))^(l₀+1) +
      (Fintype.card α:ℝ)*(3*h*((n:ℝ)/L)/(l₁+1))^(l₁+1) +
      (6*E*((n:ℝ)/L)/(h*(s+1)))^(s+1) +
      (3*E*((n:ℝ)/L)^2/(k+1))^(k+1) := by
  apply (expectation_mono H L n (badCost_dom T C htwo h P l₀ l₁ s k)).trans
  apply (expectation_badCost H L hL n hn T C htwo h P l₀ l₁ s k hP).trans
  have hER : (T.card:ℝ) ≤ E := by exact_mod_cast hE
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have hhc : (h:ℝ)*(heavy T C h).card ≤ 2*E := by
    exact_mod_cast (heavy_card_bound T C htwo h).trans (Nat.mul_le_mul_left 2 hE)
  have hbase : 3*(heavy T C h).card*((n:ℝ)/L)/(s+1) ≤ 6*E*((n:ℝ)/L)/(h*(s+1)) := by
    apply (div_le_div_iff₀ (by positivity : (0:ℝ) < s+1) (by positivity)).mpr
    have hb := mul_le_mul_of_nonneg_right hhc (show (0:ℝ) ≤ 3*((n:ℝ)/L)*(s+1) by positivity)
    nlinarith only [hb]
  apply add_le_add (add_le_add (add_le_add _ le_rfl) _) _
  · gcongr
  · exact pow_le_pow_left₀ (by positivity) hbase _
  · gcongr

#print axioms link_one_tail
#print axioms selected_vertex_tail
#print axioms badCost_dom
#print axioms expectation_badCost
#print axioms two_tail
end
end Erdos773.GreedyTwoWitnessTails
