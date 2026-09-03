import Submission.GreedyHypergraphState

/-!
Finite averages for a stopped greedy process. The inclusion bound is a
configuration-counting tool; it does not establish a long running time.
-/
namespace Erdos773.StoppedGreedyMoments
open Finset GreedyHypergraphState
set_option maxHeartbeats 1500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Stop before sampling from an available set of cardinality below L. -/
def Ready (H : Finset (Finset α)) (L : ℕ) (I : Finset α) : Prop :=
  L ≤ (available H I).card ∧ (available H I).Nonempty

def step (H : Finset (Finset α)) (L : ℕ) (f : Finset α → ℝ) (I : Finset α) : ℝ := by
  classical
  exact if Ready H L I then
    (∑ v ∈ available H I, f (insert v I))/(available H I).card else f I

lemma step_const (H : Finset (Finset α)) (L : ℕ) (c : ℝ) (I : Finset α) :
    step H L (fun _ => c) I = c := by
  classical
  unfold step
  split_ifs with h
  · have hp : ((available H I).card:ℝ) ≠ 0 := by
      exact_mod_cast (card_pos.mpr h.2).ne'
    simp only [sum_const,nsmul_eq_mul]
    exact mul_div_cancel_left₀ c hp
  · rfl

lemma step_mono (H : Finset (Finset α)) (L : ℕ) {f g : Finset α → ℝ}
    (hfg : ∀ I, f I ≤ g I) (I : Finset α) : step H L f I ≤ step H L g I := by
  classical
  unfold step
  split_ifs
  · exact div_le_div_of_nonneg_right (sum_le_sum (fun v _ => hfg (insert v I))) (Nat.cast_nonneg _)
  · exact hfg I

lemma step_add (H : Finset (Finset α)) (L : ℕ) (f g : Finset α → ℝ) (I : Finset α) :
    step H L (fun I => f I+g I) I = step H L f I+step H L g I := by
  classical
  unfold step
  split_ifs <;> simp [sum_add_distrib,add_div]

lemma step_mul (H : Finset (Finset α)) (L : ℕ) (c : ℝ) (f : Finset α → ℝ) (I : Finset α) :
    step H L (fun I => c*f I) I = c*step H L f I := by
  classical
  unfold step
  split_ifs <;> simp [← mul_sum,mul_div_assoc]

/-- The expectation functional is defined entirely by finite averages. -/
def expectation (H : Finset (Finset α)) (L : ℕ) : ℕ → (Finset α → ℝ) → ℝ
  | 0, f => f ∅
  | n+1, f => expectation H L n (step H L f)

lemma expectation_const (H : Finset (Finset α)) (L n : ℕ) (c : ℝ) :
    expectation H L n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [expectation]
    have he : step H L (fun _ => c) = fun _ => c := funext (step_const H L c)
    rw [he,ih]

lemma expectation_mono (H : Finset (Finset α)) (L n : ℕ)
    {f g : Finset α → ℝ} (hfg : ∀ I, f I ≤ g I) :
    expectation H L n f ≤ expectation H L n g := by
  induction n generalizing f g with
  | zero => exact hfg ∅
  | succ n ih => exact ih (step_mono H L hfg)

lemma expectation_nonneg (H : Finset (Finset α)) (L n : ℕ)
    {f : Finset α → ℝ} (hf : ∀ I, 0 ≤ f I) : 0 ≤ expectation H L n f := by
  have hh := expectation_mono H L n hf
  simpa only [expectation_const] using hh

lemma expectation_add (H : Finset (Finset α)) (L n : ℕ) (f g : Finset α → ℝ) :
    expectation H L n (fun I => f I+g I) = expectation H L n f+expectation H L n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [expectation]
    have he : step H L (fun I => f I+g I) = fun I => step H L f I+step H L g I :=
      funext (step_add H L f g)
    rw [he,ih]

lemma expectation_mul (H : Finset (Finset α)) (L n : ℕ) (c : ℝ) (f : Finset α → ℝ) :
    expectation H L n (fun I => c*f I) = c*expectation H L n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [expectation]
    have he : step H L (fun I => c*f I) = fun I => c*step H L f I := funext (step_mul H L c f)
    rw [he,ih]

lemma expectation_sum {β : Type*} (H : Finset (Finset α)) (L n : ℕ)
    (s : Finset β) (f : β → Finset α → ℝ) :
    expectation H L n (fun I => ∑ a ∈ s, f a I) = ∑ a ∈ s, expectation H L n (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expectation_const]
  | @insert a s ha ih =>
    simp only [sum_insert ha,expectation_add,ih]

def included (S I : Finset α) : ℝ := if S ⊆ I then 1 else 0

omit [Fintype α] in
lemma included_nonneg (S I : Finset α) : 0 ≤ included S I := by unfold included; split_ifs <;> norm_num
omit [Fintype α] in
lemma included_le_one (S I : Finset α) : included S I ≤ 1 := by unfold included; split_ifs <;> norm_num
omit [Fintype α] in
lemma included_empty (I : Finset α) : included ∅ I = 1 := by simp [included]

lemma inclusion_sum_bound (H : Finset (Finset α)) (I S : Finset α) (hn : ¬S ⊆ I) :
    (∑ v ∈ available H I, included S (insert v I)) ≤ ∑ v ∈ S, included (S.erase v) I := by
  have hterm (v : α) : included S (insert v I) ≤ if v ∈ S then included (S.erase v) I else 0 := by
    by_cases hsub : S ⊆ insert v I
    · have hv : v ∈ S := by
        by_contra hnv
        apply hn
        intro a ha
        rcases mem_insert.mp (hsub ha) with hav | hai
        · exact (hnv (hav ▸ ha)).elim
        · exact hai
      have he : S.erase v ⊆ I := by
        intro a ha
        obtain ⟨hav,ha⟩ := mem_erase.mp ha
        exact (mem_insert.mp (hsub ha)).resolve_left hav
      simp [included,hsub,hv,he]
    · simp only [included,if_neg hsub]
      split_ifs <;> norm_num
  calc
    _ ≤ ∑ v ∈ available H I, if v ∈ S then included (S.erase v) I else 0 :=
      sum_le_sum (fun v _ => hterm v)
    _ ≤ ∑ v : α, if v ∈ S then included (S.erase v) I else 0 := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro v _ _
      split_ifs
      · exact included_nonneg _ _
      · exact le_rfl
    _ = _ := by simp

/-- A specified set is either already selected, or its last vertex is selected
    in this step. Each available vertex has conditional probability at most 1/L. -/
lemma step_included_bound (H : Finset (Finset α)) (L : ℕ) (hL : 0 < L) (S I : Finset α) :
    step H L (included S) I ≤ included S I+(1/(L:ℝ))*∑ v ∈ S, included (S.erase v) I := by
  classical
  have hs : 0 ≤ ∑ v ∈ S, included (S.erase v) I := sum_nonneg (fun _ _ => included_nonneg _ _)
  have hLr : (0:ℝ) < L := by exact_mod_cast hL
  by_cases hsub : S ⊆ I
  · have hh := step_mono H L (included_le_one S) I
    rw [step_const] at hh
    simp only [included,if_pos hsub]
    exact hh.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) hs))
  · simp only [included,if_neg hsub]
    unfold step
    split_ifs with hready
    · have hQ : (0:ℝ) < (available H I).card := by exact_mod_cast card_pos.mpr hready.2
      have hLQ : (L:ℝ) ≤ (available H I).card := by exact_mod_cast hready.1
      have hb := inclusion_sum_bound H I S hsub
      change (∑ v ∈ available H I, included S (insert v I))/((available H I).card:ℝ) ≤ _
      calc
        _ ≤ (∑ v ∈ S, included (S.erase v) I)/(available H I).card :=
          div_le_div_of_nonneg_right hb hQ.le
        _ ≤ (∑ v ∈ S, included (S.erase v) I)/(L:ℝ) := div_le_div_of_nonneg_left hs hLr hLQ
        _ = _ := by simp only [included]; ring
    · change included S I ≤ _
      rw [included,if_neg hsub]
      positivity

lemma pow_tangent (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    a^(k+1)+((k:ℝ)+1)*b*a^k ≤ (a+b)^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hm := mul_le_mul_of_nonneg_right ih (add_nonneg ha hb)
    have hn : 0 ≤ ((k:ℝ)+1)*b^2*a^k := by positivity
    simp only [Nat.cast_succ,pow_succ] at hm hn ⊢
    nlinarith only [hm,hn]

/-- Uniform inclusion control for the stopped process, with no independence
    assumption on the choices made at different times. -/
theorem inclusion_bound (H : Finset (Finset α)) (L : ℕ) (hL : 0 < L) (n : ℕ) :
    ∀ S : Finset α, expectation H L n (included S) ≤ ((n:ℝ)/L)^S.card := by
  have hLr : (0:ℝ) < L := by exact_mod_cast hL
  induction n with
  | zero =>
    intro S
    by_cases hS : S = ∅
    · subst S; simp [expectation,included]
    · have hc : S.card ≠ 0 := card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hS)
      simp [expectation,included,Finset.subset_empty,hS,hc]
  | succ n ih =>
    intro S
    by_cases hS : S = ∅
    · subst S
      have he : included (∅ : Finset α) = fun _ => (1:ℝ) := funext included_empty
      rw [he,expectation_const]
      simp
    have hc : 0 < S.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hS)
    have hs : (∑ v ∈ S, expectation H L n (included (S.erase v))) ≤
        (S.card:ℝ)*((n:ℝ)/L)^(S.card-1) := by
      calc
        _ ≤ ∑ _v ∈ S, ((n:ℝ)/L)^(S.card-1) := by
          apply sum_le_sum
          intro v hv
          simpa only [card_erase_of_mem hv] using ih (S.erase v)
        _ = _ := by simp
    calc
      expectation H L (n+1) (included S) ≤
          expectation H L n (fun I => included S I+(1/(L:ℝ))*∑ v ∈ S, included (S.erase v) I) :=
        expectation_mono H L n (step_included_bound H L hL S)
      _ = expectation H L n (included S)+(1/(L:ℝ))*∑ v ∈ S, expectation H L n (included (S.erase v)) := by
        rw [expectation_add,expectation_mul,expectation_sum]
      _ ≤ ((n:ℝ)/L)^S.card+(1/(L:ℝ))*(S.card:ℝ)*((n:ℝ)/L)^(S.card-1) := by
        have hm := mul_le_mul_of_nonneg_left hs (show (0:ℝ) ≤ 1/L by positivity)
        linarith [ih S]
      _ ≤ (((n+1:ℕ):ℝ)/L)^S.card := by
        obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hc.ne'
        rw [hk]
        simp only [Nat.succ_sub_one]
        have hh := pow_tangent ((n:ℝ)/L) (1/(L:ℝ)) (by positivity) (by positivity) k
        simpa only [Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one,add_div,
          mul_assoc,mul_comm,mul_left_comm] using hh

/-- Expected configuration counts follow by linearity, still allowing the
    process to have stopped before time n. -/
theorem configuration_bound (H : Finset (Finset α)) (L : ℕ) (hL : 0 < L) (n : ℕ)
    (C : Finset (Finset α)) :
    expectation H L n (fun I => ((C.filter (fun e => e ⊆ I)).card:ℝ)) ≤
      ∑ e ∈ C, ((n:ℝ)/L)^e.card := by
  have he : (fun I => ((C.filter (fun e => e ⊆ I)).card:ℝ)) =
      fun I => ∑ e ∈ C, included e I := by
    funext I
    simp [included]
  rw [he,expectation_sum]
  exact sum_le_sum (fun e _ => inclusion_bound H L hL n e)

/-- Reachability records the actual choices and the absorbing stopping rule. -/
inductive Reach (H : Finset (Finset α)) (L : ℕ) : ℕ → Finset α → Prop
  | zero : Reach H L 0 ∅
  | choose {n : ℕ} {I : Finset α} {v : α} (hI : Reach H L n I)
      (hR : Ready H L I) (hv : v ∈ available H I) : Reach H L (n+1) (insert v I)
  | hold {n : ℕ} {I : Finset α} (hI : Reach H L n I)
      (hR : ¬Ready H L I) : Reach H L (n+1) I

lemma Reach.independent {H : Finset (Finset α)} {L n : ℕ} {I : Finset α}
    (hI : Reach H L n I) (hH : ∀ e ∈ H, e.Nonempty) : Independent H I := by
  induction hI with
  | zero =>
    intro e he hsub
    obtain ⟨v,hv⟩ := hH e he
    exact notMem_empty v (hsub hv)
  | choose hI hR hv ih => exact (mem_available.mp hv).2
  | hold hI hR ih => exact ih

lemma Reach.card_le {H : Finset (Finset α)} {L n : ℕ} {I : Finset α}
    (hI : Reach H L n I) : I.card ≤ n := by
  induction hI with
  | zero => simp
  | choose hI hR hv ih =>
    rw [card_insert_of_notMem (mem_available.mp hv).1]
    omega
  | hold hI hR ih => omega

lemma Reach.short_implies_stopped {H : Finset (Finset α)} {L n : ℕ} {I : Finset α}
    (hI : Reach H L n I) (hshort : I.card < n) : ¬Ready H L I := by
  induction hI with
  | zero => simp at hshort
  | choose hI hR hv ih =>
    rw [card_insert_of_notMem (mem_available.mp hv).1] at hshort
    exact ((ih (by omega)) hR).elim
  | hold hI hR ih => exact hR

lemma ready_iff (H : Finset (Finset α)) (L : ℕ) (hL : 0 < L) (I : Finset α) :
    Ready H L I ↔ L ≤ (available H I).card := by
  constructor
  · exact And.left
  · intro h
    exact ⟨h,card_pos.mp (hL.trans_le h)⟩

lemma Reach.card_or_stopped {H : Finset (Finset α)} {L n : ℕ} {I : Finset α}
    (hI : Reach H L n I) (hL : 0 < L) : I.card = n ∨ (available H I).card < L := by
  by_cases he : I.card = n
  · exact Or.inl he
  · apply Or.inr
    have hlt : I.card < n := lt_of_le_of_ne hI.card_le he
    have hh := hI.short_implies_stopped hlt
    rw [ready_iff H L hL I] at hh
    omega

/-- Finite averaging yields an actual reachable state below its expectation. -/
theorem expectation_attained_below (H : Finset (Finset α)) (L n : ℕ)
    (f : Finset α → ℝ) :
    ∃ I : Finset α, Reach H L n I ∧ f I ≤ expectation H L n f := by
  classical
  induction n generalizing f with
  | zero => exact ⟨∅,Reach.zero,le_rfl⟩
  | succ n ih =>
    obtain ⟨I,hI,hf⟩ := ih (step H L f)
    by_cases hR : Ready H L I
    · obtain ⟨v,hv,hmin⟩ := exists_min_image (available H I)
        (fun v => f (insert v I)) hR.2
      have hp : (0:ℝ) < (available H I).card := by exact_mod_cast card_pos.mpr hR.2
      have havg : f (insert v I) ≤ step H L f I := by
        rw [step,if_pos hR]
        apply (le_div_iff₀ hp).mpr
        have hh := sum_le_sum (s := available H I) (fun w hw => hmin w hw)
        simpa only [sum_const,nsmul_eq_mul,mul_comm] using hh
      exact ⟨insert v I,Reach.choose hI hR hv,havg.trans hf⟩
    · refine ⟨I,Reach.hold hI hR,?_⟩
      simpa only [step,if_neg hR] using hf

/-- An arbitrary finite indexed configuration family, allowing repeated
    configurations and nonnegative real weights. -/
theorem weighted_configuration_bound {β : Type*} (H : Finset (Finset α))
    (L : ℕ) (hL : 0 < L) (n : ℕ) (T : Finset β) (C : β → Finset α)
    (w : β → ℝ) (hw : ∀ i ∈ T, 0 ≤ w i) :
    expectation H L n (fun I => ∑ i ∈ T, w i*included (C i) I) ≤
      ∑ i ∈ T, w i*((n:ℝ)/L)^(C i).card := by
  rw [expectation_sum]
  apply sum_le_sum
  intro i hi
  rw [expectation_mul]
  exact mul_le_mul_of_nonneg_left (inclusion_bound H L hL n (C i)) (hw i hi)

/-- The moment bound gives a genuine configuration-free greedy trajectory,
    but the alternative of early stopping is explicitly retained. -/
theorem configuration_free_run (H : Finset (Finset α))
    (hH : ∀ e ∈ H, e.Nonempty) (L : ℕ) (hL : 0 < L) (n : ℕ)
    (C : Finset (Finset α)) (hcost : (∑ e ∈ C, ((n:ℝ)/L)^e.card) < 1) :
    ∃ I : Finset α, Reach H L n I ∧ Independent H I ∧
      (I.card = n ∨ (available H I).card < L) ∧ (∀ e ∈ C, ¬e ⊆ I) := by
  obtain ⟨I,hI,hi⟩ := expectation_attained_below H L n
    (fun I => ((C.filter (fun e => e ⊆ I)).card:ℝ))
  have hb := configuration_bound H L hL n C
  have hcount : ((C.filter (fun e => e ⊆ I)).card:ℝ) < 1 := hi.trans_lt (hb.trans_lt hcost)
  have hcountN : (C.filter (fun e => e ⊆ I)).card < 1 := by exact_mod_cast hcount
  have he : C.filter (fun e => e ⊆ I) = ∅ := card_eq_zero.mp (by omega)
  refine ⟨I,hI,hI.independent hH,hI.card_or_stopped hL,?_⟩
  intro e heC hesub
  have hm : e ∈ C.filter (fun e => e ⊆ I) := mem_filter.mpr ⟨heC,hesub⟩
  rw [he] at hm
  exact notMem_empty e hm

#print axioms Reach.independent
#print axioms Reach.card_le
#print axioms Reach.card_or_stopped
#print axioms expectation_attained_below
#print axioms weighted_configuration_bound
#print axioms configuration_free_run
#print axioms inclusion_bound
#print axioms configuration_bound
end
end Erdos773.StoppedGreedyMoments
