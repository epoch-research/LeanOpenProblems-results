import Submission.ProductCorrelation

/-!
Independent sets obtained from finite random priorities. The FKG bound accounts
for overlapping links, but is not a logarithmic-gain extraction theorem.
-/
namespace Erdos773.PriorityHypergraphSelection
open Finset ProductCorrelation
set_option maxHeartbeats 1000000
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every vertex has a uniform priority in `Fin K`. -/
noncomputable def uniform (K : ℕ) (_v : α) (_t : Fin K) : ℝ := 1 / K

omit [Fintype α] [DecidableEq α] in
lemma uniform_nonneg (K : ℕ) : ∀ v : α, ∀ t : Fin K, 0 ≤ uniform K v t := by
  intros
  dsimp [uniform]
  positivity

omit [Fintype α] [DecidableEq α] in
lemma uniform_sum (K : ℕ) (hK : 0 < K) : ∀ v : α, ∑ t, uniform K v t = 1 := by
  intro v
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  simp [uniform, hK0]

omit [Fintype α] [DecidableEq α] in
lemma uniform_cdf (K : ℕ) (v : α) (t : Fin K) :
    (∑ s : Fin K, if s ≤ t then uniform K v s else 0) = ((t.val+1:ℕ):ℝ)/K := by
  have he : univ.filter (fun s : Fin K => s ≤ t) = Iic t := by ext s; simp
  rw [← sum_filter, he]
  simp only [uniform, sum_const, nsmul_eq_mul, Fin.card_Iic]
  ring

/-- A link fails to block its vertex if at least one other priority is higher. -/
def avoid {K : ℕ} (S : Finset α) (t : Fin K) (x : α → Fin K) : ℝ :=
  if ∀ i ∈ S, x i ≤ t then 0 else 1

lemma avoid_nonneg {K : ℕ} (S : Finset α) (t : Fin K) (x : α → Fin K) :
    0 ≤ avoid S t x := by unfold avoid; split_ifs <;> norm_num

lemma avoid_monotone {K : ℕ} (S : Finset α) (t : Fin K) : Monotone (avoid S t) := by
  intro x y hxy
  unfold avoid
  split_ifs with hx hy hy
  · norm_num
  · norm_num
  · exact (hx (fun i hi => (hxy i).trans (hy i hi))).elim
  · norm_num

lemma pinned_contains {K : ℕ} (hK : 0 < K) (v : α) (t : Fin K)
    (S : Finset α) (hv : v ∉ S) :
    (∑ x : α → Fin K, if ∀ i ∈ S, x i ≤ t then weight (pin (uniform K) v t) x else 0) =
      (((t.val+1:ℕ):ℝ)/K)^S.card := by
  rw [sum_weight_restrict (pin (uniform K) v t) (fun i s => i ∈ S → s ≤ t)]
  have hi (i : α) : (∑ s : Fin K, if i ∈ S → s ≤ t then pin (uniform K) v t i s else 0) =
      if i ∈ S then ((t.val+1:ℕ):ℝ)/K else 1 := by
    by_cases his : i ∈ S
    · have hiv : i ≠ v := by intro h; subst i; exact hv his
      simp only [his, true_implies, if_true, pin, if_neg hiv]
      exact uniform_cdf K i t
    · simp only [his, false_implies, if_true, if_false]
      exact pin_sum (uniform K) (uniform_sum K hK) v t i
  simp_rw [hi]
  rw [prod_ite_mem, univ_inter, prod_const]

lemma pinned_avoid {K : ℕ} (hK : 0 < K) (v : α) (t : Fin K)
    (S : Finset α) (hv : v ∉ S) :
    (∑ x : α → Fin K, weight (pin (uniform K) v t) x * avoid S t x) =
      1-(((t.val+1:ℕ):ℝ)/K)^S.card := by
  have he (x : α → Fin K) :
      weight (pin (uniform K) v t) x * avoid S t x =
        weight (pin (uniform K) v t) x -
          if ∀ i ∈ S, x i ≤ t then weight (pin (uniform K) v t) x else 0 := by
    unfold avoid
    split_ifs <;> ring
  simp_rw [he]
  rw [sum_sub_distrib, sum_weight _ (pin_sum _ (uniform_sum K hK) v t),
    pinned_contains hK v t S hv]

lemma avoid_eq_indicator {K : ℕ} (S : Finset α) (t : Fin K) (x : α → Fin K) :
    avoid S t x = if ∃ i ∈ S, t < x i then 1 else 0 := by
  have he : (∃ i ∈ S, t < x i) ↔ ¬ ∀ i ∈ S, x i ≤ t := by
    simp only [not_forall, not_le, exists_prop]
  simp only [he, avoid, ite_not]

/-- Keep a vertex exactly when it is not a maximal-priority vertex of any
incident edge. Ties are rejected as well, ensuring independence. -/
def survivors {K : ℕ} (H : Finset (Finset α)) (x : α → Fin K) : Finset α :=
  univ.filter (fun v => ∀ e ∈ H, v ∈ e → ∃ w ∈ e.erase v, x v < x w)

lemma survivors_independent {K : ℕ} (H : Finset (Finset α))
    (hH : ∀ e ∈ H, e.Nonempty) (x : α → Fin K) :
    ∀ e ∈ H, ¬ e ⊆ survivors H x := by
  intro e he hsub
  obtain ⟨v, hv, hmax⟩ := exists_max_image e x (hH e he)
  have hsurv := (mem_filter.mp (hsub hv)).2
  obtain ⟨w, hw, hlt⟩ := hsurv e he hv
  exact (not_lt_of_ge (hmax w (mem_erase.mp hw).2)) hlt

lemma survival_indicator {K : ℕ} (H : Finset (Finset α)) (v : α)
    (t : Fin K) (x : α → Fin K) (hx : x v = t) :
    (if v ∈ survivors H x then (1:ℝ) else 0) =
      ∏ e ∈ H.filter (fun e => v ∈ e), avoid (e.erase v) t x := by
  simp_rw [avoid_eq_indicator]
  simp only [prod_boole]
  congr 1
  simp only [survivors, mem_filter, mem_univ, true_and, hx]
  apply propext
  constructor
  · intro h e he
    exact h e he.1 he.2
  · intro h e he hv
    exact h e ⟨he,hv⟩

lemma pinned_survival_bound {K : ℕ} (hK : 0 < K) (H : Finset (Finset α))
    (v : α) (t : Fin K) :
    (∏ e ∈ H.filter (fun e => v ∈ e), (1-(((t.val+1:ℕ):ℝ)/K)^(e.card-1))) ≤
      ∑ x : α → Fin K, weight (pin (uniform K) v t) x *
        if v ∈ survivors H x then 1 else 0 := by
  have hFk := weight_product_correlated (pin (uniform K) v t)
    (fun e : Finset α => avoid (e.erase v) t) (H.filter (fun e => v ∈ e))
    (pin_nonneg _ (uniform_nonneg K) v t) (pin_sum _ (uniform_sum K hK) v t)
    (fun e _ x => avoid_nonneg (e.erase v) t x)
    (fun e _ => avoid_monotone (e.erase v) t)
  have hleft : (∏ e ∈ H.filter (fun e => v ∈ e),
      ∑ x : α → Fin K, weight (pin (uniform K) v t) x * avoid (e.erase v) t x) =
      ∏ e ∈ H.filter (fun e => v ∈ e), (1-(((t.val+1:ℕ):ℝ)/K)^(e.card-1)) := by
    apply prod_congr rfl
    intro e he
    rw [pinned_avoid hK v t (e.erase v) (notMem_erase v e),
      card_erase_of_mem (mem_filter.mp he).2]
  rw [hleft] at hFk
  convert hFk using 1
  apply sum_congr rfl
  intro x _
  by_cases hx : x v = t
  · rw [survival_indicator H v t x hx]
  · simp [weight_pin, hx]

/-- A completely finite random-priority lower bound for an independent set.
It applies to nonuniform hypergraphs and permits arbitrary link overlaps. -/
theorem finite_selection (K : ℕ) (hK : 0 < K) (H : Finset (Finset α))
    (hH : ∀ e ∈ H, e.Nonempty) :
    ∃ B : Finset α, (∀ e ∈ H, ¬ e ⊆ B) ∧
      (∑ v : α, (1/(K:ℝ))*∑ t : Fin K,
        ∏ e ∈ H.filter (fun e => v ∈ e), (1-(((t.val+1:ℕ):ℝ)/K)^(e.card-1))) ≤ B.card := by
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  obtain ⟨x,hx,hmax⟩ := exists_max_image univ
    (fun x : α → Fin K => ((survivors H x).card : ℝ)) univ_nonempty
  refine ⟨survivors H x, survivors_independent H hH x, ?_⟩
  have havg : (∑ y : α → Fin K, weight (uniform K) y * ((survivors H y).card : ℝ)) ≤
      ((survivors H x).card : ℝ) := by
    calc
      _ ≤ ∑ y : α → Fin K, weight (uniform K) y * ((survivors H x).card : ℝ) :=
        sum_le_sum (fun y hy => mul_le_mul_of_nonneg_left (hmax y hy)
          (weight_nonneg _ (uniform_nonneg K) y))
      _ = _ := by rw [← sum_mul, sum_weight _ (uniform_sum K hK), one_mul]
  apply le_trans _ havg
  have hc (y : α → Fin K) : ((survivors H y).card : ℝ) =
      ∑ v : α, if v ∈ survivors H y then (1:ℝ) else 0 := by simp
  conv_rhs =>
    simp only [hc, mul_sum]
    rw [sum_comm]
  apply sum_le_sum
  intro v _
  rw [expectation_mixture (uniform K) v]
  rw [mul_sum]
  apply sum_le_sum
  intro t _
  exact mul_le_mul_of_nonneg_left (pinned_survival_bound hK H v t)
    (uniform_nonneg K v t)

#print axioms pinned_contains
#print axioms pinned_avoid
#print axioms survivors_independent
#print axioms pinned_survival_bound
#print axioms finite_selection
end Erdos773.PriorityHypergraphSelection
