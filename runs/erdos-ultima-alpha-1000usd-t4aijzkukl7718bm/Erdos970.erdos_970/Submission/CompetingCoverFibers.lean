import Submission.CoverFiberIdentity

/-!
Simultaneous restrictions on primes that can finish one partial cover.
These are averaged restrictions across candidate primes, not a uniform
concentration estimate for a prescribed prime and not a settlement of Erdős 970.
-/
namespace Erdos970.CoverFibers
open Finset Real Erdos970.GapAverages

lemma exists_ordered_pair (U : Finset ℕ) (hU : 2 ≤ U.card) :
    ∃ x ∈ U, ∃ y ∈ U, x < y := by
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp (by omega : 1 < U.card)
  rcases lt_or_gt_of_ne hxy with h | h
  · exact ⟨x, hx, y, hy, h⟩
  · exact ⟨y, hy, x, hx, h⟩

/-- Simultaneous concentration implies divisibility of every survivor difference. -/
lemma concentrated_product_dvd (U R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime)
    (hc : ∀ p ∈ R, Concentrated U p) {x y : ℕ} (hx : x ∈ U) (hy : y ∈ U)
    (hxy : x ≤ y) : (∏ p ∈ R, p) ∣ y - x := by
  apply prod_primes_dvd _ (fun p hp => (hR p hp).prime)
  intro p hp
  exact (Nat.modEq_iff_dvd' hxy).mp ((hc p hp).2 x hx y hy)

/-- The product of all candidate completing primes is smaller than the interval,
provided there are at least two old survivors. -/
theorem concentrated_product_lt (U R : Finset ℕ) (m : ℕ)
    (hUm : U ⊆ range m) (hU : 2 ≤ U.card) (hR : ∀ p ∈ R, p.Prime)
    (hc : ∀ p ∈ R, Concentrated U p) : (∏ p ∈ R, p) < m := by
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_ordered_pair U hU
  have hd := concentrated_product_dvd U R hR hc hx hy hxy.le
  have hh := Nat.le_of_dvd (Nat.sub_pos_of_lt hxy) hd
  have hym : y < m := mem_range.mp (hUm hy)
  omega

/-- In logarithmic form, the total prime-choice weight is at most log m. -/
theorem concentrated_log_sum_le (U R : Finset ℕ) (m : ℕ)
    (hUm : U ⊆ range m) (hU : 2 ≤ U.card) (hR : ∀ p ∈ R, p.Prime) :
    (∑ p ∈ R, if Concentrated U p then log (p : ℝ) else 0) ≤ log (m : ℝ) := by
  let T := R.filter (fun p => Concentrated U p)
  have hT : ∀ p ∈ T, p.Prime := fun p hp => hR p (mem_filter.mp hp).1
  have hp : (∏ p ∈ T, p) < m :=
    concentrated_product_lt U T m hUm hU hT (fun p hp => (mem_filter.mp hp).2)
  have hpos : (0 : ℝ) < ∏ p ∈ T, (p : ℝ) := prod_pos
    (fun p hp => by exact_mod_cast (hT p hp).pos)
  have he : (∑ p ∈ R, if Concentrated U p then log (p : ℝ) else 0) =
      log (∏ p ∈ T, (p : ℝ)) := by
    rw [log_prod (s := T) (f := fun p : ℕ => (p : ℝ)) (fun p hp => (ne_of_gt (show (0 : ℝ) < p by
      exact_mod_cast (hT p hp).pos))), sum_filter]
  rw [he]
  apply log_le_log hpos
  rw [← Nat.cast_prod]
  exact_mod_cast hp.le

/-- If all distinct candidate pairs have product at least m, at most one can
concentrate the same nonsingleton survivor set. -/
theorem concentrated_candidates_card_le_one (U R : Finset ℕ) (m : ℕ)
    (hUm : U ⊆ range m) (hU : 2 ≤ U.card) (hR : ∀ p ∈ R, p.Prime)
    (hprod : ∀ p ∈ R, ∀ q ∈ R, p ≠ q → m ≤ p * q) :
    (R.filter (fun p => Concentrated U p)).card ≤ 1 := by
  apply card_le_one.mpr
  intro p hp q hq
  obtain ⟨hpR, hpU⟩ := mem_filter.mp hp
  obtain ⟨hqR, hqU⟩ := mem_filter.mp hq
  by_contra hpq
  have hc : ∀ t ∈ ({p, q} : Finset ℕ), Concentrated U t := by
    intro t ht
    rcases mem_insert.mp ht with rfl | ht
    · exact hpU
    · simpa only [mem_singleton.mp ht] using hqU
  have ht : ∀ t ∈ ({p, q} : Finset ℕ), t.Prime := by
    intro t ht
    rcases mem_insert.mp ht with rfl | ht
    · exact hR _ hpR
    · simpa only [mem_singleton.mp ht] using hR q hqR
  have hh := concentrated_product_lt U {p, q} m hUm hU ht hc
  rw [prod_pair hpq] at hh
  exact hh.not_ge (hprod p hpR q hqR hpq)

lemma concentrated_of_card_one (U : Finset ℕ) (hU : U.card = 1) (p : ℕ) :
    Concentrated U p := by
  obtain ⟨x, rfl⟩ := card_eq_one.mp hU
  simp [Concentrated]

/-- Probability of exactly one old survivor. The singleton case must be
retained: such a set is concentrated modulo every prime. -/
noncomputable def singletonFraction (P : Finset ℕ) (m : ℕ) : ℝ :=
  phaseMean P (fun r => if (phaseSurvivors P m r).card = 1 then 1 else 0)

lemma concentrated_log_pointwise (U R : Finset ℕ) (m : ℕ)
    (hUm : U ⊆ range m) (hR : ∀ p ∈ R, p.Prime) :
    (∑ p ∈ R, (log (p : ℝ)) * if Concentrated U p then (1 : ℝ) else 0) ≤
      log (m : ℝ) * (1 - (if U = ∅ then 1 else 0) -
        (if U.card = 1 then 1 else 0)) +
      (∑ p ∈ R, log (p : ℝ)) * (if U.card = 1 then 1 else 0) := by
  by_cases he : U = ∅
  · simp [he, Concentrated]
  · by_cases hs : U.card = 1
    · simp [he, hs, concentrated_of_card_one U hs]
    · have hc : 2 ≤ U.card := by have := card_pos.mpr (nonempty_iff_ne_empty.mpr he); omega
      simpa only [he, hs, if_false, sub_zero, mul_one, mul_zero, add_zero, mul_ite]
        using concentrated_log_sum_le U R m hUm hc hR

/-- A simultaneous weighted concentration bound across all candidate primes. -/
theorem concentratedFraction_log_sum_le (P R : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime) (m : ℕ) :
    (∑ p ∈ R, log (p : ℝ) * concentratedFraction P p m) ≤
      log (m : ℝ) * (1 - coveredFraction P m - singletonFraction P m) +
      (∑ p ∈ R, log (p : ℝ)) * singletonFraction P m := by
  classical
  have h := phaseMean_mono (P := P) (fun r => concentrated_log_pointwise
    (phaseSurvivors P m r) R m (filter_subset _ _) hR)
  rw [phaseMean_sum] at h
  simp_rw [phaseMean_mul, phaseSurvivors_empty_iff] at h
  rw [phaseMean_add, phaseMean_mul, phaseMean_sub, phaseMean_sub,
    phaseMean_const P hP, phaseMean_mul] at h
  exact h

lemma concentrated_count_pointwise (U R : Finset ℕ) (m : ℕ)
    (hUm : U ⊆ range m) (hR : ∀ p ∈ R, p.Prime)
    (hprod : ∀ p ∈ R, ∀ q ∈ R, p ≠ q → m ≤ p * q) :
    (∑ p ∈ R, if Concentrated U p then (1 : ℝ) else 0) ≤
      1 - (if U = ∅ then 1 else 0) - (if U.card = 1 then 1 else 0) +
        (R.card : ℝ) * (if U.card = 1 then 1 else 0) := by
  by_cases he : U = ∅
  · simp [he, Concentrated]
  · by_cases hs : U.card = 1
    · simp [he, hs, concentrated_of_card_one U hs]
    · have hc : 2 ≤ U.card := by have := card_pos.mpr (nonempty_iff_ne_empty.mpr he); omega
      simp only [he, hs, if_false, sub_zero, mul_zero, add_zero, sum_boole]
      exact_mod_cast concentrated_candidates_card_le_one U R m hUm hc hR hprod

/-- The completion events are disjoint outside the empty and singleton old
survivor cases. This is not an independence assertion. -/
theorem concentratedFraction_sum_le (P R : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime) (m : ℕ)
    (hprod : ∀ p ∈ R, ∀ q ∈ R, p ≠ q → m ≤ p * q) :
    (∑ p ∈ R, concentratedFraction P p m) ≤
      1 - coveredFraction P m + ((R.card : ℝ) - 1) * singletonFraction P m := by
  classical
  have h := phaseMean_mono (P := P) (fun r => concentrated_count_pointwise
    (phaseSurvivors P m r) R m (filter_subset _ _) hR hprod)
  rw [phaseMean_sum] at h
  simp_rw [phaseSurvivors_empty_iff] at h
  rw [phaseMean_add, phaseMean_sub, phaseMean_sub, phaseMean_const P hP,
    phaseMean_mul] at h
  change (∑ p ∈ R, concentratedFraction P p m) ≤
    1 - coveredFraction P m - singletonFraction P m +
      (R.card : ℝ) * singletonFraction P m at h
  linarith

/-- The insertion identity transfers the aggregate bound to actual cover
increments, with no hidden independence assumption. -/
theorem weighted_cover_increment_sum_le (P R : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime)
    (hd : Disjoint P R) (m : ℕ)
    (hprod : ∀ p ∈ R, ∀ q ∈ R, p ≠ q → m ≤ p * q) :
    (∑ p ∈ R, (p : ℝ) * (coveredFraction (insert p P) m - coveredFraction P m)) ≤
      1 - coveredFraction P m + ((R.card : ℝ) - 1) * singletonFraction P m := by
  have he : (∑ p ∈ R, (p : ℝ) *
      (coveredFraction (insert p P) m - coveredFraction P m)) =
      ∑ p ∈ R, concentratedFraction P p m := by
    apply sum_congr rfl
    intro p hp
    have hn : p ∉ P := fun hh => disjoint_left.mp hd hh hp
    rw [coveredFraction_insert P p (hR p hp).pos hn]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hR p hp).ne_zero
    field_simp
    ring
  rw [he]
  exact concentratedFraction_sum_le P R hP hR m hprod

#print axioms concentrated_product_lt
#print axioms concentrated_candidates_card_le_one
#print axioms concentratedFraction_log_sum_le
#print axioms concentratedFraction_sum_le
#print axioms weighted_cover_increment_sum_le
end Erdos970.CoverFibers
