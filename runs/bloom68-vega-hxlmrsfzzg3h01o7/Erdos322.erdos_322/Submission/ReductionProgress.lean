import FormalConjecturesUtil

/-!
# Independent logical reductions for Erdős Problem 322

This file proves the cubic case and identifies the exact missing condition
for a disproof: a subpolynomial upper bound in at least one fixed degree
`k ≥ 4`. It supplies no such upper bound and does not prove or disprove
the universal conjecture. Neither admitted declaration in `Spec.lean` is
imported or used.
-/

namespace Erdos322ReductionProgress

-- Identical finite counting definition, isolated from the admitted declarations in Spec.lean.
def representationCount (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k → Fin (n + 1))).filter
    (fun a ↦ ∑ i, (a i : ℕ) ^ k = n)).card

lemma cubic_identity (p m : ℤ) :
    (p^4)^3 + (p*(9*m^3-p^3))^3 + (3*m*(3*m^3-p^3))^3 = 729*m^12 := by
  ring

lemma representationCount_zero (k : ℕ) : representationCount k 0 = 1 := by
  cases k with
  | zero => simp [representationCount]
  | succ k => simp [representationCount]


lemma cubic_identity_nat {p m : ℕ} (hp : p ≤ m) :
    (p^4)^3 + (p*(9*m^3-p^3))^3 + (3*m*(3*m^3-p^3))^3 = 729*m^12 := by
  have hpow : p^3 ≤ m^3 := Nat.pow_le_pow_left hp 3
  have h3 : p^3 ≤ 3*m^3 := by omega
  have h9 : p^3 ≤ 9*m^3 := by omega
  zify [h3, h9]
  ring

def cubicTuple (m p : ℕ) : Fin 3 → ℕ :=
  ![p^4, p*(9*m^3-p^3), 3*m*(3*m^3-p^3)]

lemma cubicTuple_sum {m p : ℕ} (hp : p ≤ m) :
    ∑ i, (cubicTuple m p i)^3 = 729*m^12 := by
  simpa [cubicTuple, Fin.sum_univ_succ, add_assoc] using cubic_identity_nat hp

lemma cubicTuple_bound {m p : ℕ} (hp : p ≤ m) (i : Fin 3) :
    cubicTuple m p i ≤ 729*m^12 := by
  calc
    cubicTuple m p i ≤ (cubicTuple m p i)^3 := Nat.le_self_pow (by decide) _
    _ ≤ ∑ j, (cubicTuple m p j)^3 :=
      Finset.single_le_sum (f := fun j : Fin 3 ↦ (cubicTuple m p j)^3)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    _ = 729*m^12 := cubicTuple_sum hp

lemma cubic_lower_bound (m : ℕ) : m+1 ≤ representationCount 3 (729*m^12) := by
  let f : Fin (m+1) → (Fin 3 → Fin (729*m^12+1)) :=
    fun p i ↦ ⟨cubicTuple m p i, Nat.lt_succ_of_le
      (cubicTuple_bound (Nat.le_of_lt_succ p.isLt) i)⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Fin.ext
    apply Nat.pow_left_injective (by decide : 4 ≠ 0)
    exact congrArg (fun a ↦ (a 0).val) hpq
  have hmem (p : Fin (m+1)) :
      f p ∈ ((Finset.univ : Finset (Fin 3 → Fin (729*m^12+1))).filter
        (fun a ↦ ∑ i, (a i : ℕ)^3 = 729*m^12)) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, cubicTuple_sum (Nat.le_of_lt_succ p.isLt)⟩
  have h := Finset.card_le_card_of_injOn (s := Finset.univ) f (fun p _ ↦ hmem p) hf.injOn
  simpa [representationCount] using h

lemma cubic_power_gap (m : ℕ) : 729*m^12 < (m+1)^24 := by
  have h3 : 3*m < (m+1)^2 := by
    have h := Nat.le_self_pow (by decide : 2 ≠ 0) m
    nlinarith
  calc
    729*m^12 ≤ (3*m)^12 := by rw [mul_pow]; norm_num; omega
    _ < ((m+1)^2)^12 := Nat.pow_lt_pow_left h3 (by decide)
    _ = (m+1)^24 := by ring

lemma cubic_rpow_gap (m : ℕ) :
    ((729*m^12 : ℕ) : ℝ) ^ (1/24 : ℝ) < ((m+1 : ℕ) : ℝ) := by
  rw [one_div]
  apply (Real.rpow_inv_lt_iff_of_pos (by positivity) (by positivity)
    (by norm_num : (0:ℝ)<24)).2
  exact_mod_cast cubic_power_gap m

lemma cubic_infinite :
    {n : ℕ | (n : ℝ)^(1/24 : ℝ) < representationCount 3 n}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun m : ℕ ↦ 729*m^12)
  · intro m l h
    apply Nat.pow_left_injective (by decide : 12 ≠ 0)
    change 729*m^12 = 729*l^12 at h
    change m^12 = l^12
    omega
  · intro m
    change ((729*m^12 : ℕ) : ℝ)^(1/24 : ℝ) < (representationCount 3 (729*m^12) : ℝ)
    exact (cubic_rpow_gap m).trans_le (by exact_mod_cast cubic_lower_bound m)

lemma cubic_case : ∃ c > (0:ℝ),
    {n : ℕ | (n : ℝ)^c < representationCount 3 n}.Infinite :=
  ⟨1/24, by norm_num, cubic_infinite⟩


lemma exact_negation_iff :
    (¬ (∀ k : ℕ, 3 ≤ k → ∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ)^c < representationCount k n}.Infinite)) ↔
    ∃ k : ℕ, 3 ≤ k ∧ ∀ c > (0 : ℝ), ∃ N : ℕ, ∀ n : ℕ,
      N < n → (representationCount k n : ℝ) ≤ (n : ℝ)^c := by
  classical
  constructor
  · intro h
    obtain ⟨k, h⟩ := not_forall.mp h
    obtain ⟨hk, h⟩ := _root_.not_imp.mp h
    refine ⟨k, hk, ?_⟩
    intro c hc
    have hnot : ¬ {n : ℕ | (n : ℝ)^c < representationCount k n}.Infinite :=
      fun hi ↦ h ⟨c, hc, hi⟩
    rw [Set.infinite_iff_exists_gt] at hnot
    push_neg at hnot
    obtain ⟨N, hN⟩ := hnot
    refine ⟨N, ?_⟩
    intro n hn
    exact le_of_not_gt (fun hh ↦ (not_le_of_gt hn) (hN n hh))
  · rintro ⟨k, hk, hb⟩ h
    obtain ⟨c, hc, hi⟩ := h k hk
    obtain ⟨N, hN⟩ := hb c hc
    obtain ⟨n, hn, hnN⟩ := hi.exists_gt N
    exact (not_lt_of_ge (hN n hnN)) hn

/-- Positive-power large values at infinitely many arguments. -/
def PowerLarge (k : ℕ) : Prop :=
  ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < representationCount k n}.Infinite

/-- The usual subpolynomial upper bound, excluding the argument zero. -/
def Subpolynomial (k : ℕ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
    (representationCount k n : ℝ) ≤ C * (n : ℝ)^ε

lemma subpolynomial_of_not_powerLarge (k : ℕ) (h : ¬ PowerLarge k) :
    Subpolynomial k := by
  classical
  intro ε hε
  have hnot : ¬ {n : ℕ | (n : ℝ)^ε < representationCount k n}.Infinite :=
    fun hi ↦ h ⟨ε, hε, hi⟩
  rw [Set.infinite_iff_exists_gt] at hnot
  push_neg at hnot
  obtain ⟨N, hN⟩ := hnot
  let C : ℕ := 1 + ∑ i ∈ Finset.range (N+1), representationCount k i
  have hC : 1 ≤ C := by simp [C]
  refine ⟨C, by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hC), ?_⟩
  intro n hn
  have hpow : 1 ≤ (n : ℝ)^ε := Real.one_le_rpow (by exact_mod_cast hn) hε.le
  by_cases hsmall : n ≤ N
  · have hbound : representationCount k n ≤ C := by
      have hs : representationCount k n ≤
          ∑ i ∈ Finset.range (N+1), representationCount k i :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr (by omega))
      exact hs.trans (by dsimp [C]; omega)
    calc
      (representationCount k n : ℝ) ≤ (C : ℝ) := by exact_mod_cast hbound
      _ ≤ (C : ℝ) * (n : ℝ)^ε := le_mul_of_one_le_right (by positivity) hpow
  · have hbound : (representationCount k n : ℝ) ≤ (n : ℝ)^ε :=
      le_of_not_gt (fun hb ↦ hsmall (hN n hb))
    exact hbound.trans (le_mul_of_one_le_left (by positivity) (by exact_mod_cast hC))

lemma not_powerLarge_of_subpolynomial (k : ℕ) (h : Subpolynomial k) :
    ¬ PowerLarge k := by
  rintro ⟨c, hc, hi⟩
  obtain ⟨C, hC, hb⟩ := h (c/2) (by positivity)
  have ht : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)^(c/2)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < c/2)).comp
      tendsto_natCast_atTop_atTop
  have he : ∀ᶠ n : ℕ in Filter.atTop, C ≤ (n : ℝ)^(c/2) :=
    Filter.tendsto_atTop.mp ht C
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  obtain ⟨n, hn, hngt⟩ := hi.exists_gt N
  have hnpos : 0 < n := by omega
  have hbound : (representationCount k n : ℝ) ≤ (n : ℝ)^c := by
    calc
      (representationCount k n : ℝ) ≤ C * (n : ℝ)^(c/2) := hb n hnpos
      _ ≤ (n : ℝ)^(c/2) * (n : ℝ)^(c/2) :=
        mul_le_mul_of_nonneg_right (hN n (by omega)) (by positivity)
      _ = (n : ℝ)^c := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < n)]
        congr 1
        ring
  exact (not_lt_of_ge hbound) hn

/-- The exact logical relation with the customary Hypothesis K bound. -/
theorem not_powerLarge_iff_subpolynomial (k : ℕ) :
    ¬ PowerLarge k ↔ Subpolynomial k :=
  ⟨subpolynomial_of_not_powerLarge k, not_powerLarge_of_subpolynomial k⟩

/-- The cubic case is excluded from any valid counterexample to the universal claim. -/
theorem exact_remaining_disproof_iff :
    (¬ (∀ k : ℕ, 3 ≤ k → ∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ)^c < representationCount k n}.Infinite)) ↔
    ∃ k : ℕ, 4 ≤ k ∧ Subpolynomial k := by
  classical
  constructor
  · intro h
    obtain ⟨k, h⟩ := not_forall.mp h
    obtain ⟨hk, h⟩ := _root_.not_imp.mp h
    have hne : k ≠ 3 := by
      rintro rfl
      exact h cubic_case
    refine ⟨k, by omega, ?_⟩
    exact subpolynomial_of_not_powerLarge k h
  · rintro ⟨k, hk, hs⟩ h
    exact not_powerLarge_of_subpolynomial k hs (h k (by omega))

#print axioms cubic_case
#print axioms not_powerLarge_iff_subpolynomial
#print axioms exact_remaining_disproof_iff

end Erdos322ReductionProgress
