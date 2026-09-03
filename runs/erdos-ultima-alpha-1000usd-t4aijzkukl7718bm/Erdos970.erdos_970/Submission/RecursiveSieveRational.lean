import Submission.RecursiveSieveTransfer

/-! A computable rational form of the recursive first-hit envelope. -/
namespace Erdos970.RecursiveSieve

section Linear
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- At each node the expected intersection mass is `x`. The lower branch is
permitted to return zero when `x ≤ k+1`, which makes evaluation much cheaper. -/
def linearEnvelope (q : ℕ → R) (k : ℕ) (x : R) : R × R :=
  (if x ≤ (k : R) + 1 then 0 else max 0 (x - 1 -
      ∑ i : Fin k, (linearEnvelope q i.val (x * q i.val)).2),
    x + 1 - ∑ i : Fin k, (linearEnvelope q i.val (x * q i.val)).1)
termination_by k

end Linear

theorem linearEnvelope_eq_envelope (q : ℕ → ℝ) (m : ℝ) (k : ℕ) (T : Finset ℕ)
    (hT : ∀ i ∈ T, k ≤ i) :
    linearEnvelope q k (m * ∏ i ∈ T, q i) =
      envelope (fun T => m * ∏ i ∈ T, q i - 1)
        (fun T => m * ∏ i ∈ T, q i + 1)
        (fun n T => decide ((n : ℝ) + 1 < m * ∏ i ∈ T, q i)) k T := by
  induction k using Nat.strong_induction_on generalizing T with
  | h k ih =>
    have hn (i : Fin k) : i.val ∉ T := by
      intro hi
      exact (not_lt_of_ge (hT i.val hi)) i.isLt
    have ht (i : Fin k) : ∀ j ∈ insert i.val T, i.val ≤ j := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact le_rfl
      · exact i.isLt.le.trans (hT j hj)
    have hm (i : Fin k) : m * ∏ j ∈ insert i.val T, q j =
        (m * ∏ j ∈ T, q j) * q i.val := by
      rw [Finset.prod_insert (hn i)]
      ring
    have he (i : Fin k) := ih i.val i.isLt (insert i.val T) (ht i)
    simp only [hm] at he
    conv_lhs => rw [linearEnvelope]
    conv_rhs => rw [envelope]
    simp only [← he, Bool.decide_coe]
    by_cases hx : m * ∏ i ∈ T, q i ≤ (k : ℝ) + 1
    · simp [hx, not_lt.mpr hx]
    · simp [hx, lt_of_not_ge hx]

/-- Only the coordinates strictly below `k` enter the recursion. -/
theorem linearEnvelope_congr {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (q r : ℕ → R) (k : ℕ) (x : R)
    (hqr : ∀ i < k, q i = r i) : linearEnvelope q k x = linearEnvelope r k x := by
  induction k using Nat.strong_induction_on generalizing x with
  | h k ih =>
    have he (i : Fin k) : linearEnvelope q i.val (x * q i.val) =
        linearEnvelope r i.val (x * r i.val) := by
      rw [hqr i.val i.isLt]
      exact ih i.val i.isLt _ (fun j hj => hqr j (hj.trans i.isLt))
    conv_lhs => rw [linearEnvelope]
    conv_rhs => rw [linearEnvelope]
    simp only [he]

/-- Rational evaluation and real evaluation agree. No native evaluator is needed. -/
theorem cast_linearEnvelope (q : ℕ → ℚ) (k : ℕ) (x : ℚ) :
    Prod.map (fun y : ℚ => (y : ℝ)) (fun y : ℚ => (y : ℝ))
        (linearEnvelope q k x) =
      linearEnvelope (fun i => (q i : ℝ)) k (x : ℝ) := by
  induction k using Nat.strong_induction_on generalizing x with
  | h k ih =>
    have hl (i : Fin k) := congrArg Prod.fst (ih i.val i.isLt (x * q i.val))
    have hu (i : Fin k) := congrArg Prod.snd (ih i.val i.isLt (x * q i.val))
    simp only [Prod.map_fst, Prod.map_snd, Rat.cast_mul] at hl hu
    have hc : ((x : ℝ) ≤ (k : ℝ) + 1) ↔ x ≤ (k : ℚ) + 1 := by
      exact_mod_cast (Iff.rfl : x ≤ (k : ℚ) + 1 ↔ x ≤ (k : ℚ) + 1)
    conv_lhs => arg 3; rw [linearEnvelope]
    conv_rhs => rw [linearEnvelope]
    apply Prod.ext
    · dsimp only [Prod.map, Prod.fst]
      simp only [hc]
      split_ifs
      · simp
      · simp only [Rat.cast_max, Rat.cast_zero, Rat.cast_sub, Rat.cast_one,
          Rat.cast_sum, hu]
    · dsimp only [Prod.map, Prod.snd]
      simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_sum, hl]

/-- Extend a finite reference marginal by one. These extra coordinates are always hit. -/
def extendMarginal {K : ℕ} (q : Fin K → ℝ) (i : ℕ) : ℝ :=
  if h : i < K then q ⟨i,h⟩ else 1

lemma liftSet_insert_lt {K : ℕ} (T : Finset ℕ) (i : ℕ) (hi : i < K) :
    liftSet K (insert i T) = insert ⟨i,hi⟩ (liftSet K T) := by
  ext j
  simp [liftSet, Fin.ext_iff]

lemma liftSet_insert_ge {K : ℕ} (T : Finset ℕ) (i : ℕ) (hi : K ≤ i) :
    liftSet K (insert i T) = liftSet K T := by
  ext j
  have hj : j.val ≠ i := by have := j.isLt; omega
  simp [liftSet, hj]

lemma prod_extendMarginal {K : ℕ} (q : Fin K → ℝ) (T : Finset ℕ) :
    (∏ i ∈ T, extendMarginal q i) = ∏ i ∈ liftSet K T, q i := by
  induction T using Finset.induction_on with
  | empty => simp [liftSet]
  | @insert i T hi ih =>
    rw [Finset.prod_insert hi, ih]
    by_cases hik : i < K
    · have hnot : (⟨i,hik⟩ : Fin K) ∉ liftSet K T := by simp [liftSet, hi]
      rw [liftSet_insert_lt T i hik, Finset.prod_insert hnot]
      simp [extendMarginal, hik]
    · rw [liftSet_insert_ge T i (Nat.le_of_not_gt hik)]
      simp [extendMarginal, hik]

/-- A computable recursive envelope at dominating marginals suffices. -/
theorem survivor_of_positive_linearEnvelope (K m : ℕ) (q q' : Fin K → ℝ)
    (hq : ∀ i, q i < 1 ∧ q i ≤ q' i ∧ q' i ≤ 1)
    (ω : ℕ → Fin K → Bool)
    (herr : ∀ T : Finset (Fin K),
      |(∑ j ∈ Finset.range m, FiniteSelberg.hitMonomial T (ω j)) -
        (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (hpos : 0 < (linearEnvelope (extendMarginal q') K (m : ℝ)).1) :
    ∃ j < m, ∀ i, ω j i = false := by
  have he := linearEnvelope_eq_envelope (extendMarginal q') (m : ℝ) K ∅
    (by simp)
  simp only [Finset.prod_empty, mul_one, prod_extendMarginal] at he
  rw [he] at hpos
  exact survivor_from_dominating_envelope K m q q' hq ω herr _ hpos

#print axioms cast_linearEnvelope
#print axioms survivor_of_positive_linearEnvelope
end Erdos970.RecursiveSieve
