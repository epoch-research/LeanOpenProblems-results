import Submission.RoundedSieve

/-! Positional packing inequalities supplementing separate intersection counts.
These lemmas do not assert a uniform quadratic Jacobsthal bound. -/
namespace Erdos970.PatternPacking

open Erdos970.BrunCriterion

/-- A family whose pairwise common prime products exceed the interval length
can occur at at most one position. The condition also includes equal members. -/
theorem pattern_union_card_le_one (m : ℕ) (F : Finset (Finset ℕ)) (r : ℕ → ℕ)
    (hprime : ∀ A ∈ F, ∀ p ∈ A, p.Prime)
    (hcommon : ∀ A ∈ F, ∀ B ∈ F, m ≤ ∏ p ∈ A ∩ B, p) :
    ((Finset.range m).filter (fun i => ∃ A ∈ F, ∀ p ∈ A, i ≡ r p [MOD p])).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hi, A, hA, hiA⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj, B, hB, hjB⟩ := Finset.mem_filter.mp hj
  have hQ : ∀ p ∈ A ∩ B, p.Prime :=
    fun p hp => hprime A hA p (Finset.mem_inter.mp hp).1
  obtain ⟨b, hb⟩ := intersection_residue (A ∩ B) hQ r
  have hiQ : i ≡ b [MOD ∏ p ∈ A ∩ B, p] :=
    (hb i).mp (fun p hp => hiA p (Finset.mem_inter.mp hp).1)
  have hjQ : j ≡ b [MOD ∏ p ∈ A ∩ B, p] :=
    (hb j).mp (fun p hp => hjB p (Finset.mem_inter.mp hp).2)
  exact (hiQ.trans hjQ.symm).eq_of_lt_of_lt
    ((Finset.mem_range.mp hi).trans_le (hcommon A hA B hB))
    ((Finset.mem_range.mp hj).trans_le (hcommon A hA B hB))

/-- Two subsets of size at least three in a four-element set share two elements. -/
theorem two_common_of_three_of_card_four {α : Type*} [DecidableEq α]
    (P A B : Finset α) (hP : P.card = 4) (hA : A ⊆ P) (hB : B ⊆ P)
    (ha : 3 ≤ A.card) (hb : 3 ≤ B.card) : 2 ≤ (A ∩ B).card := by
  have hu : (A ∪ B).card ≤ P.card :=
    Finset.card_le_card (Finset.union_subset hA hB)
  have hh := Finset.card_union_add_card_inter A B
  omega

/-- For four primes whose pairwise products are at least the interval length,
at most one position can hit three or more of them. -/
theorem three_of_four_card_le_one (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ)
    (hP : P.card = 4) (hprime : ∀ p ∈ P, p.Prime)
    (hprod : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → m ≤ p * q) :
    ((Finset.range m).filter
      (fun i => 3 ≤ (P.filter (fun p => i ≡ r p [MOD p])).card)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hi, hiP⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj, hjP⟩ := Finset.mem_filter.mp hj
  have hh := two_common_of_three_of_card_four P
    (P.filter (fun p => i ≡ r p [MOD p]))
    (P.filter (fun p => j ≡ r p [MOD p])) hP
    (Finset.filter_subset _ _) (Finset.filter_subset _ _) hiP hjP
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 <
    ((P.filter (fun p => i ≡ r p [MOD p])) ∩
      (P.filter (fun p => j ≡ r p [MOD p]))).card)
  obtain ⟨hpI, hpJ⟩ := Finset.mem_inter.mp hp
  obtain ⟨hqI, hqJ⟩ := Finset.mem_inter.mp hq
  obtain ⟨hpP, hip⟩ := Finset.mem_filter.mp hpI
  obtain ⟨_, hjp⟩ := Finset.mem_filter.mp hpJ
  obtain ⟨hqP, hiq⟩ := Finset.mem_filter.mp hqI
  obtain ⟨_, hjq⟩ := Finset.mem_filter.mp hqJ
  have hc : p.Coprime q := (Nat.coprime_primes (hprime p hpP) (hprime q hqP)).mpr hpq
  have hij : i ≡ j [MOD p * q] := Nat.modEq_and_modEq_iff_modEq_mul hc |>.mp
    ⟨hip.trans hjp.symm, hiq.trans hjq.symm⟩
  exact hij.eq_of_lt_of_lt
    ((Finset.mem_range.mp hi).trans_le (hprod p hpP q hqP hpq))
    ((Finset.mem_range.mp hj).trans_le (hprod p hpP q hqP hpq))

/-- The threshold for three hits among four coordinates has a five-term polynomial. -/
theorem three_of_four_indicator {α : Type*} [DecidableEq α]
    (P : Finset α) (hP : P.card = 4) (f : α → Prop) [DecidablePred f] :
    (∑ Q ∈ P.powersetCard 3, (if ∀ p ∈ Q, f p then (1 : ℝ) else 0)) -
      3 * (if ∀ p ∈ P, f p then (1 : ℝ) else 0) =
        if 3 ≤ (P.filter f).card then 1 else 0 := by
  classical
  have hsets : (P.powersetCard 3).filter (fun Q => ∀ p ∈ Q, f p) =
      (P.filter f).powersetCard 3 := by
    ext Q
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hQP, hQcard⟩, hQf⟩
      exact ⟨fun p hp => Finset.mem_filter.mpr ⟨hQP hp, hQf p hp⟩, hQcard⟩
    · rintro ⟨hQ, hQcard⟩
      exact ⟨⟨fun p hp => (Finset.mem_filter.mp (hQ hp)).1, hQcard⟩,
        fun p hp => (Finset.mem_filter.mp (hQ hp)).2⟩
  have hsum : (∑ Q ∈ P.powersetCard 3, (if ∀ p ∈ Q, f p then (1 : ℝ) else 0)) =
      ((P.filter f).card.choose 3 : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, hsets, Finset.card_powersetCard]
    simp
  have hall : (∀ p ∈ P, f p) ↔ (P.filter f).card = 4 := by
    constructor
    · intro h
      rw [Finset.filter_eq_self.mpr h, hP]
    · intro h
      have he := Finset.eq_of_subset_of_card_le (Finset.filter_subset f P)
        (by omega : P.card ≤ (P.filter f).card)
      exact Finset.filter_eq_self.mp he
  have hle : (P.filter f).card ≤ 4 := by
    simpa [hP] using Finset.card_le_card (Finset.filter_subset f P)
  simp only [hsum, hall]
  generalize (P.filter f).card = n at *
  interval_cases n <;> norm_num

/-- The packing bound can therefore be used as a linear inequality in intersection counts. -/
theorem three_of_four_polynomial_sum_le_one (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ)
    (hP : P.card = 4) (hprime : ∀ p ∈ P, p.Prime)
    (hprod : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → m ≤ p * q) :
    (∑ i ∈ Finset.range m,
      ((∑ Q ∈ P.powersetCard 3,
        (if ∀ p ∈ Q, i ≡ r p [MOD p] then (1 : ℝ) else 0)) -
      3 * (if ∀ p ∈ P, i ≡ r p [MOD p] then (1 : ℝ) else 0))) ≤ 1 := by
  classical
  simp_rw [three_of_four_indicator P hP]
  rw [← Finset.sum_filter, Finset.sum_const]
  simpa using (show
    (((Finset.range m).filter
      (fun i => 3 ≤ (P.filter (fun p => i ≡ r p [MOD p])).card)).card : ℝ) ≤ 1 by
        exact_mod_cast three_of_four_card_le_one m P r hP hprime hprod)

/-- Four half-weight nonempty patterns give a small rational moment population. -/
def fourPatternDoubleCount (Q : Finset ℕ) : ℕ :=
  (if Q ⊆ {2, 3} then 1 else 0) + (if Q ⊆ {2, 5} then 1 else 0) +
    (if Q ⊆ {3, 5} then 1 else 0) + (if Q ⊆ {7} then 1 else 0)

/-- This population has total mass two and satisfies all separate rounded moment bounds. -/
theorem fourPatternDoubleCount_bounds (Q : Finset ℕ) (hQ : Q ⊆ {2, 3, 5, 7}) :
    2 * (2 / (∏ p ∈ Q, p)) ≤ fourPatternDoubleCount Q ∧
    fourPatternDoubleCount Q ≤
      2 * BlockSieve.SievePolynomial.ceilQuotient 2 (∏ p ∈ Q, p) := by
  have hh : ∀ A ∈ ({2, 3, 5, 7} : Finset ℕ).powerset,
      2 * (2 / (∏ p ∈ A, p)) ≤ fourPatternDoubleCount A ∧
      fourPatternDoubleCount A ≤
        2 * BlockSieve.SievePolynomial.ceilQuotient 2 (∏ p ∈ A, p) := by decide
  exact hh Q (Finset.mem_powerset.mpr hQ)

/-- The first three patterns cannot occur at different positions of an actual length-two interval. -/
theorem actual_three_pattern_packing (r : ℕ → ℕ) :
    ((Finset.range 2).filter (fun i =>
      ∃ A ∈ ({({2, 3} : Finset ℕ), {2, 5}, {3, 5}} : Finset (Finset ℕ)),
        ∀ p ∈ A, i ≡ r p [MOD p])).card ≤ 1 := by
  apply pattern_union_card_le_one
  · decide
  · decide

/-- Their half-weight masses total three halves, violating the additional packing bound. -/
theorem fourPattern_packing_violation :
    (1 : ℚ) < (1 / 2 + 1 / 2 + 1 / 2 : ℚ) := by norm_num

#print axioms three_of_four_polynomial_sum_le_one
#print axioms fourPatternDoubleCount_bounds
#print axioms actual_three_pattern_packing
#print axioms pattern_union_card_le_one
#print axioms three_of_four_card_le_one

end Erdos970.PatternPacking
