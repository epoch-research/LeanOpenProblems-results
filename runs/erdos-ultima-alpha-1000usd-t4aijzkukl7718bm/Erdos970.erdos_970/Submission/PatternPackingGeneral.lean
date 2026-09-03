import Submission.PatternPacking

/-! All-but-one hit thresholds and general separated-pattern packing. -/
namespace Erdos970.PatternPacking

open Erdos970.BrunCriterion

/-- If every product of all but two block primes is at least the interval length,
at most one position can hit all but one block prime. -/
theorem all_but_one_card_le_one (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ)
    (hcard : 2 ≤ P.card) (hprime : ∀ p ∈ P, p.Prime)
    (hprod : ∀ Q ⊆ P, Q.card = P.card - 2 → m ≤ ∏ p ∈ Q, p) :
    ((Finset.range m).filter (fun i => P.card - 1 ≤
      (P.filter (fun p => i ≡ r p [MOD p])).card)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hi, hiP⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj, hjP⟩ := Finset.mem_filter.mp hj
  let A := P.filter (fun p => i ≡ r p [MOD p])
  let B := P.filter (fun p => j ≡ r p [MOD p])
  have hA : A ⊆ P := Finset.filter_subset _ _
  have hB : B ⊆ P := Finset.filter_subset _ _
  have hU : (A ∪ B).card ≤ P.card := Finset.card_le_card (Finset.union_subset hA hB)
  have hI : P.card - 2 ≤ (A ∩ B).card := by
    have hh := Finset.card_union_add_card_inter A B
    change P.card - 1 ≤ A.card at hiP
    change P.card - 1 ≤ B.card at hjP
    omega
  obtain ⟨Q, hQ, hQcard⟩ := Finset.exists_subset_card_eq hI
  have hQP : Q ⊆ P := fun p hp => hA (Finset.mem_inter.mp (hQ hp)).1
  obtain ⟨b, hb⟩ := intersection_residue Q (fun p hp => hprime p (hQP hp)) r
  have hiQ : i ≡ b [MOD ∏ p ∈ Q, p] := (hb i).mp (fun p hp =>
    (Finset.mem_filter.mp (Finset.mem_inter.mp (hQ hp)).1).2)
  have hjQ : j ≡ b [MOD ∏ p ∈ Q, p] := (hb j).mp (fun p hp =>
    (Finset.mem_filter.mp (Finset.mem_inter.mp (hQ hp)).2).2)
  exact (hiQ.trans hjQ.symm).eq_of_lt_of_lt
    ((Finset.mem_range.mp hi).trans_le (hprod Q hQP hQcard))
    ((Finset.mem_range.mp hj).trans_le (hprod Q hQP hQcard))

/-- A threshold at all but one hit still has only one term per deleted coordinate,
plus the full-block monomial. -/
theorem all_but_one_indicator {α : Type*} [DecidableEq α]
    (P : Finset α) (n : ℕ) (hP : P.card = n + 1)
    (f : α → Prop) [DecidablePred f] :
    (∑ Q ∈ P.powersetCard n, (if ∀ p ∈ Q, f p then (1 : ℝ) else 0)) -
      (n : ℝ) * (if ∀ p ∈ P, f p then (1 : ℝ) else 0) =
        if n ≤ (P.filter f).card then 1 else 0 := by
  classical
  have hsets : (P.powersetCard n).filter (fun Q => ∀ p ∈ Q, f p) =
      (P.filter f).powersetCard n := by
    ext Q
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hQP, hQcard⟩, hQf⟩
      exact ⟨fun p hp => Finset.mem_filter.mpr ⟨hQP hp, hQf p hp⟩, hQcard⟩
    · rintro ⟨hQ, hQcard⟩
      exact ⟨⟨fun p hp => (Finset.mem_filter.mp (hQ hp)).1, hQcard⟩,
        fun p hp => (Finset.mem_filter.mp (hQ hp)).2⟩
  have hsum : (∑ Q ∈ P.powersetCard n, (if ∀ p ∈ Q, f p then (1 : ℝ) else 0)) =
      ((P.filter f).card.choose n : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, hsets, Finset.card_powersetCard]
    simp
  have hall : (∀ p ∈ P, f p) ↔ (P.filter f).card = n + 1 := by
    constructor
    · intro h
      rw [Finset.filter_eq_self.mpr h, hP]
    · intro h
      have he := Finset.eq_of_subset_of_card_le (Finset.filter_subset f P)
        (by omega : P.card ≤ (P.filter f).card)
      exact Finset.filter_eq_self.mp he
  have hle : (P.filter f).card ≤ n + 1 := by
    simpa [hP] using Finset.card_le_card (Finset.filter_subset f P)
  simp only [hsum, hall]
  by_cases hlt : (P.filter f).card < n
  · simp [Nat.choose_eq_zero_of_lt hlt, not_le.mpr hlt]
    omega
  · have he : (P.filter f).card = n ∨ (P.filter f).card = n + 1 := by omega
    rcases he with he | he
    · simp [he]
    · simp [he, Nat.choose_succ_self_right]

/-- A finite set with minimum gap `d` has at most the ceiling of `m/d` points below `m`. -/
theorem separated_card_le_ceil (S : Finset ℕ) (m d : ℕ) (hd : 0 < d)
    (hm : ∀ i ∈ S, i < m)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i < j → d ≤ j - i) :
    S.card ≤ BlockSieve.SievePolynomial.ceilQuotient m d := by
  classical
  apply (Finset.card_le_card_of_injOn (s := S)
    (t := Finset.range (BlockSieve.SievePolynomial.ceilQuotient m d))
    (fun i => i / d) ?_ ?_).trans_eq (Finset.card_range _)
  · intro i hi
    change i / d ∈ Finset.range _
    rw [Finset.mem_range]
    unfold BlockSieve.SievePolynomial.ceilQuotient
    by_cases hmod : m % d = 0
    · rw [if_pos hmod, Nat.add_zero]
      apply (Nat.div_lt_iff_lt_mul hd).mpr
      have hh := Nat.mod_add_div m d
      rw [hmod, Nat.zero_add, Nat.mul_comm] at hh
      simpa [hh] using hm i hi
    · rw [if_neg hmod]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (hm i hi).le)
  · intro i hi j hj hij
    change i / d = j / d at hij
    have hi0 := Nat.mod_add_div i d
    have hj0 := Nat.mod_add_div j d
    have hi1 := Nat.mod_lt i hd
    have hj1 := Nat.mod_lt j hd
    rw [hij] at hi0
    rcases lt_trichotomy i j with h | h | h
    · have hh := hsep i hi j hj h
      omega
    · exact h
    · have hh := hsep j hj i hi h
      omega

/-- Families with a lower bound on common products have an exact spacing budget. -/
theorem pattern_union_card_le_ceil (m d : ℕ) (hd : 0 < d)
    (F : Finset (Finset ℕ)) (r : ℕ → ℕ)
    (hprime : ∀ A ∈ F, ∀ p ∈ A, p.Prime)
    (hcommon : ∀ A ∈ F, ∀ B ∈ F, d ≤ ∏ p ∈ A ∩ B, p) :
    ((Finset.range m).filter (fun i => ∃ A ∈ F, ∀ p ∈ A, i ≡ r p [MOD p])).card ≤
      BlockSieve.SievePolynomial.ceilQuotient m d := by
  classical
  apply separated_card_le_ceil _ m d hd
  · intro i hi
    exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  · intro i hi j hj hij
    obtain ⟨_, A, hA, hiA⟩ := Finset.mem_filter.mp hi
    obtain ⟨_, B, hB, hjB⟩ := Finset.mem_filter.mp hj
    have hQ : ∀ p ∈ A ∩ B, p.Prime :=
      fun p hp => hprime A hA p (Finset.mem_inter.mp hp).1
    obtain ⟨b, hb⟩ := intersection_residue (A ∩ B) hQ r
    have hiQ : i ≡ b [MOD ∏ p ∈ A ∩ B, p] :=
      (hb i).mp (fun p hp => hiA p (Finset.mem_inter.mp hp).1)
    have hjQ : j ≡ b [MOD ∏ p ∈ A ∩ B, p] :=
      (hb j).mp (fun p hp => hjB p (Finset.mem_inter.mp hp).2)
    have hdvd : (∏ p ∈ A ∩ B, p) ∣ j - i :=
      (Nat.modEq_iff_dvd' hij.le).mp (hiQ.trans hjQ.symm)
    exact (hcommon A hA B hB).trans
      (Nat.le_of_dvd (Nat.sub_pos_of_lt hij) hdvd)

#print axioms pattern_union_card_le_ceil
#print axioms all_but_one_card_le_one
#print axioms all_but_one_indicator
#print axioms separated_card_le_ceil

end Erdos970.PatternPacking
