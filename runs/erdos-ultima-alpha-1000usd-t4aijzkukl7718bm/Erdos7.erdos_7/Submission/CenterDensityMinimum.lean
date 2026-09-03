import Submission.AffineUnitDensity

/-! A weighted covering-cost certificate that a normalized centre minimizes
all affine unit-density tests. This is an auxiliary obstruction to a method,
not an odd covering system. -/
namespace Erdos7CenterDensityMinimum
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable
attribute [local instance] Nat.decidablePrime'
variable {I : Type} [Fintype I]

def composite (m : I → ℕ) : Finset I := Finset.univ.filter (fun i => ¬ (m i).Prime)
def primes (m : I → ℕ) : Finset I := Finset.univ.filter (fun i => (m i).Prime)

def score (m : I → ℕ) (a : I → ℤ) (w : I → ℚ) (c : ℤ) : ℚ :=
  ∑ i, if IsUnit ((a i-c : ℤ) : ZMod (m i)) then w i else 0

def row (m : I → ℕ) (a : I → ℤ) (w : I → ℚ) (i : I) (c : ℤ) : ℚ :=
  ∑ j ∈ composite m, if m i ∣ m j ∧ (m i : ℤ) ∣ a j-c then w j else 0

lemma missing_unit_has_prime (m : I → ℕ) (a : I → ℤ)
    (hclosed : ∀ j p, p.Prime → p ∣ m j → ∃ i, m i = p)
    (j : I) (c : ℤ) (hj : ¬ IsUnit ((a j-c : ℤ) : ZMod (m j))) :
    ∃ i ∈ primes m, m i ∣ m j ∧ (m i : ℤ) ∣ a j-c := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_nat_coprime] at hj
  simp only [Int.natAbs_natCast] at hj
  obtain ⟨p,hp,hpm,hpa⟩ := Nat.Prime.not_coprime_iff_dvd.mp hj
  obtain ⟨i,hi⟩ := hclosed j p hp hpm
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi ▸ hp⟩, ?_⟩
  rw [hi]
  exact ⟨hpm, Int.natCast_dvd.mpr hpa⟩

/-- Any lost composite term is charged to a changed prime coordinate. If every
one-coordinate column is paid for by that prime term, changing several
coordinates cannot improve the total score either. -/
theorem score_ge_composite_sum (m : I → ℕ) (a : I → ℤ) (w : I → ℚ)
    (hw : ∀ i, 0 ≤ w i)
    (hclosed : ∀ j p, p.Prime → p ∣ m j → ∃ i, m i = p)
    (hrow : ∀ i, (m i).Prime → ∀ c : ℤ,
      row m a w i c ≤ if IsUnit ((a i-c : ℤ) : ZMod (m i)) then w i else 0) (c : ℤ) :
    ∑ j ∈ composite m, w j ≤ score m a w c := by
  let S (i : I) : ℚ := if IsUnit ((a i-c : ℤ) : ZMod (m i)) then w i else 0
  let Q (i j : I) : ℚ := if m i ∣ m j ∧ (m i : ℤ) ∣ a j-c then w j else 0
  have hQ (i j : I) : 0 ≤ Q i j := by
    dsimp [Q]
    split_ifs
    · exact hw j
    · exact le_refl 0
  have hpoint (j : I) : w j ≤ S j + ∑ i ∈ primes m, Q i j := by
    by_cases hj : IsUnit ((a j-c : ℤ) : ZMod (m j))
    · have hh : 0 ≤ ∑ i ∈ primes m, Q i j := Finset.sum_nonneg (fun i _ => hQ i j)
      simp only [S, if_pos hj]
      linarith
    · obtain ⟨i,hi,hij⟩ := missing_unit_has_prime m a hclosed j c hj
      have hh := Finset.single_le_sum (fun k (_ : k ∈ primes m) => hQ k j) hi
      simpa only [S, Q, if_neg hj, if_pos hij, zero_add] using hh
  calc
    ∑ j ∈ composite m, w j ≤ ∑ j ∈ composite m, (S j + ∑ i ∈ primes m, Q i j) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = (∑ j ∈ composite m, S j) + ∑ i ∈ primes m, row m a w i c := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      rfl
    _ ≤ (∑ j ∈ composite m, S j) + ∑ i ∈ primes m, S i := by
      exact add_le_add (le_refl _) (Finset.sum_le_sum
        (fun i hi => hrow i (Finset.mem_filter.mp hi).2 c))
    _ = score m a w c := by
      simp only [composite, primes, Finset.sum_filter, score, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (m i).Prime <;> simp [hi,S]

/-- When the baseline centre removes exactly the prime terms, the row
certificate proves it is a global minimizer, not merely a local minimum. -/
theorem zero_minimizes (m : I → ℕ) (a : I → ℤ) (w : I → ℚ)
    (hw : ∀ i, 0 ≤ w i)
    (hclosed : ∀ j p, p.Prime → p ∣ m j → ∃ i, m i = p)
    (hzero : ∀ i, IsUnit (a i : ZMod (m i)) ↔ ¬ (m i).Prime)
    (hrow : ∀ i, (m i).Prime → ∀ c : ℤ,
      row m a w i c ≤ if IsUnit ((a i-c : ℤ) : ZMod (m i)) then w i else 0) (c : ℤ) :
    score m a w 0 ≤ score m a w c := by
  have he : score m a w 0 = ∑ j ∈ composite m, w j := by
    simp only [score, sub_zero, hzero, composite, Finset.sum_filter]
  rw [he]
  exact score_ge_composite_sum m a w hw hclosed hrow c

lemma row_congr_center (m : I → ℕ) (a : I → ℤ) (w : I → ℚ)
    (i : I) (c d : ℤ) (hcd : c ≡ d [ZMOD (m i : ℤ)]) :
    row m a w i c = row m a w i d := by
  have he (j : I) : (m i : ℤ) ∣ a j-c ↔ (m i : ℤ) ∣ a j-d := by
    rw [← Int.modEq_iff_dvd, ← Int.modEq_iff_dvd]
    exact ⟨fun h => hcd.symm.trans h, fun h => hcd.trans h⟩
  simp only [row, he]

lemma prime_center_unit_iff {p : ℕ} (hp : p.Prime) (c : ℤ) :
    IsUnit ((-c : ℤ) : ZMod p) ↔ ¬ (p : ℤ) ∣ c := by
  rw [Int.cast_neg, IsUnit.neg_iff, ZMod.coe_int_isUnit_iff_isCoprime,
    Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast,
    hp.coprime_iff_not_dvd, ← Int.natCast_dvd]

/-- Only finitely many nonzero root columns need checking at each prime. -/
theorem row_bound_of_finite (m : I → ℕ) (a : I → ℤ) (w : I → ℚ)
    (hzero : ∀ i, (m i).Prime → a i = 0)
    (hfin : ∀ i, (m i).Prime → ∀ t : Fin (m i),
      row m a w i (t.val : ℤ) ≤ if t.val = 0 then 0 else w i) :
    ∀ i, (m i).Prime → ∀ c : ℤ,
      row m a w i c ≤ if IsUnit ((a i-c : ℤ) : ZMod (m i)) then w i else 0 := by
  intro i hpi c
  have hpos : (0 : ℤ) < m i := by exact_mod_cast hpi.pos
  have hn := Int.emod_nonneg c hpos.ne'
  let t : Fin (m i) := ⟨(c % (m i : ℤ)).toNat, by
    have hlt := Int.emod_lt_of_pos c hpos
    exact_mod_cast (show (((c % (m i : ℤ)).toNat : ℕ) : ℤ) < m i by
      rw [Int.toNat_of_nonneg hn]; exact hlt)⟩
  have ht : (t.val : ℤ) = c % (m i : ℤ) := Int.toNat_of_nonneg hn
  have hct : c ≡ (t.val : ℤ) [ZMOD (m i : ℤ)] := by
    rw [ht]
    exact (Int.mod_modEq _ _).symm
  rw [row_congr_center m a w i c t.val hct, hzero i hpi, zero_sub]
  simp only [prime_center_unit_iff hpi]
  have hz : t.val = 0 ↔ (m i : ℤ) ∣ c := by
    rw [Int.dvd_iff_emod_eq_zero, ← ht]
    exact Int.natCast_eq_zero.symm
  have hh := hfin i hpi t
  by_cases hd : (m i : ℤ) ∣ c
  · simpa only [if_neg (not_not.mpr hd), if_pos (hz.mpr hd)] using hh
  · simpa only [if_pos hd, if_neg (fun ht0 => hd (hz.mp ht0))] using hh

#print axioms row_bound_of_finite
#print axioms score_ge_composite_sum
#print axioms zero_minimizes
end
end Erdos7CenterDensityMinimum
