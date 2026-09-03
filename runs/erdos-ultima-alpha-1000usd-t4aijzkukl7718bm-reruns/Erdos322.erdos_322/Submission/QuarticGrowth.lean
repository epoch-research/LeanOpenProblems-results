import FormalConjecturesUtil

/-! Explicit unbounded quartic representation counts via the Eisenstein norm. -/

namespace Erdos322

def representationCount (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k → Fin (n + 1))).filter
    (fun a ↦ ∑ i, (a i : ℕ) ^ k = n)).card

private def eisenPair : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | t + 1 =>
    let p := eisenPair t
    (p.1 - 2 * p.2, 2 * p.1 + 3 * p.2)

private theorem eisenPair_norm (t : ℕ) :
    (eisenPair t).1 ^ 2 + (eisenPair t).1 * (eisenPair t).2 +
      (eisenPair t).2 ^ 2 = (7 : ℤ) ^ t := by
  induction t with
  | zero => norm_num [eisenPair]
  | succ t ht =>
    simp only [eisenPair, pow_succ]
    nlinarith [ht]

private theorem eisenPair_residues (t : ℕ) :
    ((eisenPair t).1 % 7 = 1 ∧ (eisenPair t).2 % 7 = 0) ∨
    ((eisenPair t).1 % 7 = 1 ∧ (eisenPair t).2 % 7 = 2) ∨
    ((eisenPair t).1 % 7 = 4 ∧ (eisenPair t).2 % 7 = 1) ∨
    ((eisenPair t).1 % 7 = 2 ∧ (eisenPair t).2 % 7 = 4) := by
  induction t with
  | zero => norm_num [eisenPair]
  | succ t ht =>
    simp only [eisenPair]
    rcases ht with h | h | h | h <;> omega

private theorem eisenPair_first_not_dvd (t : ℕ) :
    ¬ (7 : ℤ) ∣ (eisenPair t).1 := by
  have h := eisenPair_residues t
  intro hd
  have := Int.emod_eq_zero_of_dvd hd
  omega

private def quarticTuple (m j : ℕ) : Fin 4 → ℤ :=
  let p := eisenPair (2 * (m - j))
  ![(7 : ℤ) ^ j * p.1, (7 : ℤ) ^ j * p.2,
    (7 : ℤ) ^ j * (p.1 + p.2), 0]

private theorem quarticTuple_sum (m j : ℕ) (hj : j ≤ m) :
    ∑ i, quarticTuple m j i ^ 4 = 2 * (7 : ℤ) ^ (4 * m) := by
  have hn := eisenPair_norm (2 * (m - j))
  have hexp : 4 * j + 2 * (2 * (m - j)) = 4 * m := by omega
  calc
    ∑ i, quarticTuple m j i ^ 4 =
        2 * ((7 : ℤ) ^ j) ^ 4 *
          ((eisenPair (2 * (m - j))).1 ^ 2 +
            (eisenPair (2 * (m - j))).1 * (eisenPair (2 * (m - j))).2 +
            (eisenPair (2 * (m - j))).2 ^ 2) ^ 2 := by
      simp [Fin.sum_univ_four, quarticTuple]
      ring
    _ = 2 * (7 : ℤ) ^ (4 * m) := by
      rw [hn, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
      congr 2
      omega

private theorem quarticTuple_first_valuation (m j : ℕ) :
    padicValNat 7 (quarticTuple m j 0).natAbs = j := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hd := eisenPair_first_not_dvd (2 * (m - j))
  have hn : (eisenPair (2 * (m - j))).1 ≠ 0 := by
    intro h
    exact hd (h ▸ dvd_zero 7)
  change padicValInt 7 ((7 : ℤ) ^ j * (eisenPair (2 * (m - j))).1) = j
  rw [padicValInt.mul (pow_ne_zero _ (by norm_num)) hn,
    padicValInt.eq_zero_of_not_dvd hd, add_zero]
  simp only [padicValInt, Int.natAbs_pow]
  norm_num [padicValNat.pow]

private theorem quarticTuple_natAbs_sum (m j : ℕ) (hj : j ≤ m) :
    ∑ i, (quarticTuple m j i).natAbs ^ 4 = 2 * 7 ^ (4 * m) := by
  have h := quarticTuple_sum m j hj
  apply Int.natCast_inj.mp
  push_cast
  simpa only [Int.natCast_natAbs, (by decide : Even (4 : ℕ)).pow_abs] using h

private def boundedQuarticTuple (m : ℕ) (j : Fin (m + 1)) :
    Fin 4 → Fin (2 * 7 ^ (4 * m) + 1) :=
  fun i ↦ ⟨(quarticTuple m j i).natAbs, by
    have hsum := quarticTuple_natAbs_sum m j (Nat.le_of_lt_succ j.isLt)
    have hle : (quarticTuple m j i).natAbs ≤ (quarticTuple m j i).natAbs ^ 4 :=
      Nat.le_pow (by decide)
    have hi : (quarticTuple m j i).natAbs ^ 4 ≤
        ∑ l, (quarticTuple m j l).natAbs ^ 4 :=
      Finset.single_le_sum (f := fun l : Fin 4 ↦ (quarticTuple m j l).natAbs ^ 4)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    omega⟩

private theorem boundedQuarticTuple_injective (m : ℕ) :
    Function.Injective (boundedQuarticTuple m) := by
  intro a b h
  have h0 := congrArg (fun f ↦ (f 0 : Fin (2 * 7 ^ (4 * m) + 1)).val) h
  change (quarticTuple m a 0).natAbs = (quarticTuple m b 0).natAbs at h0
  have hv := congrArg (padicValNat 7) h0
  rw [quarticTuple_first_valuation, quarticTuple_first_valuation] at hv
  exact Fin.ext hv

/-- Explicit logarithmically growing peaks in the quartic representation count. -/
theorem quartic_count_lower (m : ℕ) :
    m + 1 ≤ representationCount 4 (2 * 7 ^ (4 * m)) := by
  classical
  unfold representationCount
  have h := Finset.card_le_card_of_injOn (boundedQuarticTuple m)
    (s := Finset.univ)
    (t := Finset.univ.filter (fun a : Fin 4 → Fin (2 * 7 ^ (4 * m) + 1) ↦
      ∑ i, (a i : ℕ) ^ 4 = 2 * 7 ^ (4 * m)))
    (by
      intro a _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact quarticTuple_natAbs_sum m a (Nat.le_of_lt_succ a.isLt))
    (boundedQuarticTuple_injective m).injOn
  simpa using h

/-- The quartic representation count exceeds every fixed bound infinitely often. -/
theorem quartic_counts_exceed_any_bound (M : ℕ) :
    {n : ℕ | M < representationCount 4 n}.Infinite := by
  have hi : Function.Injective (fun t : ℕ ↦ 2 * 7 ^ (4 * (M + t))) := by
    intro a b h
    dsimp only at h
    have hpow : 7 ^ (4 * (M + a)) = 7 ^ (4 * (M + b)) := by omega
    have hexp := Nat.pow_right_injective (by decide : 2 ≤ 7) hpow
    omega
  apply (Set.infinite_range_of_injective hi).mono
  rintro n ⟨t, rfl⟩
  change M < representationCount 4 (2 * 7 ^ (4 * (M + t)))
  have h := quartic_count_lower (M + t)
  omega


private theorem eisenPair_coprime (t : ℕ) :
    (eisenPair t).1.natAbs.Coprime (eisenPair t).2.natAbs := by
  apply Nat.coprime_of_dvd
  intro p hp hpa hpb
  have ha : (p : ℤ) ∣ (eisenPair t).1 := Int.ofNat_dvd_left.mpr hpa
  have hb : (p : ℤ) ∣ (eisenPair t).2 := Int.ofNat_dvd_left.mpr hpb
  have hn : (p : ℤ) ∣ (7 : ℤ) ^ t := by
    rw [← eisenPair_norm t, pow_two, pow_two]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_left ha _))
      (dvd_mul_of_dvd_left hb _)
  have hn' : p ∣ 7 ^ t := by exact_mod_cast hn
  have heq : p = 7 :=
    (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow hn')
  subst p
  exact eisenPair_first_not_dvd t ha

private theorem quarticTuple_first_two_gcd (m j : ℕ) :
    (quarticTuple m j 0).natAbs.gcd (quarticTuple m j 1).natAbs = 7 ^ j := by
  simp [quarticTuple, Int.natAbs_mul, Int.natAbs_pow, Nat.gcd_mul_left,
    (eisenPair_coprime (2 * (m - j))).gcd_eq_one]

/-- In the norm construction, the parameter `j` is precisely the common scaling factor. -/
private theorem quarticTuple_gcd (m j : ℕ) :
    (Finset.univ : Finset (Fin 4)).gcd (fun i ↦ (quarticTuple m j i).natAbs) = 7 ^ j := by
  apply Nat.dvd_antisymm
  · rw [← quarticTuple_first_two_gcd m j]
    exact Nat.dvd_gcd (Finset.gcd_dvd (Finset.mem_univ 0))
      (Finset.gcd_dvd (Finset.mem_univ 1))
  · apply Finset.dvd_gcd
    intro i _
    fin_cases i <;> simp [quarticTuple, Int.natAbs_mul, Int.natAbs_pow]

private theorem quarticTuple_primitive_iff (m j : ℕ) :
    (Finset.univ : Finset (Fin 4)).gcd (fun i ↦ (quarticTuple m j i).natAbs) = 1 ↔ j = 0 := by
  rw [quarticTuple_gcd]
  simp


/-- Ordered representations with no common factor in all their coordinates. -/
def primitiveRepresentationCount (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k → Fin (n + 1))).filter
    (fun a ↦ (∑ i, (a i : ℕ) ^ k = n) ∧
      (Finset.univ : Finset (Fin k)).gcd (fun i ↦ (a i : ℕ)) = 1)).card

private def primitiveQuarticTuple (m j : ℕ) (i : Fin 4) : ℕ :=
  if i = 3 then 1 else (quarticTuple m j i).natAbs

private theorem primitiveQuarticTuple_sum (m j : ℕ) (hj : j ≤ m) :
    ∑ i, primitiveQuarticTuple m j i ^ 4 = 2 * 7 ^ (4 * m) + 1 := by
  have h := quarticTuple_natAbs_sum m j hj
  have hz : quarticTuple m j 3 = 0 := rfl
  simp [Fin.sum_univ_four, hz] at h
  simp [Fin.sum_univ_four, primitiveQuarticTuple]
  omega

private theorem primitiveQuarticTuple_gcd (m j : ℕ) :
    (Finset.univ : Finset (Fin 4)).gcd (primitiveQuarticTuple m j) = 1 := by
  apply Nat.dvd_one.mp
  have h := Finset.gcd_dvd (f := primitiveQuarticTuple m j) (Finset.mem_univ (3 : Fin 4))
  simpa [primitiveQuarticTuple] using h

private def boundedPrimitiveQuarticTuple (m : ℕ) (j : Fin (m + 1)) :
    Fin 4 → Fin (2 * 7 ^ (4 * m) + 1 + 1) :=
  fun i ↦ ⟨primitiveQuarticTuple m j i, by
    have hsum := primitiveQuarticTuple_sum m j (Nat.le_of_lt_succ j.isLt)
    have hle : primitiveQuarticTuple m j i ≤ primitiveQuarticTuple m j i ^ 4 :=
      Nat.le_pow (by decide)
    have hi : primitiveQuarticTuple m j i ^ 4 ≤
        ∑ l, primitiveQuarticTuple m j l ^ 4 :=
      Finset.single_le_sum (f := fun l : Fin 4 ↦ primitiveQuarticTuple m j l ^ 4)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    omega⟩

private theorem boundedPrimitiveQuarticTuple_injective (m : ℕ) :
    Function.Injective (boundedPrimitiveQuarticTuple m) := by
  intro a b h
  have h0 := congrArg (fun f ↦ (f 0 : Fin (2 * 7 ^ (4 * m) + 1 + 1)).val) h
  change (quarticTuple m a 0).natAbs = (quarticTuple m b 0).natAbs at h0
  have hv := congrArg (padicValNat 7) h0
  rw [quarticTuple_first_valuation, quarticTuple_first_valuation] at hv
  exact Fin.ext hv

/-- Adding a coordinate equal to one makes the logarithmic quartic family primitive. -/
theorem primitive_quartic_count_lower (m : ℕ) :
    m + 1 ≤ primitiveRepresentationCount 4 (2 * 7 ^ (4 * m) + 1) := by
  classical
  unfold primitiveRepresentationCount
  have h := Finset.card_le_card_of_injOn (boundedPrimitiveQuarticTuple m)
    (s := Finset.univ)
    (t := Finset.univ.filter
      (fun a : Fin 4 → Fin (2 * 7 ^ (4 * m) + 1 + 1) ↦
        (∑ i, (a i : ℕ) ^ 4 = 2 * 7 ^ (4 * m) + 1) ∧
          (Finset.univ : Finset (Fin 4)).gcd (fun i ↦ (a i : ℕ)) = 1))
    (by
      intro a _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨primitiveQuarticTuple_sum m a (Nat.le_of_lt_succ a.isLt),
        primitiveQuarticTuple_gcd m a⟩)
    (boundedPrimitiveQuarticTuple_injective m).injOn
  simpa using h

theorem primitiveRepresentationCount_le (k n : ℕ) :
    primitiveRepresentationCount k n ≤ representationCount k n := by
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact ha.1

/-- Primitive quartic counts exceed every fixed bound infinitely often. -/
theorem primitive_quartic_counts_exceed_any_bound (M : ℕ) :
    {n : ℕ | M < primitiveRepresentationCount 4 n}.Infinite := by
  have hi : Function.Injective (fun t : ℕ ↦ 2 * 7 ^ (4 * (M + t)) + 1) := by
    intro a b h
    dsimp only at h
    have hpow : 7 ^ (4 * (M + a)) = 7 ^ (4 * (M + b)) := by omega
    have hexp := Nat.pow_right_injective (by decide : 2 ≤ 7) hpow
    omega
  apply (Set.infinite_range_of_injective hi).mono
  rintro n ⟨t, rfl⟩
  change M < primitiveRepresentationCount 4 (2 * 7 ^ (4 * (M + t)) + 1)
  have h := primitive_quartic_count_lower (M + t)
  omega

end Erdos322
