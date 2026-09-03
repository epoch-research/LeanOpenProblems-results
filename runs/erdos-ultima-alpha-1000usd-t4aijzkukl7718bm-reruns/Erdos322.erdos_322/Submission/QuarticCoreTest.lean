import FormalConjecturesUtil

/-!
# Erdős Problem 322

*Reference:* [erdosproblems.com/322](https://www.erdosproblems.com/322)
-/

namespace Erdos322

/-- For `k ≥ 3`, the number of ordered representations of `n` as a sum of `k` many `k`th
powers of nonnegative integers. The bases can be restricted to the interval from `0` to `n`. -/
def representationCount (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k → Fin (n + 1))).filter
    (fun a ↦ ∑ i, (a i : ℕ) ^ k = n)).card

private def triple (m a : ℕ) : Fin 3 → ℕ :=
  ![9 * a ^ 4, 3 * a * (3 * m) ^ 3 - 9 * a ^ 4,
    (3 * m) ^ 4 - 9 * a ^ 3 * (3 * m)]

private theorem triple_sum (m a : ℕ) (ha : a ≤ m) :
    ∑ i, triple m a i ^ 3 = (3 * m) ^ 12 := by
  have hpow : a ^ 3 ≤ m ^ 3 := Nat.pow_le_pow_left ha 3
  have h₁ : 9 * a ^ 4 ≤ 3 * a * (3 * m) ^ 3 := by
    calc
      9 * a ^ 4 = 9 * a * a ^ 3 := by ring
      _ ≤ 9 * a * m ^ 3 := Nat.mul_le_mul_left _ hpow
      _ ≤ 3 * a * (3 * m) ^ 3 := by
        nlinarith [Nat.zero_le (a * m ^ 3)]
  have h₂ : 9 * a ^ 3 * (3 * m) ≤ (3 * m) ^ 4 := by
    calc
      9 * a ^ 3 * (3 * m) ≤ 9 * m ^ 3 * (3 * m) := by gcongr
      _ ≤ (3 * m) ^ 4 := by nlinarith [Nat.zero_le (m ^ 4)]
  simp [Fin.sum_univ_three, triple]
  zify [h₁, h₂]
  ring

private def boundedTripleUpTo (m : ℕ) (a : Fin (m + 1)) :
    Fin 3 → Fin ((3 * m) ^ 12 + 1) :=
  fun i ↦ ⟨triple m a i, by
    have h := triple_sum m a (Nat.le_of_lt_succ a.isLt)
    have hi : triple m a i ^ 3 ≤ ∑ j, triple m a j ^ 3 :=
      Finset.single_le_sum (f := fun j : Fin 3 ↦ triple m a j ^ 3)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hle : triple m a i ≤ triple m a i ^ 3 := Nat.le_pow (by decide)
    omega⟩

private theorem triple_first_lt_last (m a b : ℕ) (hm : 0 < m)
    (ha : a ≤ m) (hb : b ≤ m) : triple m a 0 < triple m b 2 := by
  have hfirst : triple m a 0 ≤ 9 * m ^ 4 := by
    exact Nat.mul_le_mul_left 9 (Nat.pow_le_pow_left ha 4)
  have hlast : 54 * m ^ 4 ≤ triple m b 2 := by
    change 54 * m ^ 4 ≤ (3 * m) ^ 4 - 9 * b ^ 3 * (3 * m)
    apply Nat.le_sub_of_add_le
    calc
      54 * m ^ 4 + 9 * b ^ 3 * (3 * m) ≤
          54 * m ^ 4 + 9 * m ^ 3 * (3 * m) := by gcongr
      _ = (3 * m) ^ 4 := by ring
  have hpos : 0 < m ^ 4 := pow_pos hm _
  omega

private def rotatedTriple (m : ℕ) (a : Fin (m + 1) × Fin 3) :
    Fin 3 → Fin ((3 * m) ^ 12 + 1) :=
  fun i ↦ boundedTripleUpTo m a.1 (i + a.2)

private theorem rotatedTriple_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (rotatedTriple m) := by
  rintro ⟨a, j⟩ ⟨b, l⟩ h
  have h₀ := congrArg (fun f ↦ ((f 0 : Fin ((3 * m) ^ 12 + 1)) : ℕ)) h
  have h₁ := congrArg (fun f ↦ ((f 1 : Fin ((3 * m) ^ 12 + 1)) : ℕ)) h
  have h₂ := congrArg (fun f ↦ ((f 2 : Fin ((3 * m) ^ 12 + 1)) : ℕ)) h
  have hab := triple_first_lt_last m a b hm
    (Nat.le_of_lt_succ a.isLt) (Nat.le_of_lt_succ b.isLt)
  have hba := triple_first_lt_last m b a hm
    (Nat.le_of_lt_succ b.isLt) (Nat.le_of_lt_succ a.isLt)
  fin_cases j <;> fin_cases l <;>
    dsimp [rotatedTriple, boundedTripleUpTo, Fin.add_def] at h₀ h₁ h₂
  all_goals try omega
  all_goals
    refine Prod.ext ?_ rfl
    apply Fin.ext
    simp [triple] at h₀ h₁ h₂
    assumption

private theorem rotatedTriple_sum (m : ℕ) (a : Fin (m + 1) × Fin 3) :
    ∑ i, ((rotatedTriple m a i) : ℕ) ^ 3 = (3 * m) ^ 12 := by
  rcases a with ⟨a, j⟩
  have ht := triple_sum m a (Nat.le_of_lt_succ a.isLt)
  simp only [Fin.sum_univ_three] at ht ⊢
  fin_cases j <;> dsimp [rotatedTriple, boundedTripleUpTo, Fin.add_def] <;> omega

/-- A sharper cubic bound, including all three cyclic permutations. -/
theorem cubic_count_lower_strong (m : ℕ) (hm : 0 < m) :
    3 * (m + 1) ≤ representationCount 3 ((3 * m) ^ 12) := by
  classical
  unfold representationCount
  have h := Finset.card_le_card_of_injOn (rotatedTriple m)
    (s := Finset.univ)
    (t := Finset.univ.filter (fun a : Fin 3 → Fin ((3 * m) ^ 12 + 1) ↦
      ∑ i, (a i : ℕ) ^ 3 = (3 * m) ^ 12))
    (by
      intro a _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact rotatedTriple_sum m a)
    (rotatedTriple_injective m hm).injOn
  simpa [mul_comm] using h

/-- For cubes one may take the exponent to be exactly `1 / 12`. -/
theorem cubic_exponent_one_twelfth :
    {n : ℕ | (n : ℝ) ^ (1 / 12 : ℝ) < representationCount 3 n}.Infinite := by
  have hinj : Function.Injective (fun m : ℕ ↦ (3 * (m + 1)) ^ 12) := by
    intro a b h
    have h' := Nat.pow_left_injective (by decide : 12 ≠ 0) h
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro n ⟨m, rfl⟩
  change (((3 * (m + 1)) ^ 12 : ℕ) : ℝ) ^ (1 / 12 : ℝ) < _
  have hrpow : (((3 * (m + 1)) ^ 12 : ℕ) : ℝ) ^ (1 / 12 : ℝ) =
      ((3 * (m + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    convert Real.pow_rpow_inv_natCast (Nat.cast_nonneg (3 * (m + 1)))
      (by decide : 12 ≠ 0) using 1
    norm_num
  rw [hrpow]
  exact_mod_cast (show 3 * (m + 1) < representationCount 3 ((3 * (m + 1)) ^ 12) from
    (by omega : 3 * (m + 1) < 3 * (m + 1 + 1)).trans_le
      (cubic_count_lower_strong (m + 1) (by omega)))

/-- The conjecture for the exponent `k = 3`. -/
theorem cubic_case : ∃ c > (0 : ℝ),
    {n : ℕ | (n : ℝ) ^ c < representationCount 3 n}.Infinite := by
  exact ⟨1 / 12, by norm_num, cubic_exponent_one_twelfth⟩

private theorem fourth_mod_five_le_one (a : ℕ) : a ^ 4 % 5 ≤ 1 := by
  rw [Nat.pow_mod]
  have h : a % 5 < 5 := Nat.mod_lt a (by decide)
  interval_cases a % 5 <;> norm_num

theorem five_dvd_all_of_fourth_sum {a : Fin 4 → ℕ} {n : ℕ}
    (h : ∑ i, a i ^ 4 = n) (hn : 5 ∣ n) : ∀ i, 5 ∣ a i := by
  have hb0 := fourth_mod_five_le_one (a 0)
  have hb1 := fourth_mod_five_le_one (a 1)
  have hb2 := fourth_mod_five_le_one (a 2)
  have hb3 := fourth_mod_five_le_one (a 3)
  have hm := congrArg (fun x ↦ x % 5) h
  simp only [Fin.sum_univ_four, Nat.mod_eq_zero_of_dvd hn] at hm
  have hz : ∀ i : Fin 4, a i ^ 4 % 5 = 0 := by
    have h0 : a 0 ^ 4 % 5 = 0 := by omega
    have h1 : a 1 ^ 4 % 5 = 0 := by omega
    have h2 : a 2 ^ 4 % 5 = 0 := by omega
    have h3 : a 3 ^ 4 % 5 = 0 := by omega
    intro i
    fin_cases i <;> assumption
  intro i
  exact (by decide : Nat.Prime 5).dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero (hz i))


private def scaleFive (n : ℕ) (a : Fin 4 → Fin (n + 1)) :
    Fin 4 → Fin (625 * n + 1) := fun i ↦
  ⟨5 * (a i : ℕ), by have := (a i).isLt; omega⟩

private theorem scaleFive_sum (n : ℕ) (a : Fin 4 → Fin (n + 1))
    (ha : ∑ i, (a i : ℕ) ^ 4 = n) :
    ∑ i, (scaleFive n a i : ℕ) ^ 4 = 625 * n := by
  change (∑ i, (5 * (a i : ℕ)) ^ 4) = 625 * n
  simp only [mul_pow, show (5 : ℕ) ^ 4 = 625 by norm_num, ← Finset.mul_sum, ha]

/-- Multiplication of the target by `5^4` introduces no new quartic representations. -/
theorem quartic_count_scale_five (n : ℕ) :
    representationCount 4 (625 * n) = representationCount 4 n := by
  classical
  unfold representationCount
  symm
  apply Finset.card_nbij (scaleFive n)
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact scaleFive_sum n a ha
  · intro a ha b hb hab
    funext i
    apply Fin.ext
    have heq := congrArg (fun f ↦ ((f i : Fin (625 * n + 1)) : ℕ)) hab
    change 5 * (a i : ℕ) = 5 * (b i : ℕ) at heq
    omega
  · intro b hb
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hd : ∀ i : Fin 4, 5 ∣ (b i : ℕ) :=
      five_dvd_all_of_fourth_sum hb (by omega)
    let c : Fin 4 → ℕ := fun i ↦ (b i : ℕ) / 5
    have hc : ∑ i, c i ^ 4 = n := by
      apply Nat.mul_left_cancel (by decide : 0 < 625)
      calc
        625 * ∑ i, c i ^ 4 = ∑ i, (5 * c i) ^ 4 := by
          simp only [mul_pow, show (5 : ℕ) ^ 4 = 625 by norm_num, Finset.mul_sum]
        _ = ∑ i, (b i : ℕ) ^ 4 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [show 5 * c i = (b i : ℕ) from Nat.mul_div_cancel' (hd i)]
        _ = 625 * n := hb
    let a : Fin 4 → Fin (n + 1) := fun i ↦ ⟨c i, by
      have hpow : c i ≤ c i ^ 4 := Nat.le_pow (by decide)
      have hsum : c i ^ 4 ≤ ∑ j, c j ^ 4 :=
        Finset.single_le_sum (f := fun j : Fin 4 ↦ c j ^ 4)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      omega⟩
    refine ⟨a, ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hc
    · funext i
      apply Fin.ext
      change 5 * c i = (b i : ℕ)
      exact Nat.mul_div_cancel' (hd i)

/-- On pure powers of `5^4`, there are only the four one-term representations. -/
theorem quartic_count_pure_five_power (t : ℕ) :
    representationCount 4 (625 ^ t) = 4 := by
  induction t with
  | zero =>
    norm_num only [pow_zero]
    decide
  | succ t ih =>
    rw [pow_succ', quartic_count_scale_five, ih]

private theorem fourth_mod_sixteen_le_one (a : ℕ) : a ^ 4 % 16 ≤ 1 := by
  rw [Nat.pow_mod]
  have h : a % 16 < 16 := Nat.mod_lt a (by decide)
  interval_cases a % 16 <;> norm_num

theorem two_dvd_all_of_fourth_sum {a : Fin 4 → ℕ} {n : ℕ}
    (h : ∑ i, a i ^ 4 = n) (hn : 16 ∣ n) : ∀ i, 2 ∣ a i := by
  have hb0 := fourth_mod_sixteen_le_one (a 0)
  have hb1 := fourth_mod_sixteen_le_one (a 1)
  have hb2 := fourth_mod_sixteen_le_one (a 2)
  have hb3 := fourth_mod_sixteen_le_one (a 3)
  have hm := congrArg (fun x ↦ x % 16) h
  simp only [Fin.sum_univ_four, Nat.mod_eq_zero_of_dvd hn] at hm
  have hz : ∀ i : Fin 4, a i ^ 4 % 16 = 0 := by
    have h0 : a 0 ^ 4 % 16 = 0 := by omega
    have h1 : a 1 ^ 4 % 16 = 0 := by omega
    have h2 : a 2 ^ 4 % 16 = 0 := by omega
    have h3 : a 3 ^ 4 % 16 = 0 := by omega
    intro i
    fin_cases i <;> assumption
  intro i
  exact (by decide : Nat.Prime 2).dvd_of_dvd_pow
    (dvd_trans (by decide : 2 ∣ 16) (Nat.dvd_of_mod_eq_zero (hz i)))


private def scaleTwo (n : ℕ) (a : Fin 4 → Fin (n + 1)) :
    Fin 4 → Fin (16 * n + 1) := fun i ↦
  ⟨2 * (a i : ℕ), by have := (a i).isLt; omega⟩

private theorem scaleTwo_sum (n : ℕ) (a : Fin 4 → Fin (n + 1))
    (ha : ∑ i, (a i : ℕ) ^ 4 = n) :
    ∑ i, (scaleTwo n a i : ℕ) ^ 4 = 16 * n := by
  change (∑ i, (2 * (a i : ℕ)) ^ 4) = 16 * n
  simp only [mul_pow, show (2 : ℕ) ^ 4 = 16 by norm_num, ← Finset.mul_sum, ha]

/-- Multiplication of the target by `2^4` introduces no new quartic representations. -/
theorem quartic_count_scale_two (n : ℕ) :
    representationCount 4 (16 * n) = representationCount 4 n := by
  classical
  unfold representationCount
  symm
  apply Finset.card_nbij (scaleTwo n)
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact scaleTwo_sum n a ha
  · intro a ha b hb hab
    funext i
    apply Fin.ext
    have heq := congrArg (fun f ↦ ((f i : Fin (16 * n + 1)) : ℕ)) hab
    change 2 * (a i : ℕ) = 2 * (b i : ℕ) at heq
    omega
  · intro b hb
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hd : ∀ i : Fin 4, 2 ∣ (b i : ℕ) :=
      two_dvd_all_of_fourth_sum hb (by omega)
    let c : Fin 4 → ℕ := fun i ↦ (b i : ℕ) / 2
    have hc : ∑ i, c i ^ 4 = n := by
      apply Nat.mul_left_cancel (by decide : 0 < 16)
      calc
        16 * ∑ i, c i ^ 4 = ∑ i, (2 * c i) ^ 4 := by
          simp only [mul_pow, show (2 : ℕ) ^ 4 = 16 by norm_num, Finset.mul_sum]
        _ = ∑ i, (b i : ℕ) ^ 4 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [show 2 * c i = (b i : ℕ) from Nat.mul_div_cancel' (hd i)]
        _ = 16 * n := hb
    let a : Fin 4 → Fin (n + 1) := fun i ↦ ⟨c i, by
      have hpow : c i ≤ c i ^ 4 := Nat.le_pow (by decide)
      have hsum : c i ^ 4 ≤ ∑ j, c j ^ 4 :=
        Finset.single_le_sum (f := fun j : Fin 4 ↦ c j ^ 4)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      omega⟩
    refine ⟨a, ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hc
    · funext i
      apply Fin.ext
      change 2 * c i = (b i : ℕ)
      exact Nat.mul_div_cancel' (hd i)


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


open Filter

/-- Having no polynomially large peaks is exactly eventual domination by every
positive power. This holds for an arbitrary real-valued sequence. -/
private theorem no_polynomial_peaks_iff (r : ℕ → ℝ) :
    (¬ ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < r n}.Infinite) ↔
      ∀ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, r n ≤ (n : ℝ) ^ c := by
  constructor
  · intro h c hc
    have hf : {n : ℕ | (n : ℝ) ^ c < r n}.Finite := by
      by_contra hi
      exact h ⟨c, hc, hi⟩
    obtain ⟨N, hN⟩ := hf.bddAbove
    filter_upwards [eventually_gt_atTop N] with n hn
    by_contra hr
    have hmem : n ∈ {n : ℕ | (n : ℝ) ^ c < r n} := not_le.mp hr
    have := hN hmem
    omega
  · intro h ⟨c, hc, hinf⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h c hc)
    have hs : {n : ℕ | (n : ℝ) ^ c < r n} ⊆ Set.Iio N := by
      intro n hn
      by_contra hnot
      have hge : N ≤ n := Nat.le_of_not_gt hnot
      exact (not_lt_of_ge (hN n hge)) hn
    exact hinf (Set.Finite.subset (Set.finite_Iio N) hs)


/-- The usual uniform `O(n^ε)` condition is equivalent to the absence of
polynomially large peaks. -/
private theorem no_polynomial_peaks_iff_uniform_bound (r : ℕ → ℕ) :
    (¬ ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < (r n : ℝ)}.Infinite) ↔
      ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ),
        ∀ n : ℕ, 1 ≤ n → (r n : ℝ) ≤ C * (n : ℝ) ^ ε := by
  rw [no_polynomial_peaks_iff]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h ε hε)
    let S : ℝ := ∑ i ∈ Finset.range N, (r i : ℝ)
    have hS : 0 ≤ S := by dsimp [S]; positivity
    refine ⟨1 + S, by positivity, ?_⟩
    intro n hn
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hp : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow hnreal hε.le
    by_cases hsmall : n < N
    · have hrs : (r n : ℝ) ≤ S := by
        exact Finset.single_le_sum (f := fun i : ℕ ↦ (r i : ℝ))
          (fun _ _ ↦ Nat.cast_nonneg _) (Finset.mem_range.mpr hsmall)
      calc
        (r n : ℝ) ≤ 1 + S := by linarith
        _ = (1 + S) * 1 := by ring
        _ ≤ (1 + S) * (n : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_left hp (by positivity)
    · calc
        (r n : ℝ) ≤ (n : ℝ) ^ ε := hN n (by omega)
        _ = 1 * (n : ℝ) ^ ε := by ring
        _ ≤ (1 + S) * (n : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · intro h c hc
    have hh : 0 < c / 2 := by linarith
    obtain ⟨C, hCpos, hC⟩ := h (c / 2) hh
    have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (c / 2)) atTop atTop :=
      (tendsto_rpow_atTop hh).comp tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually_ge_atTop C, eventually_ge_atTop (1 : ℕ)] with n hpow hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    calc
      (r n : ℝ) ≤ C * (n : ℝ) ^ (c / 2) := hC n hn
      _ ≤ (n : ℝ) ^ (c / 2) * (n : ℝ) ^ (c / 2) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = (n : ℝ) ^ c := by
        rw [← Real.rpow_add hnpos]
        congr 1
        ring

/-- The exact negation of the conjecture is equivalent to a uniform subpolynomial
bound for one exponent at least four. The cubic case excludes the exponent three. -/
theorem negation_iff_uniform_bound :
    (¬ (∀ k : ℕ, 3 ≤ k → ∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ) ^ c < representationCount k n}.Infinite)) ↔
    ∃ k : ℕ, 4 ≤ k ∧ ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ n : ℕ, 1 ≤ n → (representationCount k n : ℝ) ≤ C * (n : ℝ) ^ ε := by
  classical
  constructor
  · intro h
    obtain ⟨k, hk⟩ := not_forall.mp h
    have hk3 : 3 ≤ k := by
      by_contra hn
      exact hk (fun hle ↦ False.elim (hn hle))
    have hpeak : ¬ ∃ c > (0 : ℝ),
        {n : ℕ | (n : ℝ) ^ c < representationCount k n}.Infinite := by
      intro hp
      exact hk (fun _ ↦ hp)
    have hk4 : 4 ≤ k := by
      by_contra hn
      have heq : k = 3 := by omega
      subst k
      exact hpeak cubic_case
    exact ⟨k, hk4,
      (no_polynomial_peaks_iff_uniform_bound (representationCount k)).mp hpeak⟩
  · rintro ⟨k, hk4, hbound⟩ h
    exact ((no_polynomial_peaks_iff_uniform_bound (representationCount k)).mpr hbound)
      (h k (by omega))

/- Primitive representations and common-factor scaling. -/

open Filter

theorem divisor_count_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  let δ : ℝ := (2 : ℝ) ^ ε - 1
  have hδ : 0 < δ := sub_pos.mpr (Real.one_lt_rpow (by norm_num) hε)
  let B : ℝ := 1 + δ⁻¹
  have hB : 1 ≤ B := by
    dsimp [B]
    have := inv_nonneg.mpr hδ.le
    linarith
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hδB : 1 ≤ B * δ := by
    have hi := inv_mul_cancel₀ (ne_of_gt hδ)
    dsimp [B]
    nlinarith
  have hlin (a : ℕ) : (a + 1 : ℝ) ≤ B * ((2 : ℝ) ^ ε) ^ a := by
    have hb := one_add_mul_le_pow (show -2 ≤ δ by linarith) a
    have he : 1 + δ = (2 : ℝ) ^ ε := by dsimp [δ]; ring
    rw [he] at hb
    calc
      (a + 1 : ℝ) ≤ B * (1 + a * δ) := by
        nlinarith [mul_le_mul_of_nonneg_left hδB (Nat.cast_nonneg a)]
      _ ≤ B * ((2 : ℝ) ^ ε) ^ a := mul_le_mul_of_nonneg_left hb hBpos.le
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 2)
  refine ⟨B ^ N, pow_pos hBpos _, ?_⟩
  intro n hn
  have hrpow (p a : ℕ) : ((p : ℝ) ^ ε) ^ a = ((p : ℝ) ^ a) ^ ε := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p),
      mul_comm ε (a : ℝ), Real.rpow_natCast_mul (Nat.cast_nonneg p)]
  have hlocal (p a : ℕ) (hp : p.Prime) :
      (a + 1 : ℝ) ≤ (if p < N then B else 1) * ((p : ℝ) ^ a) ^ ε := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    by_cases hpN : p < N
    · rw [if_pos hpN, ← hrpow]
      exact (hlin a).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hp2 hε.le) a)
        hBpos.le)
    · rw [if_neg hpN, one_mul, ← hrpow]
      have htwo : (a + 1 : ℝ) ≤ (2 : ℝ) ^ a := by
        exact_mod_cast (Nat.succ_le_iff.mpr (Nat.lt_two_pow_self (n := a)))
      exact htwo.trans (pow_le_pow_left₀ (by norm_num) (hN p (by omega)) a)
  have hconst : (∏ p ∈ n.primeFactors, if p < N then B else 1) ≤ B ^ N := by
    rw [← Finset.prod_filter, Finset.prod_const]
    apply pow_le_pow_right₀ hB
    have hs : n.primeFactors.filter (fun p ↦ p < N) ⊆ Finset.range N := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    simpa using Finset.card_le_card hs
  have hprod : (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) = n := by
    have h := Nat.factorization_prod_pow_eq_self hn.ne'
    simpa [Finsupp.prod, Nat.support_factorization] using congrArg (fun m : ℕ ↦ (m : ℝ)) h
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, (n.factorization p + 1 : ℝ) := by
      rw [Nat.card_divisors hn.ne']
      simp
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < N then B else 1) * ((p : ℝ) ^ n.factorization p) ^ ε := by
      apply Finset.prod_le_prod (fun _ _ ↦ by positivity)
      intro p hp
      exact hlocal p _ (Nat.prime_of_mem_primeFactors hp)
    _ = (∏ p ∈ n.primeFactors, if p < N then B else 1) * (n : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, Real.finset_prod_rpow]
      · rw [hprod]
      · intro p hp; positivity
    _ ≤ B ^ N * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hconst (by positivity)

private abbrev Rep (k n : ℕ) :=
  {a : Fin k → Fin (n + 1) // ∑ i, (a i : ℕ) ^ k = n}

private abbrev PRep (k n : ℕ) :=
  {a : Fin k → Fin (n + 1) // (∑ i, (a i : ℕ) ^ k = n) ∧
    (Finset.univ : Finset (Fin k)).gcd (fun i ↦ (a i : ℕ)) = 1}

private theorem card_rep (k n : ℕ) : Fintype.card (Rep k n) = representationCount k n := by
  simp [Rep, Fintype.card_subtype, representationCount]

private theorem card_prep (k n : ℕ) :
    Fintype.card (PRep k n) = primitiveRepresentationCount k n := by
  simp [PRep, Fintype.card_subtype, primitiveRepresentationCount]

private def commonDivisor {k n : ℕ} (a : Rep k n) : ℕ :=
  (Finset.univ : Finset (Fin k)).gcd (fun i ↦ (a.val i : ℕ))

private theorem commonDivisor_dvd {k n : ℕ} (a : Rep k n) (i : Fin k) :
    commonDivisor a ∣ (a.val i : ℕ) := Finset.gcd_dvd (Finset.mem_univ i)

private theorem rep_some_nonzero {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (a : Rep k n) :
    ∃ i, (a.val i : ℕ) ≠ 0 := by
  by_contra h
  push_neg at h
  have ha := a.property
  simp [h, zero_pow hk.ne'] at ha
  omega

private theorem commonDivisor_pos {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (a : Rep k n) :
    0 < commonDivisor a := by
  obtain ⟨i, hi⟩ := rep_some_nonzero hk hn a
  apply Nat.pos_of_ne_zero
  intro h
  have := commonDivisor_dvd a i
  rw [h, zero_dvd_iff] at this
  exact hi this

private theorem commonDivisor_pow_dvd {k n : ℕ} (a : Rep k n) :
    commonDivisor a ^ k ∣ n := by
  have h : commonDivisor a ^ k ∣ ∑ i, (a.val i : ℕ) ^ k :=
    Finset.dvd_sum (fun i _ ↦ pow_dvd_pow_of_dvd (commonDivisor_dvd a i) k)
  simpa only [a.property] using h

private theorem commonDivisor_mem {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (a : Rep k n) :
    commonDivisor a ∈ n.divisors := by
  exact Nat.mem_divisors.mpr
    ⟨dvd_trans (dvd_pow (dvd_refl _) hk.ne') (commonDivisor_pow_dvd a), hn.ne'⟩

private theorem quotient_sum {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (a : Rep k n) :
    ∑ i, ((a.val i : ℕ) / commonDivisor a) ^ k = n / commonDivisor a ^ k := by
  have hd := commonDivisor_pos hk hn a
  have h : commonDivisor a ^ k *
      (∑ i, ((a.val i : ℕ) / commonDivisor a) ^ k) = n := by
    calc
      _ = ∑ i, (a.val i : ℕ) ^ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [← mul_pow, Nat.mul_div_cancel' (commonDivisor_dvd a i)]
      _ = n := a.property
  have hh := congrArg (fun m : ℕ ↦ m / commonDivisor a ^ k) h
  simpa only [Nat.mul_div_cancel_left _ (pow_pos hd _)] using hh

private def normalizeRep {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (a : Rep k n) :
    PRep k (n / commonDivisor a ^ k) :=
  ⟨fun i ↦ ⟨(a.val i : ℕ) / commonDivisor a, by
    have hs := quotient_sum hk hn a
    have hb := Finset.single_le_sum
      (f := fun j : Fin k ↦ ((a.val j : ℕ) / commonDivisor a) ^ k)
      (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hp := Nat.le_pow (a := (a.val i : ℕ) / commonDivisor a) hk
    exact Nat.lt_succ_of_le (hp.trans (hb.trans_eq hs))⟩,
    quotient_sum hk hn a, by
      obtain ⟨i, hi⟩ := rep_some_nonzero hk hn a
      exact Finset.gcd_div_eq_one (Finset.mem_univ i) hi⟩

private theorem normalizeRep_recover {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (a : Rep k n) (i : Fin k) :
    commonDivisor a * ((normalizeRep hk hn a).val i : ℕ) = (a.val i : ℕ) :=
  Nat.mul_div_cancel' (commonDivisor_dvd a i)

private def normalizationMap {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (a : Rep k n) :
    (d : n.divisors) × PRep k (n / (d : ℕ) ^ k) :=
  ⟨⟨commonDivisor a, commonDivisor_mem hk hn a⟩, normalizeRep hk hn a⟩

private theorem normalizationMap_injective {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    Function.Injective (normalizationMap hk hn) := by
  intro a b h
  have hd := congrArg (fun s : (d : n.divisors) × PRep k (n / (d : ℕ) ^ k) ↦
    (s.1 : ℕ)) h
  change commonDivisor a = commonDivisor b at hd
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hq := congrArg (fun s : (d : n.divisors) × PRep k (n / (d : ℕ) ^ k) ↦
    (s.2.val i : ℕ)) h
  change ((normalizeRep hk hn a).val i : ℕ) = ((normalizeRep hk hn b).val i : ℕ) at hq
  calc
    (a.val i : ℕ) = commonDivisor a * ((normalizeRep hk hn a).val i : ℕ) :=
      (normalizeRep_recover hk hn a i).symm
    _ = commonDivisor b * ((normalizeRep hk hn b).val i : ℕ) := congrArg₂ Nat.mul hd hq
    _ = (b.val i : ℕ) := normalizeRep_recover hk hn b i

/-- Common-factor normalization bounds the full count by a sum of primitive counts. -/
theorem representationCount_le_sum_primitive {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    representationCount k n ≤ ∑ d ∈ n.divisors, primitiveRepresentationCount k (n / d ^ k) := by
  have h := Fintype.card_le_of_injective _ (normalizationMap_injective hk hn)
  rw [card_rep, Fintype.card_sigma] at h
  simp_rw [card_prep] at h
  have he : (∑ d : n.divisors, primitiveRepresentationCount k (n / (d : ℕ) ^ k)) =
      ∑ d ∈ n.divisors, primitiveRepresentationCount k (n / d ^ k) :=
    Finset.sum_coe_sort n.divisors (fun d : ℕ ↦ primitiveRepresentationCount k (n / d ^ k))
  exact he ▸ h

private theorem primitive_count_zero (k : ℕ) : primitiveRepresentationCount k 0 = 0 := by
  have hg : (Finset.univ : Finset (Fin k)).gcd (fun _ ↦ (0 : ℕ)) = 0 :=
    Finset.gcd_eq_zero_iff.mpr (fun _ _ ↦ rfl)
  simp [primitiveRepresentationCount, hg]

/-- Uniform subpolynomial bounds for primitive and unrestricted counts are equivalent. -/
theorem primitive_bound_iff_full_bound {k : ℕ} (hk : 0 < k) :
    (∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
      (primitiveRepresentationCount k n : ℝ) ≤ C * (n : ℝ) ^ ε) ↔
    (∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
      (representationCount k n : ℝ) ≤ C * (n : ℝ) ^ ε) := by
  constructor
  · intro h ε hε
    have hhalf : 0 < ε / 2 := by linarith
    obtain ⟨A, hA, hprim⟩ := h (ε / 2) hhalf
    obtain ⟨B, hB, hdiv⟩ := divisor_count_subpolynomial (ε / 2) hhalf
    refine ⟨A * B, mul_pos hA hB, ?_⟩
    intro n hn
    have hnpos : 0 < n := by omega
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hterm (d : ℕ) :
        (primitiveRepresentationCount k (n / d ^ k) : ℝ) ≤ A * (n : ℝ) ^ (ε / 2) := by
      by_cases hz : n / d ^ k = 0
      · simp only [hz, primitive_count_zero, Nat.cast_zero]
        exact mul_nonneg hA.le (Real.rpow_nonneg hnreal.le _)
      · calc
          (primitiveRepresentationCount k (n / d ^ k) : ℝ) ≤
              A * ((n / d ^ k : ℕ) : ℝ) ^ (ε / 2) := hprim (n / d ^ k) (Nat.one_le_iff_ne_zero.mpr hz)
          _ ≤ A * (n : ℝ) ^ (ε / 2) := by
            apply mul_le_mul_of_nonneg_left _ hA.le
            apply Real.rpow_le_rpow (by positivity) _ hhalf.le
            exact_mod_cast Nat.div_le_self n (d ^ k)
    calc
      (representationCount k n : ℝ) ≤
          ∑ d ∈ n.divisors, (primitiveRepresentationCount k (n / d ^ k) : ℝ) := by
        exact_mod_cast representationCount_le_sum_primitive hk hnpos
      _ ≤ ∑ _d ∈ n.divisors, A * (n : ℝ) ^ (ε / 2) :=
        Finset.sum_le_sum (fun d _ ↦ hterm d)
      _ = (n.divisors.card : ℝ) * (A * (n : ℝ) ^ (ε / 2)) := by simp
      _ ≤ (B * (n : ℝ) ^ (ε / 2)) * (A * (n : ℝ) ^ (ε / 2)) :=
        mul_le_mul_of_nonneg_right (hdiv n hnpos) (by positivity)
      _ = (A * B) * (n : ℝ) ^ ε := by
        have hp : (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2) = (n : ℝ) ^ ε := by
          rw [← Real.rpow_add hnreal]
          congr 1
          ring
        calc
          _ = (A * B) * ((n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2)) := by ring
          _ = _ := by rw [hp]
  · intro h ε hε
    obtain ⟨C, hC, hb⟩ := h ε hε
    refine ⟨C, hC, fun n hn ↦ ?_⟩
    have hp : (primitiveRepresentationCount k n : ℝ) ≤ representationCount k n := by
      exact_mod_cast primitiveRepresentationCount_le k n
    exact hp.trans (hb n hn)

/-- Common-factor scaling alone cannot create polynomially large peaks. -/
theorem primitive_peaks_iff_full_peaks {k : ℕ} (hk : 0 < k) :
    (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < primitiveRepresentationCount k n}.Infinite) ↔
    (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < representationCount k n}.Infinite) := by
  have h := primitive_bound_iff_full_bound hk
  rw [← no_polynomial_peaks_iff_uniform_bound (primitiveRepresentationCount k),
    ← no_polynomial_peaks_iff_uniform_bound (representationCount k)] at h
  exact not_iff_not.mp h

namespace QuarticSuperlog

open scoped BigOperators
abbrev EZ := Zsqrtd (-3)

def content (z : EZ) : ℕ := Int.gcd z.re z.im

lemma content_eq_one {z : EZ} (h : IsCoprime z (star z)) : content z = 1 := by
  have hd : ((content z : ℤ) : EZ) ∣ z := by
    rw [Zsqrtd.intCast_dvd]
    exact ⟨Int.gcd_dvd_left _ _, Int.gcd_dvd_right _ _⟩
  have hs : ((content z : ℤ) : EZ) ∣ star z := by
    rw [Zsqrtd.intCast_dvd]
    exact ⟨Int.gcd_dvd_left _ _, dvd_neg.mpr (Int.gcd_dvd_right _ _)⟩
  obtain ⟨a,b,hab⟩ := h
  have hu : ((content z : ℤ) : EZ) ∣ 1 := by
    rw [← hab]
    exact dvd_add (dvd_mul_of_dvd_right hd _) (dvd_mul_of_dvd_right hs _)
  have hu' : (content z : ℤ) ∣ (1 : ℤ) := (Zsqrtd.intCast_dvd_intCast _ _).mp hu
  exact Nat.dvd_one.mp (by exact_mod_cast hu')

lemma content_smul (d : ℕ) (z : EZ) : content ((d : EZ) * z) = d * content z := by
  simp [content, Int.gcd_mul_left]

lemma norm_cast_coprime {z w : EZ} (h : IsCoprime z.norm w.norm) :
    IsCoprime z (star w) := by
  have hc := h.map (Int.castRingHom EZ)
  simp only [Int.coe_castRingHom, Zsqrtd.norm_eq_mul_conj] at hc
  exact hc.of_mul_left_left.of_mul_right_right

lemma norm_pow (z : EZ) (m : ℕ) : (z ^ m).norm = z.norm ^ m :=
  map_pow Zsqrtd.normMonoidHom z m

lemma norm_prod {ι : Type*} (s : Finset ι) (z : ι → EZ) :
    (∏ i ∈ s, z i).norm = ∏ i ∈ s, (z i).norm :=
  map_prod Zsqrtd.normMonoidHom z s

lemma coprime_prod_star {ι : Type*} (s : Finset ι) (z : ι → EZ)
    (h : ∀ i ∈ s, ∀ j ∈ s, IsCoprime (z i) (star (z j))) :
    IsCoprime (∏ i ∈ s, z i) (star (∏ i ∈ s, z i)) := by
  rw [star_prod]
  exact IsCoprime.prod_left fun i hi ↦ IsCoprime.prod_right fun j hj ↦ h i hi j hj

lemma primitive_product {r : ℕ} (a : Fin r → EZ)
    (h : ∀ i j, IsCoprime (a i) (star (a j))) (e : Fin r → ℕ) :
    content (∏ i, a i ^ e i) = 1 := by
  apply content_eq_one
  apply coprime_prod_star
  intro i _ j _
  rw [star_pow]
  exact (h i j).pow

lemma new_norm_coprime (B : ℕ) : Nat.Coprime (1 + 12 * B ^ 2) B := by
  apply Nat.isCoprime_iff_coprime.mp
  refine ⟨1, -12 * (B : ℤ), ?_⟩
  push_cast
  ring

lemma new_element_coprime (B : ℕ) :
    IsCoprime (⟨1, 2 * B⟩ : EZ) (star (⟨1, 2 * B⟩ : EZ)) := by
  let a : EZ := ⟨1, 2 * B⟩
  refine ⟨star a - 6 * (B : EZ) ^ 2, -6 * (B : EZ) ^ 2, ?_⟩
  ext <;> simp [a, pow_two] <;> ring

lemma good_system (r : ℕ) : ∃ (q : Fin r → ℕ) (a : Fin r → EZ),
    (∀ i, 1 < q i) ∧ (∀ i, (a i).norm = (q i : ℤ)) ∧
    Pairwise (Function.onFun Nat.Coprime q) ∧
    (∀ i j, IsCoprime (a i) (star (a j))) := by
  induction r with
  | zero =>
    refine ⟨Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_⟩ <;> intro i <;> exact i.elim0
  | succ r ih =>
    obtain ⟨q,a,hq,ha,hqq,haa⟩ := ih
    let B := ∏ i, q i
    have hB : 0 < B := Finset.prod_pos fun i _ ↦ (by have := hq i; omega)
    let Q := 1 + 12 * B ^ 2
    let A : EZ := ⟨1, 2 * B⟩
    have hQ : 1 < Q := by dsimp [Q]; nlinarith [sq_pos_of_pos hB]
    have hA : A.norm = (Q : ℤ) := by simp [A, Q, Zsqrtd.norm]; ring
    have hQi (i : Fin r) : Nat.Coprime Q (q i) :=
      (new_norm_coprime B).of_dvd_right (Finset.dvd_prod_of_mem q (Finset.mem_univ i))
    refine ⟨Fin.cons Q q, Fin.cons A a, ?_, ?_, ?_, ?_⟩
    · intro i; refine Fin.cases hQ (fun j ↦ hq j) i
    · intro i; refine Fin.cases hA (fun j ↦ ha j) i
    · intro i
      induction i using Fin.cases with
      | zero =>
        intro j
        induction j using Fin.cases with
        | zero => exact fun h ↦ False.elim (h rfl)
        | succ j => exact fun _ ↦ hQi j
      | succ i =>
        intro j
        induction j using Fin.cases with
        | zero => exact fun _ ↦ (hQi i).symm
        | succ j =>
          intro hij
          exact hqq (by intro he; exact hij (congrArg Fin.succ he))
    · intro i j
      refine Fin.cases ?_ (fun i' ↦ ?_) i
      · refine Fin.cases (new_element_coprime B) (fun j' ↦ ?_) j
        apply norm_cast_coprime
        simp only [Fin.cons_zero, Fin.cons_succ, hA, ha]
        exact (hQi j').isCoprime
      · refine Fin.cases ?_ (fun j' ↦ haa i' j') j
        apply norm_cast_coprime
        simp only [Fin.cons_zero, Fin.cons_succ, ha, hA]
        exact (hQi i').symm.isCoprime

lemma coprime_power_product_injective {r m : ℕ} (q : Fin r → ℕ)
    (hq : ∀ i, 1 < q i) (hqq : Pairwise (Function.onFun Nat.Coprime q)) :
    Function.Injective (fun j : Fin r → Fin (m + 1) ↦ ∏ i, q i ^ (j i : ℕ)) := by
  intro j k hjk
  funext i
  apply Fin.ext
  have hg (j : Fin r → Fin (m + 1)) :
      (∏ l, q l ^ (j l : ℕ)).gcd (q i ^ m) = q i ^ (j i : ℕ) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    apply Nat.gcd_mul_of_coprime_of_dvd
    · apply Nat.Coprime.prod_left
      intro l hl
      exact (hqq (Finset.mem_erase.mp hl).1).pow _ _
    · exact Nat.pow_dvd_pow _ (Nat.le_of_lt_succ (j i).isLt)
  have he := congrArg (fun d ↦ Nat.gcd d (q i ^ m)) hjk
  dsimp only at he
  rw [hg, hg] at he
  exact Nat.pow_right_injective (hq i) he

def divisorWord {r m : ℕ} (q : Fin r → ℕ) (j : Fin r → Fin (m + 1)) : ℕ :=
  ∏ i, q i ^ (j i : ℕ)

def primitiveWord {r m : ℕ} (a : Fin r → EZ) (j : Fin r → Fin (m + 1)) : EZ :=
  ∏ i, a i ^ (2 * (m - (j i : ℕ)))

def word {r m : ℕ} (q : Fin r → ℕ) (a : Fin r → EZ)
    (j : Fin r → Fin (m + 1)) : EZ :=
  (divisorWord q j : EZ) * primitiveWord a j

lemma word_content {r m : ℕ} (q : Fin r → ℕ) (a : Fin r → EZ)
    (haa : ∀ i j, IsCoprime (a i) (star (a j))) (j : Fin r → Fin (m + 1)) :
    content (word q a j) = divisorWord q j := by
  rw [word, content_smul, primitiveWord, primitive_product a haa, mul_one]

lemma word_norm {r m : ℕ} (q : Fin r → ℕ) (a : Fin r → EZ)
    (ha : ∀ i, (a i).norm = (q i : ℤ)) (j : Fin r → Fin (m + 1)) :
    (word q a j).norm = (∏ i, (q i : ℤ)) ^ (2 * m) := by
  simp only [word, Zsqrtd.norm_mul, Zsqrtd.norm_natCast, divisorWord,
    primitiveWord, norm_prod, norm_pow, ha, Nat.cast_prod, Nat.cast_pow]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_two, ← pow_mul, ← pow_add]
  congr 1
  have := (j i).isLt
  omega

def quarticVector (z : EZ) : Fin 4 → ℕ :=
  ![(z.re + z.im).natAbs, (z.re - z.im).natAbs, (2 * z.im).natAbs, 1]

lemma quarticVector_sum (z : EZ) :
    (∑ i, quarticVector z i ^ 4 : ℕ) = 2 * z.norm.natAbs ^ 2 + 1 := by
  apply Int.natCast_inj.mp
  push_cast
  simp only [Fin.sum_univ_four, quarticVector, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Int.natCast_natAbs,
    (by decide : Even (4 : ℕ)).pow_abs, sq_abs]
  simp [Zsqrtd.norm]
  ring

lemma quarticVector_content {z w : EZ} (h : quarticVector z = quarticVector w) :
    content z = content w := by
  have h0 := congrFun h (0 : Fin 4)
  have h1 := congrFun h (1 : Fin 4)
  have h2 := congrFun h (2 : Fin 4)
  change (z.re + z.im).natAbs = (w.re + w.im).natAbs at h0
  change (z.re - z.im).natAbs = (w.re - w.im).natAbs at h1
  change (2 * z.im).natAbs = (2 * w.im).natAbs at h2
  have hx : z.re.natAbs = w.re.natAbs := by
    apply Int.natAbs_eq_natAbs_iff.mpr
    rcases Int.natAbs_eq_natAbs_iff.mp h0 with h0 | h0 <;>
    rcases Int.natAbs_eq_natAbs_iff.mp h1 with h1 | h1 <;>
    rcases Int.natAbs_eq_natAbs_iff.mp h2 with h2 | h2 <;> omega
  have hy : z.im.natAbs = w.im.natAbs := by
    simp only [Int.natAbs_mul] at h2
    omega
  simp only [content, Int.gcd_eq_natAbs, hx, hy]

lemma vector_word_injective {r m : ℕ} (q : Fin r → ℕ) (a : Fin r → EZ)
    (hq : ∀ i, 1 < q i) (hqq : Pairwise (Function.onFun Nat.Coprime q))
    (haa : ∀ i j, IsCoprime (a i) (star (a j))) :
    Function.Injective (fun j : Fin r → Fin (m + 1) ↦ quarticVector (word q a j)) := by
  intro j k hjk
  have h := quarticVector_content hjk
  rw [word_content q a haa, word_content q a haa] at h
  exact coprime_power_product_injective q hq hqq h

lemma count_of_injective_vectors {ι : Type*} [Fintype ι] (n : ℕ)
    (v : ι → Fin 4 → ℕ) (hv : Function.Injective v)
    (hs : ∀ j, ∑ i, v j i ^ 4 = n) (h3 : ∀ j, v j 3 = 1) :
    Fintype.card ι ≤ Erdos322.primitiveRepresentationCount 4 n := by
  classical
  let f : ι → Fin 4 → Fin (n + 1) := fun j i ↦ ⟨v j i, by
    have hb : v j i ≤ v j i ^ 4 := Nat.le_pow (by decide)
    have hc : v j i ^ 4 ≤ ∑ l, v j l ^ 4 :=
      Finset.single_le_sum (f := fun l : Fin 4 ↦ v j l ^ 4)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hn := hs j
    omega⟩
  have hf : Function.Injective f := by
    intro j k he
    apply hv
    funext i
    exact congrArg (fun g ↦ (g i).val) he
  unfold Erdos322.primitiveRepresentationCount
  have hc := Finset.card_le_card_of_injOn f (s := Finset.univ)
    (t := Finset.univ.filter (fun g : Fin 4 → Fin (n + 1) ↦
      (∑ i, (g i : ℕ) ^ 4 = n) ∧ Finset.univ.gcd (fun i ↦ (g i : ℕ)) = 1))
    (by
      intro j _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hs j, Nat.dvd_one.mp ?_⟩
      have hd := Finset.gcd_dvd (f := fun i ↦ (f j i : ℕ)) (Finset.mem_univ (3 : Fin 4))
      change _ ∣ v j 3 at hd
      rw [h3 j] at hd
      exact hd)
    hf.injOn
  simpa using hc

lemma system_lower_bound {r : ℕ} (q : Fin r → ℕ) (a : Fin r → EZ)
    (hq : ∀ i, 1 < q i) (ha : ∀ i, (a i).norm = (q i : ℤ))
    (hqq : Pairwise (Function.onFun Nat.Coprime q))
    (haa : ∀ i j, IsCoprime (a i) (star (a j))) (m : ℕ) :
    (m + 1) ^ r ≤ Erdos322.primitiveRepresentationCount 4
      (2 * (∏ i, q i) ^ (4 * m) + 1) := by
  have hv := vector_word_injective (m := m) q a hq hqq haa
  have hs (j : Fin r → Fin (m + 1)) : ∑ i, quarticVector (word q a j) i ^ 4 =
      2 * (∏ i, q i) ^ (4 * m) + 1 := by
    rw [quarticVector_sum, word_norm q a ha, ← Nat.cast_prod,
      Int.natAbs_pow, Int.natAbs_natCast, ← pow_mul]
    congr 3
    omega
  have h := count_of_injective_vectors _ _ hv hs (fun _ ↦ rfl)
  simpa using h

/-- At exponentially growing targets the primitive quartic count dominates any fixed
power of the exponent. In particular, no fixed power of the logarithm is an upper bound. -/
theorem quartic_arbitrary_log_degree (r : ℕ) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ m : ℕ, (m + 1) ^ (r + 1) ≤
      Erdos322.primitiveRepresentationCount 4 (2 * B ^ (4 * m) + 1) := by
  obtain ⟨q,a,hq,ha,hqq,haa⟩ := good_system (r + 1)
  refine ⟨∏ i, q i, ?_, system_lower_bound q a hq ha hqq haa⟩
  have hpos : 0 < ∏ i, q i := Finset.prod_pos fun i _ ↦ by have := hq i; omega
  have hd : q 0 ∣ ∏ i, q i := Finset.dvd_prod_of_mem q (Finset.mem_univ 0)
  exact (hq 0).trans_le (Nat.le_of_dvd hpos hd)

lemma quartic_target_log_bound {B : ℕ} (hB : 2 ≤ B) (m : ℕ) :
    Real.log (2 * (B : ℝ) ^ (4 * m) + 1) ≤ (3 + 4 * B : ℕ) * (m + 1 : ℕ) := by
  have hB1 : 1 ≤ (B : ℝ) := by exact_mod_cast (show 1 ≤ B by omega)
  have hp : 1 ≤ (B : ℝ) ^ (4 * m) := one_le_pow₀ hB1
  have hlog : Real.log (3 * (B : ℝ) ^ (4 * m)) =
      Real.log 3 + (4 * m : ℕ) * Real.log B := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  calc
    Real.log (2 * (B : ℝ) ^ (4 * m) + 1) ≤
        Real.log (3 * (B : ℝ) ^ (4 * m)) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 3 + (4 * m : ℕ) * Real.log B := hlog
    _ ≤ 3 + (4 * m : ℕ) * (B : ℝ) := by
      gcongr
      · exact Real.log_le_self (by norm_num)
      · exact Real.log_le_self (by positivity)
    _ ≤ (3 + 4 * B : ℕ) * (m + 1 : ℕ) := by push_cast; nlinarith

/-- Every fixed polylogarithmic bound fails infinitely often, even when all
quartic representations are required to be primitive. -/
theorem primitive_quartic_superlogarithmic (A : ℕ) :
    {n : ℕ | (Real.log n) ^ A <
      Erdos322.primitiveRepresentationCount 4 n}.Infinite := by
  obtain ⟨B,hB,hcount⟩ := quartic_arbitrary_log_degree A
  let C := 3 + 4 * B
  let M := C ^ A
  let f : ℕ → ℕ := fun t ↦ 2 * B ^ (4 * (M + t)) + 1
  have hf : Function.Injective f := by
    intro s t h
    change 2 * B ^ (4 * (M + s)) + 1 = 2 * B ^ (4 * (M + t)) + 1 at h
    have hp : B ^ (4 * (M + s)) = B ^ (4 * (M + t)) := by omega
    have he := Nat.pow_right_injective hB hp
    omega
  apply (Set.infinite_range_of_injective hf).mono
  rintro n ⟨t,rfl⟩
  let m := M + t
  have hm : C ^ A < m + 1 := by dsimp [m,M]; omega
  have hpos : 0 < (m + 1 : ℕ) := by omega
  have hn : 1 ≤ f t := by dsimp [f]; omega
  have hlog : Real.log (f t) ≤ (C : ℝ) * (m + 1 : ℕ) := by
    simpa [f,m,C] using quartic_target_log_bound hB (M + t)
  have hnonneg : 0 ≤ Real.log (f t) := Real.log_nonneg (by exact_mod_cast hn)
  change (Real.log (f t)) ^ A < _
  calc
    (Real.log (f t)) ^ A ≤ ((C : ℝ) * (m + 1 : ℕ)) ^ A :=
      pow_le_pow_left₀ hnonneg hlog A
    _ = (C : ℝ) ^ A * ((m + 1 : ℕ) : ℝ) ^ A := mul_pow _ _ _
    _ < ((m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) ^ A := by
      apply mul_lt_mul_of_pos_right
      · exact_mod_cast hm
      · positivity
    _ = ((m + 1 : ℕ) : ℝ) ^ (A + 1) := by ring
    _ ≤ Erdos322.primitiveRepresentationCount 4 (f t) := by
      exact_mod_cast hcount m

/-- The unrestricted count also exceeds every fixed power of the logarithm infinitely often. -/
theorem quartic_superlogarithmic (A : ℕ) :
    {n : ℕ | (Real.log n) ^ A < Erdos322.representationCount 4 n}.Infinite := by
  apply (primitive_quartic_superlogarithmic A).mono
  intro n hn
  have hle : (Erdos322.primitiveRepresentationCount 4 n : ℝ) ≤
      Erdos322.representationCount 4 n := by
    exact_mod_cast Erdos322.primitiveRepresentationCount_le 4 n
  exact lt_of_lt_of_le hn hle

lemma good_system_quantitative (r : ℕ) : ∃ (q : Fin r → ℕ) (a : Fin r → EZ),
    (∀ i, 1 < q i) ∧ (∀ i, (a i).norm = (q i : ℤ)) ∧
    Pairwise (Function.onFun Nat.Coprime q) ∧
    (∀ i j, IsCoprime (a i) (star (a j))) ∧
    4 * (∏ i, q i) ≤ 4 ^ (3 ^ r) := by
  induction r with
  | zero =>
    refine ⟨Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · norm_num
  | succ r ih =>
    obtain ⟨q,a,hq,ha,hqq,haa,hsize⟩ := ih
    let B := ∏ i, q i
    have hB : 0 < B := Finset.prod_pos fun i _ ↦ (by have := hq i; omega)
    let Q := 1 + 12 * B ^ 2
    let A : EZ := ⟨1, 2 * B⟩
    have hQ : 1 < Q := by dsimp [Q]; nlinarith [sq_pos_of_pos hB]
    have hA : A.norm = (Q : ℤ) := by simp [A, Q, Zsqrtd.norm]; ring
    have hQi (i : Fin r) : Nat.Coprime Q (q i) :=
      (new_norm_coprime B).of_dvd_right (Finset.dvd_prod_of_mem q (Finset.mem_univ i))
    refine ⟨Fin.cons Q q, Fin.cons A a, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; refine Fin.cases hQ (fun j ↦ hq j) i
    · intro i; refine Fin.cases hA (fun j ↦ ha j) i
    · intro i
      induction i using Fin.cases with
      | zero =>
        intro j
        induction j using Fin.cases with
        | zero => exact fun h ↦ False.elim (h rfl)
        | succ j => exact fun _ ↦ hQi j
      | succ i =>
        intro j
        induction j using Fin.cases with
        | zero => exact fun _ ↦ (hQi i).symm
        | succ j =>
          intro hij
          exact hqq (by intro he; exact hij (congrArg Fin.succ he))
    · intro i j
      refine Fin.cases ?_ (fun i' ↦ ?_) i
      · refine Fin.cases (new_element_coprime B) (fun j' ↦ ?_) j
        apply norm_cast_coprime
        simp only [Fin.cons_zero, Fin.cons_succ, hA, ha]
        exact (hQi j').isCoprime
      · refine Fin.cases ?_ (fun j' ↦ haa i' j') j
        apply norm_cast_coprime
        simp only [Fin.cons_zero, Fin.cons_succ, ha, hA]
        exact (hQi i').symm.isCoprime
    · simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      change 4 * (Q * B) ≤ 4 ^ (3 ^ (r + 1))
      have hcube : B ≤ B ^ 3 := Nat.le_pow (by decide)
      calc
        4 * (Q * B) ≤ (4 * B) ^ 3 := by dsimp [Q]; nlinarith
        _ ≤ (4 ^ (3 ^ r)) ^ 3 := Nat.pow_le_pow_left hsize 3
        _ = 4 ^ (3 ^ (r + 1)) := by rw [← pow_mul, pow_succ]

/-- A quantitative version of the superlogarithmic lower bound. The target is
at most doubly exponential in `r`, while the count is at least exponential in `r²`. -/
theorem quartic_quantitative_peaks (r : ℕ) :
    ∃ n : ℕ, 2 * 2 ^ (4 * 3 ^ r) + 1 ≤ n ∧
      n ≤ 3 * 4 ^ (12 * 9 ^ r) ∧
      3 ^ (r * (r + 1)) ≤ Erdos322.primitiveRepresentationCount 4 n := by
  obtain ⟨q,a,hq,ha,hqq,haa,hsize⟩ := good_system_quantitative (r + 1)
  let B := ∏ i, q i
  have hpos : 0 < B := Finset.prod_pos fun i _ ↦ by have := hq i; omega
  have hB : 2 ≤ B := by
    have hd : q 0 ∣ B := Finset.dvd_prod_of_mem q (Finset.mem_univ 0)
    exact (hq 0).trans_le (Nat.le_of_dvd hpos hd)
  have hBupper : B ≤ 4 ^ (3 ^ (r + 1)) := by change 4 * B ≤ _ at hsize; omega
  refine ⟨2 * B ^ (4 * 3 ^ r) + 1, ?_, ?_, ?_⟩
  · gcongr
  · have hp : 1 ≤ B ^ (4 * 3 ^ r) := one_le_pow₀ (by omega)
    calc
      2 * B ^ (4 * 3 ^ r) + 1 ≤ 3 * B ^ (4 * 3 ^ r) := by omega
      _ ≤ 3 * (4 ^ (3 ^ (r + 1))) ^ (4 * 3 ^ r) := by gcongr
      _ = 3 * 4 ^ (12 * 9 ^ r) := by
        rw [← pow_mul]
        congr 2
        calc
          3 ^ (r + 1) * (4 * 3 ^ r) = 12 * (3 ^ r * 3 ^ r) := by rw [pow_succ]; ring
          _ = 12 * 9 ^ r := by rw [← mul_pow]; norm_num
  · calc
      3 ^ (r * (r + 1)) = (3 ^ r) ^ (r + 1) := pow_mul _ _ _
      _ ≤ (3 ^ r + 1) ^ (r + 1) := Nat.pow_le_pow_left (by omega) _
      _ ≤ Erdos322.primitiveRepresentationCount 4 (2 * B ^ (4 * 3 ^ r) + 1) :=
        system_lower_bound q a hq ha hqq haa (3 ^ r)

lemma loglog_bound_of_target_bound {r n : ℕ} (hr : 1 ≤ r) (hn : 3 ≤ n)
    (hupper : n ≤ 3 * 4 ^ (12 * 9 ^ r)) :
    0 ≤ Real.log (Real.log n) ∧ Real.log (Real.log n) ≤ 73 * (r : ℝ) := by
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hlower : 1 ≤ Real.log (n : ℝ) := by
    apply (Real.le_log_iff_exp_le hnpos).mpr
    exact Real.exp_one_lt_three.le.trans hnreal
  have hp : 1 ≤ (9 : ℝ) ^ r := one_le_pow₀ (by norm_num)
  have hlogupper : Real.log (n : ℝ) ≤ 64 * (9 : ℝ) ^ r := by
    calc
      Real.log (n : ℝ) ≤ Real.log (3 * (4 : ℝ) ^ (12 * 9 ^ r)) := by
        apply Real.log_le_log hnpos
        exact_mod_cast hupper
      _ = Real.log 3 + (12 * 9 ^ r : ℕ) * Real.log 4 := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      _ ≤ 3 + (12 * 9 ^ r : ℕ) * 4 := by
        gcongr
        · exact Real.log_le_self (by norm_num)
        · exact Real.log_le_self (by norm_num)
      _ ≤ 64 * (9 : ℝ) ^ r := by push_cast; nlinarith
  refine ⟨Real.log_nonneg hlower, ?_⟩
  calc
    Real.log (Real.log n) ≤ Real.log (64 * (9 : ℝ) ^ r) :=
      Real.log_le_log (by linarith) hlogupper
    _ = Real.log 64 + (r : ℝ) * Real.log 9 := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    _ ≤ 64 + (r : ℝ) * 9 := by
      gcongr
      · exact Real.log_le_self (by norm_num)
      · exact Real.log_le_self (by norm_num)
    _ ≤ 73 * (r : ℝ) := by
      have hrreal : (1 : ℝ) ≤ r := by exact_mod_cast hr
      linarith

/-- Explicit quasipolylogarithmic peaks for the primitive quartic count. -/
theorem primitive_quartic_loglog_square :
    {n : ℕ | (2 : ℝ) ^ ((Real.log (Real.log n)) ^ 2 / 10000) <
      Erdos322.primitiveRepresentationCount 4 n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro M
  let r := M + 1
  have hr : 1 ≤ r := by dsimp [r]; omega
  obtain ⟨n,hnlow,hnupper,hncount⟩ := quartic_quantitative_peaks r
  have htwo : 1 ≤ 2 ^ (4 * 3 ^ r) := one_le_pow₀ (by omega)
  have hn : 3 ≤ n := by omega
  obtain ⟨hllpos,hllupper⟩ := loglog_bound_of_target_bound hr hn hnupper
  have hrreal : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hsquare : (Real.log (Real.log n)) ^ 2 ≤ (73 * (r : ℝ)) ^ 2 :=
    (sq_le_sq₀ hllpos (by positivity)).mpr hllupper
  have hexp : (Real.log (Real.log n)) ^ 2 / 10000 < (r * (r + 1) : ℕ) := by
    push_cast
    nlinarith [sq_nonneg (r : ℝ)]
  refine ⟨n, ?_, ?_⟩
  · change (2 : ℝ) ^ ((Real.log (Real.log n)) ^ 2 / 10000) < _
    calc
      (2 : ℝ) ^ ((Real.log (Real.log n)) ^ 2 / 10000) <
          (2 : ℝ) ^ ((r * (r + 1) : ℕ) : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
      _ = (2 : ℝ) ^ (r * (r + 1)) := Real.rpow_natCast _ _
      _ ≤ (3 : ℝ) ^ (r * (r + 1)) := by gcongr; norm_num
      _ ≤ Erdos322.primitiveRepresentationCount 4 n := by exact_mod_cast hncount
  · have h3 := Nat.lt_pow_self (n := r) (by decide : 1 < 3)
    have h2 := Nat.lt_pow_self (n := 4 * 3 ^ r) (by decide : 1 < 2)
    have hrM : M < r := by dsimp [r]; omega
    omega

/-- The same explicit lower bound holds without the primitivity restriction. -/
theorem quartic_loglog_square :
    {n : ℕ | (2 : ℝ) ^ ((Real.log (Real.log n)) ^ 2 / 10000) <
      Erdos322.representationCount 4 n}.Infinite := by
  apply primitive_quartic_loglog_square.mono
  intro n hn
  have hle : (Erdos322.primitiveRepresentationCount 4 n : ℝ) ≤
      Erdos322.representationCount 4 n := by
    exact_mod_cast Erdos322.primitiveRepresentationCount_le 4 n
  exact lt_of_lt_of_le hn hle

lemma parameter_count_le_divisor_count {r m : ℕ} (q : Fin r → ℕ)
    (hq : ∀ i, 1 < q i) (hqq : Pairwise (Function.onFun Nat.Coprime q)) :
    (m + 1) ^ r ≤ ((∏ i, q i) ^ m).divisors.card := by
  classical
  have hpos : 0 < ∏ i, q i := Finset.prod_pos fun i _ ↦ by have := hq i; omega
  have h := Finset.card_le_card_of_injOn
    (fun j : Fin r → Fin (m + 1) ↦ ∏ i, q i ^ (j i : ℕ))
    (s := Finset.univ) (t := ((∏ i, q i) ^ m).divisors)
    (by
      intro j _
      apply Nat.mem_divisors.mpr
      refine ⟨?_, (pow_pos hpos m).ne'⟩
      rw [← Finset.prod_pow]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ ↦
        Nat.pow_dvd_pow _ (Nat.le_of_lt_succ (j i).isLt))
    (coprime_power_product_injective q hq hqq).injOn
  simpa using h

/-- The number of representations supplied by the construction is uniformly
subpolynomial in its target, even when the number of norm factors varies. -/
theorem constructed_family_uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ (r m : ℕ) (q : Fin r → ℕ),
      (∀ i, 1 < q i) → Pairwise (Function.onFun Nat.Coprime q) →
      ((m + 1 : ℕ) : ℝ) ^ r ≤ C * ((2 * (∏ i, q i) ^ (4 * m) + 1 : ℕ) : ℝ) ^ ε := by
  obtain ⟨C,hC,hdiv⟩ := Erdos322.divisor_count_subpolynomial ε hε
  refine ⟨C,hC,fun r m q hq hqq ↦ ?_⟩
  have hB : 0 < ∏ i, q i := Finset.prod_pos fun i _ ↦ by have := hq i; omega
  have hpow : 0 < (∏ i, q i) ^ m := pow_pos hB _
  have hle : (∏ i, q i) ^ m ≤ 2 * (∏ i, q i) ^ (4 * m) + 1 := by
    have h := Nat.pow_le_pow_right hB (show m ≤ 4 * m by omega)
    omega
  calc
    ((m + 1 : ℕ) : ℝ) ^ r ≤ (((∏ i, q i) ^ m).divisors.card : ℝ) := by
      exact_mod_cast parameter_count_le_divisor_count q hq hqq
    _ ≤ C * (((∏ i, q i) ^ m : ℕ) : ℝ) ^ ε := hdiv _ hpow
    _ ≤ C * ((2 * (∏ i, q i) ^ (4 * m) + 1 : ℕ) : ℝ) ^ ε := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hle) hε.le

end QuarticSuperlog


/- Bounds for binary positive definite norm equations. -/
namespace QuarticAdditive

private lemma square_roots_same_gcd {n a r s : ℕ} (hn : 0 < n)
    (hr : r ^ 2 ≡ a ^ 2 [MOD n]) (hs : s ^ 2 ≡ a ^ 2 [MOD n])
    (hg : n.gcd (r + a) = n.gcd (s + a)) :
    r ≡ s [MOD n / n.gcd (2 * a)] := by
  let g := n.gcd (r + a)
  have hqr : r ≡ a [MOD n / g] := by
    apply Nat.ModEq.cancel_left_div_gcd hn
    convert hr.add_right (r * a) using 1 <;> ring
  have hqs : s ≡ a [MOD n / g] := by
    rw [show g = n.gcd (s + a) from hg]
    apply Nat.ModEq.cancel_left_div_gcd hn
    convert hs.add_right (s * a) using 1 <;> ring
  have hqrsub : ((n / g : ℕ) : ℤ) ∣ (r : ℤ) - a := by
    exact Nat.modEq_iff_dvd.mp hqr.symm
  have hqsub : ((n / g : ℕ) : ℤ) ∣ (s : ℤ) - r := by
    exact Nat.modEq_iff_dvd.mp (hqr.trans hqs.symm)
  have hgr : (g : ℤ) ∣ (r : ℤ) + a := by
    exact_mod_cast Nat.gcd_dvd_right n (r + a)
  have hgs : (g : ℤ) ∣ (s : ℤ) + a := by
    have : g ∣ s + a := by rw [show g = n.gcd (s + a) from hg]; exact Nat.gcd_dvd_right _ _
    exact_mod_cast this
  have hgsub : (g : ℤ) ∣ (s : ℤ) - r := by
    convert dvd_sub hgs hgr using 1; ring
  have hprod : (g : ℤ) * (n / g : ℕ) = n := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left n (r + a))
  have h1 : (n : ℤ) ∣ ((r : ℤ) + a) * (s - r) := by
    rw [← hprod]
    exact mul_dvd_mul hgr hqsub
  have h2 : (n : ℤ) ∣ ((r : ℤ) - a) * (s - r) := by
    rw [← hprod, mul_comm]
    exact mul_dvd_mul hqrsub hgsub
  have hmul : 2 * a * r ≡ 2 * a * s [MOD n] := by
    apply Nat.modEq_iff_dvd.mpr
    convert dvd_sub h1 h2 using 1; push_cast; ring
  exact hmul.cancel_left_div_gcd hn

/-- A root of a quadratic congruence with small derivative controls the total
number of roots, by an elementary divisor injection. -/
theorem square_congruence_count {n a K : ℕ} (hn : 0 < n)
    (hK : n.gcd (2 * a) ≤ K) :
    ((Finset.range n).filter fun r ↦ r ^ 2 ≡ a ^ 2 [MOD n]).card ≤
      n.divisors.card * K := by
  classical
  let G := n.gcd (2 * a)
  let q := n / G
  have hG : 0 < G := Nat.gcd_pos_of_pos_left _ hn
  have hdG : G ∣ n := Nat.gcd_dvd_left _ _
  have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd hn hdG) hG
  have hnq : G * q = n := Nat.mul_div_cancel' hdG
  have h := Finset.card_le_card_of_injOn
    (fun r : ℕ ↦ (n.gcd (r + a), r / q))
    (s := (Finset.range n).filter fun r ↦ r ^ 2 ≡ a ^ 2 [MOD n])
    (t := n.divisors ×ˢ Finset.range K) (by
      intro r hr
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr
      obtain ⟨hrn, hroot⟩ := hr
      refine Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, hn.ne'⟩, ?_⟩
      apply Finset.mem_range.mpr
      have hdiv : r / q < G := (Nat.div_lt_iff_lt_mul hq).mpr (by rwa [hnq])
      exact hdiv.trans_le hK)
    (by
      intro r hr s hs heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr hs
      have hg := congrArg Prod.fst heq
      have hdiv := congrArg Prod.snd heq
      have hmod : r % q = s % q := square_roots_same_gcd hn
        hr.2 hs.2 hg
      have h1 := Nat.div_add_mod r q
      have h2 := Nat.div_add_mod s q
      change r / q = s / q at hdiv
      rw [hdiv] at h1
      omega)
  simpa using h


def binaryNormSolutions (d n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun p ↦ p.1 ^ 2 + d * p.2 ^ 2 = n)

def primitiveBinaryNormSolutions (d n : ℕ) : Finset (ℕ × ℕ) :=
  (binaryNormSolutions d n).filter (fun p ↦ p.1.Coprime p.2)

private def normRoot (n : ℕ) (p : ℕ × ℕ) : ℕ :=
  ((p.1 : ZMod n) * (p.2 : ZMod n)⁻¹).val

private lemma norm_coprime_right {d n x y : ℕ}
    (h : x ^ 2 + d * y ^ 2 = n) (hc : x.Coprime y) : y.Coprime n := by
  rw [← h, show d * y ^ 2 = (d * y) * y by ring,
    Nat.coprime_add_mul_right_right]
  exact hc.symm.pow_right 2

private lemma normRoot_mul {d n x y : ℕ} (hn : 0 < n)
    (h : x ^ 2 + d * y ^ 2 = n) (hc : x.Coprime y) :
    normRoot n (x, y) * y ≡ x [MOD n] := by
  letI : NeZero n := ⟨hn.ne'⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  have hi := ZMod.mul_inv_of_unit (y : ZMod n)
    ((ZMod.isUnit_iff_coprime _ _).mpr (norm_coprime_right h hc))
  simp only [Nat.cast_mul, normRoot, ZMod.natCast_zmod_val]
  calc
    (x : ZMod n) * (y : ZMod n)⁻¹ * y = x * (y * (y : ZMod n)⁻¹) := by ring
    _ = x := by rw [hi, mul_one]

private lemma normRoot_square {d n x y : ℕ} (hn : 0 < n)
    (h : x ^ 2 + d * y ^ 2 = n) (hc : x.Coprime y) :
    normRoot n (x, y) ^ 2 + d ≡ 0 [MOD n] := by
  have hr := normRoot_mul hn h hc
  have heq : (normRoot n (x, y) ^ 2 + d) * y ^ 2 ≡ 0 * y ^ 2 [MOD n] := by
    have hh : x ^ 2 + d * y ^ 2 ≡ 0 [MOD n] :=
      Nat.modEq_zero_iff_dvd.mpr (h ▸ dvd_refl n)
    convert ((hr.pow 2).add_right (d * y ^ 2)).trans hh using 1 <;> ring
  have hc' : n.Coprime (y ^ 2) := (norm_coprime_right h hc).symm.pow_right 2
  exact heq.cancel_right_of_coprime hc'

private lemma normRoot_derivative_bound {d n x y : ℕ} (hd : 0 < d) (hn : 0 < n)
    (h : x ^ 2 + d * y ^ 2 = n) (hc : x.Coprime y) :
    n.gcd (2 * normRoot n (x, y)) ≤ 2 * d := by
  let r := normRoot n (x, y)
  let g := n.gcd r
  have hgx : g ∣ x := by
    have hmod := (normRoot_mul hn h hc).of_dvd (Nat.gcd_dvd_left n r)
    have hzero : r * y ≡ 0 [MOD g] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _)
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans hzero)
  have hgd : g ∣ d := by
    have hdyy : g ∣ d * y ^ 2 := by
      have hsum : g ∣ x ^ 2 + d * y ^ 2 := h ▸ Nat.gcd_dvd_left n r
      exact (Nat.dvd_add_iff_right (dvd_pow hgx (by decide : 2 ≠ 0))).mpr hsum
    exact ((hc.of_dvd_left hgx).pow_right 2).dvd_of_dvd_mul_right hdyy
  have hbound : n.gcd (2 * r) ∣ 2 * d := by
    exact (Nat.gcd_mul_right_dvd_mul_gcd n 2 r).trans
      (mul_dvd_mul (Nat.gcd_dvd_right n 2) hgd)
  exact Nat.le_of_dvd (by positivity) hbound

private lemma cross_product_lt {d n x y u v : ℕ} (hd : 2 ≤ d) (hn : 0 < n)
    (h : x ^ 2 + d * y ^ 2 = n) (h' : u ^ 2 + d * v ^ 2 = n) :
    x * v < n := by
  have hx : x ^ 2 ≤ n := by omega
  have hv : 2 * v ^ 2 ≤ n := by nlinarith
  have hm : 2 * (x * v) ^ 2 ≤ n ^ 2 := by
    calc
      2 * (x * v) ^ 2 = x ^ 2 * (2 * v ^ 2) := by ring
      _ ≤ n * n := Nat.mul_le_mul hx hv
      _ = n ^ 2 := by ring
  by_contra hnot
  have hh := Nat.pow_le_pow_left (Nat.le_of_not_lt hnot) 2
  nlinarith [sq_pos_of_pos hn]

private lemma normRoot_injective {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) :
    Set.InjOn (normRoot n) (primitiveBinaryNormSolutions d n : Set (ℕ × ℕ)) := by
  intro p hp q hq heq
  obtain ⟨⟨hpbd, hp⟩, hpc⟩ := by
    simpa only [primitiveBinaryNormSolutions, binaryNormSolutions,
      Finset.mem_coe, Finset.mem_filter] using hp
  obtain ⟨⟨hqbd, hq⟩, hqc⟩ := by
    simpa only [primitiveBinaryNormSolutions, binaryNormSolutions,
      Finset.mem_coe, Finset.mem_filter] using hq
  have hr := (normRoot_mul hn hp hpc).mul_right q.2
  have hs := (normRoot_mul hn hq hqc).mul_right p.2
  have he : p.1 * q.2 ≡ q.1 * p.2 [MOD n] := by
    apply hr.symm.trans
    convert hs using 1
    rw [heq]
    ring
  have hc : p.1 * q.2 = q.1 * p.2 := he.eq_of_lt_of_lt
    (cross_product_lt hd hn hp hq) (cross_product_lt hd hn hq hp)
  have hsq : p.1 ^ 2 = q.1 ^ 2 := by
    apply Nat.mul_left_cancel hn
    calc
      n * p.1 ^ 2 = p.1 ^ 2 * q.1 ^ 2 + d * (p.1 * q.2) ^ 2 := by rw [← hq]; ring
      _ = p.1 ^ 2 * q.1 ^ 2 + d * (q.1 * p.2) ^ 2 := by rw [hc]
      _ = n * q.1 ^ 2 := by rw [← hp]; ring
  have hx : p.1 = q.1 := by nlinarith
  have hy : p.2 = q.2 := by
    rw [hx] at hp
    have hmul : d * p.2 ^ 2 = d * q.2 ^ 2 := by omega
    exact Nat.pow_left_injective (by decide : 2 ≠ 0)
      (Nat.mul_left_cancel (by omega : 0 < d) hmul)
  exact Prod.ext hx hy


lemma mem_binaryNormSolutions {d n : ℕ} (hd : 0 < d) (p : ℕ × ℕ) :
    p ∈ binaryNormSolutions d n ↔ p.1 ^ 2 + d * p.2 ^ 2 = n := by
  simp only [binaryNormSolutions, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    have hx := Nat.le_pow (by decide : 0 < 2) (a := p.1)
    have hy := Nat.le_pow (by decide : 0 < 2) (a := p.2)
    have hdy : p.2 ^ 2 ≤ d * p.2 ^ 2 := Nat.le_mul_of_pos_left _ hd
    exact ⟨⟨by omega, by omega⟩, h⟩

theorem primitive_binary_norm_count {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) :
    (primitiveBinaryNormSolutions d n).card ≤ n.divisors.card * (2 * d) := by
  classical
  by_cases hempty : (primitiveBinaryNormSolutions d n) = ∅
  · simp [hempty]
  obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hp' := Finset.mem_filter.mp hp
  have hpNorm := (mem_binaryNormSolutions (by omega : 0 < d) p).mp hp'.1
  let a := normRoot n p
  have hroots := square_congruence_count (a := a) hn
    (normRoot_derivative_bound (by omega : 0 < d) hn hpNorm hp'.2)
  apply le_trans _ hroots
  apply Finset.card_le_card_of_injOn (normRoot n)
  · intro q hq
    simp only [Finset.mem_coe, primitiveBinaryNormSolutions, Finset.mem_filter] at hq
    have hqNorm := (mem_binaryNormSolutions (by omega : 0 < d) q).mp hq.1
    change normRoot n q ∈ (Finset.range n).filter (fun r ↦ r ^ 2 ≡ a ^ 2 [MOD n])
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · letI : NeZero n := ⟨hn.ne'⟩
      exact Finset.mem_range.mpr (ZMod.val_lt _)
    · have hr := normRoot_square hn hqNorm hq.2
      have hs := normRoot_square hn hpNorm hp'.2
      exact Nat.ModEq.add_right_cancel (Nat.ModEq.refl d) (hr.trans hs.symm)
  · exact normRoot_injective hd hn

private lemma norm_gcd_pos {d n : ℕ} (hn : 0 < n) (p : ℕ × ℕ)
    (hp : p.1 ^ 2 + d * p.2 ^ 2 = n) : 0 < p.1.gcd p.2 := by
  by_contra hnot
  have hg : p.1.gcd p.2 = 0 := by omega
  obtain ⟨hx,hy⟩ := Nat.gcd_eq_zero_iff.mp hg
  simp [hx, hy] at hp
  omega

private lemma norm_quotient_mul {d n : ℕ} (p : ℕ × ℕ)
    (hp : p.1 ^ 2 + d * p.2 ^ 2 = n) :
    p.1.gcd p.2 ^ 2 * ((p.1 / p.1.gcd p.2) ^ 2 +
      d * (p.2 / p.1.gcd p.2) ^ 2) = n := by
  calc
    _ = (p.1.gcd p.2 * (p.1 / p.1.gcd p.2)) ^ 2 +
        d * (p.1.gcd p.2 * (p.2 / p.1.gcd p.2)) ^ 2 := by ring
    _ = p.1 ^ 2 + d * p.2 ^ 2 := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _),
        Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)]
    _ = n := hp

private lemma norm_quotient_primitive {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (p : ℕ × ℕ) (hp : p.1 ^ 2 + d * p.2 ^ 2 = n) :
    (p.1 / p.1.gcd p.2, p.2 / p.1.gcd p.2) ∈
      primitiveBinaryNormSolutions d (n / p.1.gcd p.2 ^ 2) := by
  have hg := norm_gcd_pos hn p hp
  have hmul := norm_quotient_mul p hp
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · apply (mem_binaryNormSolutions hd _).mpr
    change (p.1 / p.1.gcd p.2) ^ 2 + d * (p.2 / p.1.gcd p.2) ^ 2 = _
    rw [← hmul, Nat.mul_div_cancel_left _ (pow_pos hg 2)]
  · change (p.1 / p.1.gcd p.2).gcd (p.2 / p.1.gcd p.2) = 1
    rw [Nat.gcd_div (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _), Nat.div_self hg]

theorem binary_norm_count {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) :
    (binaryNormSolutions d n).card ≤ (2 * d) * n.divisors.card ^ 2 := by
  classical
  let S := binaryNormSolutions d n
  let gs := S.image (fun p ↦ p.1.gcd p.2)
  have hgs : gs ⊆ n.divisors := by
    intro g hg
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hg
    have hpNorm := (mem_binaryNormSolutions (by omega : 0 < d) p).mp hp
    have hmul := norm_quotient_mul p hpNorm
    have hsq : p.1.gcd p.2 ^ 2 ∣ n := ⟨_, hmul.symm⟩
    exact Nat.mem_divisors.mpr ⟨(dvd_pow_self _ (by decide : 2 ≠ 0)).trans hsq, hn.ne'⟩
  have hfiber (g : ℕ) (hg : g ∈ gs) :
      (S.filter (fun p ↦ p.1.gcd p.2 = g)).card ≤ n.divisors.card * (2 * d) := by
    obtain ⟨p,hp,hpg⟩ := Finset.mem_image.mp hg
    have hpNorm := (mem_binaryNormSolutions (by omega : 0 < d) p).mp hp
    have hgpos : 0 < g := hpg ▸ norm_gcd_pos hn p hpNorm
    have hmul := norm_quotient_mul p hpNorm
    rw [hpg] at hmul
    have hsq : g ^ 2 ∣ n := ⟨_, hmul.symm⟩
    have hmpos : 0 < n / g ^ 2 :=
      Nat.div_pos (Nat.le_of_dvd hn hsq) (pow_pos hgpos 2)
    have hdiv : (n / g ^ 2).divisors.card ≤ n.divisors.card :=
      Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' (Nat.div_dvd_of_dvd hsq))
    apply le_trans _ ((primitive_binary_norm_count hd hmpos).trans
      (Nat.mul_le_mul_right (2 * d) hdiv))
    apply Finset.card_le_card_of_injOn (fun q : ℕ × ℕ ↦ (q.1 / g, q.2 / g))
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter] at hq
      have hqNorm := (mem_binaryNormSolutions (by omega : 0 < d) q).mp hq.1
      have hh := norm_quotient_primitive (by omega : 0 < d) hn q hqNorm
      rwa [hq.2] at hh
    · intro q hq r hr heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hq hr
      have h1 : q.1 / g = r.1 / g := congrArg Prod.fst heq
      have h2 : q.2 / g = r.2 / g := congrArg Prod.snd heq
      have hq1 : g * (q.1 / g) = q.1 := by
        rw [← hq.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hq2 : g * (q.2 / g) = q.2 := by
        rw [← hq.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have hr1 : g * (r.1 / g) = r.1 := by
        rw [← hr.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hr2 : g * (r.2 / g) = r.2 := by
        rw [← hr.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      apply Prod.ext
      · rw [← hq1, ← hr1, h1]
      · rw [← hq2, ← hr2, h2]
  calc
    S.card = ∑ g ∈ gs, (S.filter (fun p ↦ p.1.gcd p.2 = g)).card :=
      Finset.card_eq_sum_card_image _ _
    _ ≤ ∑ g ∈ gs, n.divisors.card * (2 * d) := Finset.sum_le_sum hfiber
    _ = gs.card * (n.divisors.card * (2 * d)) := by simp
    _ ≤ n.divisors.card * (n.divisors.card * (2 * d)) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hgs)
    _ = (2 * d) * n.divisors.card ^ 2 := by ring


lemma binary_norm_zero {d : ℕ} (hd : 0 < d) : binaryNormSolutions d 0 = {(0,0)} := by
  ext p
  rw [mem_binaryNormSolutions hd, Finset.mem_singleton]
  constructor
  · intro h
    have hx : p.1 = 0 := by nlinarith
    have hy : p.2 = 0 := by
      have : d * p.2 ^ 2 = 0 := by omega
      have : p.2 ^ 2 = 0 := (mul_eq_zero.mp this).resolve_left hd.ne'
      nlinarith
    exact Prod.ext hx hy
  · rintro rfl
    simp

theorem binary_norm_subpolynomial {d : ℕ} (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
      ((binaryNormSolutions d n).card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C,hC,hdiv⟩ := Erdos322.divisor_count_subpolynomial (ε / 2) (by linarith)
  refine ⟨(2 * d : ℝ) * C ^ 2, by positivity, ?_⟩
  intro n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : ((n : ℝ) ^ (ε / 2)) ^ 2 = (n : ℝ) ^ ε := by
    rw [pow_two, ← Real.rpow_add hnr]
    congr 1
    ring
  calc
    ((binaryNormSolutions d n).card : ℝ) ≤ (2 * d : ℝ) * (n.divisors.card : ℝ) ^ 2 := by
      exact_mod_cast binary_norm_count hd hn
    _ ≤ (2 * d : ℝ) * (C * (n : ℝ) ^ (ε / 2)) ^ 2 := by gcongr; exact hdiv n hn
    _ = ((2 * d : ℝ) * C ^ 2) * (n : ℝ) ^ ε := by rw [mul_pow, hp]; ring

/-- A convenient uniform variant including target zero and all smaller targets. -/
theorem binary_norm_subpolynomial_up_to {d : ℕ} (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ N n : ℕ, n ≤ N →
      ((binaryNormSolutions d n).card : ℝ) ≤ C * (N + 1 : ℝ) ^ ε := by
  obtain ⟨C,hC,hbound⟩ := binary_norm_subpolynomial hd ε hε
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun N n hn ↦ ?_⟩
  by_cases hz : n = 0
  · subst n
    rw [binary_norm_zero (by omega : 0 < d), Finset.card_singleton, Nat.cast_one]
    have hpow : 1 ≤ (N + 1 : ℝ) ^ ε := Real.one_le_rpow (by have := Nat.cast_nonneg (α := ℝ) N; linarith) hε.le
    nlinarith [le_max_left (1 : ℝ) C]
  · calc
      ((binaryNormSolutions d n).card : ℝ) ≤ C * (n : ℝ) ^ ε := hbound n (by omega)
      _ ≤ max 1 C * (N + 1 : ℝ) ^ ε := by
        apply mul_le_mul (le_max_right _ _) _ (by positivity) (by positivity)
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast (by omega : n ≤ N + 1)) hε.le

end QuarticAdditive


/- Uniform subpolynomial bounds on the quartic additive-relation locus. -/
namespace QuarticAdditive

private def fixedAdditiveQuarticReps (n : ℕ) : Finset (Fin 4 → Fin (n + 1)) :=
  Finset.univ.filter (fun a ↦ (∑ i, (a i : ℕ) ^ 4 = n) ∧
    (a 2 : ℕ) = (a 0 : ℕ) + (a 1 : ℕ))

def fixedAdditiveQuarticCount (n : ℕ) : ℕ := (fixedAdditiveQuarticReps n).card

private def outerNormPair {n : ℕ} (a : Fin 4 → Fin (n + 1)) : ℕ × ℕ :=
  ((a 3 : ℕ) ^ 2, (a 0 : ℕ) ^ 2 + (a 0 : ℕ) * (a 1 : ℕ) + (a 1 : ℕ) ^ 2)

private def innerNormPair {n : ℕ} (a : Fin 4 → Fin (n + 1)) : ℕ × ℕ :=
  (2 * (a 0 : ℕ) + (a 1 : ℕ), (a 1 : ℕ))

private lemma outerNormPair_mem {n : ℕ} {a : Fin 4 → Fin (n + 1)}
    (ha : a ∈ fixedAdditiveQuarticReps n) :
    outerNormPair a ∈ binaryNormSolutions 2 n := by
  simp only [fixedAdditiveQuarticReps, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  apply (mem_binaryNormSolutions (by decide) _).mpr
  dsimp [outerNormPair]
  have hsum := ha.1
  simp only [Fin.sum_univ_four, ha.2] at hsum
  calc
    ((a 3 : ℕ) ^ 2) ^ 2 + 2 * ((a 0 : ℕ) ^ 2 + (a 0 : ℕ) * (a 1 : ℕ) + (a 1 : ℕ) ^ 2) ^ 2 =
        (a 0 : ℕ) ^ 4 + (a 1 : ℕ) ^ 4 + ((a 0 : ℕ) + (a 1 : ℕ)) ^ 4 + (a 3 : ℕ) ^ 4 := by ring
    _ = n := hsum

private lemma outerNormPair_snd_le {n : ℕ} {a : Fin 4 → Fin (n + 1)}
    (ha : a ∈ fixedAdditiveQuarticReps n) : (outerNormPair a).2 ≤ n := by
  have h := (mem_binaryNormSolutions (by decide) _).mp (outerNormPair_mem ha)
  have hp := Nat.le_pow (by decide : 0 < 2) (a := (outerNormPair a).2)
  omega

private lemma innerNormPair_mem {n : ℕ} (a : Fin 4 → Fin (n + 1)) :
    innerNormPair a ∈ binaryNormSolutions 3 (4 * (outerNormPair a).2) := by
  apply (mem_binaryNormSolutions (by decide) _).mpr
  dsimp [innerNormPair, outerNormPair]
  ring

private lemma innerNormPair_fiber_injective {n : ℕ} (q : ℕ × ℕ) :
    Set.InjOn (innerNormPair (n := n))
      ((fixedAdditiveQuarticReps n).filter (fun a ↦ outerNormPair a = q) :
        Set (Fin 4 → Fin (n + 1))) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_filter, fixedAdditiveQuarticReps,
    Finset.mem_univ, true_and] at ha hb
  have h0 := congrArg Prod.fst hab
  have h1 := congrArg Prod.snd hab
  dsimp [innerNormPair] at h0 h1
  have ha0 : (a 0 : ℕ) = (b 0 : ℕ) := by omega
  have ha1 : (a 1 : ℕ) = (b 1 : ℕ) := h1
  have ha2 : (a 2 : ℕ) = (b 2 : ℕ) := by omega
  have h3 := congrArg Prod.fst (ha.2.trans hb.2.symm)
  have ha3 : (a 3 : ℕ) = (b 3 : ℕ) := Nat.pow_left_injective (by decide : 2 ≠ 0) h3
  funext i
  apply Fin.ext
  fin_cases i <;> assumption

/-- This bounds every quartic representation with `a₂ = a₀ + a₁`, allowing the
fourth coordinate and all norm factors to vary with the target. -/
theorem fixed_additive_quartic_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
      (fixedAdditiveQuarticCount n : ℝ) ≤ C * (n : ℝ) ^ ε := by
  classical
  have hδ : 0 < ε / 2 := by linarith
  obtain ⟨A,hA,houter⟩ := binary_norm_subpolynomial (by decide : 2 ≤ 2) (ε / 2) hδ
  obtain ⟨B,hB,hinner⟩ := binary_norm_subpolynomial_up_to (by decide : 2 ≤ 3) (ε / 2) hδ
  refine ⟨A * B * (5 : ℝ) ^ (ε / 2), by positivity, fun n hn ↦ ?_⟩
  let S := fixedAdditiveQuarticReps n
  let I := S.image outerNormPair
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsubset : I ⊆ binaryNormSolutions 2 n := by
    intro q hq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    exact outerNormPair_mem ha
  have hfiber (q : ℕ × ℕ) (hq : q ∈ I) :
      (((S.filter (fun a ↦ outerNormPair a = q)).card : ℕ) : ℝ) ≤
        B * (4 * n + 1 : ℝ) ^ (ε / 2) := by
    have hcard : (S.filter (fun a ↦ outerNormPair a = q)).card ≤
        (binaryNormSolutions 3 (4 * q.2)).card := by
      apply Finset.card_le_card_of_injOn innerNormPair
      · intro a ha
        simp only [Finset.mem_coe, Finset.mem_filter] at ha
        have h := innerNormPair_mem a
        rwa [ha.2] at h
      · exact innerNormPair_fiber_injective q
    have hqle : q.2 ≤ n := by
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
      exact outerNormPair_snd_le ha
    calc
      (((S.filter (fun a ↦ outerNormPair a = q)).card : ℕ) : ℝ) ≤
          (binaryNormSolutions 3 (4 * q.2)).card := by exact_mod_cast hcard
      _ ≤ B * (4 * n + 1 : ℝ) ^ (ε / 2) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          hinner (4 * n) (4 * q.2) (by omega)
  have himage : (I.card : ℝ) ≤ A * (n : ℝ) ^ (ε / 2) := by
    have hc : (I.card : ℝ) ≤ (binaryNormSolutions 2 n).card := by
      exact_mod_cast Finset.card_le_card hsubset
    exact hc.trans (houter n hn)
  have hpow : (4 * n + 1 : ℝ) ^ (ε / 2) ≤
      (5 : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) hnr.le]
    apply Real.rpow_le_rpow (by positivity) _ hδ.le
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hp : (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2) = (n : ℝ) ^ ε := by
    rw [← Real.rpow_add hnr]
    congr 1
    ring
  calc
    (fixedAdditiveQuarticCount n : ℝ) =
        ∑ q ∈ I, (((S.filter (fun a ↦ outerNormPair a = q)).card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image outerNormPair S
    _ ≤ ∑ q ∈ I, B * (4 * n + 1 : ℝ) ^ (ε / 2) := Finset.sum_le_sum hfiber
    _ = (I.card : ℝ) * (B * (4 * n + 1 : ℝ) ^ (ε / 2)) := by simp
    _ ≤ (A * (n : ℝ) ^ (ε / 2)) *
        (B * ((5 : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2))) := by
      exact mul_le_mul himage (mul_le_mul_of_nonneg_left hpow hB.le)
        (by positivity) (by positivity)
    _ = (A * B * (5 : ℝ) ^ (ε / 2)) * (n : ℝ) ^ ε := by
      calc
        _ = (A * B * (5 : ℝ) ^ (ε / 2)) *
          ((n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2)) := by ring
        _ = _ := by rw [hp]


private def permAdditiveQuarticReps (n : ℕ) (σ : Equiv.Perm (Fin 4)) :
    Finset (Fin 4 → Fin (n + 1)) :=
  Finset.univ.filter (fun a ↦ (∑ i, (a i : ℕ) ^ 4 = n) ∧
    (a (σ 2) : ℕ) = (a (σ 0) : ℕ) + (a (σ 1) : ℕ))

private lemma permAdditiveQuarticReps_card (n : ℕ) (σ : Equiv.Perm (Fin 4)) :
    (permAdditiveQuarticReps n σ).card = fixedAdditiveQuarticCount n := by
  classical
  apply Finset.card_nbij (fun a i ↦ a (σ i))
  · intro a ha
    simp only [Finset.mem_coe, permAdditiveQuarticReps, fixedAdditiveQuarticReps,
      Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ⟨(Equiv.sum_comp σ (fun i ↦ (a i : ℕ) ^ 4)).trans ha.1, ha.2⟩
  · intro a ha b hb hab
    funext i
    have h := congrArg (fun f ↦ f (σ.symm i)) hab
    simpa using h
  · intro a ha
    simp only [Finset.mem_coe, fixedAdditiveQuarticReps,
      Finset.mem_filter, Finset.mem_univ, true_and] at ha
    refine ⟨fun i ↦ a (σ.symm i), ?_, ?_⟩
    · simp only [Finset.mem_coe, permAdditiveQuarticReps,
        Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
      exact ⟨(Equiv.sum_comp σ.symm (fun i ↦ (a i : ℕ) ^ 4)).trans ha.1, ha.2⟩
    · funext i
      simp

/-- Some three distinct coordinates obey an additive relation. -/
def HasAdditiveTriple {n : ℕ} (a : Fin 4 → Fin (n + 1)) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4), (a (σ 2) : ℕ) = (a (σ 0) : ℕ) + (a (σ 1) : ℕ)

instance {n : ℕ} (a : Fin 4 → Fin (n + 1)) : Decidable (HasAdditiveTriple a) :=
  inferInstanceAs (Decidable (∃ σ : Equiv.Perm (Fin 4),
    (a (σ 2) : ℕ) = (a (σ 0) : ℕ) + (a (σ 1) : ℕ)))

def additiveQuarticCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun a : Fin 4 → Fin (n + 1) ↦
    (∑ i, (a i : ℕ) ^ 4 = n) ∧ HasAdditiveTriple a)).card

def nonadditiveQuarticCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun a : Fin 4 → Fin (n + 1) ↦
    (∑ i, (a i : ℕ) ^ 4 = n) ∧ ¬ HasAdditiveTriple a)).card

lemma quartic_count_split (n : ℕ) :
    additiveQuarticCount n + nonadditiveQuarticCount n = Erdos322.representationCount 4 n := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter
    (fun a : Fin 4 → Fin (n + 1) ↦ ∑ i, (a i : ℕ) ^ 4 = n)) HasAdditiveTriple
  simpa only [Finset.filter_filter, additiveQuarticCount, nonadditiveQuarticCount,
    Erdos322.representationCount] using h

lemma additiveQuarticCount_le (n : ℕ) :
    additiveQuarticCount n ≤ 24 * fixedAdditiveQuarticCount n := by
  classical
  have heq : Finset.univ.filter (fun a : Fin 4 → Fin (n + 1) ↦
      (∑ i, (a i : ℕ) ^ 4 = n) ∧ HasAdditiveTriple a) =
      Finset.univ.biUnion (permAdditiveQuarticReps n) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      permAdditiveQuarticReps, HasAdditiveTriple]
    tauto
  change (Finset.univ.filter _).card ≤ _
  rw [heq]
  have h := Finset.card_biUnion_le (s := (Finset.univ : Finset (Equiv.Perm (Fin 4))))
    (t := permAdditiveQuarticReps n)
  simp only [permAdditiveQuarticReps_card, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, smul_eq_mul] at h
  norm_num at h
  exact h

/-- All additive-triple quartic representations, not just the previously
constructed ones, satisfy a uniform subpolynomial bound. -/
theorem additive_quartic_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
      (additiveQuarticCount n : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C,hC,hbound⟩ := fixed_additive_quartic_subpolynomial ε hε
  refine ⟨24 * C, by positivity, fun n hn ↦ ?_⟩
  calc
    (additiveQuarticCount n : ℝ) ≤ 24 * (fixedAdditiveQuarticCount n : ℝ) := by
      exact_mod_cast additiveQuarticCount_le n
    _ ≤ 24 * (C * (n : ℝ) ^ ε) := mul_le_mul_of_nonneg_left (hbound n hn) (by norm_num)
    _ = (24 * C) * (n : ℝ) ^ ε := by ring

/-- Deleting the entire additive-triple locus does not change whether the
quartic count has positive-power peaks. -/
theorem quartic_peaks_iff_nonadditive_peaks :
    (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < Erdos322.representationCount 4 n}.Infinite) ↔
    (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < nonadditiveQuarticCount n}.Infinite) := by
  constructor
  · rintro ⟨c,hc,hinf⟩
    have hhalf : 0 < c / 2 := by linarith
    obtain ⟨C,hC,hadd⟩ := additive_quartic_subpolynomial (c / 2) hhalf
    have ht : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (c / 2)) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop hhalf).comp tendsto_natCast_atTop_atTop
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop (C + 1))
    refine ⟨c / 2, hhalf, ?_⟩
    apply (hinf.diff (Set.finite_Iio (max N 1))).mono
    intro n hn
    have hlarge : max N 1 ≤ n := by
      have hnot := hn.2
      simpa only [Set.mem_Iio, not_lt] using hnot
    have hnpos : 0 < n := by omega
    have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hsmall := hadd n hnpos
    have hdom := hN n (by omega)
    have hsplit : (additiveQuarticCount n : ℝ) + nonadditiveQuarticCount n =
        Erdos322.representationCount 4 n := by exact_mod_cast quartic_count_split n
    have hp : ((n : ℝ) ^ (c / 2)) ^ 2 = (n : ℝ) ^ c := by
      rw [pow_two, ← Real.rpow_add hnr]
      congr 1
      ring
    have hmain := hn.1
    change (n : ℝ) ^ c < (Erdos322.representationCount 4 n : ℝ) at hmain
    change (n : ℝ) ^ (c / 2) < (nonadditiveQuarticCount n : ℝ)
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) ^ (c / 2) by positivity)
      (show 0 ≤ (n : ℝ) ^ (c / 2) - (C + 1) by linarith)]
  · rintro ⟨c,hc,hinf⟩
    refine ⟨c,hc,hinf.mono ?_⟩
    intro n hn
    have hle : (nonadditiveQuarticCount n : ℝ) ≤ Erdos322.representationCount 4 n := by
      exact_mod_cast (show nonadditiveQuarticCount n ≤ Erdos322.representationCount 4 n from
        by have := quartic_count_split n; omega)
    exact lt_of_lt_of_le hn hle

end QuarticAdditive


/- Nonadditive quartic representations are also unbounded. -/
namespace QuarticAdditive

/-- A common denominator for a finite collection of points on the rational curve. -/
def quarticCurveDenominator (m : ℕ) : ℕ :=
  ∏ i : Fin (m + 1), (((i : ℕ) + 3) ^ 4 + 1)

private lemma curveDenominator_pos (m : ℕ) : 0 < quarticCurveDenominator m := by
  unfold quarticCurveDenominator
  apply Finset.prod_pos
  intro i _
  positivity

private lemma curveFactor_dvd (m : ℕ) (i : Fin (m + 1)) :
    ((i : ℕ) + 3) ^ 4 + 1 ∣ quarticCurveDenominator m := by
  unfold quarticCurveDenominator
  exact Finset.dvd_prod_of_mem (fun j : Fin (m + 1) ↦ ((j : ℕ) + 3) ^ 4 + 1)
    (Finset.mem_univ i)

private def curveScale (m : ℕ) (i : Fin (m + 1)) : ℕ :=
  quarticCurveDenominator m / (((i : ℕ) + 3) ^ 4 + 1)

private lemma curveScale_pos (m : ℕ) (i : Fin (m + 1)) : 0 < curveScale m i := by
  exact Nat.div_pos (Nat.le_of_dvd (curveDenominator_pos m) (curveFactor_dvd m i))
    (by positivity)

private lemma curveScale_mul (m : ℕ) (i : Fin (m + 1)) :
    (((i : ℕ) + 3) ^ 4 + 1) * curveScale m i = quarticCurveDenominator m :=
  Nat.mul_div_cancel' (curveFactor_dvd m i)

private def curveTuple (m : ℕ) (i : Fin (m + 1)) : Fin 4 → ℕ :=
  ![2 * ((i : ℕ) + 3) * curveScale m i,
    2 * ((i : ℕ) + 3) ^ 3 * curveScale m i,
    (((i : ℕ) + 3) ^ 4 - 1) * curveScale m i,
    (((i : ℕ) + 3) ^ 4 - 1) * curveScale m i]

private lemma curveTuple_sum (m : ℕ) (i : Fin (m + 1)) :
    ∑ j, curveTuple m i j ^ 4 = 2 * quarticCurveDenominator m ^ 4 := by
  let x : ℕ := i + 3
  have hx : 3 ≤ x := by dsimp [x]; omega
  have hxp : 1 ≤ x ^ 4 := by have := Nat.le_pow (a := x) (by decide : 0 < 4); omega
  have hid : (2 * x) ^ 4 + (2 * x ^ 3) ^ 4 + 2 * (x ^ 4 - 1) ^ 4 =
      2 * (x ^ 4 + 1) ^ 4 := by
    zify [hxp]
    ring
  calc
    ∑ j, curveTuple m i j ^ 4 =
        ((2 * x) ^ 4 + (2 * x ^ 3) ^ 4 + 2 * (x ^ 4 - 1) ^ 4) * curveScale m i ^ 4 := by
      simp only [Fin.sum_univ_four, curveTuple, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      dsimp [x]
      ring
    _ = 2 * ((x ^ 4 + 1) * curveScale m i) ^ 4 := by rw [hid]; ring
    _ = 2 * quarticCurveDenominator m ^ 4 := by rw [curveScale_mul]

private lemma curveTuple_gap (m : ℕ) (i : Fin (m + 1)) :
    curveTuple m i 0 + curveTuple m i 1 < curveTuple m i 2 := by
  let x : ℕ := i + 3
  have hx : 3 ≤ x := by dsimp [x]; omega
  have hx2 : 9 ≤ x ^ 2 := by simpa using Nat.pow_le_pow_left hx 2
  have hx3 : 9 * x ≤ x ^ 3 := by nlinarith
  have hx4 : 3 * x ^ 3 ≤ x ^ 4 := by
    calc
      3 * x ^ 3 ≤ x * x ^ 3 := Nat.mul_le_mul_right _ hx
      _ = x ^ 4 := by ring
  have hbase : 2 * x + 2 * x ^ 3 < x ^ 4 - 1 := by omega
  change 2 * x * curveScale m i + 2 * x ^ 3 * curveScale m i <
    (x ^ 4 - 1) * curveScale m i
  rw [← add_mul]
  exact Nat.mul_lt_mul_of_pos_right hbase (curveScale_pos m i)

private lemma no_additive_triple_of_gap {u v w : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hgap : u + v < w) {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ![u,v,w,w] k ≠ ![u,v,w,w] i + ![u,v,w,w] j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> omega

private lemma curveTuple_nonadditive (m : ℕ) (i : Fin (m + 1)) (σ : Equiv.Perm (Fin 4)) :
    curveTuple m i (σ 2) ≠ curveTuple m i (σ 0) + curveTuple m i (σ 1) := by
  apply no_additive_triple_of_gap (u := curveTuple m i 0) (v := curveTuple m i 1)
    (w := curveTuple m i 2)
  · change 0 < 2 * ((i : ℕ) + 3) * curveScale m i
    have := curveScale_pos m i
    positivity
  · change 0 < 2 * ((i : ℕ) + 3) ^ 3 * curveScale m i
    have := curveScale_pos m i
    positivity
  · exact curveTuple_gap m i
  · exact σ.injective.ne (by decide)
  · exact σ.injective.ne (by decide)
  · exact σ.injective.ne (by decide)

private def boundedCurveTuple (m : ℕ) (i : Fin (m + 1)) :
    Fin 4 → Fin (2 * quarticCurveDenominator m ^ 4 + 1) := fun j ↦
  ⟨curveTuple m i j, by
    have hs := curveTuple_sum m i
    have hb : curveTuple m i j ^ 4 ≤ ∑ l, curveTuple m i l ^ 4 :=
      Finset.single_le_sum (f := fun l ↦ curveTuple m i l ^ 4)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    have hp := Nat.le_pow (a := curveTuple m i j) (by decide : 0 < 4)
    omega⟩

private lemma boundedCurveTuple_injective (m : ℕ) : Function.Injective (boundedCurveTuple m) := by
  intro i j heq
  have h0 := congrArg (fun a ↦ ((a 0 : Fin (2 * quarticCurveDenominator m ^ 4 + 1)) : ℕ)) heq
  have h1 := congrArg (fun a ↦ ((a 1 : Fin (2 * quarticCurveDenominator m ^ 4 + 1)) : ℕ)) heq
  change curveTuple m i 0 = curveTuple m j 0 at h0
  change curveTuple m i 1 = curveTuple m j 1 at h1
  have hi : curveTuple m i 1 = curveTuple m i 0 * ((i : ℕ) + 3) ^ 2 := by
    dsimp [curveTuple]
    ring
  have hj : curveTuple m j 1 = curveTuple m j 0 * ((j : ℕ) + 3) ^ 2 := by
    dsimp [curveTuple]
    ring
  have hpos : 0 < curveTuple m i 0 := by
    change 0 < 2 * ((i : ℕ) + 3) * curveScale m i
    have := curveScale_pos m i
    positivity
  have hp : ((i : ℕ) + 3) ^ 2 = ((j : ℕ) + 3) ^ 2 := by
    apply Nat.mul_left_cancel hpos
    rw [← hi, h0, ← hj, h1]
  have hval := Nat.pow_left_injective (by decide : 2 ≠ 0) hp
  apply Fin.ext
  omega

/-- The complement of the additive-triple locus has arbitrarily large counts. -/
theorem nonadditive_quartic_count_lower (m : ℕ) :
    m + 1 ≤ nonadditiveQuarticCount (2 * quarticCurveDenominator m ^ 4) := by
  classical
  unfold nonadditiveQuarticCount
  have h := Finset.card_le_card_of_injOn (boundedCurveTuple m)
    (s := Finset.univ)
    (t := Finset.univ.filter (fun a : Fin 4 → Fin (2 * quarticCurveDenominator m ^ 4 + 1) ↦
      (∑ i, (a i : ℕ) ^ 4 = 2 * quarticCurveDenominator m ^ 4) ∧ ¬ HasAdditiveTriple a))
    (by
      intro i _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨curveTuple_sum m i, ?_⟩
      rintro ⟨σ,hσ⟩
      exact curveTuple_nonadditive m i σ hσ)
    (boundedCurveTuple_injective m).injOn
  simpa using h

private lemma curveTarget_large (m : ℕ) : m < 2 * quarticCurveDenominator m ^ 4 := by
  have hd := curveFactor_dvd m (⟨m, by omega⟩ : Fin (m + 1))
  have hle := Nat.le_of_dvd (curveDenominator_pos m) hd
  change (m + 3) ^ 4 + 1 ≤ quarticCurveDenominator m at hle
  have h1 := Nat.le_pow (a := m + 3) (by decide : 0 < 4)
  have h2 := Nat.le_pow (a := quarticCurveDenominator m) (by decide : 0 < 4)
  omega

/-- Even after all additive triples are removed, no fixed uniform count bound
is possible. This remains much weaker than a positive-power lower bound. -/
theorem nonadditive_quartic_counts_exceed_any_bound (M : ℕ) :
    {n : ℕ | M < nonadditiveQuarticCount n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  refine ⟨2 * quarticCurveDenominator (max M N) ^ 4, ?_, ?_⟩
  · change M < nonadditiveQuarticCount (2 * quarticCurveDenominator (max M N) ^ 4)
    have h := nonadditive_quartic_count_lower (max M N)
    omega
  · have h := curveTarget_large (max M N)
    omega

end QuarticAdditive


namespace QuarticAdditive


private lemma cross_product_lt_of_first_pos {d n x y u v : ℕ} (hd : 0 < d) (hn : 0 < n)
    (hu : 0 < u) (h : x ^ 2 + d * y ^ 2 = n) (h' : u ^ 2 + d * v ^ 2 = n) :
    x * v < n := by
  by_cases hx : x = 0
  · simpa [hx] using hn
  have hxp : 0 < x ^ 2 := pow_pos (by omega) 2
  have hv : v ^ 2 < n := by
    have hh : v ^ 2 ≤ d * v ^ 2 := Nat.le_mul_of_pos_left _ hd
    have hh' : 0 < u ^ 2 := pow_pos hu 2
    omega
  have hm : (x * v) ^ 2 < n ^ 2 := by
    calc
      (x * v) ^ 2 = x ^ 2 * v ^ 2 := by ring
      _ < x ^ 2 * n := Nat.mul_lt_mul_of_pos_left hv hxp
      _ ≤ n * n := Nat.mul_le_mul_right n (by omega)
      _ = n ^ 2 := by ring
  by_contra hnot
  have hh := Nat.pow_le_pow_left (Nat.le_of_not_lt hnot) 2
  omega

private lemma normRoot_tag_injective {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    Set.InjOn (fun p : ℕ × ℕ ↦ (normRoot n p, decide (p.1 = 0)))
      (primitiveBinaryNormSolutions d n : Set (ℕ × ℕ)) := by
  intro p hp q hq heq
  obtain ⟨⟨hpbd, hp⟩, hpc⟩ := by
    simpa only [primitiveBinaryNormSolutions, binaryNormSolutions,
      Finset.mem_coe, Finset.mem_filter] using hp
  obtain ⟨⟨hqbd, hq⟩, hqc⟩ := by
    simpa only [primitiveBinaryNormSolutions, binaryNormSolutions,
      Finset.mem_coe, Finset.mem_filter] using hq
  have hroot : normRoot n p = normRoot n q := congrArg Prod.fst heq
  have htag : decide (p.1 = 0) = decide (q.1 = 0) := congrArg Prod.snd heq
  have hz := decide_eq_decide.mp htag
  have hx : p.1 = q.1 := by
    by_cases hp0 : p.1 = 0
    · exact hp0.trans (hz.mp hp0).symm
    have hq0 : q.1 ≠ 0 := fun h ↦ hp0 (hz.mpr h)
    have hr := (normRoot_mul hn hp hpc).mul_right q.2
    have hs := (normRoot_mul hn hq hqc).mul_right p.2
    have he : p.1 * q.2 ≡ q.1 * p.2 [MOD n] := by
      apply hr.symm.trans
      convert hs using 1
      rw [hroot]
      ring
    have hc : p.1 * q.2 = q.1 * p.2 := he.eq_of_lt_of_lt
      (cross_product_lt_of_first_pos hd hn (by omega) hp hq)
      (cross_product_lt_of_first_pos hd hn (by omega) hq hp)
    have hsq : p.1 ^ 2 = q.1 ^ 2 := by
      apply Nat.mul_left_cancel hn
      calc
        n * p.1 ^ 2 = p.1 ^ 2 * q.1 ^ 2 + d * (p.1 * q.2) ^ 2 := by rw [← hq]; ring
        _ = p.1 ^ 2 * q.1 ^ 2 + d * (q.1 * p.2) ^ 2 := by rw [hc]
        _ = n * q.1 ^ 2 := by rw [← hp]; ring
    exact Nat.pow_left_injective (by decide : 2 ≠ 0) hsq
  have hy : p.2 = q.2 := by
    rw [hx] at hp
    have hmul : d * p.2 ^ 2 = d * q.2 ^ 2 := by omega
    exact Nat.pow_left_injective (by decide : 2 ≠ 0) (Nat.mul_left_cancel hd hmul)
  exact Prod.ext hx hy

/-- A slightly weaker bound that also includes the Gaussian norm. -/
theorem primitive_binary_norm_count_general {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    (primitiveBinaryNormSolutions d n).card ≤ n.divisors.card * (4 * d) := by
  classical
  by_cases hempty : (primitiveBinaryNormSolutions d n) = ∅
  · simp [hempty]
  obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hp' := Finset.mem_filter.mp hp
  have hpNorm := (mem_binaryNormSolutions hd p).mp hp'.1
  let a := normRoot n p
  let R := (Finset.range n).filter (fun r ↦ r ^ 2 ≡ a ^ 2 [MOD n])
  have hroots := square_congruence_count (a := a) hn
    (normRoot_derivative_bound hd hn hpNorm hp'.2)
  have hcard : (primitiveBinaryNormSolutions d n).card ≤ (R ×ˢ (Finset.univ : Finset Bool)).card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ ↦ (normRoot n p, decide (p.1 = 0)))
    · intro q hq
      simp only [Finset.mem_coe, primitiveBinaryNormSolutions, Finset.mem_filter] at hq
      have hqNorm := (mem_binaryNormSolutions hd q).mp hq.1
      change (normRoot n q, decide (q.1 = 0)) ∈ R ×ˢ (Finset.univ : Finset Bool)
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
      · letI : NeZero n := ⟨hn.ne'⟩
        exact Finset.mem_range.mpr (ZMod.val_lt _)
      · have hr := normRoot_square hn hqNorm hq.2
        have hs := normRoot_square hn hpNorm hp'.2
        exact Nat.ModEq.add_right_cancel (Nat.ModEq.refl d) (hr.trans hs.symm)
    · exact normRoot_tag_injective hd hn
  have hcard' : (primitiveBinaryNormSolutions d n).card ≤ R.card * 2 := by simpa using hcard
  calc
    (primitiveBinaryNormSolutions d n).card ≤ R.card * 2 := hcard'
    _ ≤ (n.divisors.card * (2 * d)) * 2 := Nat.mul_le_mul_right 2 hroots
    _ = n.divisors.card * (4 * d) := by ring

theorem binary_norm_count_general {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    (binaryNormSolutions d n).card ≤ (4 * d) * n.divisors.card ^ 2 := by
  classical
  let S := binaryNormSolutions d n
  let gs := S.image (fun p ↦ p.1.gcd p.2)
  have hgs : gs ⊆ n.divisors := by
    intro g hg
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hg
    have hpNorm := (mem_binaryNormSolutions (by omega : 0 < d) p).mp hp
    have hmul := norm_quotient_mul p hpNorm
    have hsq : p.1.gcd p.2 ^ 2 ∣ n := ⟨_, hmul.symm⟩
    exact Nat.mem_divisors.mpr ⟨(dvd_pow_self _ (by decide : 2 ≠ 0)).trans hsq, hn.ne'⟩
  have hfiber (g : ℕ) (hg : g ∈ gs) :
      (S.filter (fun p ↦ p.1.gcd p.2 = g)).card ≤ n.divisors.card * (4 * d) := by
    obtain ⟨p,hp,hpg⟩ := Finset.mem_image.mp hg
    have hpNorm := (mem_binaryNormSolutions (by omega : 0 < d) p).mp hp
    have hgpos : 0 < g := hpg ▸ norm_gcd_pos hn p hpNorm
    have hmul := norm_quotient_mul p hpNorm
    rw [hpg] at hmul
    have hsq : g ^ 2 ∣ n := ⟨_, hmul.symm⟩
    have hmpos : 0 < n / g ^ 2 :=
      Nat.div_pos (Nat.le_of_dvd hn hsq) (pow_pos hgpos 2)
    have hdiv : (n / g ^ 2).divisors.card ≤ n.divisors.card :=
      Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' (Nat.div_dvd_of_dvd hsq))
    apply le_trans _ ((primitive_binary_norm_count_general hd hmpos).trans
      (Nat.mul_le_mul_right (4 * d) hdiv))
    apply Finset.card_le_card_of_injOn (fun q : ℕ × ℕ ↦ (q.1 / g, q.2 / g))
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter] at hq
      have hqNorm := (mem_binaryNormSolutions (by omega : 0 < d) q).mp hq.1
      have hh := norm_quotient_primitive (by omega : 0 < d) hn q hqNorm
      rwa [hq.2] at hh
    · intro q hq r hr heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hq hr
      have h1 : q.1 / g = r.1 / g := congrArg Prod.fst heq
      have h2 : q.2 / g = r.2 / g := congrArg Prod.snd heq
      have hq1 : g * (q.1 / g) = q.1 := by
        rw [← hq.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hq2 : g * (q.2 / g) = q.2 := by
        rw [← hq.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have hr1 : g * (r.1 / g) = r.1 := by
        rw [← hr.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hr2 : g * (r.2 / g) = r.2 := by
        rw [← hr.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      apply Prod.ext
      · rw [← hq1, ← hr1, h1]
      · rw [← hq2, ← hr2, h2]
  calc
    S.card = ∑ g ∈ gs, (S.filter (fun p ↦ p.1.gcd p.2 = g)).card :=
      Finset.card_eq_sum_card_image _ _
    _ ≤ ∑ g ∈ gs, n.divisors.card * (4 * d) := Finset.sum_le_sum hfiber
    _ = gs.card * (n.divisors.card * (4 * d)) := by simp
    _ ≤ n.divisors.card * (n.divisors.card * (4 * d)) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hgs)
    _ = (4 * d) * n.divisors.card ^ 2 := by ring

theorem binary_norm_subpolynomial_general {d : ℕ} (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
      ((binaryNormSolutions d n).card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C,hC,hdiv⟩ := Erdos322.divisor_count_subpolynomial (ε / 2) (by linarith)
  refine ⟨(4 * d : ℝ) * C ^ 2, by positivity, ?_⟩
  intro n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : ((n : ℝ) ^ (ε / 2)) ^ 2 = (n : ℝ) ^ ε := by
    rw [pow_two, ← Real.rpow_add hnr]
    congr 1
    ring
  calc
    ((binaryNormSolutions d n).card : ℝ) ≤ (4 * d : ℝ) * (n.divisors.card : ℝ) ^ 2 := by
      exact_mod_cast binary_norm_count_general hd hn
    _ ≤ (4 * d : ℝ) * (C * (n : ℝ) ^ (ε / 2)) ^ 2 := by gcongr; exact hdiv n hn
    _ = ((4 * d : ℝ) * C ^ 2) * (n : ℝ) ^ ε := by rw [mul_pow, hp]; ring

/-- A convenient uniform variant including target zero and all smaller targets. -/
theorem binary_norm_subpolynomial_general_up_to {d : ℕ} (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ N n : ℕ, n ≤ N →
      ((binaryNormSolutions d n).card : ℝ) ≤ C * (N + 1 : ℝ) ^ ε := by
  obtain ⟨C,hC,hbound⟩ := binary_norm_subpolynomial_general hd ε hε
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun N n hn ↦ ?_⟩
  by_cases hz : n = 0
  · subst n
    rw [binary_norm_zero (by omega : 0 < d), Finset.card_singleton, Nat.cast_one]
    have hpow : 1 ≤ (N + 1 : ℝ) ^ ε := Real.one_le_rpow (by have := Nat.cast_nonneg (α := ℝ) N; linarith) hε.le
    nlinarith [le_max_left (1 : ℝ) C]
  · calc
      ((binaryNormSolutions d n).card : ℝ) ≤ C * (n : ℝ) ^ ε := hbound n (by omega)
      _ ≤ max 1 C * (N + 1 : ℝ) ^ ε := by
        apply mul_le_mul (le_max_right _ _) _ (by positivity) (by positivity)
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast (by omega : n ≤ N + 1)) hε.le

end QuarticAdditive


/- A uniform upper bound for the full quartic representation count. -/
namespace QuarticUpper

open QuarticAdditive

private lemma le_fourth_root {x n : ℕ} (h : x ^ 4 ≤ n) : x ≤ n.sqrt.sqrt := by
  apply Nat.le_sqrt.mpr
  apply Nat.le_sqrt.mpr
  convert h using 1; ring

private lemma fourth_root_box_bound {n : ℕ} (hn : 0 < n) :
    ((n.sqrt.sqrt + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ (1 / 2 : ℝ) := by
  let r := n.sqrt.sqrt
  have hr : 0 < r := Nat.sqrt_pos.mpr (Nat.sqrt_pos.mpr hn)
  have hr4 : r ^ 4 ≤ n := by
    have h1 := Nat.sqrt_le n.sqrt
    have h2 := Nat.sqrt_le n
    calc
      r ^ 4 = (r * r) ^ 2 := by ring
      _ ≤ n.sqrt ^ 2 := Nat.pow_le_pow_left h1 2
      _ ≤ n := by simpa [pow_two] using h2
  have hnr : (0 : ℝ) ≤ n := by positivity
  have hr4r : (r : ℝ) ^ 4 ≤ n := by exact_mod_cast hr4
  have hr2r : (r : ℝ) ^ 2 ≤ Real.sqrt n := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hnr]
    convert hr4r using 1; ring
  have hbox : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * (r : ℝ) ^ 2 := by
    have hle : r + 1 ≤ 2 * r := by omega
    have hpow := Nat.pow_le_pow_left hle 2
    have hcast : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((2 * r : ℕ) : ℝ) ^ 2 := by exact_mod_cast hpow
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hcast
  calc
    ((r + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * (r : ℝ) ^ 2 := hbox
    _ ≤ 4 * Real.sqrt n := by gcongr
    _ = 4 * (n : ℝ) ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]

private def quarticReps (n : ℕ) : Finset (Fin 4 → Fin (n + 1)) :=
  Finset.univ.filter (fun a ↦ ∑ i, (a i : ℕ) ^ 4 = n)

private def firstPair {n : ℕ} (a : Fin 4 → Fin (n + 1)) : ℕ × ℕ :=
  ((a 0 : ℕ), (a 1 : ℕ))

private def lastSquaredPair {n : ℕ} (a : Fin 4 → Fin (n + 1)) : ℕ × ℕ :=
  ((a 2 : ℕ) ^ 2, (a 3 : ℕ) ^ 2)

private lemma firstPair_image_bound {n : ℕ} (hn : 0 < n) :
    (((quarticReps n).image firstPair).card : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 2 : ℝ) := by
  classical
  have hsubset : (quarticReps n).image firstPair ⊆
      Finset.range (n.sqrt.sqrt + 1) ×ˢ Finset.range (n.sqrt.sqrt + 1) := by
    intro q hq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    simp only [quarticReps, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have h0 : (a 0 : ℕ) ^ 4 ≤ n := by
      exact (Finset.single_le_sum (f := fun i : Fin 4 ↦ (a i : ℕ) ^ 4)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ _)).trans_eq ha
    have h1 : (a 1 : ℕ) ^ 4 ≤ n := by
      exact (Finset.single_le_sum (f := fun i : Fin 4 ↦ (a i : ℕ) ^ 4)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ _)).trans_eq ha
    simp only [Finset.mem_product, Finset.mem_range, firstPair]
    exact ⟨by have := le_fourth_root h0; omega, by have := le_fourth_root h1; omega⟩
  have hcard : ((quarticReps n).image firstPair).card ≤ (n.sqrt.sqrt + 1) ^ 2 := by
    simpa [pow_two] using Finset.card_le_card hsubset
  exact (by exact_mod_cast hcard : (((quarticReps n).image firstPair).card : ℝ) ≤
    ((n.sqrt.sqrt + 1 : ℕ) : ℝ) ^ 2).trans (fourth_root_box_bound hn)

private lemma quartic_fiber_bound (n : ℕ) (q : ℕ × ℕ) :
    ((quarticReps n).filter (fun a ↦ firstPair a = q)).card ≤
      (binaryNormSolutions 1 (n - q.1 ^ 4 - q.2 ^ 4)).card := by
  classical
  apply Finset.card_le_card_of_injOn lastSquaredPair
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, quarticReps,
      Finset.mem_univ, true_and] at ha
    have h0 : (a 0 : ℕ) = q.1 := congrArg Prod.fst ha.2
    have h1 : (a 1 : ℕ) = q.2 := congrArg Prod.snd ha.2
    have hsum := ha.1
    simp only [Fin.sum_univ_four, h0, h1] at hsum
    apply (mem_binaryNormSolutions (by decide) _).mpr
    change ((a 2 : ℕ) ^ 2) ^ 2 + 1 * ((a 3 : ℕ) ^ 2) ^ 2 = _
    norm_num only [one_mul, ← pow_mul]
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
    have h0 := congrArg Prod.fst (ha.2.trans hb.2.symm)
    have h1 := congrArg Prod.snd (ha.2.trans hb.2.symm)
    have h2 := congrArg Prod.fst hab
    have h3 := congrArg Prod.snd hab
    have ha0 : (a 0 : ℕ) = (b 0 : ℕ) := h0
    have ha1 : (a 1 : ℕ) = (b 1 : ℕ) := h1
    have ha2 : (a 2 : ℕ) = (b 2 : ℕ) := Nat.pow_left_injective (by decide : 2 ≠ 0) h2
    have ha3 : (a 3 : ℕ) = (b 3 : ℕ) := Nat.pow_left_injective (by decide : 2 ≠ 0) h3
    funext i
    apply Fin.ext
    fin_cases i <;> assumption

/-- An elementary uniform bound for all quartic representations. The exponent
`1/2 + ε` is not small enough to settle the conjecture. -/
theorem quartic_count_upper_half (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
      (Erdos322.representationCount 4 n : ℝ) ≤ C * (n : ℝ) ^ (1 / 2 + ε : ℝ) := by
  classical
  obtain ⟨C,hC,hbound⟩ := binary_norm_subpolynomial_general_up_to (by decide : 0 < 1) ε hε
  refine ⟨4 * C * (2 : ℝ) ^ ε, by positivity, fun n hn ↦ ?_⟩
  let S := quarticReps n
  let I := S.image firstPair
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (n + 1 : ℝ) ^ ε ≤ (2 : ℝ) ^ ε * (n : ℝ) ^ ε := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hnr.le]
    have hone : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact Real.rpow_le_rpow (by positivity) (by linarith) hε.le
  have hfiber (q : ℕ × ℕ) (hq : q ∈ I) :
      (((S.filter (fun a ↦ firstPair a = q)).card : ℕ) : ℝ) ≤ C * (n + 1 : ℝ) ^ ε := by
    have hcard : (((S.filter (fun a ↦ firstPair a = q)).card : ℕ) : ℝ) ≤
        (binaryNormSolutions 1 (n - q.1 ^ 4 - q.2 ^ 4)).card := by
      exact_mod_cast quartic_fiber_bound n q
    exact hcard.trans (hbound n (n - q.1 ^ 4 - q.2 ^ 4) (by omega))
  calc
    (Erdos322.representationCount 4 n : ℝ) =
        ∑ q ∈ I, (((S.filter (fun a ↦ firstPair a = q)).card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image firstPair S
    _ ≤ ∑ q ∈ I, C * (n + 1 : ℝ) ^ ε := Finset.sum_le_sum hfiber
    _ = (I.card : ℝ) * (C * (n + 1 : ℝ) ^ ε) := by simp
    _ ≤ (4 * (n : ℝ) ^ (1 / 2 : ℝ)) * (C * ((2 : ℝ) ^ ε * (n : ℝ) ^ ε)) := by
      exact mul_le_mul (firstPair_image_bound hn) (mul_le_mul_of_nonneg_left hpow hC.le)
        (by positivity) (by positivity)
    _ = (4 * C * (2 : ℝ) ^ ε) * (n : ℝ) ^ (1 / 2 + ε : ℝ) := by
      rw [Real.rpow_add hnr]
      ring


/-- Exponents larger than `1/2` cannot witness the quartic conjecture. -/
theorem quartic_large_exponents_finite {c : ℝ} (hc : 1 / 2 < c) :
    {n : ℕ | (n : ℝ) ^ c < Erdos322.representationCount 4 n}.Finite := by
  let δ : ℝ := (c - 1 / 2) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨C,hC,hbound⟩ := quartic_count_upper_half δ hδ
  have ht : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ δ) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop C)
  apply (Set.finite_Iio (max N 1)).subset
  intro n hn
  by_contra hnot
  have hlarge : max N 1 ≤ n := by simpa only [Set.mem_Iio, not_lt] using hnot
  have hnpos : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hdom := hN n (by omega)
  have hp : (n : ℝ) ^ δ * (n : ℝ) ^ (1 / 2 + δ) = (n : ℝ) ^ c := by
    rw [← Real.rpow_add hnr]
    congr 1
    dsimp [δ]
    ring
  have hle : (Erdos322.representationCount 4 n : ℝ) ≤ (n : ℝ) ^ c := by
    calc
      (Erdos322.representationCount 4 n : ℝ) ≤ C * (n : ℝ) ^ (1 / 2 + δ) := hbound n hnpos
      _ ≤ (n : ℝ) ^ δ * (n : ℝ) ^ (1 / 2 + δ) :=
        mul_le_mul_of_nonneg_right hdom (by positivity)
      _ = (n : ℝ) ^ c := hp
  exact not_lt_of_ge hle hn

theorem quartic_peak_exponent_le_half {c : ℝ}
    (h : {n : ℕ | (n : ℝ) ^ c < Erdos322.representationCount 4 n}.Infinite) : c ≤ 1 / 2 := by
  by_contra hnot
  exact h (quartic_large_exponents_finite (lt_of_not_ge hnot))

end QuarticUpper

/- Full-count moment criteria and the bounds currently available. The criterion
below is an equivalence, not a proof of its right-hand side. -/

namespace MomentReduction

noncomputable section

/-- Positive-index integer moments of a counting sequence. -/
def countMoment (r : ℕ → ℕ) (q N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (r n : ℝ)^q

/-- Uniform domination by every positive power. -/
def Subpolynomial (r : ℕ → ℕ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
    (r n : ℝ) ≤ C * (n : ℝ)^ε

/-- Every fixed positive integer moment has at most quadratic summatory growth.
The constant may depend on the moment order. -/
def QuadraticMoments (r : ℕ → ℕ) : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
    countMoment r q N ≤ C * (N : ℝ)^2

theorem subpolynomial_iff_quadratic_moments (r : ℕ → ℕ) :
    Subpolynomial r ↔ QuadraticMoments r := by
  constructor
  · intro h q hq
    have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    obtain ⟨A, hA, hbound⟩ := h (1/(q : ℝ)) (by positivity)
    refine ⟨A^q, pow_pos hA _, ?_⟩
    intro N hN
    have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 N) : (r n : ℝ)^q ≤ A^q * N := by
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
      have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r n) (hbound n hn1) q
      rw [mul_pow] at hp
      have hroot : ((n : ℝ)^(1/(q : ℝ)))^q = n := by
        simpa only [one_div] using Real.rpow_inv_natCast_pow
          (by positivity : (0 : ℝ) ≤ n) (by omega : q ≠ 0)
      rw [hroot] at hp
      exact hp.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) (by positivity))
    calc
      countMoment r q N ≤ ∑ _n ∈ Finset.Icc 1 N, A^q * (N : ℝ) :=
        Finset.sum_le_sum hterm
      _ = A^q * (N : ℝ)^2 := by simp [Nat.card_Icc]; ring
  · intro h ε hε
    obtain ⟨q, hq⟩ := exists_nat_gt (2/ε)
    have hqr : (0 : ℝ) < q := (div_pos (by norm_num) hε).trans hq
    have hqnat : 1 ≤ q := by
      have hqpos : 0 < q := by exact_mod_cast hqr
      omega
    have hexp : (2 : ℝ) ≤ ε * q := by
      have ht := (div_lt_iff₀ hε).mp hq
      nlinarith
    obtain ⟨A, hA, hbound⟩ := h q hqnat
    let C := max 1 A
    have hC1 : 1 ≤ C := le_max_left _ _
    have hCA : A ≤ C := le_max_right _ _
    have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC1
    refine ⟨C, hC, ?_⟩
    intro n hn
    have hsingle : (r n : ℝ)^q ≤ countMoment r q n :=
      Finset.single_le_sum (f := fun j : ℕ => (r j : ℝ)^q)
        (fun _ _ => by positivity) (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
    have hCq : A ≤ C^q := hCA.trans (le_self_pow₀ hC1 (by omega))
    have hnpow : (n : ℝ)^2 ≤ ((n : ℝ)^ε)^q := by
      rw [← Real.rpow_mul_natCast (by positivity)]
      exact (Real.rpow_natCast (n : ℝ) 2).symm.le.trans
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hexp)
    apply (pow_le_pow_iff_left₀ (by positivity : (0 : ℝ) ≤ r n)
      (by positivity : 0 ≤ C*(n : ℝ)^ε) (by omega : q ≠ 0)).mp
    calc
      (r n : ℝ)^q ≤ A * (n : ℝ)^2 := hsingle.trans (hbound n hn)
      _ ≤ C^q * ((n : ℝ)^ε)^q := mul_le_mul hCq hnpow (by positivity) (by positivity)
      _ = (C * (n : ℝ)^ε)^q := (mul_pow _ _ _).symm

/-- The exact negation of the original conjecture is equivalent to a bound on
all integer moments for one exponent at least four. No such bound is assumed. -/
theorem negation_iff_quadratic_moments :
    (¬ (∀ k : ℕ, 3 ≤ k → ∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ)^c < representationCount k n}.Infinite)) ↔
      ∃ k : ℕ, 4 ≤ k ∧ QuadraticMoments (representationCount k) := by
  rw [negation_iff_uniform_bound]
  apply exists_congr
  intro k
  exact and_congr_right (fun _ => subpolynomial_iff_quadratic_moments (representationCount k))


theorem single_le_countMoment (r : ℕ → ℕ) (q n : ℕ) (hn : 1 ≤ n) :
    (r n : ℝ)^q ≤ countMoment r q n := by
  exact Finset.single_le_sum (f := fun j : ℕ => (r j : ℝ)^q)
    (fun _ _ => by positivity) (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)

/-- The cubic construction necessarily violates the moment criterion. -/
theorem cubic_twenty_fifth_moment_not_quadratic :
    ¬ (∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      countMoment (representationCount 3) 25 N ≤ C*(N : ℝ)^2) := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 C)
  have hmpos : 0 < m := by
    have : (0 : ℝ) < m := lt_trans (by positivity : (0 : ℝ) < max 1 C) hm
    exact_mod_cast this
  have hC3 : C < 3*(m : ℝ) := by
    have hCm : C < m := (le_max_right _ _).trans_lt hm
    have hmr : (0 : ℝ) < m := by exact_mod_cast hmpos
    linarith
  have hn : 1 ≤ (3*m)^12 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hcount : (3*(m : ℝ)) ≤ representationCount 3 ((3*m)^12) := by
    have hc := cubic_count_lower_strong m hmpos
    exact_mod_cast (show 3*m ≤ representationCount 3 ((3*m)^12) by omega)
  have hlow : (3*(m : ℝ))^25 ≤ countMoment (representationCount 3) 25 ((3*m)^12) :=
    (pow_le_pow_left₀ (by positivity) hcount 25).trans
      (single_le_countMoment _ 25 _ hn)
  have hup := hbound ((3*m)^12) hn
  have hnorm : (((3*m)^12 : ℕ) : ℝ)^2 = (3*(m : ℝ))^24 := by push_cast; ring
  rw [hnorm] at hup
  have hstrict : C*(3*(m : ℝ))^24 < (3*(m : ℝ))^25 := by
    calc
      C*(3*(m : ℝ))^24 < (3*(m : ℝ))*(3*(m : ℝ))^24 :=
        mul_lt_mul_of_pos_right hC3 (by positivity)
      _ = (3*(m : ℝ))^25 := by ring
  exact not_lt_of_ge (hlow.trans hup) hstrict

private abbrev Rep (k n : ℕ) :=
  {a : Fin k → Fin (n+1) // ∑ i, (a i : ℕ)^k = n}

private theorem rep_card (k n : ℕ) :
    Fintype.card (Rep k n) = representationCount k n := by
  simp [Rep, Fintype.card_subtype, representationCount]

private def rootBoxMap (k N : ℕ) (hk : k ≠ 0)
    (v : (n : Fin (N+1)) × Rep k n) : Fin k → Fin (k.nthRoot N+1) :=
  fun i => ⟨v.2.1 i, by
    have hi : (v.2.1 i : ℕ)^k ≤ v.1 :=
      (Finset.single_le_sum (f := fun j : Fin k => (v.2.1 j : ℕ)^k)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans_eq v.2.2
    have hn : (v.1 : ℕ) ≤ N := Nat.le_of_lt_succ v.1.isLt
    exact Nat.lt_succ_of_le ((Nat.le_nthRoot_iff hk).mpr (hi.trans hn))⟩

private theorem rootBoxMap_injective (k N : ℕ) (hk : k ≠ 0) :
    Function.Injective (rootBoxMap k N hk) := by
  rintro ⟨n,a⟩ ⟨m,b⟩ he
  have hvals : ∀ i, (a.1 i : ℕ) = b.1 i := by
    intro i
    exact congrArg Fin.val (congrFun he i)
  have hnm : n = m := by
    apply Fin.ext
    calc
      (n : ℕ) = ∑ i, (a.1 i : ℕ)^k := a.2.symm
      _ = ∑ i, (b.1 i : ℕ)^k := by simp only [hvals]
      _ = m := b.2
  subst m
  congr 1
  apply Subtype.ext
  funext i
  exact Fin.ext (hvals i)

/-- The total number of representations up to `N` fits in the integer root box. -/
theorem summatory_count_le_root_box (k N : ℕ) (hk : 0 < k) :
    ∑ n ∈ Finset.range (N+1), representationCount k n ≤ (k.nthRoot N+1)^k := by
  classical
  have hc := Fintype.card_le_of_injective (rootBoxMap k N hk.ne')
    (rootBoxMap_injective k N hk.ne')
  simpa only [Fintype.card_sigma, rep_card, Fintype.card_fun, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range] using hc

/-- A uniform linear first-moment estimate for the full count, at every exponent. -/
theorem first_moment_linear (k N : ℕ) (hk : 0 < k) (hN : 1 ≤ N) :
    countMoment (representationCount k) 1 N ≤ (2 : ℝ)^k*N := by
  have hroot : 1 ≤ k.nthRoot N := (Nat.le_nthRoot_iff hk.ne').mpr (by simpa using hN)
  have hbox : (k.nthRoot N+1)^k ≤ 2^k*N := by
    calc
      (k.nthRoot N+1)^k ≤ (2*k.nthRoot N)^k := Nat.pow_le_pow_left (by omega) k
      _ = 2^k*(k.nthRoot N)^k := Nat.mul_pow _ _ _
      _ ≤ 2^k*N := Nat.mul_le_mul_left _ (Nat.pow_nthRoot_le (.inl hk.ne'))
  have hsub : ∑ n ∈ Finset.Icc 1 N, representationCount k n ≤
      ∑ n ∈ Finset.range (N+1), representationCount k n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hn).2; omega)
    · intros; exact Nat.zero_le _
  have hb := hsub.trans ((summatory_count_le_root_box k N hk).trans hbox)
  simpa only [countMoment, pow_one, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat] using (show ((∑ n ∈ Finset.Icc 1 N, representationCount k n : ℕ) : ℝ) ≤
      ((2^k*N : ℕ) : ℝ) by exact_mod_cast hb)


/-- Combining the full quartic upper bound with its linear first moment gives
bounds on every fixed moment, but with an exponent growing with the order. -/
theorem quartic_moment_upper (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      countMoment (representationCount 4) (q+1) N ≤
        C*(N : ℝ)^(1+(q : ℝ)/2+ε) := by
  let δ : ℝ := ε/((q : ℝ)+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA, hbound⟩ := QuarticUpper.quartic_count_upper_half δ hδ
  have hδq : δ*(q : ℝ) ≤ ε := by
    have hpos : (0 : ℝ) < (q : ℝ)+1 := by positivity
    have hcancel : δ*((q : ℝ)+1) = ε := div_mul_cancel₀ ε hpos.ne'
    have : 0 ≤ δ := hδ.le
    nlinarith
  refine ⟨16*A^q, by positivity, ?_⟩
  intro N hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNr
  let K : ℝ := (A*(N : ℝ)^(1/2+δ))^q
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have ht (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (representationCount 4 n : ℝ)^(q+1) ≤ K*(representationCount 4 n : ℝ) := by
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hb : (representationCount 4 n : ℝ) ≤ A*(N : ℝ)^(1/2+δ) := by
      exact (hbound n (by omega)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnN) (by positivity)) hA.le)
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hb q) (by positivity)
  have hsum : countMoment (representationCount 4) (q+1) N ≤
      K*countMoment (representationCount 4) 1 N := by
    unfold countMoment
    simp only [pow_one]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum ht
  have hfirst : countMoment (representationCount 4) 1 N ≤ 16*(N : ℝ) := by
    have hf := first_moment_linear 4 N (by decide) hN
    norm_num at hf
    exact hf
  have halg : K*(16*(N : ℝ)) =
      (16*A^q)*(N : ℝ)^((1/2+δ)*(q : ℝ)+1) := by
    dsimp [K]
    rw [mul_pow, ← Real.rpow_mul_natCast hNpos.le, Real.rpow_add_one hNpos.ne']
    ring
  have hexp : (1/2+δ)*(q : ℝ)+1 ≤ 1+(q : ℝ)/2+ε := by nlinarith
  calc
    countMoment (representationCount 4) (q+1) N ≤ K*(16*(N : ℝ)) :=
      hsum.trans (mul_le_mul_of_nonneg_left hfirst hK)
    _ = (16*A^q)*(N : ℝ)^((1/2+δ)*(q : ℝ)+1) := halg
    _ ≤ (16*A^q)*(N : ℝ)^(1+(q : ℝ)/2+ε) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hNr hexp) (by positivity)

/-- The second moment meets the quadratic criterion. The higher moments needed
for the full criterion are not supplied by this theorem. -/
theorem quartic_second_moment_quadratic :
    ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      countMoment (representationCount 4) 2 N ≤ C*(N : ℝ)^2 := by
  obtain ⟨C, hC, hbound⟩ := quartic_moment_upper 1 (1/2) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hb := hbound N hN
  norm_num at hb
  exact hb

/-- At order three the available estimate is only `N^(2+ε)`. -/
theorem quartic_third_moment_near_quadratic (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      countMoment (representationCount 4) 3 N ≤ C*(N : ℝ)^(2+ε) := by
  convert quartic_moment_upper 2 ε hε using 1
  norm_num

end

end MomentReduction

/- Primitive nonadditive quartic counts are unbounded. The construction uses an
integer tripling recurrence on an intersection of two quadrics. This proves no
positive-power lower bound. -/
namespace PrimitiveNonadditive

private def F {R : Type*} [CommRing R] (s t : R) : R :=
  3468*s^8 - 612*s^4*t^4 - 140*s^2*t^6 - 9*t^8
private def G {R : Type*} [CommRing R] (s t : R) : R :=
  10404*s^8 + 4760*s^6*t^2 + 612*s^4*t^4 - 3*t^8
private def H {R : Type*} [CommRing R] (s t : R) : R :=
  3468*s^8 + 2312*s^6*t^2 + 612*s^4*t^4 + 72*s^2*t^6 + 3*t^8
private def J {R : Type*} [CommRing R] (s t : R) : R :=
  3468*s^8 + 2448*s^6*t^2 + 612*s^4*t^4 + 68*s^2*t^6 + 3*t^8
private def K {R : Type*} [CommRing R] (s t : R) : R :=
  F s t ^ 4 + 4*t^4*(102*s^4+35*s^2*t^2+3*t^4)*
    (F s t - G s t)*(F s t ^ 2 + G s t ^ 2)

private theorem first_quadric {R : Type*} [CommRing R] (s t : R) :
    (6*s^2+t^2)*H s t ^ 2 = 6*(s*F s t)^2+(t*G s t)^2 := by
  simp only [F, G, H]
  ring

private theorem second_quadric {R : Type*} [CommRing R] (s t : R) :
    (1207*s^2+213*t^2)*J s t ^ 2 = 1207*(s*F s t)^2+213*(t*G s t)^2 := by
  simp only [F, G, J]
  ring

private theorem defect_step {R : Type*} [CommRing R] (s t : R) :
    34*(s*F s t)^4-(t*G s t)^4 = (34*s^4-t^4)*K s t := by
  simp only [F, G, K]
  ring

private theorem mod_three : ∀ s t : ZMod 3, s ≠ 0 → t ≠ 0 →
    F s t = 1 ∧ G s t = 2 ∧ H s t = 2 ∧ J s t = 2 := by
  decide

private theorem mod_nine : ∀ s t : ZMod 9,
    s^2 ≠ 0 → t^2 ≠ 0 → K s t = 6 := by
  decide

structure QuadPoint where
  s : ℤ
  t : ℤ
  z : ℤ
  w : ℤ

def next (P : QuadPoint) : QuadPoint :=
  ⟨P.s * F P.s P.t, P.t * G P.s P.t, P.z * H P.s P.t, P.w * J P.s P.t⟩

def point : ℕ → QuadPoint
  | 0 => ⟨2, 1, 5, 71⟩
  | n+1 => next (point n)

private theorem next_preserves (P : QuadPoint)
    (h₁ : P.z^2 = 6*P.s^2+P.t^2)
    (h₂ : P.w^2 = 1207*P.s^2+213*P.t^2) :
    (next P).z^2 = 6*(next P).s^2+(next P).t^2 ∧
    (next P).w^2 = 1207*(next P).s^2+213*(next P).t^2 := by
  constructor
  · change (P.z * H P.s P.t)^2 = _
    rw [mul_pow, h₁, first_quadric]
    rfl
  · change (P.w * J P.s P.t)^2 = _
    rw [mul_pow, h₂, second_quadric]
    rfl

theorem point_on_quadrics (n : ℕ) :
    (point n).z^2 = 6*(point n).s^2+(point n).t^2 ∧
    (point n).w^2 = 1207*(point n).s^2+213*(point n).t^2 := by
  induction n with
  | zero => norm_num [point]
  | succ n ih => exact next_preserves _ ih.1 ih.2

private theorem point_units_three (n : ℕ) :
    ((point n).s : ZMod 3) ≠ 0 ∧ ((point n).t : ZMod 3) ≠ 0 ∧
    ((point n).w : ZMod 3) ≠ 0 := by
  induction n with
  | zero => norm_num [point]; decide
  | succ n ih =>
    obtain ⟨hF, hG, hH, hJ⟩ := mod_three _ _ ih.1 ih.2.1
    have hf : ((F (point n).s (point n).t : ℤ) : ZMod 3) = 1 := by
      simpa [F] using hF
    have hg : ((G (point n).s (point n).t : ℤ) : ZMod 3) = 2 := by
      simpa [G] using hG
    have hj : ((J (point n).s (point n).t : ℤ) : ZMod 3) = 2 := by
      simpa [J] using hJ
    simpa only [point, next, Int.cast_mul, hf, hg, hj, mul_one, ne_eq,
      mul_eq_zero, not_or] using
      And.intro ih.1 (And.intro (And.intro ih.2.1 (by decide : (2 : ZMod 3) ≠ 0))
        (And.intro ih.2.2 (by decide : (2 : ZMod 3) ≠ 0)))

private theorem square_mod_nine_ne_zero (a : ℤ) (h : (a : ZMod 3) ≠ 0) :
    (a : ZMod 9)^2 ≠ 0 := by
  intro he
  have hd : (9 : ℤ) ∣ a^2 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using he)
  have hd3 : (3 : ℤ) ∣ a^2 := dvd_trans (by norm_num) hd
  have ha : (3 : ℤ) ∣ a := Int.prime_three.dvd_of_dvd_pow hd3
  exact h ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ha)

private theorem factor_mod_nine (n : ℕ) :
    ((K (point n).s (point n).t : ℤ) : ZMod 9) = 6 := by
  have h := mod_nine ((point n).s : ZMod 9) ((point n).t : ZMod 9)
    (square_mod_nine_ne_zero _ (point_units_three n).1)
    (square_mod_nine_ne_zero _ (point_units_three n).2.1)
  simpa [K, F, G] using h

private theorem factor_valuation (n : ℕ) :
    K (point n).s (point n).t ≠ 0 ∧ padicValInt 3 (K (point n).s (point n).t) = 1 := by
  let k : ℤ := K (point n).s (point n).t
  have hk : (k : ZMod 9) = 6 := factor_mod_nine n
  have hn : k ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at hk
    exact (by decide : (0 : ZMod 9) ≠ 6) hk
  have hd : (9 : ℤ) ∣ k-6 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa using sub_eq_zero.mpr hk
  have hd3 : (3 : ℤ) ∣ k := by
    have : (3 : ℤ) ∣ k-6 := dvd_trans (by norm_num) hd
    omega
  have hn9 : ¬(9 : ℤ) ∣ k := by
    intro h
    have hz : (k : ZMod 9) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    rw [hz] at hk
    exact (by decide : (0 : ZMod 9) ≠ 6) hk
  have hlo : 1 ≤ padicValInt 3 k := by
    have h := (padicValInt_dvd_iff (p := 3) 1 k).mp (by simpa using hd3)
    exact h.resolve_left hn
  have hhi : ¬ 2 ≤ padicValInt 3 k := by
    intro h
    apply hn9
    simpa using (padicValInt_dvd_iff (p := 3) 2 k).mpr (Or.inr h)
  refine ⟨hn, ?_⟩
  change padicValInt 3 k = 1
  omega

def defect (n : ℕ) : ℤ := 34*(point n).s^4-(point n).t^4

theorem defect_valuation (n : ℕ) : defect n ≠ 0 ∧ padicValInt 3 (defect n) = n+1 := by
  induction n with
  | zero =>
    constructor
    · decide
    · change padicValNat 3 (3*181) = 1
      rw [padicValNat.mul (by decide) (by decide), padicValNat.self (by decide),
        padicValNat.eq_zero_of_not_dvd (by decide : ¬3 ∣ 181)]
  | succ n ih =>
    have he : defect (n+1) = defect n * K (point n).s (point n).t := by
      exact defect_step _ _
    obtain ⟨hk, hv⟩ := factor_valuation n
    rw [he]
    exact ⟨mul_ne_zero ih.1 hk, by rw [padicValInt.mul ih.1 hk, ih.2, hv]⟩

private theorem point_t_ne_zero (n : ℕ) : (point n).t ≠ 0 := by
  intro h
  exact (point_units_three n).2.1 (by simp [h])

private theorem point_w_ne_zero (n : ℕ) : (point n).w ≠ 0 := by
  intro h
  exact (point_units_three n).2.2 (by simp [h])

private theorem point_t_valuation (n : ℕ) : padicValInt 3 (point n).t = 0 := by
  apply padicValInt.eq_zero_of_not_dvd
  intro h
  exact (point_units_three n).2.1 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h)

def ratio (n : ℕ) : ℚ := ((point n).s : ℚ)^2 / ((point n).t : ℚ)^2

theorem ratio_valuation (n : ℕ) : padicValRat 3 (34*ratio n ^ 2 - 1) = n+1 := by
  have ht : ((point n).t : ℚ) ≠ 0 := by exact_mod_cast point_t_ne_zero n
  have hd : ((defect n : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (defect_valuation n).1
  have he : 34*ratio n ^ 2 - 1 = (defect n : ℚ) / ((point n).t : ℚ)^4 := by
    simp only [ratio, defect, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    field_simp
  rw [he, padicValRat.div hd (pow_ne_zero 4 ht), padicValRat.pow ht]
  rw [padicValRat.of_int, padicValRat.of_int, (defect_valuation n).2,
    point_t_valuation]
  simp

theorem ratio_injective : Function.Injective ratio := by
  intro m n h
  have hv := congrArg (fun x : ℚ ↦ padicValRat 3 (34*x^2-1)) h
  dsimp only at hv
  rw [ratio_valuation, ratio_valuation] at hv
  exact_mod_cast (by omega : (m : ℤ) = n)

def rationalTriple (n : ℕ) : Fin 3 → ℚ :=
  ![71*((point n).s+(point n).t)/(point n).w,
    71*((point n).s-(point n).t)/(point n).w,
    142*(point n).z/(point n).w]

theorem rationalTriple_sum (n : ℕ) : ∑ i, rationalTriple n i ^ 4 = 10082 := by
  have hw : ((point n).w : ℚ) ≠ 0 := by exact_mod_cast point_w_ne_zero n
  have h₁ : ((point n).z : ℚ)^2 = 6*((point n).s : ℚ)^2+((point n).t : ℚ)^2 := by
    exact_mod_cast (point_on_quadrics n).1
  have h₂ : ((point n).w : ℚ)^2 = 1207*((point n).s : ℚ)^2+213*((point n).t : ℚ)^2 := by
    exact_mod_cast (point_on_quadrics n).2
  simp only [rationalTriple, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  field_simp
  linear_combination (142 : ℚ)^4 * congrArg (fun x : ℚ ↦ x^2) h₁ -
    10082 * congrArg (fun x : ℚ ↦ x^2) h₂

private theorem ratio_recovery (n : ℕ) : ratio n =
    (rationalTriple n 2 ^ 2 - 2*(rationalTriple n 0 ^ 2 + rationalTriple n 1 ^ 2)) /
    (12*(rationalTriple n 0 ^ 2 + rationalTriple n 1 ^ 2)-rationalTriple n 2 ^ 2) := by
  have ht : ((point n).t : ℚ) ≠ 0 := by exact_mod_cast point_t_ne_zero n
  have hw : ((point n).w : ℚ) ≠ 0 := by exact_mod_cast point_w_ne_zero n
  have h₁ : ((point n).z : ℚ)^2 = 6*((point n).s : ℚ)^2+((point n).t : ℚ)^2 := by
    exact_mod_cast (point_on_quadrics n).1
  have hd : 12*(rationalTriple n 0 ^ 2 + rationalTriple n 1 ^ 2)-rationalTriple n 2 ^ 2 =
      100820 * ((point n).t : ℚ)^2 / ((point n).w : ℚ)^2 := by
    simp only [rationalTriple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp
    linear_combination -20164 * h₁
  rw [hd]
  simp only [ratio, rationalTriple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  field_simp
  linear_combination -20164 * h₁

theorem squared_triple_injective : Function.Injective
    (fun n : ℕ ↦ fun i : Fin 3 ↦ rationalTriple n i ^ 2) := by
  intro m n h
  apply ratio_injective
  have hi : ∀ i, rationalTriple m i ^ 2 = rationalTriple n i ^ 2 := fun i ↦ congrFun h i
  rw [ratio_recovery, ratio_recovery, hi 0, hi 1, hi 2]

def integerTriple (n : ℕ) : Fin 3 → ℤ :=
  ![71*((point n).s+(point n).t), 71*((point n).s-(point n).t), 142*(point n).z]

private theorem rationalTriple_eq (n : ℕ) (i : Fin 3) :
    rationalTriple n i = (integerTriple n i : ℚ) / (point n).w := by
  fin_cases i <;> simp [rationalTriple, integerTriple]

theorem integerTriple_sum (n : ℕ) :
    ∑ i, integerTriple n i ^ 4 = 10082 * (point n).w^4 := by
  have h := rationalTriple_sum n
  simp only [rationalTriple_eq, div_pow, ← Finset.sum_div] at h
  have hw : ((point n).w : ℚ) ≠ 0 := by exact_mod_cast point_w_ne_zero n
  have he := (div_eq_iff (pow_ne_zero 4 hw)).mp h
  exact_mod_cast he

private theorem norm_three_obstruction (a b w : ℤ) (hw : (w : ZMod 3) ≠ 0) :
    a^2+a*b+b^2 ≠ 71*w^2 := by
  intro he
  have hc : (a : ZMod 3)^2+(a : ZMod 3)*b+b^2 = 71*(w : ZMod 3)^2 := by
    simpa using congrArg (Int.castRingHom (ZMod 3)) he
  have hw2 : (w : ZMod 3)^2 = 1 := by
    have h : ∀ x : ZMod 3, x ≠ 0 → x^2 = 1 := by decide
    exact h _ hw
  rw [hw2] at hc
  norm_num at hc
  have h : ∀ x y : ZMod 3, x^2+x*y+y^2 ≠ 71 := by decide
  exact h _ _ hc

private theorem not_additive_of_sum (a b c w : ℤ)
    (hs : a^4+b^4+c^4 = 10082*w^4) (hw : (w : ZMod 3) ≠ 0) : c ≠ a+b := by
  intro he
  rw [he] at hs
  have hi : a^4+b^4+(a+b)^4 = 2*(a^2+a*b+b^2)^2 := by ring
  rw [hi] at hs
  have hsq : (a^2+a*b+b^2)^2 = (71*w^2)^2 := by nlinarith [hs]
  have hp : 0 ≤ a^2+a*b+b^2 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a+b)]
  exact norm_three_obstruction a b w hw ((sq_eq_sq₀ hp (by positivity)).mp hsq)

theorem integerTriple_abs_nonadditive (n : ℕ) (σ : Equiv.Perm (Fin 3)) :
    |integerTriple n (σ 2)| ≠ |integerTriple n (σ 0)| + |integerTriple n (σ 1)| := by
  have hs : ∑ i, |integerTriple n (σ i)| ^ 4 = 10082 * (point n).w^4 := by
    simpa only [Even.pow_abs (by decide : Even 4)] using
      (Equiv.sum_comp σ (fun i ↦ integerTriple n i ^ 4)).trans (integerTriple_sum n)
  simp only [Fin.sum_univ_three] at hs
  exact not_additive_of_sum _ _ _ _ hs (point_units_three n).2.2

private def natTriple (n : ℕ) (i : Fin 3) : ℕ := (integerTriple n i).natAbs

private theorem natTriple_sum (n : ℕ) :
    ∑ i, natTriple n i ^ 4 = 10082 * (point n).w.natAbs^4 := by
  have hi := integerTriple_sum n
  have h : ∑ i, (natTriple n i : ℤ)^4 = 10082 * ((point n).w.natAbs : ℤ)^4 := by
    simpa only [natTriple, Int.natCast_natAbs, Even.pow_abs (by decide : Even 4)] using hi
  exact_mod_cast h

private theorem natTriple_nonadditive (n : ℕ) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    natTriple n k ≠ natTriple n i + natTriple n j := by
  have h₀ := integerTriple_abs_nonadditive n (Equiv.refl _)
  have h₁ := integerTriple_abs_nonadditive n (Equiv.swap 1 2)
  have h₂ := integerTriple_abs_nonadditive n (Equiv.swap 0 2)
  simp only [Equiv.refl_apply] at h₀
  simp [Equiv.swap_apply_def, Fin.ext_iff] at h₁ h₂
  have hh₀ : natTriple n 2 ≠ natTriple n 0 + natTriple n 1 := by
    have h : (natTriple n 2 : ℤ) ≠ (natTriple n 0 : ℤ) + natTriple n 1 := by
      simpa only [natTriple, Int.natCast_natAbs] using h₀
    exact_mod_cast h
  have hh₁ : natTriple n 1 ≠ natTriple n 0 + natTriple n 2 := by
    have h : (natTriple n 1 : ℤ) ≠ (natTriple n 0 : ℤ) + natTriple n 2 := by
      simpa only [natTriple, Int.natCast_natAbs] using h₁
    exact_mod_cast h
  have hh₂ : natTriple n 0 ≠ natTriple n 2 + natTriple n 1 := by
    have h : (natTriple n 0 : ℤ) ≠ (natTriple n 2 : ℤ) + natTriple n 1 := by
      simpa only [natTriple, Int.natCast_natAbs] using h₂
    exact_mod_cast h
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> omega

def commonDenominator (m : ℕ) : ℕ := ∏ i : Fin (m+1), (point i).w.natAbs

private theorem commonDenominator_pos (m : ℕ) : 0 < commonDenominator m := by
  apply Finset.prod_pos
  intro i _
  exact Int.natAbs_pos.mpr (point_w_ne_zero i)

private theorem point_denominator_dvd (m : ℕ) (i : Fin (m+1)) :
    (point i).w.natAbs ∣ commonDenominator m :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

private def scale (m : ℕ) (i : Fin (m+1)) : ℕ := commonDenominator m / (point i).w.natAbs

private theorem scale_mul (m : ℕ) (i : Fin (m+1)) :
    (point i).w.natAbs * scale m i = commonDenominator m :=
  Nat.mul_div_cancel' (point_denominator_dvd m i)

private theorem scale_pos (m : ℕ) (i : Fin (m+1)) : 0 < scale m i :=
  Nat.div_pos (Nat.le_of_dvd (commonDenominator_pos m) (point_denominator_dvd m i))
    (Int.natAbs_pos.mpr (point_w_ne_zero i))

private def tuple (m : ℕ) (i : Fin (m+1)) : Fin 4 → ℕ :=
  Fin.snoc (fun j : Fin 3 ↦ 2 * natTriple i j * scale m i) 1

def representedNumber (m : ℕ) : ℕ := 10082 * (2*commonDenominator m)^4+1

private theorem tuple_sum (m : ℕ) (i : Fin (m+1)) :
    ∑ j, tuple m i j ^ 4 = representedNumber m := by
  rw [Fin.sum_univ_castSucc]
  simp only [tuple, Fin.snoc_castSucc, Fin.snoc_last, one_pow]
  simp_rw [mul_pow]
  rw [← Finset.sum_mul, ← Finset.mul_sum, natTriple_sum]
  dsimp [representedNumber]
  have h := scale_mul m i
  calc
    2^4 * (10082 * (point i).w.natAbs^4) * scale m i ^ 4 + 1 =
        10082 * (2*((point i).w.natAbs * scale m i))^4+1 := by ring
    _ = _ := by rw [h]

private theorem tuple_gcd (m : ℕ) (i : Fin (m+1)) :
    Finset.univ.gcd (tuple m i) = 1 := by
  apply Nat.dvd_one.mp
  have h := Finset.gcd_dvd (f := tuple m i) (Finset.mem_univ (Fin.last 3))
  simpa only [tuple, Fin.snoc_last] using h

private theorem tuple_abs_ratio (m : ℕ) (i : Fin (m+1)) (j : Fin 3) :
    ((tuple m i j.castSucc : ℕ) : ℚ) / (2*commonDenominator m) = |rationalTriple i j| := by
  have hd : ((point i).w.natAbs : ℚ) ≠ 0 := by
    exact_mod_cast (Int.natAbs_pos.mpr (point_w_ne_zero i)).ne'
  have hl : (commonDenominator m : ℚ) ≠ 0 := by
    exact_mod_cast (commonDenominator_pos m).ne'
  have hs : ((point i).w.natAbs : ℚ) * (scale m i : ℚ) = commonDenominator m := by
    exact_mod_cast scale_mul m i
  rw [rationalTriple_eq, abs_div]
  simp only [tuple, Fin.snoc_castSucc, natTriple, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_natAbs, Int.cast_abs]
  rw [show |((point i).w : ℚ)| = ((point i).w.natAbs : ℚ) by
    simp only [Nat.cast_natAbs, Int.cast_abs]]
  field_simp
  linear_combination |(integerTriple i j : ℚ)| * hs

private theorem tuple_injective (m : ℕ) : Function.Injective (tuple m) := by
  intro i j he
  apply Fin.ext
  apply squared_triple_injective
  funext k
  have h := congrArg (fun f : Fin 4 → ℕ ↦ ((f k.castSucc : ℕ) : ℚ) /
    (2*commonDenominator m)) he
  change ((tuple m i k.castSucc : ℕ) : ℚ) / (2*commonDenominator m) =
    ((tuple m j k.castSucc : ℕ) : ℚ) / (2*commonDenominator m) at h
  rw [tuple_abs_ratio, tuple_abs_ratio] at h
  have h2 := congrArg (fun x : ℚ ↦ x^2) h
  dsimp only at h2
  simpa only [sq_abs] using h2

private theorem tuple_nonadditive_indices (m : ℕ) (n : Fin (m+1)) (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    tuple m n k ≠ tuple m n i + tuple m n j := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
  all_goals simp only [tuple, Fin.snoc_castSucc, Fin.snoc_last] at *
  · intro he
    apply natTriple_nonadditive n i j k
      (fun h ↦ hij (congrArg Fin.castSucc h)) (fun h ↦ hik (congrArg Fin.castSucc h))
      (fun h ↦ hjk (congrArg Fin.castSucc h))
    apply Nat.mul_left_cancel (n := 2*scale m n) (by have := scale_pos m n; positivity)
    nlinarith [he]
  all_goals try simp only [mul_assoc] at *
  all_goals omega

private def boundedTuple (m : ℕ) (n : Fin (m+1)) : Fin 4 → Fin (representedNumber m+1) :=
  fun i ↦ ⟨tuple m n i, by
    have hs := tuple_sum m n
    have hi : tuple m n i ^ 4 ≤ ∑ j, tuple m n j ^ 4 :=
      Finset.single_le_sum (f := fun j ↦ tuple m n j ^ 4)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hp := Nat.le_pow (a := tuple m n i) (by decide : 0 < 4)
    omega⟩

private theorem boundedTuple_injective (m : ℕ) : Function.Injective (boundedTuple m) := by
  intro i j he
  apply tuple_injective m
  funext k
  exact congrArg (fun f ↦ ((f k : Fin (representedNumber m+1)) : ℕ)) he

private theorem boundedTuple_nonadditive (m : ℕ) (n : Fin (m+1)) :
    ¬ Erdos322.QuarticAdditive.HasAdditiveTriple (boundedTuple m n) := by
  rintro ⟨σ, he⟩
  exact tuple_nonadditive_indices m n (σ 0) (σ 1) (σ 2)
    (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) he

/-- The part of the quartic count that is both primitive and outside every additive-triple locus. -/
def primitiveNonadditiveCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun a : Fin 4 → Fin (n+1) ↦
    (∑ i, (a i : ℕ)^4 = n) ∧ Finset.univ.gcd (fun i ↦ (a i : ℕ)) = 1 ∧
      ¬ Erdos322.QuarticAdditive.HasAdditiveTriple a)).card

theorem primitive_nonadditive_count_lower (m : ℕ) :
    m+1 ≤ primitiveNonadditiveCount (representedNumber m) := by
  classical
  unfold primitiveNonadditiveCount
  have hc := Finset.card_le_card_of_injOn (boundedTuple m) (s := Finset.univ)
    (t := Finset.univ.filter (fun a : Fin 4 → Fin (representedNumber m+1) ↦
      (∑ i, (a i : ℕ)^4 = representedNumber m) ∧
        Finset.univ.gcd (fun i ↦ (a i : ℕ)) = 1 ∧
        ¬ Erdos322.QuarticAdditive.HasAdditiveTriple a))
    (by
      intro i _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨tuple_sum m i, tuple_gcd m i, boundedTuple_nonadditive m i⟩)
    (boundedTuple_injective m).injOn
  simpa using hc

theorem primitive_nonadditive_counts_exceed_any_bound (M : ℕ) :
    {n : ℕ | M < primitiveNonadditiveCount n}.Infinite := by
  intro hf
  let C := hf.toFinset.sup primitiveNonadditiveCount
  let m := M+C
  have hc := primitive_nonadditive_count_lower m
  have hm : M < primitiveNonadditiveCount (representedNumber m) := by omega
  have hn : representedNumber m ∈ hf.toFinset := hf.mem_toFinset.mpr hm
  have hu : primitiveNonadditiveCount (representedNumber m) ≤ C := Finset.le_sup hn
  omega

theorem primitiveNonadditiveCount_le_primitive (n : ℕ) :
    primitiveNonadditiveCount n ≤ Erdos322.primitiveRepresentationCount 4 n := by
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact ⟨ha.1, ha.2.1⟩

theorem primitiveNonadditiveCount_le_nonadditive (n : ℕ) :
    primitiveNonadditiveCount n ≤ Erdos322.QuarticAdditive.nonadditiveQuarticCount n := by
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact ⟨ha.1, ha.2.2⟩


end PrimitiveNonadditive

/- Removing both common factors and the additive-triple locus. -/
namespace PrimitiveNonadditiveReduction

open Erdos322 Erdos322.QuarticAdditive Erdos322.PrimitiveNonadditive
open Erdos322.MomentReduction

/-- The discarded primitive representations are among the additive ones. -/
theorem primitive_count_le_additive_add (n : ℕ) :
    primitiveRepresentationCount 4 n ≤
      additiveQuarticCount n + primitiveNonadditiveCount n := by
  classical
  let S := Finset.univ.filter (fun a : Fin 4 → Fin (n+1) ↦
    (∑ i, (a i : ℕ)^4 = n) ∧ Finset.univ.gcd (fun i ↦ (a i : ℕ)) = 1)
  have hs : (S.filter HasAdditiveTriple).card ≤ additiveQuarticCount n := by
    apply Finset.card_le_card
    intro a ha
    simp only [S, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha ⊢
    exact ⟨ha.1.1, ha.2⟩
  have ht : (S.filter (fun a ↦ ¬ HasAdditiveTriple a)).card =
      primitiveNonadditiveCount n := by
    unfold S primitiveNonadditiveCount
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hp := Finset.card_filter_add_card_filter_not (s := S) HasAdditiveTriple
  rw [ht] at hp
  change S.card ≤ _
  omega

/-- A subpolynomial bound on the primitive nonadditive part is equivalent to
one on the entire quartic representation count. Neither bound is asserted. -/
theorem primitive_nonadditive_bound_iff_full_bound :
    Subpolynomial primitiveNonadditiveCount ↔
      Subpolynomial (representationCount 4) := by
  constructor
  · intro h
    apply (primitive_bound_iff_full_bound (by decide : 0 < 4)).mp
    intro ε hε
    obtain ⟨A, hA, hpn⟩ := h ε hε
    obtain ⟨B, hB, hadd⟩ := additive_quartic_subpolynomial ε hε
    refine ⟨B+A, add_pos hB hA, fun n hn ↦ ?_⟩
    have hle : (primitiveRepresentationCount 4 n : ℝ) ≤
        (additiveQuarticCount n : ℝ) + primitiveNonadditiveCount n := by
      exact_mod_cast primitive_count_le_additive_add n
    calc
      (primitiveRepresentationCount 4 n : ℝ) ≤
          (additiveQuarticCount n : ℝ) + primitiveNonadditiveCount n := hle
      _ ≤ B*(n : ℝ)^ε + A*(n : ℝ)^ε :=
        add_le_add (hadd n (by omega)) (hpn n hn)
      _ = (B+A)*(n : ℝ)^ε := by ring
  · intro h ε hε
    obtain ⟨C, hC, hfull⟩ := h ε hε
    refine ⟨C, hC, fun n hn ↦ ?_⟩
    have hle : (primitiveNonadditiveCount n : ℝ) ≤ representationCount 4 n := by
      exact_mod_cast (primitiveNonadditiveCount_le_primitive n).trans
        (primitiveRepresentationCount_le 4 n)
    exact hle.trans (hfull n hn)

/-- Deleting the additive part from the primitive count preserves the existence
of power peaks, possibly with a smaller positive exponent. -/
theorem primitive_peaks_iff_primitive_nonadditive_peaks :
    (∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ)^c < primitiveRepresentationCount 4 n}.Infinite) ↔
    (∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ)^c < primitiveNonadditiveCount n}.Infinite) := by
  constructor
  · rintro ⟨c, hc, hi⟩
    have hh : 0 < c/2 := by linarith
    obtain ⟨C, hC, hadd⟩ := additive_quartic_subpolynomial (c/2) hh
    have ht : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)^(c/2))
        Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop hh).comp tendsto_natCast_atTop_atTop
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop (C+1))
    refine ⟨c/2, hh, (hi.diff (Set.finite_Iio (max N 1))).mono ?_⟩
    intro n hn
    have hlarge : max N 1 ≤ n := by
      simpa only [Set.mem_Iio, not_lt] using hn.2
    have hnpos : 0 < n := by omega
    have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hsmall := hadd n hnpos
    have hdom := hN n (by omega)
    have hsplit : (primitiveRepresentationCount 4 n : ℝ) ≤
        (additiveQuarticCount n : ℝ) + primitiveNonadditiveCount n := by
      exact_mod_cast primitive_count_le_additive_add n
    have hp : ((n : ℝ)^(c/2))^2 = (n : ℝ)^c := by
      rw [pow_two, ← Real.rpow_add hnr]
      congr 1
      ring
    have hmain := hn.1
    change (n : ℝ)^c < (primitiveRepresentationCount 4 n : ℝ) at hmain
    change (n : ℝ)^(c/2) < (primitiveNonadditiveCount n : ℝ)
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ)^(c/2) by positivity)
      (show 0 ≤ (n : ℝ)^(c/2) - (C+1) by linarith)]
  · rintro ⟨c, hc, hi⟩
    refine ⟨c, hc, hi.mono fun n hn ↦ ?_⟩
    have hle : (primitiveNonadditiveCount n : ℝ) ≤ primitiveRepresentationCount 4 n := by
      exact_mod_cast primitiveNonadditiveCount_le_primitive n
    exact hn.trans_le hle

/-- Exact quartic peak criterion after both reductions. -/
theorem quartic_peaks_iff_primitive_nonadditive_peaks :
    (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < representationCount 4 n}.Infinite) ↔
    (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < primitiveNonadditiveCount n}.Infinite) :=
  (primitive_peaks_iff_full_peaks (by decide : 0 < 4)).symm.trans
    primitive_peaks_iff_primitive_nonadditive_peaks

/-- The all-moment criterion can likewise be restricted to this part. -/
theorem quartic_subpolynomial_iff_primitive_nonadditive_moments :
    Subpolynomial (representationCount 4) ↔
      QuadraticMoments primitiveNonadditiveCount :=
  primitive_nonadditive_bound_iff_full_bound.symm.trans
    (subpolynomial_iff_quadratic_moments primitiveNonadditiveCount)

end PrimitiveNonadditiveReduction

/- Bounds on positive binary quadratic norms, uniform in their coefficient. -/
namespace UniformBinaryNorm

open Erdos322.QuarticAdditive

private lemma coprime_right {d n x y : ℕ}
    (h : x^2+d*y^2=n) (hc : x.Coprime y) : y.Coprime n := by
  rw [← h, show d*y^2 = (d*y)*y by ring, Nat.coprime_add_mul_right_right]
  exact hc.symm.pow_right 2

/-- Ramified primes in a primitive representation of a squarefree-coefficient
norm occur to exponent one in the target. -/
private lemma reduced_coprime {d n x y : ℕ} (hs : Squarefree d)
    (h : x^2+d*y^2=n) (hc : x.Coprime y) : (n / n.gcd d).Coprime x := by
  apply Nat.coprime_of_dvd
  intro p hp hpm hpx
  have hpn : p ∣ n := hpm.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n d))
  have hpdy : p ∣ d*y^2 := (Nat.dvd_add_iff_right (dvd_pow hpx (by decide : 2 ≠ 0))).mpr (h ▸ hpn)
  have hpy : p.Coprime y := hc.of_dvd_left hpx
  have hpd : p ∣ d := (hpy.pow_right 2).dvd_of_dvd_mul_right hpdy
  have hpg : p ∣ n.gcd d := Nat.dvd_gcd hpn hpd
  have hppn : p^2 ∣ n := by
    have hm := mul_dvd_mul hpg hpm
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left n d)] at hm
    simpa only [pow_two] using hm
  have hppx : p^2 ∣ x^2 := pow_dvd_pow_of_dvd hpx 2
  have hppdy : p^2 ∣ d*y^2 := (Nat.dvd_add_iff_right hppx).mpr (h ▸ hppn)
  have hppd : p^2 ∣ d := (hpy.pow 2 2).dvd_of_dvd_mul_right hppdy
  exact hp.not_isUnit (hs p (by simpa only [pow_two] using hppd))

private lemma common_factor_dvd_first {d n x y : ℕ} (hs : Squarefree d)
    (h : x^2+d*y^2=n) : n.gcd d ∣ x := by
  have hgs : Squarefree (n.gcd d) := hs.squarefree_of_dvd (Nat.gcd_dvd_right n d)
  apply (hgs.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp
  have hgd : n.gcd d ∣ d*y^2 := dvd_mul_of_dvd_left (Nat.gcd_dvd_right n d) _
  apply (Nat.dvd_add_iff_left hgd).mpr
  rw [h]
  exact Nat.gcd_dvd_left n d

private def root (m : ℕ) (p : ℕ × ℕ) : ℕ :=
  ((p.1 : ZMod m)*(p.2 : ZMod m)⁻¹).val

private lemma root_mul {d n m x y : ℕ} (hm : 0 < m) (hmn : m ∣ n)
    (h : x^2+d*y^2=n) (hc : x.Coprime y) : root m (x,y)*y ≡ x [MOD m] := by
  letI : NeZero m := ⟨hm.ne'⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  have hi := ZMod.mul_inv_of_unit (y : ZMod m)
    ((ZMod.isUnit_iff_coprime _ _).mpr ((coprime_right h hc).of_dvd_right hmn))
  simp only [Nat.cast_mul, root, ZMod.natCast_zmod_val]
  calc
    (x : ZMod m)*(y : ZMod m)⁻¹*y = x*(y*(y : ZMod m)⁻¹) := by ring
    _ = x := by rw [hi, mul_one]

private lemma root_square {d n m x y : ℕ} (hm : 0 < m) (hmn : m ∣ n)
    (h : x^2+d*y^2=n) (hc : x.Coprime y) : root m (x,y)^2+d ≡ 0 [MOD m] := by
  have hr := root_mul hm hmn h hc
  have he : (root m (x,y)^2+d)*y^2 ≡ 0*y^2 [MOD m] := by
    have hh : x^2+d*y^2 ≡ 0 [MOD m] := Nat.modEq_zero_iff_dvd.mpr (h ▸ hmn)
    convert ((hr.pow 2).add_right (d*y^2)).trans hh using 1 <;> ring
  exact he.cancel_right_of_coprime (((coprime_right h hc).of_dvd_right hmn).symm.pow_right 2)

private lemma root_derivative {d n m x y : ℕ} (hm : 0 < m) (hmn : m ∣ n)
    (h : x^2+d*y^2=n) (hc : x.Coprime y) (hmx : m.Coprime x) :
    m.gcd (2*root m (x,y)) ≤ 2 := by
  have hr := root_mul hm hmn h hc
  have hrc : (root m (x,y)*y).Coprime m := by
    change (root m (x,y)*y).gcd m = 1
    rw [hr.gcd_eq]
    exact hmx.symm
  have hrc' : m.gcd (root m (x,y)) = 1 := (Nat.coprime_mul_iff_left.mp hrc).1.symm
  have hdiv := Nat.gcd_mul_right_dvd_mul_gcd m 2 (root m (x,y))
  rw [hrc', mul_one] at hdiv
  exact Nat.le_of_dvd (by decide : 0 < 2) (hdiv.trans (Nat.gcd_dvd_right m 2))

private lemma cross_lt {d n x y u v : ℕ} (hd : 0 < d) (hn : 0 < n)
    (hu : 0 < u) (h : x^2+d*y^2=n) (h' : u^2+d*v^2=n) : x*v < n := by
  by_cases hx : x = 0
  · simpa [hx] using hn
  have hxp : 0 < x^2 := pow_pos (by omega) 2
  have hv : v^2 < n := by
    have hh : v^2 ≤ d*v^2 := Nat.le_mul_of_pos_left _ hd
    have hh' : 0 < u^2 := pow_pos hu 2
    omega
  have hm : (x*v)^2 < n^2 := by
    calc
      (x*v)^2 = x^2*v^2 := by ring
      _ < x^2*n := Nat.mul_lt_mul_of_pos_left hv hxp
      _ ≤ n*n := Nat.mul_le_mul_right n (by omega)
      _ = n^2 := by ring
  by_contra hnot
  have hh := Nat.pow_le_pow_left (Nat.le_of_not_lt hnot) 2
  omega

private lemma root_tag_injective {d n : ℕ} (hd : 0 < d) (hs : Squarefree d) (hn : 0 < n) :
    Set.InjOn (fun p : ℕ × ℕ ↦ (root (n / n.gcd d) p, decide (p.1=0)))
      (primitiveBinaryNormSolutions d n : Set (ℕ × ℕ)) := by
  intro p hp q hq he
  obtain ⟨hp, hpc⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq, hqc⟩ := Finset.mem_filter.mp hq
  have hp' := (mem_binaryNormSolutions hd p).mp hp
  have hq' := (mem_binaryNormSolutions hd q).mp hq
  let g := n.gcd d
  let m := n/g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left d hn
  have hgn : g ∣ n := Nat.gcd_dvd_left n d
  have hm : 0 < m := Nat.div_pos (Nat.le_of_dvd hn hgn) hg
  have hmn : m ∣ n := Nat.div_dvd_of_dvd hgn
  have hgm : g*m=n := Nat.mul_div_cancel' hgn
  have hgp : g ∣ p.1 := common_factor_dvd_first hs hp'
  have hgq : g ∣ q.1 := common_factor_dvd_first hs hq'
  have hcop : g.Coprime m := ((reduced_coprime hs hp' hpc).of_dvd_right hgp).symm
  have hr : root m p = root m q := congrArg Prod.fst he
  have hz : p.1=0 ↔ q.1=0 := decide_eq_decide.mp (congrArg Prod.snd he)
  have hx : p.1=q.1 := by
    by_cases hp0 : p.1=0
    · exact hp0.trans (hz.mp hp0).symm
    have hq0 : q.1 ≠ 0 := fun h ↦ hp0 (hz.mpr h)
    have h₁ := (root_mul hm hmn hp' hpc).mul_right q.2
    have h₂ := (root_mul hm hmn hq' hqc).mul_right p.2
    have hem : p.1*q.2 ≡ q.1*p.2 [MOD m] := by
      apply h₁.symm.trans
      convert h₂ using 1
      rw [hr]
      ring
    have heg : p.1*q.2 ≡ q.1*p.2 [MOD g] :=
      (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hgp _)).trans
        (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hgq _)).symm
    have hen : p.1*q.2 ≡ q.1*p.2 [MOD n] := by
      rw [← hgm]
      exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨heg, hem⟩
    have hc : p.1*q.2=q.1*p.2 := hen.eq_of_lt_of_lt
      (cross_lt hd hn (by omega) hp' hq') (cross_lt hd hn (by omega) hq' hp')
    have hsq : p.1^2=q.1^2 := by
      apply Nat.mul_left_cancel hn
      calc
        n*p.1^2 = p.1^2*q.1^2+d*(p.1*q.2)^2 := by rw [← hq']; ring
        _ = p.1^2*q.1^2+d*(q.1*p.2)^2 := by rw [hc]
        _ = n*q.1^2 := by rw [← hp']; ring
    exact Nat.pow_left_injective (by decide : 2 ≠ 0) hsq
  have hy : p.2=q.2 := by
    rw [hx] at hp'
    have hmul : d*p.2^2=d*q.2^2 := by omega
    exact Nat.pow_left_injective (by decide : 2 ≠ 0) (Nat.mul_left_cancel hd hmul)
  exact Prod.ext hx hy

/-- The primitive bound is independent of a squarefree norm coefficient. -/
theorem primitive_norm_count_squarefree {d n : ℕ} (hd : 0 < d)
    (hs : Squarefree d) (hn : 0 < n) :
    (primitiveBinaryNormSolutions d n).card ≤ 4*n.divisors.card := by
  classical
  by_cases he : primitiveBinaryNormSolutions d n = ∅
  · simp [he]
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr he
  obtain ⟨hp, hpc⟩ := Finset.mem_filter.mp hp
  have hp' := (mem_binaryNormSolutions hd p).mp hp
  let m := n/n.gcd d
  have hm : 0 < m := Nat.div_pos
    (Nat.le_of_dvd hn (Nat.gcd_dvd_left n d)) (Nat.gcd_pos_of_pos_left d hn)
  have hmn : m ∣ n := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n d)
  let a := root m p
  let R := (Finset.range m).filter (fun r ↦ r^2 ≡ a^2 [MOD m])
  have hroots : R.card ≤ m.divisors.card*2 := square_congruence_count hm
    (root_derivative hm hmn hp' hpc (reduced_coprime hs hp' hpc))
  have hb : (primitiveBinaryNormSolutions d n).card ≤ (R ×ˢ (Finset.univ : Finset Bool)).card := by
    apply Finset.card_le_card_of_injOn (fun q : ℕ × ℕ ↦ (root m q, decide (q.1=0)))
    · intro q hq
      obtain ⟨hq, hqc⟩ := Finset.mem_filter.mp hq
      have hq' := (mem_binaryNormSolutions hd q).mp hq
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
      · letI : NeZero m := ⟨hm.ne'⟩
        exact Finset.mem_range.mpr (ZMod.val_lt _)
      · exact Nat.ModEq.add_right_cancel (Nat.ModEq.refl d)
          ((root_square hm hmn hq' hqc).trans (root_square hm hmn hp' hpc).symm)
    · exact root_tag_injective hd hs hn
  have hdiv : m.divisors.card ≤ n.divisors.card :=
    Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' hmn)
  have hb' : (primitiveBinaryNormSolutions d n).card ≤ R.card*2 := by simpa using hb
  nlinarith


private lemma norm_gcd_pos {d n : ℕ} (hn : 0 < n) (p : ℕ × ℕ)
    (hp : p.1 ^ 2 + d * p.2 ^ 2 = n) : 0 < p.1.gcd p.2 := by
  by_contra hnot
  have hg : p.1.gcd p.2 = 0 := by omega
  obtain ⟨hx,hy⟩ := Nat.gcd_eq_zero_iff.mp hg
  simp [hx, hy] at hp
  omega

private lemma norm_quotient_mul {d n : ℕ} (p : ℕ × ℕ)
    (hp : p.1 ^ 2 + d * p.2 ^ 2 = n) :
    p.1.gcd p.2 ^ 2 * ((p.1 / p.1.gcd p.2) ^ 2 +
      d * (p.2 / p.1.gcd p.2) ^ 2) = n := by
  calc
    _ = (p.1.gcd p.2 * (p.1 / p.1.gcd p.2)) ^ 2 +
        d * (p.1.gcd p.2 * (p.2 / p.1.gcd p.2)) ^ 2 := by ring
    _ = p.1 ^ 2 + d * p.2 ^ 2 := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _),
        Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)]
    _ = n := hp

private lemma norm_quotient_primitive {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (p : ℕ × ℕ) (hp : p.1 ^ 2 + d * p.2 ^ 2 = n) :
    (p.1 / p.1.gcd p.2, p.2 / p.1.gcd p.2) ∈
      primitiveBinaryNormSolutions d (n / p.1.gcd p.2 ^ 2) := by
  have hg := norm_gcd_pos hn p hp
  have hmul := norm_quotient_mul p hp
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · apply (mem_binaryNormSolutions hd _).mpr
    change (p.1 / p.1.gcd p.2) ^ 2 + d * (p.2 / p.1.gcd p.2) ^ 2 = _
    rw [← hmul, Nat.mul_div_cancel_left _ (pow_pos hg 2)]
  · change (p.1 / p.1.gcd p.2).gcd (p.2 / p.1.gcd p.2) = 1
    rw [Nat.gcd_div (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _), Nat.div_self hg]

theorem norm_count_squarefree {d n : ℕ} (hd : 0 < d) (hs : Squarefree d) (hn : 0 < n) :
    (binaryNormSolutions d n).card ≤ 4 * n.divisors.card ^ 2 := by
  classical
  let S := binaryNormSolutions d n
  let gs := S.image (fun p ↦ p.1.gcd p.2)
  have hgs : gs ⊆ n.divisors := by
    intro g hg
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hg
    have hpNorm := (mem_binaryNormSolutions (by omega : 0 < d) p).mp hp
    have hmul := norm_quotient_mul p hpNorm
    have hsq : p.1.gcd p.2 ^ 2 ∣ n := ⟨_, hmul.symm⟩
    exact Nat.mem_divisors.mpr ⟨(dvd_pow_self _ (by decide : 2 ≠ 0)).trans hsq, hn.ne'⟩
  have hfiber (g : ℕ) (hg : g ∈ gs) :
      (S.filter (fun p ↦ p.1.gcd p.2 = g)).card ≤ n.divisors.card * 4 := by
    obtain ⟨p,hp,hpg⟩ := Finset.mem_image.mp hg
    have hpNorm := (mem_binaryNormSolutions (by omega : 0 < d) p).mp hp
    have hgpos : 0 < g := hpg ▸ norm_gcd_pos hn p hpNorm
    have hmul := norm_quotient_mul p hpNorm
    rw [hpg] at hmul
    have hsq : g ^ 2 ∣ n := ⟨_, hmul.symm⟩
    have hmpos : 0 < n / g ^ 2 :=
      Nat.div_pos (Nat.le_of_dvd hn hsq) (pow_pos hgpos 2)
    have hdiv : (n / g ^ 2).divisors.card ≤ n.divisors.card :=
      Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' (Nat.div_dvd_of_dvd hsq))
    have hb := (primitive_norm_count_squarefree hd hs hmpos).trans
      (Nat.mul_le_mul_left 4 hdiv)
    rw [mul_comm 4] at hb
    apply le_trans _ hb
    apply Finset.card_le_card_of_injOn (fun q : ℕ × ℕ ↦ (q.1 / g, q.2 / g))
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter] at hq
      have hqNorm := (mem_binaryNormSolutions (by omega : 0 < d) q).mp hq.1
      have hh := norm_quotient_primitive (by omega : 0 < d) hn q hqNorm
      rwa [hq.2] at hh
    · intro q hq r hr heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hq hr
      have h1 : q.1 / g = r.1 / g := congrArg Prod.fst heq
      have h2 : q.2 / g = r.2 / g := congrArg Prod.snd heq
      have hq1 : g * (q.1 / g) = q.1 := by
        rw [← hq.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hq2 : g * (q.2 / g) = q.2 := by
        rw [← hq.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have hr1 : g * (r.1 / g) = r.1 := by
        rw [← hr.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hr2 : g * (r.2 / g) = r.2 := by
        rw [← hr.2]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      apply Prod.ext
      · rw [← hq1, ← hr1, h1]
      · rw [← hq2, ← hr2, h2]
  calc
    S.card = ∑ g ∈ gs, (S.filter (fun p ↦ p.1.gcd p.2 = g)).card :=
      Finset.card_eq_sum_card_image _ _
    _ ≤ ∑ g ∈ gs, n.divisors.card * 4 := Finset.sum_le_sum hfiber
    _ = gs.card * (n.divisors.card * 4) := by simp
    _ ≤ n.divisors.card * (n.divisors.card * 4) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hgs)
    _ = 4 * n.divisors.card ^ 2 := by ring

/-- A coefficient-uniform divisor bound, with no squarefreeness assumption. -/
theorem binary_norm_count_uniform {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    (binaryNormSolutions d n).card ≤ 4*n.divisors.card^2 := by
  obtain ⟨a, b, hba, has⟩ := Nat.sq_mul_squarefree d
  have ha : 0 < a := Nat.pos_of_ne_zero has.ne_zero
  have hb : 0 < b := by
    by_contra hnot
    have hb0 : b=0 := by omega
    simp [hb0] at hba
    omega
  apply le_trans _ (norm_count_squarefree ha has hn)
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ ↦ (p.1, b*p.2))
  · intro p hp
    apply (mem_binaryNormSolutions ha _).mpr
    have hp' := (mem_binaryNormSolutions hd p).mp hp
    change p.1^2+a*(b*p.2)^2=n
    calc
      p.1^2+a*(b*p.2)^2 = p.1^2+(b^2*a)*p.2^2 := by ring
      _ = n := by rw [hba]; exact hp'
  · intro p hp q hq he
    have h₁ := congrArg Prod.fst he
    change p.1=q.1 at h₁
    have h₂ : b*p.2=b*q.2 := congrArg Prod.snd he
    exact Prod.ext h₁ (Nat.mul_left_cancel hb h₂)

/-- The same subpolynomial constant works for every positive norm coefficient,
including a coefficient chosen as a function of the target. -/
theorem binary_norm_subpolynomial_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ d n : ℕ, 0 < d → 0 < n →
      ((binaryNormSolutions d n).card : ℝ) ≤ C*(n : ℝ)^ε := by
  obtain ⟨C, hC, hdiv⟩ := Erdos322.divisor_count_subpolynomial (ε/2) (by linarith)
  refine ⟨4*C^2, by positivity, fun d n hd hn ↦ ?_⟩
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : ((n : ℝ)^(ε/2))^2 = (n : ℝ)^ε := by
    rw [pow_two, ← Real.rpow_add hnr]
    congr 1
    ring
  calc
    ((binaryNormSolutions d n).card : ℝ) ≤ 4*(n.divisors.card : ℝ)^2 := by
      exact_mod_cast binary_norm_count_uniform hd hn
    _ ≤ 4*(C*(n : ℝ)^(ε/2))^2 := by gcongr; exact hdiv n hn
    _ = (4*C^2)*(n : ℝ)^ε := by rw [mul_pow, hp]; ring

/-- A uniform bound for any finite collection of solutions of a positive
binary diagonal quadratic equation, even when both coefficients vary. -/
theorem diagonal_binary_subpolynomial_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ a d n : ℕ, 0 < a → 0 < d → 0 < n →
      ∀ S : Finset (ℕ × ℕ), (∀ p ∈ S, a*p.1^2+d*p.2^2=n) →
        (S.card : ℝ) ≤ C*(n : ℝ)^ε := by
  classical
  obtain ⟨C, hC, hb⟩ := binary_norm_subpolynomial_uniform (ε/2) (by linarith)
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun a d n ha hd hn S hS ↦ ?_⟩
  by_cases hzero : ∀ p ∈ S, p.1=0
  · have hcard : S.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro p hp q hq
      have hp' := hS p hp
      have hq' := hS q hq
      rw [hzero p hp] at hp'
      rw [hzero q hq] at hq'
      simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add] at hp' hq'
      apply Prod.ext ((hzero p hp).trans (hzero q hq).symm)
      exact Nat.pow_left_injective (by decide : 2 ≠ 0)
        (Nat.mul_left_cancel hd (hp'.trans hq'.symm))
    have hp : 1 ≤ (n : ℝ)^ε := Real.one_le_rpow (by exact_mod_cast hn) hε.le
    have hc : (S.card : ℝ) ≤ 1 := by exact_mod_cast hcard
    apply hc.trans
    calc
      (1 : ℝ) = 1*1 := by norm_num
      _ ≤ max 1 C*(n : ℝ)^ε := mul_le_mul (le_max_left _ _) hp (by norm_num) (by positivity)
  · push_neg at hzero
    obtain ⟨p, hp, hpx⟩ := hzero
    have han : a ≤ n := by
      have hp' := hS p hp
      have hx : 1 ≤ p.1^2 := one_le_pow₀ (by omega)
      have hh := Nat.mul_le_mul_left a hx
      nlinarith
    have hcard : S.card ≤ (binaryNormSolutions (a*d) (a*n)).card := by
      apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ ↦ (a*p.1, p.2))
      · intro p hp
        apply (mem_binaryNormSolutions (Nat.mul_pos ha hd) _).mpr
        change (a*p.1)^2+(a*d)*p.2^2=a*n
        calc
          (a*p.1)^2+(a*d)*p.2^2 = a*(a*p.1^2+d*p.2^2) := by ring
          _ = a*n := by rw [hS p hp]
      · intro p hp q hq he
        have h₁ : a*p.1=a*q.1 := congrArg Prod.fst he
        have h₂ := congrArg Prod.snd he
        change p.2=q.2 at h₂
        exact Prod.ext (Nat.mul_left_cancel ha h₁) h₂
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hh : ((a*n : ℕ) : ℝ)^(ε/2) ≤ (n : ℝ)^ε := by
      calc
        ((a*n : ℕ) : ℝ)^(ε/2) ≤ ((n : ℝ)*(n : ℝ))^(ε/2) := by
          apply Real.rpow_le_rpow (by positivity) _ (by linarith)
          exact_mod_cast Nat.mul_le_mul_right n han
        _ = (n : ℝ)^ε := by
          rw [Real.mul_rpow hnr.le hnr.le, ← Real.rpow_add hnr]
          congr 1
          ring
    calc
      (S.card : ℝ) ≤ (binaryNormSolutions (a*d) (a*n)).card := by exact_mod_cast hcard
      _ ≤ C*((a*n : ℕ) : ℝ)^(ε/2) := hb (a*d) (a*n) (Nat.mul_pos ha hd) (Nat.mul_pos ha hn)
      _ ≤ max 1 C*(n : ℝ)^ε := mul_le_mul (le_max_right _ _) hh (by positivity) (by positivity)

end UniformBinaryNorm

/- A uniform bound for quartic representations with a multiplicative coordinate relation. -/
namespace QuarticMultiplicative

open Erdos322.QuarticAdditive

private def matrixTuple (u v : ℕ × ℕ) : Fin 4 → ℕ :=
  ![u.1*v.1, u.1*v.2, u.2*v.1, u.2*v.2]

private lemma matrixTuple_sum (u v : ℕ × ℕ) :
    ∑ i, matrixTuple u v i ^ 4 = (u.1^4+u.2^4)*(v.1^4+v.2^4) := by
  simp [Fin.sum_univ_four, matrixTuple]
  ring

/-- Every nonnegative integral rank-one two-by-two matrix is an outer product
of two nonnegative integral vectors. Zero rows and columns are included. -/
private lemma rank_one_factorization (a : Fin 4 → ℕ) (h : a 0*a 3=a 1*a 2) :
    ∃ u v : ℕ × ℕ, a=matrixTuple u v := by
  by_cases hx : a 0=0
  · by_cases hy : a 1=0
    · refine ⟨(0,1),(a 2,a 3),?_⟩
      funext i
      fin_cases i <;> simp [matrixTuple, hx, hy]
    · have hz : a 2=0 := by
        rw [hx, zero_mul] at h
        exact (mul_eq_zero.mp h.symm).resolve_left hy
      refine ⟨(a 1,a 3),(0,1),?_⟩
      funext i
      fin_cases i <;> simp [matrixTuple, hx, hz]
  · let g := (a 0).gcd (a 1)
    have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hx)
    obtain ⟨x,y,hcop,hxg,hyg⟩ := Nat.exists_coprime (a 0) (a 1)
    change a 0=x*g at hxg
    change a 1=y*g at hyg
    have hxp : 0 < x := by
      by_contra hn
      have hx0 : x=0 := by omega
      simp [hx0] at hxg
      exact hx hxg
    have hcross : x*a 3=y*a 2 := by
      apply Nat.mul_left_cancel hg
      calc
        g*(x*a 3) = a 0*a 3 := by rw [hxg]; ring
        _ = a 1*a 2 := h
        _ = g*(y*a 2) := by rw [hyg]; ring
    have hdiv : x ∣ a 2 := hcop.dvd_of_dvd_mul_left (hcross ▸ dvd_mul_right x (a 3))
    obtain ⟨z,hz⟩ := hdiv
    have hw : a 3=y*z := by
      apply Nat.mul_left_cancel hxp
      calc
        x*a 3 = y*a 2 := hcross
        _ = x*(y*z) := by rw [hz]; ring
    refine ⟨(g,z),(x,y),?_⟩
    funext i
    fin_cases i <;> simp [matrixTuple, hxg, hyg, hz, hw, mul_comm]

private def fourthPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n+1) ×ˢ Finset.range (n+1)).filter (fun p ↦ p.1^4+p.2^4=n)

private lemma mem_fourthPairs (n : ℕ) (p : ℕ × ℕ) :
    p ∈ fourthPairs n ↔ p.1^4+p.2^4=n := by
  simp only [fourthPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact And.right
  · intro hp
    have h₁ := Nat.le_pow (a := p.1) (by decide : 0 < 4)
    have h₂ := Nat.le_pow (a := p.2) (by decide : 0 < 4)
    exact ⟨⟨by omega, by omega⟩,hp⟩

private lemma fourthPairs_bound {n : ℕ} (hn : 0 < n) :
    (fourthPairs n).card ≤ 4*n.divisors.card^2 := by
  apply le_trans _ (Erdos322.UniformBinaryNorm.binary_norm_count_uniform (by decide : 0 < 1) hn)
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ ↦ (p.1^2,p.2^2))
  · intro p hp
    apply (mem_binaryNormSolutions (by decide : 0 < 1) _).mpr
    have hp' := (mem_fourthPairs n p).mp hp
    change (p.1^2)^2+1*(p.2^2)^2=n
    simpa only [← pow_mul, one_mul] using hp'
  · intro p hp q hq he
    have h₁ : p.1^2=q.1^2 := congrArg Prod.fst he
    have h₂ : p.2^2=q.2^2 := congrArg Prod.snd he
    exact Prod.ext (Nat.pow_left_injective (by decide : 2 ≠ 0) h₁)
      (Nat.pow_left_injective (by decide : 2 ≠ 0) h₂)

private def fixedReps (n : ℕ) : Finset (Fin 4 → Fin (n+1)) :=
  Finset.univ.filter (fun a ↦ (∑ i, (a i : ℕ)^4=n) ∧
    (a 0 : ℕ)*(a 3 : ℕ)=(a 1 : ℕ)*(a 2 : ℕ))

def fixedMultiplicativeCount (n : ℕ) : ℕ := (fixedReps n).card

private def factorImages (n d : ℕ) : Finset (Fin 4 → ℕ) :=
  (fourthPairs d ×ˢ fourthPairs (n/d)).image (fun p ↦ matrixTuple p.1 p.2)

private lemma fixed_count_le_divisor_sum {n : ℕ} (hn : 0 < n) :
    fixedMultiplicativeCount n ≤
      ∑ d ∈ n.divisors, (fourthPairs d).card*(fourthPairs (n/d)).card := by
  classical
  have hcard : fixedMultiplicativeCount n ≤ (n.divisors.biUnion (factorImages n)).card := by
    apply Finset.card_le_card_of_injOn (fun a : Fin 4 → Fin (n+1) ↦ fun i ↦ (a i : ℕ))
    · intro a ha
      simp only [Finset.mem_coe, fixedReps, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨u,v,he⟩ := rank_one_factorization (fun i ↦ (a i : ℕ)) ha.2
      let d := u.1^4+u.2^4
      let e := v.1^4+v.2^4
      have hm : d*e=n := by
        rw [← matrixTuple_sum u v, ← he]
        exact ha.1
      have hd : 0 < d := by
        by_contra hn'
        have hd0 : d=0 := by omega
        rw [hd0, zero_mul] at hm
        omega
      have hdn : d ∣ n := ⟨e,hm.symm⟩
      have hquot : n/d=e := by rw [← hm, Nat.mul_div_cancel_left _ hd]
      apply Finset.mem_biUnion.mpr
      refine ⟨d,Nat.mem_divisors.mpr ⟨hdn,hn.ne'⟩,?_⟩
      apply Finset.mem_image.mpr
      refine ⟨(u,v),Finset.mem_product.mpr ⟨?_,?_⟩,he.symm⟩
      · exact (mem_fourthPairs d u).mpr rfl
      · rw [hquot]
        exact (mem_fourthPairs e v).mpr rfl
    · intro a ha b hb he
      funext i
      exact Fin.ext (congrArg (fun f ↦ f i) he)
  apply hcard.trans (Finset.card_biUnion_le.trans ?_)
  apply Finset.sum_le_sum
  intro d hd
  exact (Finset.card_image_le (s := fourthPairs d ×ˢ fourthPairs (n/d))).trans_eq
    (Finset.card_product _ _)

/-- The whole fixed multiplicative-relation locus has a divisor bound. -/
theorem fixed_multiplicative_divisor_bound {n : ℕ} (hn : 0 < n) :
    fixedMultiplicativeCount n ≤ 16*n.divisors.card^5 := by
  apply (fixed_count_le_divisor_sum hn).trans
  have ht (d : ℕ) (hd : d ∈ n.divisors) :
      (fourthPairs d).card*(fourthPairs (n/d)).card ≤ 16*n.divisors.card^4 := by
    have hdn := (Nat.mem_divisors.mp hd).1
    have hdp : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hqp : 0 < n/d := Nat.div_pos (Nat.le_of_dvd hn hdn) hdp
    have hdcard : d.divisors.card ≤ n.divisors.card :=
      Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' hdn)
    have hqcard : (n/d).divisors.card ≤ n.divisors.card :=
      Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' (Nat.div_dvd_of_dvd hdn))
    calc
      (fourthPairs d).card*(fourthPairs (n/d)).card ≤
          (4*d.divisors.card^2)*(4*(n/d).divisors.card^2) :=
        Nat.mul_le_mul (fourthPairs_bound hdp) (fourthPairs_bound hqp)
      _ ≤ (4*n.divisors.card^2)*(4*n.divisors.card^2) := by gcongr
      _ = 16*n.divisors.card^4 := by ring
  calc
    ∑ d ∈ n.divisors, (fourthPairs d).card*(fourthPairs (n/d)).card ≤
        ∑ _d ∈ n.divisors, 16*n.divisors.card^4 := Finset.sum_le_sum ht
    _ = 16*n.divisors.card^5 := by simp; ring

/-- Some permutation of the four coordinates forms a rank-one matrix. -/
def HasProductRelation {n : ℕ} (a : Fin 4 → Fin (n+1)) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4),
    (a (σ 0) : ℕ)*(a (σ 3) : ℕ)=(a (σ 1) : ℕ)*(a (σ 2) : ℕ)

instance {n : ℕ} (a : Fin 4 → Fin (n+1)) : Decidable (HasProductRelation a) :=
  inferInstanceAs (Decidable (∃ σ : Equiv.Perm (Fin 4),
    (a (σ 0) : ℕ)*(a (σ 3) : ℕ)=(a (σ 1) : ℕ)*(a (σ 2) : ℕ)))

def multiplicativeQuarticCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun a : Fin 4 → Fin (n+1) ↦
    (∑ i, (a i : ℕ)^4=n) ∧ HasProductRelation a)).card

private def permReps (n : ℕ) (σ : Equiv.Perm (Fin 4)) : Finset (Fin 4 → Fin (n+1)) :=
  Finset.univ.filter (fun a ↦ (∑ i, (a i : ℕ)^4=n) ∧
    (a (σ 0) : ℕ)*(a (σ 3) : ℕ)=(a (σ 1) : ℕ)*(a (σ 2) : ℕ))

private lemma permReps_card (n : ℕ) (σ : Equiv.Perm (Fin 4)) :
    (permReps n σ).card=fixedMultiplicativeCount n := by
  classical
  apply Finset.card_nbij (fun a i ↦ a (σ i))
  · intro a ha
    simp only [Finset.mem_coe, permReps, fixedReps,
      Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ⟨(Equiv.sum_comp σ (fun i ↦ (a i : ℕ)^4)).trans ha.1,ha.2⟩
  · intro a ha b hb he
    funext i
    have hh := congrArg (fun f ↦ f (σ.symm i)) he
    simpa using hh
  · intro a ha
    simp only [Finset.mem_coe, fixedReps, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    refine ⟨fun i ↦ a (σ.symm i),?_,?_⟩
    · simp only [Finset.mem_coe, permReps, Finset.mem_filter,
        Finset.mem_univ, true_and, Equiv.symm_apply_apply]
      exact ⟨(Equiv.sum_comp σ.symm (fun i ↦ (a i : ℕ)^4)).trans ha.1,ha.2⟩
    · funext i
      simp

private lemma multiplicative_le (n : ℕ) :
    multiplicativeQuarticCount n ≤ 24*fixedMultiplicativeCount n := by
  classical
  have he : Finset.univ.filter (fun a : Fin 4 → Fin (n+1) ↦
      (∑ i, (a i : ℕ)^4=n) ∧ HasProductRelation a) = Finset.univ.biUnion (permReps n) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      permReps, HasProductRelation]
    tauto
  change (Finset.univ.filter _).card ≤ _
  rw [he]
  have hb := Finset.card_biUnion_le (s := (Finset.univ : Finset (Equiv.Perm (Fin 4))))
    (t := permReps n)
  simp only [permReps_card, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, smul_eq_mul] at hb
  norm_num at hb
  exact hb

/-- All ordered quartic representations containing a product relation satisfy
this bound, regardless of the factors used in a construction. -/
theorem multiplicative_quartic_divisor_bound {n : ℕ} (hn : 0 < n) :
    multiplicativeQuarticCount n ≤ 384*n.divisors.card^5 := by
  calc
    multiplicativeQuarticCount n ≤ 24*fixedMultiplicativeCount n := multiplicative_le n
    _ ≤ 24*(16*n.divisors.card^5) := Nat.mul_le_mul_left _ (fixed_multiplicative_divisor_bound hn)
    _ = 384*n.divisors.card^5 := by ring

theorem multiplicative_quartic_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
      (multiplicativeQuarticCount n : ℝ) ≤ C*(n : ℝ)^ε := by
  obtain ⟨C,hC,hdiv⟩ := Erdos322.divisor_count_subpolynomial (ε/5) (by linarith)
  refine ⟨384*C^5,by positivity,fun n hn ↦ ?_⟩
  have hp : ((n : ℝ)^(ε/5))^5=(n : ℝ)^ε := by
    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ n)]
    congr 1
    norm_num
  calc
    (multiplicativeQuarticCount n : ℝ) ≤ 384*(n.divisors.card : ℝ)^5 := by
      exact_mod_cast multiplicative_quartic_divisor_bound hn
    _ ≤ 384*(C*(n : ℝ)^(ε/5))^5 := by gcongr; exact hdiv n hn
    _ = (384*C^5)*(n : ℝ)^ε := by rw [mul_pow,hp]; ring

end QuarticMultiplicative

/- Removing additive and multiplicative exceptional loci does not make the
primitive quartic representation count bounded. -/
namespace QuarticCore

open PrimitiveNonadditive QuarticAdditive QuarticMultiplicative

private theorem product_inequalities (a b c : ℕ)
    (ha : a=0 ∨ 71 ≤ a) (hb : b=0 ∨ 71 ≤ b)
    (hp : 0 < a+b) (hl : 2*(a^2+b^2) ≤ c^2)
    (hu : c^2 ≤ 12*(a^2+b^2)) :
    c ≠ a*b ∧ b ≠ a*c ∧ a ≠ b*c := by
  have hac : a < c := by
    by_contra hn
    have hca : c^2 ≤ a^2 := Nat.pow_le_pow_left (by omega) 2
    have hsq : 0 < a^2+b^2 := by
      rcases ha with rfl | ha
      · nlinarith [Nat.mul_self_le_mul_self (show 1 ≤ b by omega)]
      · nlinarith [Nat.mul_self_le_mul_self ha]
    nlinarith
  have hbc : b < c := by
    by_contra hn
    have hcb : c^2 ≤ b^2 := Nat.pow_le_pow_left (by omega) 2
    have hsq : 0 < a^2+b^2 := by
      rcases ha with rfl | ha
      · nlinarith [Nat.mul_self_le_mul_self (show 1 ≤ b by omega)]
      · nlinarith [Nat.mul_self_le_mul_self ha]
    nlinarith
  have hc : 0 < c := by omega
  refine ⟨?_,?_,?_⟩
  · intro he
    rcases ha with rfl | ha
    · simp at he; omega
    rcases hb with rfl | hb
    · simp at he; omega
    rcases le_total a b with hab | hba
    · have hs : a^2 ≤ b^2 := Nat.pow_le_pow_left hab 2
      have hlo : 71*b ≤ c := by nlinarith
      have hsq : (71*b)^2 ≤ c^2 := Nat.pow_le_pow_left hlo 2
      nlinarith
    · have hs : b^2 ≤ a^2 := Nat.pow_le_pow_left hba 2
      have hlo : 71*a ≤ c := by nlinarith
      have hsq : (71*a)^2 ≤ c^2 := Nat.pow_le_pow_left hlo 2
      nlinarith
  · intro he
    rcases ha with rfl | ha
    · simp at he; omega
    · nlinarith
  · intro he
    rcases hb with rfl | hb
    · simp at he; omega
    · nlinarith

private theorem no_product_relation (n : ℕ) (v : Fin 4 → Fin (n+1))
    (h3 : (v 3 : ℕ)=1)
    (h0 : (v 0 : ℕ) ≠ (v 1 : ℕ)*(v 2 : ℕ))
    (h1 : (v 1 : ℕ) ≠ (v 0 : ℕ)*(v 2 : ℕ))
    (h2 : (v 2 : ℕ) ≠ (v 0 : ℕ)*(v 1 : ℕ)) :
    ¬HasProductRelation v := by
  change (v ⟨3, by decide⟩ : ℕ)=1 at h3
  rintro ⟨σ,he⟩
  have h01 := σ.injective.ne (by decide : (0 : Fin 4) ≠ 1)
  have h02 := σ.injective.ne (by decide : (0 : Fin 4) ≠ 2)
  have h03 := σ.injective.ne (by decide : (0 : Fin 4) ≠ 3)
  have h12 := σ.injective.ne (by decide : (1 : Fin 4) ≠ 2)
  have h13 := σ.injective.ne (by decide : (1 : Fin 4) ≠ 3)
  have h23 := σ.injective.ne (by decide : (2 : Fin 4) ≠ 3)
  generalize hi : σ 0 = i at *
  generalize hj : σ 1 = j at *
  generalize hk : σ 2 = k at *
  generalize hl : σ 3 = l at *
  clear hi hj hk hl σ
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals fin_cases k <;> try contradiction
  all_goals fin_cases l <;> try contradiction
  all_goals simp only [h3, mul_one, one_mul] at he
  all_goals try first
    | exact h0 he
    | exact h0 he.symm
    | exact h1 he
    | exact h1 he.symm
    | exact h2 he
    | exact h2 he.symm
  all_goals rw [mul_comm] at he
  all_goals first
    | exact h0 he
    | exact h0 he.symm
    | exact h1 he
    | exact h1 he.symm
    | exact h2 he
    | exact h2 he.symm

private theorem tuple_sq (m : ℕ) (i : Fin (m+1)) (j : Fin 3) :
    (tuple m i j.castSucc : ℤ)^2 = (2*scale m i)^2 * (integerTriple i j)^2 := by
  simp only [tuple, Fin.snoc_castSucc, natTriple, Nat.cast_mul, Nat.cast_ofNat,
    Int.natCast_natAbs, mul_pow, sq_abs]
  ring

private theorem tuple_pinching (m : ℕ) (i : Fin (m+1)) :
    0 < tuple m i 0+tuple m i 1 ∧
    2*((tuple m i 0)^2+(tuple m i 1)^2) ≤ (tuple m i 2)^2 ∧
    (tuple m i 2)^2 ≤ 12*((tuple m i 0)^2+(tuple m i 1)^2) := by
  let a := tuple m i 0
  let b := tuple m i 1
  let c := tuple m i 2
  have hq := (point_on_quadrics i).1
  have ha : (a : ℤ)^2 = (142 * scale m i)^2*((point i).s+(point i).t)^2 := by
    rw [show a = tuple m i (0 : Fin 3).castSucc from rfl, tuple_sq]
    simp [integerTriple]
    ring
  have hb : (b : ℤ)^2 = (142 * scale m i)^2*((point i).s-(point i).t)^2 := by
    rw [show b = tuple m i (1 : Fin 3).castSucc from rfl, tuple_sq]
    simp [integerTriple]
    ring
  have hc : (c : ℤ)^2 = (284 * scale m i)^2*(point i).z^2 := by
    rw [show c = tuple m i (2 : Fin 3).castSucc from rfl, tuple_sq]
    simp [integerTriple]
    ring
  have hs : 0 < (scale m i : ℤ) := by exact_mod_cast scale_pos m i
  have hl : 2*((a : ℤ)^2+(b : ℤ)^2) ≤ (c : ℤ)^2 := by
    rw [ha,hb,hc,hq]
    nlinarith [sq_nonneg ((scale m i : ℤ)*(point i).s)]
  have hu : (c : ℤ)^2 ≤ 12*((a : ℤ)^2+(b : ℤ)^2) := by
    rw [ha,hb,hc,hq]
    nlinarith [sq_nonneg ((scale m i : ℤ)*(point i).t)]
  have hp : 0 < a+b := by
    by_contra hn
    have ha0 : a=0 := by omega
    have hb0 : b=0 := by omega
    have hs0 : (142*(scale m i : ℤ))^2 ≠ 0 := by positivity
    have hst : (point i).s+(point i).t = 0 := by
      have hh : (142*(scale m i : ℤ))^2*((point i).s+(point i).t)^2=0 := by
        rw [←ha,ha0]; norm_num
      exact eq_zero_of_pow_eq_zero (mul_eq_zero.mp hh |>.resolve_left hs0)
    have hst' : (point i).s-(point i).t = 0 := by
      have hh : (142*(scale m i : ℤ))^2*((point i).s-(point i).t)^2=0 := by
        rw [←hb,hb0]; norm_num
      exact eq_zero_of_pow_eq_zero (mul_eq_zero.mp hh |>.resolve_left hs0)
    exact point_t_ne_zero i (by omega)
  exact ⟨hp,by exact_mod_cast hl,by exact_mod_cast hu⟩

private theorem tuple_multiple (m : ℕ) (i : Fin (m+1)) (j : Fin 3) :
    71 ∣ tuple m i j.castSucc := by
  simp only [tuple, Fin.snoc_castSucc, natTriple]
  have hd : 71 ∣ (integerTriple i j).natAbs := by
    fin_cases j
    · simp [integerTriple, Int.natAbs_mul]
    · simp [integerTriple, Int.natAbs_mul]
    · change 71 ∣ (142*(point i).z).natAbs
      rw [Int.natAbs_mul]
      exact dvd_mul_of_dvd_left (by norm_num : 71 ∣ (142 : ℤ).natAbs) _
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd 2) _

private theorem boundedTuple_nonmultiplicative (m : ℕ) (i : Fin (m+1)) :
    ¬HasProductRelation (boundedTuple m i) := by
  have ha : tuple m i 0=0 ∨ 71 ≤ tuple m i 0 := by
    by_cases h : tuple m i 0=0
    · exact Or.inl h
    · exact Or.inr (Nat.le_of_dvd (Nat.pos_of_ne_zero h) (tuple_multiple m i 0))
  have hb : tuple m i 1=0 ∨ 71 ≤ tuple m i 1 := by
    by_cases h : tuple m i 1=0
    · exact Or.inl h
    · exact Or.inr (Nat.le_of_dvd (Nat.pos_of_ne_zero h) (tuple_multiple m i 1))
  obtain ⟨hp,hl,hu⟩ := tuple_pinching m i
  obtain ⟨h2,h1,h0⟩ := product_inequalities _ _ _ ha hb hp hl hu
  exact no_product_relation _ _ (by change tuple m i (Fin.last 3) = 1; simp only [tuple, Fin.snoc_last]) h0 h1 h2

/-- Primitive quartic representations with neither an additive-triple relation
nor a product relation in any coordinate ordering. -/
def coreCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun a : Fin 4 → Fin (n+1) ↦
    (∑ i, (a i : ℕ)^4=n) ∧ Finset.univ.gcd (fun i ↦ (a i : ℕ))=1 ∧
      ¬HasAdditiveTriple a ∧ ¬HasProductRelation a)).card

theorem core_count_lower (m : ℕ) :
    m+1 ≤ coreCount (representedNumber m) := by
  classical
  unfold coreCount
  have hc := Finset.card_le_card_of_injOn (boundedTuple m) (s := Finset.univ)
    (t := Finset.univ.filter (fun a : Fin 4 → Fin (representedNumber m+1) ↦
      (∑ i, (a i : ℕ)^4=representedNumber m) ∧
        Finset.univ.gcd (fun i ↦ (a i : ℕ))=1 ∧
          ¬HasAdditiveTriple a ∧ ¬HasProductRelation a))
    (by
      intro i _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨tuple_sum m i, tuple_gcd m i, boundedTuple_nonadditive m i,
        boundedTuple_nonmultiplicative m i⟩)
    (boundedTuple_injective m).injOn
  simpa using hc

theorem core_counts_exceed_any_bound (M : ℕ) :
    {n : ℕ | M < coreCount n}.Infinite := by
  intro hf
  let C := hf.toFinset.sup coreCount
  let m := M+C
  have hc := core_count_lower m
  have hm : M < coreCount (representedNumber m) := by omega
  have hn : representedNumber m ∈ hf.toFinset := hf.mem_toFinset.mpr hm
  have hu : coreCount (representedNumber m) ≤ C := Finset.le_sup hn
  omega

open MomentReduction PrimitiveNonadditiveReduction

theorem coreCount_le_primitiveNonadditiveCount (n : ℕ) :
    coreCount n ≤ primitiveNonadditiveCount n := by
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact ⟨ha.1,ha.2.1,ha.2.2.1⟩

theorem primitive_nonadditive_le_multiplicative_add_core (n : ℕ) :
    primitiveNonadditiveCount n ≤ multiplicativeQuarticCount n+coreCount n := by
  classical
  let S := Finset.univ.filter (fun a : Fin 4 → Fin (n+1) ↦
    (∑ i, (a i : ℕ)^4=n) ∧ Finset.univ.gcd (fun i ↦ (a i : ℕ))=1 ∧
      ¬HasAdditiveTriple a)
  have hs : (S.filter HasProductRelation).card ≤ multiplicativeQuarticCount n := by
    apply Finset.card_le_card
    intro a ha
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
    exact ⟨ha.1.1,ha.2⟩
  have ht : (S.filter (fun a ↦ ¬HasProductRelation a)).card=coreCount n := by
    unfold S coreCount
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hp := Finset.card_filter_add_card_filter_not (s := S) HasProductRelation
  rw [ht] at hp
  change S.card ≤ _
  omega

/-- A subpolynomial bound for this smaller core would suffice to disprove the
quartic case. No such bound is asserted here. -/
theorem core_bound_iff_full_bound :
    Subpolynomial coreCount ↔ Subpolynomial (representationCount 4) := by
  constructor
  · intro h
    apply primitive_nonadditive_bound_iff_full_bound.mp
    intro ε hε
    obtain ⟨A,hA,ha⟩ := h ε hε
    obtain ⟨B,hB,hb⟩ := multiplicative_quartic_subpolynomial ε hε
    refine ⟨B+A,add_pos hB hA,fun n hn ↦ ?_⟩
    have hle : (primitiveNonadditiveCount n : ℝ) ≤
        (multiplicativeQuarticCount n : ℝ)+coreCount n := by
      exact_mod_cast primitive_nonadditive_le_multiplicative_add_core n
    calc
      (primitiveNonadditiveCount n : ℝ) ≤
          (multiplicativeQuarticCount n : ℝ)+coreCount n := hle
      _ ≤ B*(n : ℝ)^ε+A*(n : ℝ)^ε := add_le_add (hb n (by omega)) (ha n hn)
      _ = (B+A)*(n : ℝ)^ε := by ring
  · intro h ε hε
    obtain ⟨C,hC,hb⟩ := primitive_nonadditive_bound_iff_full_bound.mpr h ε hε
    refine ⟨C,hC,fun n hn ↦ ?_⟩
    have hle : (coreCount n : ℝ) ≤ primitiveNonadditiveCount n := by
      exact_mod_cast coreCount_le_primitiveNonadditiveCount n
    exact hle.trans (hb n hn)

/-- Removing common factors and both exceptional relations preserves the
existence of positive-power peaks. Neither side of the equivalence is proved. -/
theorem quartic_peaks_iff_core_peaks :
    (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < representationCount 4 n}.Infinite) ↔
    (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < coreCount n}.Infinite) := by
  apply not_iff_not.mp
  exact (no_polynomial_peaks_iff_uniform_bound (representationCount 4)).trans
    (core_bound_iff_full_bound.symm.trans
      (no_polynomial_peaks_iff_uniform_bound coreCount).symm)

theorem quartic_subpolynomial_iff_core_moments :
    Subpolynomial (representationCount 4) ↔ QuadraticMoments coreCount :=
  core_bound_iff_full_bound.symm.trans (subpolynomial_iff_quadratic_moments coreCount)

end QuarticCore

end Erdos322
