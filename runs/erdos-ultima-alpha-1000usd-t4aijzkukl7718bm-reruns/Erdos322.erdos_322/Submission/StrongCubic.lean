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

private def boundedTriple (m : ℕ) (a : Fin m) : Fin 3 → Fin ((3 * m) ^ 12 + 1) :=
  fun i ↦ ⟨triple m a i, by
    have h := triple_sum m a (Nat.le_of_lt a.isLt)
    have hi : triple m a i ^ 3 ≤ ∑ j, triple m a j ^ 3 :=
      Finset.single_le_sum (f := fun j : Fin 3 ↦ triple m a j ^ 3)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hle : triple m a i ≤ triple m a i ^ 3 := Nat.le_pow (by decide)
    omega⟩

private theorem boundedTriple_injective (m : ℕ) :
    Function.Injective (boundedTriple m) := by
  intro a b h
  have h₀ := congrArg (fun f ↦ ((f 0 : Fin ((3 * m) ^ 12 + 1)) : ℕ)) h
  change 9 * (a : ℕ) ^ 4 = 9 * (b : ℕ) ^ 4 at h₀
  have hp : (a : ℕ) ^ 4 = (b : ℕ) ^ 4 := by omega
  apply Fin.ext
  exact Nat.pow_left_injective (by decide : 4 ≠ 0) hp

/-- Mahler's identity gives a linear number of representations at these twelfth powers. -/
theorem cubic_count_lower (m : ℕ) :
    m ≤ representationCount 3 ((3 * m) ^ 12) := by
  classical
  unfold representationCount
  have h := Finset.card_le_card_of_injOn (boundedTriple m)
    (s := Finset.univ)
    (t := Finset.univ.filter (fun a : Fin 3 → Fin ((3 * m) ^ 12 + 1) ↦
      ∑ i, (a i : ℕ) ^ 3 = (3 * m) ^ 12))
    (by
      intro a _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact triple_sum m a (Nat.le_of_lt a.isLt))
    (boundedTriple_injective m).injOn
  simpa using h

private theorem cubic_rpow_lt (m : ℕ) (hm : 4 ≤ m) :
    (((3 * m) ^ 12 : ℕ) : ℝ) ^ (1 / 24 : ℝ) < m := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hbase : 3 * (m : ℝ) < (m : ℝ) ^ 2 := by nlinarith
  have hpow : (3 * (m : ℝ)) ^ 12 < ((m : ℝ) ^ 2) ^ 12 :=
    pow_lt_pow_left₀ hbase (by positivity) (by decide)
  rw [← pow_mul] at hpow
  have hr := Real.rpow_lt_rpow (by positivity : (0 : ℝ) ≤ (3 * (m : ℝ)) ^ 12)
    hpow (by norm_num : (0 : ℝ) < 1 / 24)
  have heq : ((m : ℝ) ^ 24) ^ (1 / 24 : ℝ) = (m : ℝ) := by
    convert Real.pow_rpow_inv_natCast hm0 (by decide : 24 ≠ 0) using 1
    norm_num
  rw [heq] at hr
  simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using hr

/-- The conjecture for the exponent `k = 3`. -/
theorem cubic_case : ∃ c > (0 : ℝ),
    {n : ℕ | (n : ℝ) ^ c < representationCount 3 n}.Infinite := by
  refine ⟨1 / 24, by norm_num, ?_⟩
  have hinj : Function.Injective (fun m : ℕ ↦ (3 * (m + 4)) ^ 12) := by
    intro a b h
    have h' := Nat.pow_left_injective (by decide : 12 ≠ 0) h
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro n ⟨m, rfl⟩
  change (((3 * (m + 4)) ^ 12 : ℕ) : ℝ) ^ (1 / 24 : ℝ) < _
  have hcount : ((m + 4 : ℕ) : ℝ) ≤ representationCount 3 ((3 * (m + 4)) ^ 12) := by
    exact_mod_cast cubic_count_lower (m + 4)
  exact (cubic_rpow_lt (m + 4) (by omega)).trans_le hcount


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

end Erdos322
