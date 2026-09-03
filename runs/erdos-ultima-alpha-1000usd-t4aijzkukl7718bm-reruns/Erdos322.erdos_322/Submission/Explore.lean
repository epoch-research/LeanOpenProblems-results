import FormalConjecturesUtil

/-! The cubic case of the representation problem, using Mahler's identity. -/
namespace Erdos322Partial

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
    convert Real.pow_rpow_inv_natCast hm0 (by decide : 24 ≠ 0) using 1 <;> norm_num
  rw [heq] at hr
  simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using hr

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

end Erdos322Partial
