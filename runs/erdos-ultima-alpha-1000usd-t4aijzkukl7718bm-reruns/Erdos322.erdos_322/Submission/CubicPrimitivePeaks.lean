import FormalConjecturesUtil

/-! Primitive positive cubic power peaks from the Mahler family.
This addresses only the cubic case, not the universal conjecture. -/
namespace Erdos322Research.CubicPrimitivePeaks
noncomputable section
open scoped Classical

/-- Ordered positive cubic representations with no common divisor other than one. -/
def primitivePositiveCount (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin 3 → Fin (n + 1))).filter
    (fun a ↦ (∑ i, (a i : ℕ) ^ 3) = n ∧ (∀ i, 0 < (a i : ℕ)) ∧
      ∀ d : ℕ, (∀ i, d ∣ (a i : ℕ)) → d = 1)).card

private def triple (m a : ℕ) : Fin 3 → ℕ :=
  ![a ^ 4, 9 * a * m ^ 3 - a ^ 4, 9 * m ^ 4 - 3 * a ^ 3 * m]

private lemma sub_bounds (m a : ℕ) (ha : a ≤ m) :
    a ^ 4 ≤ 9 * a * m ^ 3 ∧ 3 * a ^ 3 * m ≤ 9 * m ^ 4 := by
  have hp : a ^ 3 ≤ m ^ 3 := Nat.pow_le_pow_left ha 3
  constructor
  · calc
      a ^ 4 = a * a ^ 3 := by ring
      _ ≤ a * m ^ 3 := Nat.mul_le_mul_left _ hp
      _ ≤ 9 * a * m ^ 3 := by nlinarith [Nat.zero_le (a * m ^ 3)]
  · calc
      3 * a ^ 3 * m ≤ 3 * m ^ 3 * m := by gcongr
      _ ≤ 9 * m ^ 4 := by nlinarith [Nat.zero_le (m ^ 4)]

private lemma triple_sum (m a : ℕ) (ha : a ≤ m) :
    ∑ i, triple m a i ^ 3 = 729 * m ^ 12 := by
  obtain ⟨h₁, h₂⟩ := sub_bounds m a ha
  simp [Fin.sum_univ_three, triple]
  zify [h₁, h₂]
  ring

private lemma triple_positive (m a : ℕ) (ha0 : 0 < a) (ha : a ≤ m) :
    ∀ i, 0 < triple m a i := by
  have hm : 0 < m := ha0.trans_le ha
  have hp : a ^ 3 ≤ m ^ 3 := Nat.pow_le_pow_left ha 3
  have h₁ : a ^ 4 ≤ a * m ^ 3 := by
    calc
      a ^ 4 = a * a ^ 3 := by ring
      _ ≤ a * m ^ 3 := Nat.mul_le_mul_left _ hp
  have h₂ : 3 * a ^ 3 * m ≤ 3 * m ^ 4 := by
    calc
      3 * a ^ 3 * m ≤ 3 * m ^ 3 * m := by gcongr
      _ = 3 * m ^ 4 := by ring
  intro i
  fin_cases i
  · change 0 < a ^ 4
    exact pow_pos ha0 _
  · change 0 < 9 * a * m ^ 3 - a ^ 4
    apply Nat.sub_pos_of_lt
    have : 0 < a * m ^ 3 := by positivity
    nlinarith
  · change 0 < 9 * m ^ 4 - 3 * a ^ 3 * m
    apply Nat.sub_pos_of_lt
    have : 0 < m ^ 4 := by positivity
    nlinarith

private lemma first_lt_last (m a b : ℕ) (hm : 0 < m) (ha : a ≤ m) (hb : b ≤ m) :
    triple m a 0 < triple m b 2 := by
  have hf : triple m a 0 ≤ m ^ 4 := Nat.pow_le_pow_left ha 4
  have hl : 6 * m ^ 4 ≤ triple m b 2 := by
    change 6 * m ^ 4 ≤ 9 * m ^ 4 - 3 * b ^ 3 * m
    apply Nat.le_sub_of_add_le
    calc
      6 * m ^ 4 + 3 * b ^ 3 * m ≤ 6 * m ^ 4 + 3 * m ^ 3 * m := by gcongr
      _ = 9 * m ^ 4 := by ring
  have : 0 < m ^ 4 := pow_pos hm _
  omega

private def sample (r : ℕ) (a : Fin (3 ^ r) × Fin 2) : ℕ :=
  3 * (a.1 : ℕ) + (a.2 : ℕ) + 1

private lemma sample_bounds (r : ℕ) (a : Fin (3 ^ r) × Fin 2) :
    0 < sample r a ∧ sample r a ≤ 3 ^ (r + 1) := by
  have h₁ := a.1.isLt
  have h₂ := a.2.isLt
  simp only [sample, pow_succ]
  omega

private lemma sample_coprime (r : ℕ) (a : Fin (3 ^ r) × Fin 2) :
    Nat.Coprime (sample r a) 3 := by
  apply Nat.Coprime.symm
  apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr
  have h := a.2.isLt
  dsimp [sample]
  omega

private lemma sample_injective (r : ℕ) : Function.Injective (sample r) := by
  rintro ⟨a, s⟩ ⟨b, t⟩ h
  have hs := s.isLt
  have ht := t.isLt
  dsimp [sample] at h
  apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega

private lemma triple_coprime (r : ℕ) (a : Fin (3 ^ r) × Fin 2) :
    Nat.Coprime (triple (3 ^ (r + 1)) (sample r a) 0)
      (triple (3 ^ (r + 1)) (sample r a) 2) := by
  let m := 3 ^ (r + 1)
  let b := sample r a
  have hc : Nat.Coprime b 3 := sample_coprime r a
  have hb : b ≤ m := (sample_bounds r a).2
  have hd : b ∣ 3 * b ^ 3 * m := by
    refine ⟨3 * b ^ 2 * m, ?_⟩
    ring
  have he := (sub_bounds m b hb).2
  have hcop : Nat.Coprime b (9 * m ^ 4) := by
    exact (show Nat.Coprime b 9 by simpa using hc.pow_right 2).mul_right
      ((hc.pow_right (r + 1)).pow_right 4)
  have hcop' : Nat.Coprime b (9 * m ^ 4 - 3 * b ^ 3 * m) := by
    apply (Nat.coprime_add_iff_left hd).mp
    rw [Nat.sub_add_cancel he]
    exact hcop
  exact hcop'.pow_left 4


private abbrev Index (r : ℕ) := (Fin (3 ^ r) × Fin 2) × Fin 3

private def rotated (r : ℕ) (a : Index r) (i : Fin 3) : ℕ :=
  triple (3 ^ (r + 1)) (sample r a.1) (i + a.2)

private lemma rotated_sum (r : ℕ) (a : Index r) :
    ∑ i, rotated r a i ^ 3 = 729 * (3 ^ (r + 1)) ^ 12 := by
  rcases a with ⟨a, j⟩
  have ht := triple_sum (3 ^ (r + 1)) (sample r a) (sample_bounds r a).2
  simp only [Fin.sum_univ_three] at ht ⊢
  fin_cases j <;> dsimp [rotated, Fin.add_def] <;> omega

private lemma rotated_positive (r : ℕ) (a : Index r) (i : Fin 3) :
    0 < rotated r a i :=
  triple_positive _ _ (sample_bounds r a.1).1 (sample_bounds r a.1).2 _

private lemma rotated_primitive (r : ℕ) (a : Index r) (d : ℕ)
    (hd : ∀ i, d ∣ rotated r a i) : d = 1 := by
  have h₀ : d ∣ triple (3 ^ (r + 1)) (sample r a.1) 0 := by
    simpa [rotated] using hd (0 - a.2)
  have h₂ : d ∣ triple (3 ^ (r + 1)) (sample r a.1) 2 := by
    simpa [rotated] using hd (2 - a.2)
  have h := Nat.dvd_gcd h₀ h₂
  rw [(triple_coprime r a.1).gcd_eq_one] at h
  exact Nat.dvd_one.mp h

private lemma rotated_injective (r : ℕ) : Function.Injective (rotated r) := by
  rintro ⟨a, j⟩ ⟨b, l⟩ h
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  have h₂ := congrFun h 2
  have hab := first_lt_last (3 ^ (r + 1)) (sample r a) (sample r b)
    (by positivity) (sample_bounds r a).2 (sample_bounds r b).2
  have hba := first_lt_last (3 ^ (r + 1)) (sample r b) (sample r a)
    (by positivity) (sample_bounds r b).2 (sample_bounds r a).2
  fin_cases j <;> fin_cases l <;>
    dsimp [rotated, Fin.add_def] at h₀ h₁ h₂
  all_goals try omega
  all_goals
    refine Prod.ext ?_ rfl
    apply sample_injective r
    simp [triple] at h₀ h₁ h₂
    assumption

private def boundedRotated (r : ℕ) (a : Index r) :
    Fin 3 → Fin (729 * (3 ^ (r + 1)) ^ 12 + 1) :=
  fun i ↦ ⟨rotated r a i, by
    have h := rotated_sum r a
    have hi : rotated r a i ^ 3 ≤ ∑ j, rotated r a j ^ 3 :=
      Finset.single_le_sum (f := fun j ↦ rotated r a j ^ 3)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hl : rotated r a i ≤ rotated r a i ^ 3 := Nat.le_pow (by decide)
    omega⟩

/-- A linear number of primitive, strictly positive representations at each
of these explicitly specified targets. -/
theorem primitive_count_lower (r : ℕ) :
    2 * 3 ^ (r + 1) ≤ primitivePositiveCount (729 * (3 ^ (r + 1)) ^ 12) := by
  unfold primitivePositiveCount
  have h := Finset.card_le_card_of_injOn (boundedRotated r)
    (s := Finset.univ)
    (t := Finset.univ.filter (fun a : Fin 3 → Fin (729 * (3 ^ (r + 1)) ^ 12 + 1) ↦
      (∑ i, (a i : ℕ) ^ 3) = 729 * (3 ^ (r + 1)) ^ 12 ∧
      (∀ i, 0 < (a i : ℕ)) ∧ ∀ d : ℕ, (∀ i, d ∣ (a i : ℕ)) → d = 1))
    (by
      intro a _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨rotated_sum r a, rotated_positive r a, rotated_primitive r a⟩)
    (by
      intro a _ b _ he
      apply rotated_injective r
      funext i
      exact congrArg Fin.val (congrFun he i))
  simpa [Index, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

/-- The same exponent as in the unrestricted cubic result remains valid even
when every coordinate is positive and the common gcd is one. -/
theorem primitive_exponent_one_twelfth :
    {n : ℕ | (n : ℝ) ^ (1 / 12 : ℝ) < primitivePositiveCount n}.Infinite := by
  have hinj : Function.Injective (fun r : ℕ ↦ 729 * (3 ^ (r + 1)) ^ 12) := by
    intro a b h
    have hp := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 729) h
    have he := Nat.pow_left_injective (by decide : 12 ≠ 0) hp
    have hr := Nat.pow_right_injective (by decide : 2 ≤ 3) he
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro n ⟨r, rfl⟩
  have hm : 0 < 3 ^ (r + 1) := by positivity
  have hlt : 729 * (3 ^ (r + 1)) ^ 12 < (2 * 3 ^ (r + 1)) ^ 12 := by
    rw [mul_pow]
    exact Nat.mul_lt_mul_of_pos_right (by decide : 729 < 2 ^ 12) (pow_pos hm _)
  have hreal := Real.rpow_lt_rpow
    (by positivity : (0 : ℝ) ≤ (729 * (3 ^ (r + 1)) ^ 12 : ℕ))
    (by exact_mod_cast hlt : ((729 * (3 ^ (r + 1)) ^ 12 : ℕ) : ℝ) <
      (((2 * 3 ^ (r + 1)) ^ 12 : ℕ) : ℝ))
    (by norm_num : (0 : ℝ) < (1 / 12 : ℝ))
  have hroot : ((((2 * 3 ^ (r + 1)) ^ 12 : ℕ) : ℝ)) ^ (1 / 12 : ℝ) =
      ((2 * 3 ^ (r + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    convert Real.pow_rpow_inv_natCast (Nat.cast_nonneg (2 * 3 ^ (r + 1)))
      (by decide : 12 ≠ 0) using 1
    norm_num
  rw [hroot] at hreal
  exact hreal.trans_le (by exact_mod_cast primitive_count_lower r)

end
end Erdos322Research.CubicPrimitivePeaks
