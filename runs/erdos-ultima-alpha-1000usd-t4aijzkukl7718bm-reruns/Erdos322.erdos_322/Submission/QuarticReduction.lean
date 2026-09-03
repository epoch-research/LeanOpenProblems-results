import FormalConjecturesUtil

/-! A local restriction on quartic representations. -/
namespace Erdos322Research

def representationCount (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k → Fin (n + 1))).filter
    (fun a ↦ ∑ i, (a i : ℕ) ^ k = n)).card

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


end Erdos322Research
