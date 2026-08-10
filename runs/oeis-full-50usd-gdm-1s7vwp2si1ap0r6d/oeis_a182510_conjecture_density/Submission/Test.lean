import FormalConjectures.Util.ProblemImports

open Set Filter Topology

#check Nat.ncard_Iio
/--
A182510: $a(0)=0, a(1)=1, a(n)=(a(n-1) \text{ XOR } n) - a(n-2)$, where $\text{XOR}$ is the bitwise exclusive-or operator.
-/
def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => Int.xor (a (n + 1)) (n + 2 : ℤ) - a n


theorem density_le_of_bounded_diff {S T : Set ℕ} {d_S d_T : ℝ} (hS : S.HasDensity d_S) (hT : T.HasDensity d_T)
    (C : ℝ) (h_bound : ∀ b : ℕ, ((S ∩ Iio b).ncard : ℝ) ≤ ((T ∩ Iio b).ncard : ℝ) + C) :
    d_S ≤ d_T := by
  have h_partial (U : Set ℕ) (b : ℕ) : U.partialDensity Set.univ b = ((U ∩ Iio b).ncard : ℝ) / b := by
    unfold Set.partialDensity
    rw [Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  have h_lim : Tendsto (fun b : ℕ => T.partialDensity Set.univ b + C / b) atTop (𝓝 d_T) := by
    have h_add := Tendsto.add hT (tendsto_const_div_atTop_nhds_zero_nat C)
    rw [add_zero] at h_add
    exact h_add
  apply le_of_tendsto_of_tendsto hS h_lim
  filter_upwards [eventually_ge_atTop 1] with b hb
  rw [h_partial S b, h_partial T b]
  have h_b_pos : (b : ℝ) > 0 := Nat.cast_pos.mpr hb
  have h_ne : (b : ℝ) ≠ 0 := ne_of_gt h_b_pos
  rw [div_le_iff₀ h_b_pos]
  rw [add_mul, div_mul_cancel₀ _ h_ne, div_mul_cancel₀ _ h_ne]
  exact h_bound b









#check Int.xor
#eval Int.xor 3 5
#eval Int.xor (-3) 5
#eval (Int.xor 3 5) % 2 == (3 + 5) % 2
#eval (Int.xor (-3) 5) % 2 == ((-3) + 5) % 2
#eval (Int.xor 3 (-5)) % 2 == (3 + (-5)) % 2
#eval (Int.xor (-3) (-5)) % 2 == ((-3) + (-5)) % 2
#eval (Int.xor 4 6) % 2 == (4 + 6) % 2
#eval (Int.xor (-4) 6) % 2 == ((-4) + 6) % 2

def f (n : ℕ) : ℕ :=
  if n % 6 < 3 then n + 3 else n - 3

theorem f_f (n : ℕ) : f (f n) = n := by
  unfold f
  split_ifs <;> omega

theorem f_inj : Function.Injective f := by
  intro x y h
  have h2 := congr_arg f h
  rw [f_f, f_f] at h2
  exact h2

theorem f_lt_six_mul {K n : ℕ} (h : n < 6 * K) : f n < 6 * K := by
  unfold f
  split_ifs <;> omega

theorem bodd_eq_mod_two (x : ℤ) : x % 2 = if Int.bodd x then 1 else 0 := by
  sorry

open Int

theorem testBit_zero (n : ℤ) : testBit n 0 = bodd n := by
  have h := testBit_bit_zero (bodd n) (div2 n)
  rw [bit_decomp] at h
  exact h

theorem bodd_xor (x y : ℤ) : Int.bodd (Int.xor x y) = Bool.xor (Int.bodd x) (Int.bodd y) := by
  rw [← testBit_zero (Int.xor x y)]
  rw [testBit_lxor]
  rw [testBit_zero x, testBit_zero y]

theorem bodd_sub (x y : ℤ) : bodd (x - y) = Bool.xor (bodd x) (bodd y) := by
  rw [sub_eq_add_neg, bodd_add, bodd_neg]

def p (n : ℕ) : Bool :=
  match n % 6 with
  | 0 => false
  | 1 => true
  | 2 => true
  | 3 => true
  | 4 => false
  | _ => false

theorem bodd_coe_nat (n : ℕ) : bodd (n : ℤ) = n.bodd := by rfl

theorem bodd_eq_bodd_mod_six (n : ℕ) : Nat.bodd n = Nat.bodd (n % 6) := by
  have h_div : n = 6 * (n / 6) + (n % 6) := (Nat.div_add_mod n 6).symm
  nth_rw 1 [h_div]
  rw [Nat.bodd_add, Nat.bodd_mul]
  simp

theorem bodd_add_six_mul (m k : ℕ) : Nat.bodd (6 * m + k) = Nat.bodd k := by
  rw [Nat.bodd_add, Nat.bodd_mul]
  simp

theorem add_six_mul_mod (m k : ℕ) : (6 * m + k) % 6 = k % 6 := by
  rw [add_comm, Nat.add_mul_mod_self_left]

theorem p_add_six_mul (m k : ℕ) : p (6 * m + k) = p k := by
  unfold p
  rw [add_six_mul_mod]

theorem add_six_mul_assoc (m a b : ℕ) : 6 * m + a + b = 6 * m + (a + b) := by omega


theorem a_bodd_and_next (n : ℕ) : bodd (a n) = p n ∧ bodd (a (n + 1)) = p (n + 1) := by
  induction n with
  | zero =>
    simp [a, p]
  | succ n ih =>
    rcases ih with ⟨ih1, ih2⟩
    refine ⟨ih2, ?_⟩
    have h_coe : (n + 2 : ℤ) = ↑(n + 2) := by push_cast; rfl
    have h_a_succ2 : a (n + 2) = Int.xor (a (n + 1)) (n + 2 : ℤ) - a n := by rfl
    rw [h_a_succ2, h_coe, bodd_sub, bodd_xor, ih1, ih2, bodd_coe_nat (n + 2)]
    unfold p
    have h_mod : n % 6 < 6 := Nat.mod_lt _ (by decide)
    interval_cases h : n % 6
    all_goals
      have h_div : n = 6 * (n / 6) + (n % 6) := (Nat.div_add_mod n 6).symm
      rw [h] at h_div
      rw [h_div]
      repeat rw [add_six_mul_assoc]
      simp [p_add_six_mul, bodd_add_six_mul]




theorem a_add_a_add_three (n : ℕ) :
    a (n + 3) + a n = (Int.xor (a (n + 1)) (n + 2 : ℤ) - a (n + 1)) + (Int.xor (a (n + 2)) (n + 3 : ℤ) - a (n + 2)) := by
  have h2 : a (n + 2) = Int.xor (a (n + 1)) (n + 2 : ℤ) - a n := by rfl
  have h3 : a (n + 3) = Int.xor (a (n + 2)) (n + 3 : ℤ) - a (n + 1) := by rfl
  omega




theorem test_three (b : ℕ) : (Iio b \ Iio (b - 3)).ncard ≤ 3 := by
  have h_sub : Iio (b - 3) ⊆ Iio b := by
    rintro n (hn : n < b - 3)
    exact hn.trans_le (Nat.sub_le b 3)
  rw [Set.ncard_diff h_sub (Set.finite_Iio (b - 3))]
  rw [Nat.ncard_Iio, Nat.ncard_Iio]
  omega


def f (n : ℕ) : ℕ :=
  if n % 6 < 3 then n + 3 else n - 3

def E : Set ℕ := {n : ℕ | a n > 0 ∧ a (f n) ≥ 0}

theorem a_add_a_add_three_le (n : ℕ) : a (n + 3) + a n ≤ 2 * n + 5 := by
  have h := a_add_a_add_three n
  have h1 := Int.xor_le_add (a (n + 1)) (n + 2)
  have h2 := Int.xor_le_add (a (n + 2)) (n + 3)
  push_cast at *
  omega

theorem E_sub : E ⊆ {n : ℕ | 0 < a n ∧ a n ≤ 2 * n + 5} := by
  rintro n ⟨hn1, hn2⟩
  refine ⟨hn1, ?_⟩
  unfold f at hn2
  split_ifs at hn2 with h
  · have h_le := a_add_a_add_three_le n
    omega
  · have h_ge : n ≥ 3 := by
      by_contra h_lt
      have h_mod : n % 6 = n := Nat.mod_eq_of_lt (by omega)
      have h_cond : n % 6 < 3 := by omega
      exact h h_cond
    have h_sub_add : n - 3 + 3 = n := Nat.sub_add_cancel h_ge
    have h_le := a_add_a_add_three_le (n - 3)
    rw [h_sub_add] at h_le
    omega

