import FormalConjecturesUtil

/-! A bounded-slope deficit with savings on every dyadic scale.
This module proves numerical estimates only, not a cycle decomposition theorem. -/
open scoped BigOperators
namespace Erdos184.LogDeficit

noncomputable def weight (j : ℕ) : ℝ := 1 / (((j : ℝ)+1)*((j : ℝ)+2))

lemma weight_nonneg (j : ℕ) : 0 ≤ weight j := by unfold weight; positivity

lemma weight_telescope (j : ℕ) :
    weight j = 1/((j : ℝ)+1) - 1/((j : ℝ)+2) := by
  unfold weight
  have h1 : (j : ℝ)+1 ≠ 0 := by positivity
  have h2 : (j : ℝ)+2 ≠ 0 := by positivity
  field_simp
  ring

lemma sum_weight (r : ℕ) :
    (∑ j ∈ Finset.range r, weight j) = 1 - 1/((r : ℝ)+1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ,ih,weight_telescope]
    push_cast
    ring

lemma summable_weight : Summable weight := by
  apply summable_of_sum_range_le weight_nonneg (c := 1)
  intro r
  rw [sum_weight]
  have h : 0 ≤ 1/((r : ℝ)+1) := by positivity
  linarith

lemma tsum_weight_le : (∑' j, weight j) ≤ 1 := by
  apply Real.tsum_le_of_sum_range_le weight_nonneg
  intro r
  rw [sum_weight]
  have h : 0 ≤ 1/((r : ℝ)+1) := by positivity
  linarith

noncomputable def term (n j : ℕ) : ℝ := (min n (2^j) : ℕ) * weight j
noncomputable def deficit (n : ℕ) : ℝ := ∑' j, term n j
noncomputable def charge (n : ℕ) : ℝ := 2*n - deficit n
noncomputable def budget (C n : ℕ) : ℕ := ⌊(C : ℝ) * charge n⌋₊

lemma term_nonneg (n j : ℕ) : 0 ≤ term n j := by
  exact mul_nonneg (Nat.cast_nonneg _) (weight_nonneg _)

lemma summable_term (n : ℕ) : Summable (term n) := by
  apply (summable_weight.mul_left (n : ℝ)).of_nonneg_of_le (term_nonneg n)
  intro j
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_left n (2^j))
    (weight_nonneg j)

lemma deficit_nonneg (n : ℕ) : 0 ≤ deficit n := tsum_nonneg (term_nonneg n)

lemma deficit_le (n : ℕ) : deficit n ≤ n := by
  calc
    deficit n ≤ ∑' j, (n : ℝ)*weight j :=
      (summable_term n).tsum_le_tsum (fun j =>
        mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_left n (2^j))
          (weight_nonneg j)) (summable_weight.mul_left _)
    _ = (n : ℝ)*(∑' j, weight j) := tsum_mul_left
    _ ≤ (n : ℝ)*1 := mul_le_mul_of_nonneg_left tsum_weight_le (Nat.cast_nonneg n)
    _ = n := mul_one _

lemma deficit_increment {a b : ℕ} (hab : a ≤ b) :
    deficit b ≤ deficit a + (b-a : ℕ) := by
  have h (j : ℕ) : term b j ≤ term a j + (b-a : ℕ)*weight j := by
    have hm : min b (2^j) ≤ min a (2^j) + (b-a) := by omega
    have hh := mul_le_mul_of_nonneg_right
      (show (min b (2^j) : ℝ) ≤ (min a (2^j) : ℝ)+(b-a : ℕ) by exact_mod_cast hm)
      (weight_nonneg j)
    simpa only [term,Nat.cast_min,Nat.cast_pow,Nat.cast_ofNat,add_mul] using hh
  calc
    deficit b ≤ ∑' j, (term a j + (b-a : ℕ)*weight j) :=
      (summable_term b).tsum_le_tsum h ((summable_term a).add (summable_weight.mul_left _))
    _ = deficit a + (b-a : ℕ)*(∑' j, weight j) := by
      rw [(summable_term a).tsum_add (summable_weight.mul_left _),tsum_mul_left]
      rfl
    _ ≤ deficit a + (b-a : ℕ)*1 := by
      gcongr
      exact tsum_weight_le
    _ = _ := by rw [mul_one]

lemma le_charge (n : ℕ) : (n : ℝ) ≤ charge n := by
  dsimp [charge]
  linarith [deficit_le n]

lemma charge_nonneg (n : ℕ) : 0 ≤ charge n := (Nat.cast_nonneg n).trans (le_charge n)

lemma charge_le (n : ℕ) : charge n ≤ 2*n := by
  dsimp [charge]
  linarith [deficit_nonneg n]

lemma charge_increment {a b : ℕ} (hab : a ≤ b) :
    charge a + (b-a : ℕ) ≤ charge b := by
  have h := deficit_increment hab
  have hn : (b : ℝ) = (a : ℝ)+(b-a : ℕ) := by
    exact_mod_cast (Nat.add_sub_of_le hab).symm
  dsimp [charge]
  linarith

lemma charge_mono : Monotone charge := by
  intro a b hab
  have hn : (0 : ℝ) ≤ (b-a : ℕ) := Nat.cast_nonneg _
  linarith [charge_increment hab]

lemma mul_le_budget (C n : ℕ) : C*n ≤ budget C n := by
  apply Nat.le_floor
  have h := mul_le_mul_of_nonneg_left (le_charge n) (Nat.cast_nonneg C)
  exact_mod_cast h

lemma budget_le (C n : ℕ) : budget C n ≤ 2*C*n := by
  apply Nat.floor_le_of_le
  have h := mul_le_mul_of_nonneg_left (charge_le n) (Nat.cast_nonneg C)
  push_cast
  nlinarith

lemma budget_mono (C : ℕ) : Monotone (budget C) := by
  intro a b hab
  exact Nat.floor_mono (mul_le_mul_of_nonneg_left (charge_mono hab) (Nat.cast_nonneg C))

lemma budget_succ (C n : ℕ) : budget C n + C ≤ budget C (n+1) := by
  apply Nat.le_floor
  have hfloor := Nat.floor_le (mul_nonneg (Nat.cast_nonneg C) (charge_nonneg n))
  have hi := mul_le_mul_of_nonneg_left (charge_increment (Nat.le_succ n)) (Nat.cast_nonneg C)
  simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel_left,Nat.cast_one] at hi
  push_cast
  dsimp only [budget] at *
  linarith

/-- Every dyadic scale below both sides contributes a positive concavity gap. -/
lemma dyadic_gap {a b n j : ℕ} (hn : n ≤ a+b)
    (ha : 2^j ≤ a) (hb : 2^j ≤ b) :
    (2^j : ℕ)*weight j ≤ deficit a + deficit b - deficit n := by
  let f (i : ℕ) : ℝ := term a i + term b i - term n i
  have hf : Summable f := ((summable_term a).add (summable_term b)).sub (summable_term n)
  have hnonneg (i : ℕ) : 0 ≤ f i := by
    have hm : min n (2^i) ≤ min a (2^i) + min b (2^i) := by
      have hpos : 0 ≤ (2 : ℕ)^i := Nat.zero_le _
      omega
    have hmul := mul_le_mul_of_nonneg_right
      (show (min n (2^i) : ℝ) ≤ (min a (2^i) : ℝ)+(min b (2^i) : ℝ) by exact_mod_cast hm)
      (weight_nonneg i)
    dsimp [f,term]
    push_cast
    linarith
  have hj : (2^j : ℕ)*weight j ≤ f j := by
    have hm : (min n (2^j) : ℝ) ≤ (2^j : ℕ) := by exact_mod_cast min_le_right n (2^j)
    have hmul := mul_le_mul_of_nonneg_right hm (weight_nonneg j)
    dsimp [f,term]
    rw [min_eq_right ha,min_eq_right hb]
    push_cast at *
    linarith
  calc
    (2^j : ℕ)*weight j ≤ f j := hj
    _ ≤ ∑' i, f i := hf.le_tsum j (fun i _ => hnonneg i)
    _ = deficit a + deficit b - deficit n := by
      change (∑' i, (term a i + term b i - term n i)) = _
      rw [((summable_term a).add (summable_term b)).tsum_sub (summable_term n),
        (summable_term a).tsum_add (summable_term b)]
      rfl

/-- Floors cost no extra rounding error when two integer bounds are combined. -/
lemma separator_budget {C a b n s p t j : ℕ} (hC : 0 < C)
    (hlo : n ≤ a+b) (hhi : a+b ≤ n+s) (hp : p ≤ C*t)
    (ha : 2^j ≤ a) (hb : 2^j ≤ b)
    (hs : (3*s+t : ℕ) ≤ (2^j : ℕ)*weight j) :
    budget C a + budget C b + (s-1) + p ≤ budget C n := by
  have hg := dyadic_gap hlo ha hb
  have hsum : (a : ℝ)+b ≤ n+s := by exact_mod_cast hhi
  have hdiff : charge a + charge b + (s : ℝ)+t ≤ charge n := by
    dsimp only [charge]
    push_cast at hs hg
    linarith
  have hfa := Nat.floor_le (mul_nonneg (Nat.cast_nonneg C) (charge_nonneg a))
  have hfb := Nat.floor_le (mul_nonneg (Nat.cast_nonneg C) (charge_nonneg b))
  have hmul := mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg C)
  have hcp : (p : ℝ) ≤ (C : ℝ)*t := by exact_mod_cast hp
  have hCs : (s : ℝ) ≤ (C : ℝ)*s := by
    have hc : (1 : ℝ) ≤ C := by exact_mod_cast hC
    nlinarith [show (0 : ℝ) ≤ (s : ℝ) from Nat.cast_nonneg s]
  have hsub : ((s-1 : ℕ) : ℝ) ≤ s := by exact_mod_cast Nat.sub_le s 1
  apply Nat.le_floor
  change ((budget C a + budget C b + (s-1) + p : ℕ) : ℝ) ≤ (C : ℝ)*charge n
  dsimp only [budget]
  push_cast
  nlinarith


/-- A natural-number denominator for the dyadic expansion profile. -/
def scale (n : ℕ) : ℕ := (Nat.log 2 n + 1) * (Nat.log 2 n + 2)

lemma scale_pos (n : ℕ) : 0 < scale n := by unfold scale; positivity

lemma two_le_scale (n : ℕ) : 2 ≤ scale n := by
  dsimp [scale]
  nlinarith [Nat.zero_le (Nat.log 2 n)]

lemma scale_mono : Monotone scale := by
  intro a b hab
  have h := Nat.log_mono_right (b := 2) hab
  unfold scale
  exact Nat.mul_le_mul (Nat.add_le_add_right h 1) (Nat.add_le_add_right h 2)


lemma lt_scale_mul_of_weight_lt {x y : ℕ}
    (h : ((2^(Nat.log 2 x) : ℕ) : ℝ) * weight (Nat.log 2 x) < (y : ℝ)) :
    x < 2 * scale x * y := by
  have hd : 0 < ((Nat.log 2 x : ℝ)+1)*((Nat.log 2 x : ℝ)+2) := by positivity
  rw [weight,mul_one_div,div_lt_iff₀ hd] at h
  have hpow : (2^(Nat.log 2 x) : ℕ) < y * scale x := by
    exact_mod_cast h
  have hx := Nat.lt_pow_succ_log_self (by decide : 1 < 2) x
  rw [pow_succ] at hx
  nlinarith

end Erdos184.LogDeficit
