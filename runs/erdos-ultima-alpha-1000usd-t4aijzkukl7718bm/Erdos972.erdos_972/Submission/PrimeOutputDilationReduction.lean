import Submission.PrimeOutputAmplificationScales

/-! Opening the weighted prime-divisor amplifier with the actual Möbius
coefficient. Square-divisibility errors are retained. No signed correlation
lower bound is asserted here. -/
namespace Erdos972PrimeOutputDilationReduction

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972WeightedDivisorAmplification Erdos972PrimeOutputAmplificationScales
open Erdos972PrimeGcdRows Erdos972PrimePowerError

set_option maxHeartbeats 1500000

lemma exists_large_prime_harmonicMass_above (C : ℝ) (L : ℕ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ L < p) ∧ C < harmonicMass P := by
  classical
  let Q := (range (L+1)).filter Nat.Prime
  obtain ⟨P, hP, hH⟩ := exists_large_prime_harmonicMass (C + harmonicMass Q)
  have hsub : P.filter (fun p => ¬L < p) ⊆ Q := by
    intro p hp
    obtain ⟨hpP, hpL⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), hP p hpP⟩
  have hs : harmonicMass (P.filter (fun p => ¬L < p)) ≤ harmonicMass Q := by
    unfold harmonicMass
    exact sum_le_sum_of_subset_of_nonneg hsub (fun p hp hp' => by positivity)
  have he : harmonicMass (P.filter (fun p => L < p)) +
      harmonicMass (P.filter (fun p => ¬L < p)) = harmonicMass P := by
    exact sum_filter_add_sum_filter_not P (fun p => L < p) (fun p => 1 / (p : ℝ))
  refine ⟨P.filter (fun p => L < p), ?_, ?_⟩
  · intro p hp
    exact ⟨hP p (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
  · linarith

lemma moebius_prime_dilation_error {p : ℕ} (hp : Nat.Prime p) (m : ℕ) :
    |(moebius (p*m) : ℝ) + (moebius m : ℝ)| ≤ if p ∣ m then 2 else 0 := by
  by_cases h : p ∣ m
  · rw [if_pos h]
    have h₁ : |(moebius (p*m) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := p*m)
    have h₂ : |(moebius m : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := m)
    exact (abs_add_le _ _).trans (by linarith)
  · have hc := hp.coprime_iff_not_dvd.mpr h
    have hh := isMultiplicative_moebius.map_mul_of_coprime hc
    rw [hh, moebius_apply_prime hp]
    simp [h]

lemma square_row_reindex (a : ℕ → ℝ) (N : ℕ) {p : ℕ} (hp : 0 < p) :
    (∑ m ∈ Ioc 0 (N/p), if p ∣ m then a (p*m) else 0) =
      divisorRow (Ioc 0 N) a (p^2) := by
  rw [sum_divisibility_row _ _ hp]
  unfold divisorRow
  rw [sum_divisibility_row _ _ (pow_pos hp 2)]
  simp only [Nat.div_div_eq_div_mul, pow_two, mul_assoc]

/-- The error in replacing μ(pm) by -μ(m) is supported on p²-divisible
original inputs. The harmless factor two avoids any omitted squarefree case. -/
theorem signed_row_dilation_error (a : ℕ → ℝ) (N : ℕ)
    (ha : ∀ n ∈ Ioc 0 N, 0 ≤ a n) {p : ℕ} (hp : Nat.Prime p) :
    |divisorRow (Ioc 0 N) (fun n => a n * (moebius n : ℝ)) p +
      (∑ m ∈ Ioc 0 (N/p), a (p*m) * (moebius m : ℝ))| ≤
      2 * divisorRow (Ioc 0 N) a (p^2) := by
  have hmemb (m : ℕ) (hm : m ∈ Ioc 0 (N/p)) : p*m ∈ Ioc 0 N := by
    exact mem_Ioc.mpr ⟨Nat.mul_pos hp.pos (mem_Ioc.mp hm).1,
      (Nat.mul_le_mul_left p (mem_Ioc.mp hm).2).trans (Nat.mul_div_le N p)⟩
  unfold divisorRow at ⊢
  rw [sum_divisibility_row _ _ hp.pos, ← sum_add_distrib]
  calc
    _ ≤ ∑ m ∈ Ioc 0 (N/p),
        |a (p*m) * (moebius (p*m) : ℝ) + a (p*m) * (moebius m : ℝ)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Ioc 0 (N/p), 2 * (if p ∣ m then a (p*m) else 0) := by
      apply sum_le_sum
      intro m hm
      have ham := ha _ (hmemb m hm)
      rw [← mul_add, abs_mul, abs_of_nonneg ham]
      have hh := mul_le_mul_of_nonneg_left (moebius_prime_dilation_error hp m) ham
      by_cases h : p ∣ m <;> simpa [h, mul_comm] using hh
    _ = _ := by rw [← mul_sum, square_row_reindex a N hp.pos]; rfl

noncomputable def moebiusOutputSum (α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, outputWeight α n * (moebius n : ℝ)

lemma outputWeight_mul (α : ℝ) (p m : ℕ) :
    outputWeight α (p*m) = outputWeight (α*p) m := by
  simp only [outputWeight, floorMul, Nat.cast_mul, mul_assoc]

lemma output_signed_dilation_error (α : ℝ) (N : ℕ) {p : ℕ} (hp : Nat.Prime p) :
    |divisorRow (Ioc 0 N) (fun n => outputWeight α n * (moebius n : ℝ)) p +
      moebiusOutputSum (α*p) (N/p)| ≤
      2 * divisorRow (Ioc 0 N) (outputWeight α) (p^2) := by
  simpa only [outputWeight_mul, moebiusOutputSum] using
    signed_row_dilation_error (outputWeight α) N (fun n _ => vonMangoldt_nonneg) hp

lemma sum_output_dilation_error (α : ℝ) (N : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    |(∑ p ∈ P, divisorRow (Ioc 0 N) (fun n => outputWeight α n * (moebius n : ℝ)) p) +
      ∑ p ∈ P, moebiusOutputSum (α*p) (N/p)| ≤
      2 * ∑ p ∈ P, divisorRow (Ioc 0 N) (outputWeight α) (p^2) := by
  rw [← sum_add_distrib, mul_sum]
  exact (abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun p hp => output_signed_dilation_error α N (hP p hp))

lemma reciprocal_square_sum_le (P : Finset ℕ) {L : ℕ} (hL : 0 < L)
    (hP : ∀ p ∈ P, L ≤ p) :
    (∑ p ∈ P, 1 / ((p : ℝ)^2)) ≤ harmonicMass P / L := by
  rw [harmonicMass, sum_div]
  apply sum_le_sum
  intro p hp
  have hLR : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hLp : (L : ℝ) ≤ p := Nat.cast_le.mpr (hP p hp)
  have hpR : (0 : ℝ) < p := hLR.trans_le hLp
  have hh := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hLR hLp)
    (show 0 ≤ 1/(p : ℝ) by positivity)
  convert hh using 1 <;> field_simp

lemma dilation_error_budget (α : ℝ) (N : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) {L : ℕ} (hL : 0 < L)
    (hLP : ∀ p ∈ P, L ≤ p) {X E : ℝ} (hX : 0 ≤ X)
    (hrows : ∀ p ∈ P,
      |divisorRow (Ioc 0 N) (outputWeight α) (p^2) - X / (p^2 : ℕ)| ≤ E) :
    |(∑ p ∈ P, divisorRow (Ioc 0 N) (fun n => outputWeight α n * (moebius n : ℝ)) p) +
      ∑ p ∈ P, moebiusOutputSum (α*p) (N/p)| ≤
      2 * X * harmonicMass P / L + 2 * E * P.card := by
  have hs : (∑ p ∈ P, divisorRow (Ioc 0 N) (outputWeight α) (p^2)) ≤
      X * (harmonicMass P / L) + E * P.card := by
    calc
      _ ≤ ∑ p ∈ P, (X / (p^2 : ℕ) + E) := by
        apply sum_le_sum
        intro p hp
        have hh := (abs_le.mp (hrows p hp)).2
        linarith
      _ = X * (∑ p ∈ P, 1 / ((p : ℝ)^2)) + E * P.card := by
        simp only [Nat.cast_pow, sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
        congr 1
        · apply sum_congr rfl
          intro p hp
          ring
        · ring
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (reciprocal_square_sum_le P hL hLP) hX) le_rfl
  have hh := (sum_output_dilation_error α N P hP).trans
    (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2))
  convert hh using 1 <;> ring

/-- An unconditional signed dilation comparison for the actual Möbius--prime
output sum, at arbitrarily large good scales. It does not assert cancellation
of either side, nor a prime-input/prime-output lower bound. -/
theorem exists_prime_dilation_comparison {α ε : ℝ}
    (hα : 1 < α) (hI : Irrational α) (hε : 0 < ε) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) ∧ 0 < harmonicMass P ∧
      ∀ B : ℕ, ∃ N : ℕ, B < N ∧
        |moebiusOutputSum α N +
          (∑ p ∈ P, moebiusOutputSum (α*p) (N/p)) / harmonicMass P| ≤ ε * N := by
  let L : ℕ := ⌈56/ε⌉₊ + 1
  have hL : 0 < L := by dsimp [L]; omega
  have hLR : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hLε : 56 ≤ ε * L := by
    have hh : 56/ε ≤ (L : ℝ) := (Nat.le_ceil _).trans (by dsimp [L]; push_cast; linarith)
    have hh' := (div_le_iff₀ hε).mp hh
    nlinarith only [hh']
  obtain ⟨P, hPL, hHP⟩ := exists_large_prime_harmonicMass_above (256/ε^2) L
  have hP (p : ℕ) (hp : p ∈ P) := (hPL p hp).1
  have hLP (p : ℕ) (hp : p ∈ P) : L ≤ p := (hPL p hp).2.le
  have hH : 0 < harmonicMass P := (by positivity : 0 < 256/ε^2).trans hHP
  have hεH : 64 ≤ (ε/2)^2 * harmonicMass P := by
    have hh := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hHP
    nlinarith only [hh]
  let R := P.sup (fun n => n) + 1
  have hR : 0 < R := by dsimp [R]; omega
  have hpR (p : ℕ) (hp : p ∈ P) : p ≤ R :=
    (show p ≤ P.sup (fun n => n) from le_sup (f := fun n : ℕ => n) hp).trans (Nat.le_succ _)
  let η : ℝ := min 1 (min (harmonicMass P / (4*((P.card : ℝ)^2+1)))
    (ε * harmonicMass P / (8*((P.card : ℝ)+1))))
  have hη : 0 < η := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηleft : η ≤ harmonicMass P / (4*((P.card : ℝ)^2+1)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hηright : η ≤ ε * harmonicMass P / (8*((P.card : ℝ)+1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hηc : 4*η*(P.card : ℝ)^2 ≤ harmonicMass P := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*((P.card : ℝ)^2+1))).mp hηleft
    change η * (4*((P.card : ℝ)^2+1)) ≤ harmonicMass P at hh
    nlinarith only [hh, hη.le]
  have hηp : 2*η*(P.card : ℝ) ≤ (ε/4)*harmonicMass P := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8*((P.card : ℝ)+1))).mp hηright
    change η * (8*((P.card : ℝ)+1)) ≤ ε*harmonicMass P at hh
    nlinarith only [hh, hη.le]
  refine ⟨P, hP, hH, ?_⟩
  intro B
  obtain ⟨N, X, E, hBN, hX, hX7, hE, hEη, hrows⟩ :=
    exists_small_output_rows hα hI hη (R^2) B
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hEN : E ≤ N := hEη.trans (by nlinarith only [mul_le_mul_of_nonneg_right hη1 hN])
  have hEc : 4*E*(P.card : ℝ)^2 ≤ harmonicMass P * N := by
    have h₁ := mul_le_mul_of_nonneg_right hEη (by positivity : 0 ≤ 4*(P.card : ℝ)^2)
    have h₂ := mul_le_mul_of_nonneg_right hηc hN
    nlinarith only [h₁, h₂]
  have hEpc : 2*E*(P.card : ℝ) ≤ (ε/4)*harmonicMass P*N := by
    have h₁ := mul_le_mul_of_nonneg_right hEη (by positivity : 0 ≤ 2*(P.card : ℝ))
    have h₂ := mul_le_mul_of_nonneg_right hηp hN
    nlinarith only [h₁, h₂]
  have hRR : R ≤ R^2 := Nat.le_self_pow (by omega : 2 ≠ 0) R
  have hrow1 : |divisorRow (Ioc 0 N) (outputWeight α) 1-X| ≤ E := by
    simpa only [Nat.cast_one, div_one] using hrows 1 (by norm_num) ((show 1 ≤ R from hR).trans hRR)
  have hrowp (p : ℕ) (hp : p ∈ P) := hrows p (hP p hp).pos ((hpR p hp).trans hRR)
  have hrowpq (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ P) :
      |divisorRow (Ioc 0 N) (outputWeight α) (p.lcm q)-X/(p.lcm q)| ≤ E := by
    apply hrows _ (Nat.lcm_pos (hP p hp).pos (hP q hq).pos)
    calc
      p.lcm q ≤ p*q := Nat.lcm_le_mul (hP p hp).pos (hP q hq).pos
      _ ≤ R*R := Nat.mul_le_mul (hpR p hp) (hpR q hq)
      _ = R^2 := by ring
  have hrowp2 (p : ℕ) (hp : p ∈ P) :
      |divisorRow (Ioc 0 N) (outputWeight α) (p^2)-X/(p^2 : ℕ)| ≤ E :=
    hrows _ (pow_pos (hP p hp).pos 2) (Nat.pow_le_pow_left (hpR p hp) 2)
  let A : ℝ := ∑ p ∈ P, divisorRow (Ioc 0 N) (fun n => outputWeight α n * (moebius n : ℝ)) p
  let D : ℝ := ∑ p ∈ P, moebiusOutputSum (α*p) (N/p)
  have hrep : |moebiusOutputSum α N - A/harmonicMass P| ≤ (ε/2)*N := by
    apply amplification_numeric hH hN (by positivity) hX hX7 hE hEN hEc hεH
    exact amplification_rows_sq (Ioc 0 N) P (outputWeight α) (fun n => (moebius n : ℝ))
      (fun n _ => vonMangoldt_nonneg) (fun n _ => by dsimp only; exact_mod_cast abs_moebius_le_one (n := n))
      hP hX hE hrow1 hrowp hrowpq
  have hconst : 14/(L : ℝ) ≤ ε/4 := (div_le_iff₀ hLR).mpr (by nlinarith only [hLε])
  have hmain : 2*X*harmonicMass P/L ≤ (ε/4)*harmonicMass P*N := by
    have h₁ := mul_le_mul_of_nonneg_right hX7 (by positivity : 0 ≤ 2*harmonicMass P/L)
    have h₂ := mul_le_mul_of_nonneg_right hconst (mul_nonneg hH.le hN)
    calc
      2*X*harmonicMass P/L = X*(2*harmonicMass P/L) := by ring
      _ ≤ 7*N*(2*harmonicMass P/L) := h₁
      _ = (14/(L : ℝ))*(harmonicMass P*N) := by ring
      _ ≤ (ε/4)*harmonicMass P*N := by simpa only [mul_assoc] using h₂
  have hdil : |(A+D)/harmonicMass P| ≤ (ε/2)*N := by
    rw [abs_div, abs_of_pos hH]
    apply (div_le_iff₀ hH).mpr
    have hh := dilation_error_budget α N P hP hL hLP hX hrowp2
    change |A+D| ≤ _ at hh
    linarith only [hh, hmain, hEpc]
  refine ⟨N, hBN, ?_⟩
  change |moebiusOutputSum α N + D/harmonicMass P| ≤ _
  have he : moebiusOutputSum α N + D/harmonicMass P =
      (moebiusOutputSum α N - A/harmonicMass P) + (A+D)/harmonicMass P := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith only [hrep, hdil])

#print axioms signed_row_dilation_error
#print axioms output_signed_dilation_error
#print axioms exists_large_prime_harmonicMass_above
#print axioms exists_prime_dilation_comparison

end Erdos972PrimeOutputDilationReduction
