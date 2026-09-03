import FormalConjecturesUtil

/-! The nonnegative divisor expansion of the two-point sieve correlation.
Averaging over consecutive positive differences never exceeds the independent
pair density. This is a second-moment estimate, not a gap-tail theorem. -/
namespace Erdos970.GapAverages
open Finset

noncomputable def density (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1 - 1 / (p : ℝ))

noncomputable def pairKernel (P : Finset ℕ) (h : ℕ) : ℝ :=
  ∏ p ∈ P, ((1 - 2 / (p : ℝ)) + (1 / (p : ℝ)) * if p ∣ h then 1 else 0)

noncomputable def pairWeight (P Q : Finset ℕ) : ℝ :=
  (∏ p ∈ Q, 1 / (p : ℝ)) * ∏ p ∈ P \ Q, (1 - 2 / (p : ℝ))

lemma product_dvd_iff (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (h : ℕ) :
    (∏ p ∈ Q, p) ∣ h ↔ ∀ p ∈ Q, p ∣ h := by
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert p Q hp ih =>
    have hpp := hQ p (mem_insert_self _ _)
    have hQ' : ∀ q ∈ Q, q.Prime := fun q hq => hQ q (mem_insert_of_mem hq)
    have hco : p.Coprime (∏ q ∈ Q, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact (Nat.coprime_primes hpp (hQ' q hq)).mpr (by rintro rfl; exact hp hq)
    rw [prod_insert hp, forall_mem_insert]
    constructor
    · intro hh
      exact ⟨(dvd_mul_right p _).trans hh,
        (ih hQ').mp ((dvd_mul_left _ p).trans hh)⟩
    · rintro ⟨ha, hb⟩
      exact hco.mul_dvd_of_dvd_of_dvd ha ((ih hQ').mpr hb)

lemma pairWeight_nonneg (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    0 ≤ pairWeight P Q := by
  apply mul_nonneg
  · exact prod_nonneg (fun p _ => by positivity)
  · apply prod_nonneg
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p (mem_sdiff.mp hp).1).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hh : 2 / (p : ℝ) ≤ 1 := (div_le_one hp0).mpr h2
    linarith

lemma pairKernel_expansion (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (h : ℕ) :
    pairKernel P h = ∑ Q ∈ P.powerset,
      pairWeight P Q * if (∏ p ∈ Q, p) ∣ h then 1 else 0 := by
  unfold pairKernel
  simp_rw [add_comm (1 - 2 / (_ : ℝ))]
  rw [prod_add]
  apply sum_congr rfl
  intro Q hQ
  have hQP := mem_powerset.mp hQ
  rw [prod_mul_distrib, prod_boole]
  simp only [← product_dvd_iff Q (fun p hp => hP p (hQP hp))]
  unfold pairWeight
  ring

lemma pairWeight_mass (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ Q ∈ P.powerset, pairWeight P Q / (∏ p ∈ Q, (p : ℝ))) = density P ^ 2 := by
  have he (p : ℕ) : (1 - 1 / (p : ℝ)) ^ 2 = 1 / (p : ℝ) ^ 2 + (1 - 2 / (p : ℝ)) := by
    ring
  rw [density, ← prod_pow]
  simp_rw [he]
  rw [prod_add]
  apply sum_congr rfl
  intro Q hQ
  unfold pairWeight
  have hn : (∏ p ∈ Q, 1 / (p : ℝ)) / (∏ p ∈ Q, (p : ℝ)) =
      ∏ p ∈ Q, 1 / (p : ℝ) ^ 2 := by
    rw [← prod_div_distrib]
    apply prod_congr rfl
    intro p hp
    ring
  rw [mul_div_right_comm, hn]

/-- Exact floor counts give the one-sided average correlation bound. -/
theorem sum_pairKernel_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (∑ h ∈ range n, pairKernel P (h + 1)) ≤ (n : ℝ) * density P ^ 2 := by
  simp_rw [pairKernel_expansion P hP]
  rw [sum_comm, ← pairWeight_mass P hP, mul_sum]
  apply sum_le_sum
  intro Q hQ
  rw [← mul_sum]
  have hc : (∑ h ∈ range n, if (∏ p ∈ Q, p) ∣ h + 1 then (1 : ℝ) else 0) =
      (n / (∏ p ∈ Q, p) : ℕ) := by
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one, Nat.card_multiples]
  rw [hc]
  have hh := mul_le_mul_of_nonneg_left
    (Nat.cast_div_le (α := ℝ) (m := n) (n := ∏ p ∈ Q, p)) (pairWeight_nonneg P Q hP)
  simp only [Nat.cast_prod] at hh
  convert hh using 1 <;> ring

/-- The triangularly weighted off-diagonal correlation bound. -/
theorem triangular_pairKernel_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    (2 : ℝ) * (∑ y ∈ range m, ∑ h ∈ range y, pairKernel P (h + 1)) ≤
      (m : ℝ) * (m - 1) * density P ^ 2 := by
  have hh := sum_le_sum (fun y (_hy : y ∈ range m) => sum_pairKernel_le P hP y)
  rw [← sum_mul] at hh
  have hsum : (2 : ℝ) * (∑ y ∈ range m, (y : ℝ)) = (m : ℝ) * (m - 1) := by
    have ht := sum_range_id_mul_two m
    by_cases hm : m = 0
    · simp [hm]
    · have he : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
      have ht' : (∑ y ∈ range m, (y : ℝ)) * 2 = (m : ℝ) * ((m - 1 : ℕ) : ℝ) := by
        have hcast := congrArg (fun z : ℕ => (z : ℝ)) ht
        simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat] using hcast
      rw [he] at ht'
      linarith
  calc
    _ ≤ 2 * ((∑ y ∈ range m, (y : ℝ)) * density P ^ 2) := by linarith
    _ = _ := by rw [← mul_assoc, hsum]

#print axioms sum_pairKernel_le
#print axioms triangular_pairKernel_le
end Erdos970.GapAverages
