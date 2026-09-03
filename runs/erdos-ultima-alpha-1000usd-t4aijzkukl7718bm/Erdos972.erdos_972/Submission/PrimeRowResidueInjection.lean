import Submission.PrimeOutputGcdDeterminant

/-! A modular injection for prime inputs in a divisor row. This gives an
upper multiplicity bound, not a lower bound for prime pairs. -/
namespace Erdos972PrimeRowResidueInjection

open Finset ArithmeticFunction
open Erdos972PrimePowerError Erdos972PrimeRoughOutputs Erdos972SelbergLowerTest
open Erdos972PrimeOutputGcdDeterminant
set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable def cofactorResidue (α : ℝ) (d M p : ℕ) : ZMod M :=
  ((floorMul α p / d : ℕ) : ZMod M) * (p : ZMod M)⁻¹

lemma cofactorResidue_eq_mul_input {α : ℝ} {d M p : ℕ}
    (hp : p.Prime) (hM : 0 < M) (hMp : M < p) :
    cofactorResidue α d M p * (p : ZMod M) =
      ((floorMul α p / d : ℕ) : ZMod M) := by
  have hu : IsUnit (p : ZMod M) := ZMod.isUnit_prime_of_not_dvd hp (by
    intro h
    exact (not_le_of_gt hMp) (Nat.le_of_dvd hM h))
  simp only [cofactorResidue, mul_assoc, ZMod.inv_mul_of_unit _ hu, mul_one]

/-- A residue collision makes the small determinant divisible by M. Since
its absolute value is strictly less than M, it would have to vanish. -/
theorem cofactorResidue_injective {α : ℝ} (hα : 1 ≤ α) {N d M : ℕ}
    (hd : α < (d : ℝ)) (hM : 0 < M) (hN : N ≤ d*M)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hMp : M < p) (hMq : M < q) (hpN : p ≤ N) (hqN : q ≤ N)
    (hdp : d ∣ floorMul α p) (hdq : d ∣ floorMul α q)
    (he : cofactorResidue α d M p = cofactorResidue α d M q) : p = q := by
  by_contra hpq
  obtain ⟨k, l, hk, hl, hne, hlo, hhi⟩ :=
    common_divisor_determinant hα hp hq hpq hd hdp hdq
  have hd0 : 0 < d := by exact_mod_cast (lt_trans (by linarith : (0 : ℝ) < α) hd)
  have hkp : floorMul α p / d = k := by rw [hk, Nat.mul_div_right _ hd0]
  have hlq : floorMul α q / d = l := by rw [hl, Nat.mul_div_right _ hd0]
  have heq : (k : ZMod M) * q = (l : ZMod M) * p := by
    have hp' := cofactorResidue_eq_mul_input (α := α) (d := d) hp hM hMp
    have hq' := cofactorResidue_eq_mul_input (α := α) (d := d) hq hM hMq
    rw [hkp] at hp'
    rw [hlq] at hq'
    calc
      (k : ZMod M) * q = (cofactorResidue α d M p * p) * q := by rw [hp']
      _ = (cofactorResidue α d M q * q) * p := by rw [he]; ring
      _ = (l : ZMod M) * p := by rw [hq']
  have hdiv : (M : ℤ) ∣ (k : ℤ)*q-(l : ℤ)*p := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    exact sub_eq_zero.mpr heq
  have hpR : (p : ℝ) ≤ (d : ℝ)*M := by exact_mod_cast hpN.trans hN
  have hqR : (q : ℝ) ≤ (d : ℝ)*M := by exact_mod_cast hqN.trans hN
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd0
  have habs : |(k : ℝ)*q-(l : ℝ)*p| < M := by
    rw [abs_lt]
    constructor <;> nlinarith only [hlo, hhi, hpR, hqR, hdR]
  have habsZ : |(k : ℤ)*q-(l : ℤ)*p| < (M : ℤ) := by exact_mod_cast habs
  have hz := Int.eq_zero_of_abs_lt_dvd hdiv habsZ
  apply hne
  exact_mod_cast sub_eq_zero.mp hz

/-- At most M prime inputs larger than M occur in a divisor row when dM≥N
and d exceeds the slope. The modulus need not be prime. -/
theorem prime_divisor_row_card_le {α : ℝ} (hα : 1 ≤ α) {N d M : ℕ}
    (hd : α < (d : ℝ)) (hM : 0 < M) (hN : N ≤ d*M) :
    ((Ioc M N).filter (fun p => p.Prime ∧ d ∣ floorMul α p)).card ≤ M := by
  classical
  letI : NeZero M := ⟨hM.ne'⟩
  let S := (Ioc M N).filter (fun p => p.Prime ∧ d ∣ floorMul α p)
  have hinj : Set.InjOn (cofactorResidue α d M) (S : Set ℕ) := by
    intro p hp q hq he
    change p ∈ (Ioc M N).filter (fun p => p.Prime ∧ d ∣ floorMul α p) at hp
    change q ∈ (Ioc M N).filter (fun p => p.Prime ∧ d ∣ floorMul α p) at hq
    obtain ⟨hpI, hpp, hdp⟩ := mem_filter.mp hp
    obtain ⟨hqI, hqp, hdq⟩ := mem_filter.mp hq
    exact cofactorResidue_injective hα hd hM hN hpp hqp
      (mem_Ioc.mp hpI).1 (mem_Ioc.mp hqI).1
      (mem_Ioc.mp hpI).2 (mem_Ioc.mp hqI).2 hdp hdq he
  have hh := card_le_card_of_injOn (s := S) (t := (univ : Finset (ZMod M)))
    (cofactorResidue α d M) (by intro p hp; exact mem_univ _) hinj
  simpa only [card_univ, ZMod.card] using hh

/-- In particular, a divisor at least N/2 occurs at the outputs of at most
two odd prime inputs up to N. The input prime 2 is deliberately excluded. -/
theorem two_large_divisor_prime_inputs {α : ℝ} (hα : 1 ≤ α) {N d : ℕ}
    (hd : α < (d : ℝ)) (hN : N ≤ 2*d) :
    ((Ioc 2 N).filter (fun p => p.Prime ∧ d ∣ floorMul α p)).card ≤ 2 := by
  exact prime_divisor_row_card_le hα hd (by decide) (by simpa [mul_comm] using hN)

#print axioms cofactorResidue_injective
#print axioms prime_divisor_row_card_le
#print axioms two_large_divisor_prime_inputs
end Erdos972PrimeRowResidueInjection
