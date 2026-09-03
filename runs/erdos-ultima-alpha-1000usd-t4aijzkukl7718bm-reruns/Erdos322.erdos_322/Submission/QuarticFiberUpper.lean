import Submission.QuarticFiberCRT

/-! Uniform upper bounds for every quartic residue fiber at every modulus.
These congruence bounds do not imply subpolynomial exact representation counts. -/
namespace Erdos322Research.QuarticFiberUpper
noncomputable section
open Finset QuarticFiberBasic QuarticFiberScaling QuarticFiberCRT
open scoped Classical
set_option maxHeartbeats 0
set_option Elab.async false

/-- A uniform prime-power bound, including p=2 and all targets n. -/
theorem prime_power_fiber_upper (p e : ℕ) [Fact p.Prime] : ∀ n : ℕ,
    fiberCount (p^e) n ≤ 17*(e+1)^3*p^(3*e) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : 1 ≤ p := by omega
  induction e using Nat.strong_induction_on with
  | h e ih =>
    cases e with
    | zero => intro n; simp [fiberCount,Fiber,Nat.modEq_one]
    | succ e =>
      intro n
      have hc := fiber_cover_upper p e n
      simp only [Nat.divisors_prime_pow (Fact.out : p.Prime),Finset.card_map,Finset.card_range,
        ← pow_mul] at hc
      by_cases he : e+1 ≤ 4
      · have hd := divisible_box_upper p e n hp
        have hpow : p^(4*e) ≤ p^((e+1)*3) := Nat.pow_le_pow_right hp1 (by omega)
        have hh := hd.trans hpow
        calc
          fiberCount (p^(e+1)) n ≤ _ := hc
          _ ≤ p^((e+1)*3)+16*(e+1+1)^2*p^((e+1)*3) := by gcongr
          _ = (1+16*(e+2)^2)*p^((e+1)*3) := by ring
          _ ≤ 17*(e+2)^3*p^((e+1)*3) := by
            apply Nat.mul_le_mul_right
            nlinarith [Nat.zero_le (e^3)]
          _ = _ := by ring
      · let d := e+1-4
        have hd : d+4=e+1 := Nat.sub_add_cancel (by omega)
        have hdt : d<e+1 := by omega
        obtain ⟨m,hm⟩ := divisible_scaling_upper p (p^d) n hp (pow_pos hp _)
        rw [← pow_add,show 4+d=e+1 by omega] at hm
        have hi := ih d hdt m
        have hb : Fintype.card (DivFiber p (p^(e+1)) n) ≤
            17*(d+1)^3*p^((e+1)*3) := by
          calc
            Fintype.card (DivFiber p (p^(e+1)) n) ≤ _ := hm
            _ ≤ (17*(d+1)^3*p^(3*d))*p^12 := by gcongr
            _ = 17*(d+1)^3*p^((e+1)*3) := by
              rw [mul_assoc (17*(d+1)^3),← pow_add]
              congr 2
              omega
        calc
          fiberCount (p^(e+1)) n ≤ _ := hc
          _ ≤ 17*(d+1)^3*p^((e+1)*3)+16*(e+1+1)^2*p^((e+1)*3) := by gcongr
          _ = (17*(d+1)^3+16*(e+2)^2)*p^((e+1)*3) := by ring
          _ ≤ (17*(e+1)^3+16*(e+2)^2)*p^((e+1)*3) := by gcongr; omega
          _ ≤ 17*(e+2)^3*p^((e+1)*3) := by
            apply Nat.mul_le_mul_right
            nlinarith [Nat.zero_le (e^2)]
          _ = _ := by ring

/-- Uniformity in both modulus and residue: every fiber is at most q^3
 times a fixed power of the divisor function. -/
theorem all_fibers_upper (q : ℕ) : 0 < q → ∀ n : ℕ,
    fiberCount q n ≤ q.divisors.card^8*q^3 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => intro _ n; simp [fiberCount,Fiber,Nat.modEq_one]
  | prime_pow p e hp he =>
    intro _ n
    letI : Fact p.Prime := ⟨hp⟩
    have hc : 17 ≤ (e+1)^5 := by
      calc
        17 ≤ (2 : ℕ)^5 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_left (by omega) _
    calc
      fiberCount (p^e) n ≤ 17*(e+1)^3*p^(3*e) := prime_power_fiber_upper p e n
      _ ≤ (e+1)^5*(e+1)^3*p^(3*e) := by gcongr
      _ = (p^e).divisors.card^8*(p^e)^3 := by
        simp only [Nat.divisors_prime_pow hp,Finset.card_map,Finset.card_range,← pow_add,← pow_mul]
        congr 2
        omega
  | coprime a b ha hb hab ia ib =>
    intro _ n
    have hh := Nat.mul_le_mul (ia (by omega) n) (ib (by omega) n)
    rw [fiberCount_mul _ _ _ (by omega) (by omega) hab,hab.card_divisors_mul,mul_pow,mul_pow]
    convert hh using 1; ring

/-- In particular, no residue class has a power-sized normalized density. -/
theorem all_fibers_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ q : ℕ, 0 < q → ∀ n : ℕ,
      (fiberCount q n : ℝ) ≤ C*(q : ℝ)^ε*(q : ℝ)^3 := by
  obtain ⟨C,hC,hbound⟩ := divisor_count_subpolynomial (ε/8) (by positivity)
  refine ⟨C^8,pow_pos hC _,?_⟩
  intro q hq n
  have hcast : (fiberCount q n : ℝ) ≤ (q.divisors.card : ℝ)^8*(q : ℝ)^3 := by
    exact_mod_cast all_fibers_upper q hq n
  have hp : ((q : ℝ)^(ε/8))^8=(q : ℝ)^ε := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg q)]
    congr 1
    norm_num
  calc
    (fiberCount q n : ℝ) ≤ _ := hcast
    _ ≤ (C*(q : ℝ)^(ε/8))^8*(q : ℝ)^3 := by gcongr; exact hbound q hq
    _ = C^8*(q : ℝ)^ε*(q : ℝ)^3 := by rw [mul_pow,hp]

end
end Erdos322Research.QuarticFiberUpper
