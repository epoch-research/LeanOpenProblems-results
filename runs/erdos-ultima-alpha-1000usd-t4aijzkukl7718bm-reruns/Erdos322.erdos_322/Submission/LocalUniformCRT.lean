import Submission.LocalSeedLifting

/-! Quantitative CRT concentration for even critical power sums. -/
namespace Erdos322Research.LocalUniformCRT
noncomputable section
open Finset LocalPeakCounting LocalCRTConcentration LocalSeedLifting
open scoped Classical
set_option maxHeartbeats 0
set_option Elab.async false

/-- The elementary good-prime construction also controls its size. -/
theorem good_prime_avoiding_bounded (k B : ℕ) (hk : 2 ≤ k) (hB : 0 < B) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ k ∧ p.Coprime B ∧ p ≤ (2*k*B)^k+1 ∧
      ∃ a : ZMod p, a ≠ 0 ∧ a^k+1=0 := by
  have hb : 0 < (2*k*B)^k := pow_pos (by positivity) _
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (show (2*k*B)^k+1 ≠ 1 by omega)
  have hn : ¬p ∣ 2*k*B := by
    intro hh
    have hh' : p ∣ (2*k*B)^k := dvd_pow hh (by omega : k ≠ 0)
    have h1 : p ∣ 1 := by simpa using Nat.dvd_sub hd hh'
    exact hp.not_dvd_one h1
  have hpk : ¬p ∣ k := fun hh ↦ hn (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hh 2) B)
  have hpB : p.Coprime B := hp.coprime_iff_not_dvd.mpr fun hh ↦ hn (dvd_mul_of_dvd_right hh (2*k))
  refine ⟨p,hp,hpk,hpB,Nat.le_of_dvd (by omega) hd,(2*k*B : ℕ),?_,?_⟩
  · exact (ZMod.natCast_eq_zero_iff _ _).not.mpr hn
  · have hh := (ZMod.natCast_eq_zero_iff ((2*k*B)^k+1) p).mpr hd
    simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_one] using hh

/-- A convenient constant controlling both seed-density losses and prime growth. -/
def base (k : ℕ) : ℕ := (4*(k+2))^(k+3)

lemma base_large (k : ℕ) : 2*(k+2)+2 ≤ base k := by
  have hh : 4*(k+2) ≤ (4*(k+2))^(k+3) := Nat.le_pow (by omega)
  dsimp only [base]
  omega

lemma base_prime_bound (k : ℕ) : (4*(k+2))^(k+2) ≤ base k := by
  apply Nat.pow_le_pow_right (by omega : 1 ≤ 4*(k+2))
  omega

private lemma next_product_bound (k B p : ℕ) (hB : 0 < B)
    (hp : p ≤ (2*(k+2)*B)^(k+2)+1) : p*B ≤ base k*B^(k+3) := by
  have hq : 0 < (2*(k+2)*B)^(k+2) := pow_pos (by positivity) _
  have htwo : 2 ≤ (2 : ℕ)^(k+2) := Nat.le_pow (by omega)
  calc
    p*B ≤ ((2*(k+2)*B)^(k+2)+1)*B := Nat.mul_le_mul_right _ hp
    _ ≤ (2*(2*(k+2)*B)^(k+2))*B := by gcongr; omega
    _ ≤ ((4*(k+2)*B)^(k+2))*B := by
      apply Nat.mul_le_mul_right
      conv_rhs => rw [show 4*(k+2)*B=2*(2*(k+2)*B) by ring,mul_pow]
      exact Nat.mul_le_mul_right _ htwo
    _ = (4*(k+2))^(k+2)*B^(k+3) := by rw [mul_pow,show k+3=k+2+1 by omega,pow_succ]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (base_prime_bound k)

/-- r distinct good primes yield a depth-r density polynomial; the product
of those primes is at most A^(A^r), with A depending only on the exponent. -/
theorem bounded_even_concentration (k r : ℕ) (he : Even (k+2)) :
    ∃ B : ℕ, 0 < B ∧ B ≤ (base k)^((base k)^r) ∧ ∀ d : ℕ,
      (d+1)^r*(B^((k+2)*d+1))^(k+1) ≤
        (2*(k+2))^r*rootCount (k+2) (B^((k+2)*d+1)) := by
  have hA : 2*(k+2)+2 ≤ base k := base_large k
  have hA1 : 1 ≤ base k := by omega
  induction r with
  | zero =>
    refine ⟨1,by omega,by simpa using hA1,?_⟩
    intro d
    simp [rootCount,Roots]
  | succ r ih =>
    obtain ⟨B,hB,hbound,h⟩ := ih
    obtain ⟨p,hp,hpk,hpB,hpbound,a,ha,hseed⟩ :=
      good_prime_avoiding_bounded (k+2) B (by omega) hB
    letI : Fact p.Prime := ⟨hp⟩
    refine ⟨p*B,Nat.mul_pos hp.pos hB,?_,?_⟩
    · calc
        p*B ≤ base k*B^(k+3) := next_product_bound k B p hB hpbound
        _ ≤ base k*((base k)^((base k)^r))^(k+3) := by gcongr
        _ = (base k)^(1+(base k)^r*(k+3)) := by
          rw [← pow_mul,← pow_succ']
          congr 1
          omega
        _ ≤ (base k)^((base k)^(r+1)) := by
          apply Nat.pow_le_pow_right hA1
          rw [pow_succ]
          have hpow : 1 ≤ (base k)^r := one_le_pow₀ hA1
          nlinarith
    · intro d
      have h1 := uniform_even_local_density p k hpk he a hseed d
      have h2 := h d
      have hh := Nat.mul_le_mul h1 h2
      rw [mul_pow,rootCount_mul _ _ _ (pow_pos hp.pos _) (pow_pos hB _) (hpB.pow _ _)]
      calc
        (d+1)^(r+1)*(p^((k+2)*d+1)*B^((k+2)*d+1))^(k+1) =
          ((d+1)*(p^((k+2)*d+1))^(k+1))*
          ((d+1)^r*(B^((k+2)*d+1))^(k+1)) := by rw [pow_succ,mul_pow]; ring
        _ ≤ ((2*(k+2))*rootCount (k+2) (p^((k+2)*d+1)))*
            ((2*(k+2))^r*rootCount (k+2) (B^((k+2)*d+1))) := hh
        _ = (2*(k+2))^(r+1)*(rootCount (k+2) (p^((k+2)*d+1))*
            rootCount (k+2) (B^((k+2)*d+1))) := by rw [pow_succ]; ring

end
end Erdos322Research.LocalUniformCRT
