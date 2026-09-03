import Submission.QuadraticPrimeAvoidance
import Submission.SquarefreeConicFamily

/-! A fixed strict cube collision family survives any reciprocally summable
forbidden set of primes. No arbitrary-density disproof follows. -/
namespace Erdos1206.SummablePrimeConicObstruction
open Finset QuadraticLatticeLines QuadraticRootLattice QuadraticUnitResidues
  SquarefreeConicFamily QuadraticLocalAdmissibility
open scoped Classical
set_option maxHeartbeats 2000000

lemma anisotropic (i : Fin 4) : Anisotropic (a i) (b i) (c i) := by
  apply anisotropic_of_nonsquare_discriminant
  fin_cases i <;> norm_num [a,b,c]

lemma local_units (p : ℕ) (hp : p.Prime) :
    ∃ z : ZMod p × ZMod p,
      ∀ i, evalMod (a i) (b i) (c i) z ≠ 0 := by
  by_cases hsmall : p ≤ 8
  · refine ⟨(1,0),fun i => ?_⟩
    have hcop : Nat.Coprime (a i) 210 := by fin_cases i <;> norm_num [a]
    have hp210 : p∣210 := by
      have hp2 := hp.two_le
      interval_cases p <;> norm_num at *
    simp only [evalMod,Int.cast_natCast,one_pow,mul_one,zero_pow (by decide : 2≠0),
      mul_zero,add_zero]
    intro hz
    have hpa := (CharP.cast_eq_zero_iff (ZMod p) p (a i)).mp hz
    exact hp.not_dvd_one (by simpa [hcop.gcd_eq_one] using Nat.dvd_gcd hpa hp210)
  · obtain ⟨u,hu⟩ := exists_avoiding_residue hp (show 2*4 < p by omega)
      (fun i => (a i:ZMod p)) (fun i => (b i:ZMod p)) (fun i => (c i:ZMod p))
      (fun i => primitive_coefficients_mod_prime hp (by fin_cases i <;> norm_num [a,b,c]))
    refine ⟨(u,1),fun i => ?_⟩
    simpa only [evalMod,Int.cast_natCast,one_pow,mul_one] using hu i

/-- Forbidding prime multiples at finite harmonic cost never removes all
strict positive cube collisions. -/
theorem collision_avoiding (B : Set ℕ) (hB : ∀ p∈B, p.Prime)
    (hs : Summable (fun p : ℕ => if p∈B then (1:ℝ)/p else 0)) :
    ∃ n : Fin 4 → ℕ, (∀ i, 0 < n i) ∧
      n 0 < n 1 ∧ n 1 < n 2 ∧ n 2 < n 3 ∧
      (n 0)^3+(n 3)^3=(n 1)^3+(n 2)^3 ∧
      ∀ i p, p∈B → ¬ p∣n i := by
  obtain ⟨u,t,hu,havoid⟩ := QuadraticPrimeAvoidance.exists_avoiding anisotropic B hB hs
    (fun p hp => local_units p (hB p hp))
  obtain ⟨h0,h01,h12,h23⟩ := ordered t u hu
  refine ⟨fun i => F i t u,?_,h01,h12,h23,identity t u,?_⟩
  · intro i
    fin_cases i <;> dsimp <;> omega
  · intro i p hp hd
    apply havoid i p hp
    have hcast : (p:ℤ) ∣ (F i t u:ℤ) := by exact_mod_cast hd
    convert hcast using 1
    simp only [F,QuadraticSquarefreeSieve.quad,form,Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
    ring

/-- A prime-multiple-free source at summable prime cost is not cube-Sidon.
This theorem does not concern general divisor-closed or positive-density sets. -/
theorem not_sidon (B : Set ℕ) (hB : ∀ p∈B, p.Prime)
    (hs : Summable (fun p : ℕ => if p∈B then (1:ℝ)/p else 0)) :
    ¬ IsSidon ((fun n : ℕ => n^3) '' {n : ℕ | ∀ p∈B, ¬ p∣n}) := by
  intro hsidon
  obtain ⟨n,hn,h01,h12,h23,he,havoid⟩ := collision_avoiding B hB hs
  have hm (i : Fin 4) : n i ∈ {n : ℕ | ∀ p∈B, ¬ p∣n} := havoid i
  have hh := hsidon _ ⟨n 0,hm 0,rfl⟩ _ ⟨n 1,hm 1,rfl⟩
    _ ⟨n 3,hm 3,rfl⟩ _ ⟨n 2,hm 2,rfl⟩ he
  rcases hh with hh | hh
  · have heq := Nat.pow_left_injective (by decide : 3≠0) hh.1
    omega
  · have heq := Nat.pow_left_injective (by decide : 3≠0) hh.1
    omega

#print axioms collision_avoiding
#print axioms not_sidon
end Erdos1206.SummablePrimeConicObstruction
