import Submission.NonemptyArithmeticCompletion
import Submission.ArithmeticReduction

/-! Nonempty completion of an irredundant arithmetic cover, retaining its
pure-divisor avoidance. Completion may destroy irredundance. -/
namespace Erdos7ProtectedArithmeticCompletion
open scoped BigOperators
open Erdos7NonemptyArithmeticCompletion Erdos7Reduction
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The protected-class hypothesis follows from actual irredundance and
coverage, before any new classes are added. -/
theorem original_avoids_protected {I J : Type*} (m : I → ℕ) (a : I → ℤ)
    (hpriv : ∀ i, ∃ x : ℤ, ∀ j, j ≠ i → ¬ (m j : ℤ) ∣ x-a j)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i) (pure : J → I) (i : I) :
    AvoidsProtected (fun j => m (pure j)) (fun j => a (pure j)) (m i) (a i) := by
  intro j hne hd
  apply residue_not_congruent_of_proper_modulus_divisor m a hpriv hc
    (show pure j ≠ i from fun h => hne (congrArg m h)) hd

/-- Every old class remains exactly as it was; all new classes are nonempty
and avoid each protected divisor whenever that divisor is proper. -/
theorem irredundant_protected_completion {I J : Type*} (m : I → ℕ) (a : I → ℤ)
    (hm : Function.Injective m) (hgt : ∀ i, 1 < m i)
    (hpriv : ∀ i, ∃ x : ℤ, ∀ j, j ≠ i → ¬ (m j : ℤ) ∣ x-a j)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i) (pure : J → I)
    (g : ℤ) (hg : ∀ j, ¬ (m (pure j) : ℤ) ∣ g-a (pure j))
    (N : ℕ) (hN : 0 < N) (hodd : Odd N) (hdiv : ∀ i, m i ∣ N) :
    ∃ b : ℕ → ℤ,
      (∀ i, b (m i)=a i) ∧
      (∀ n, AvoidsProtected (fun j => m (pure j)) (fun j => a (pure j)) n (b n)) ∧
      (∀ n ∈ nontrivialDivisors N, 1 < n ∧ Odd n) ∧
      (∀ x : ℤ, ∃ n : ↥(nontrivialDivisors N), (n.val : ℤ) ∣ x-b n.val) := by
  obtain ⟨hD,hold,hcov⟩ := full_divisor_completion m a hm hgt hc N hN hodd hdiv
    (fun _ => g)
  exact ⟨completedResidue m a (fun _ => g),hold,
    fun n => complete_avoids_protected m a (fun j => m (pure j))
      (fun j => a (pure j)) (original_avoids_protected m a hpriv hc pure) g hg n,
    hD,hcov⟩

lemma not_twentyseven_dvd_extended (N T : ℕ) (hN : ¬ 27 ∣ N) :
    ¬ 27 ∣ N*5^T := by
  intro h
  exact hN (((show Nat.Coprime 27 5 by decide).pow_right T).dvd_mul_right.mp h)

lemma current_pattern_mem (N T u b : ℕ) (hN : 0 < N) (h9 : 9 ∣ N)
    (hu : u ≤ 2) (hb : 1 ≤ b) (hbT : b ≤ T) :
    3^u*5^b ∈ nontrivialDivisors (N*5^T) := by
  apply (mem_nontrivialDivisors _ _ (Nat.mul_pos hN (pow_pos (by decide) T))).mpr
  have h3 : 0 < 3^u := pow_pos (by decide) u
  have h5 : 5 ≤ 5^b := by
    simpa using Nat.pow_le_pow_right (show 0 < 5 by decide) hb
  refine ⟨by nlinarith,?_⟩
  have hd3 : 3^u ∣ N := (show 3^u ∣ 9 from by
    simpa using pow_dvd_pow 3 hu).trans h9
  exact Nat.mul_dvd_mul hd3 (pow_dvd_pow 5 hbT)

/-- Completed 3/5 current rows have no empty mixed pattern. The same original
pure3 and pure9 are protected while the five-adic exponent cap is made as large
as desired. No claim of irredundance is made about these completed covers. -/
theorem ternary_five_completions {I : Type*} (m : I → ℕ) (a : I → ℤ)
    (hm : Function.Injective m) (hgt : ∀ i, 1 < m i)
    (hpriv : ∀ i, ∃ x : ℤ, ∀ j, j ≠ i → ¬ (m j : ℤ) ∣ x-a j)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i)
    (i3 i9 : I) (hm3 : m i3=3) (ha3 : a i3=0) (hm9 : m i9=9) (ha9 : a i9=1)
    (N : ℕ) (hN : 0 < N) (hodd : Odd N) (hdiv : ∀ i, m i ∣ N)
    (h27 : ¬ 27 ∣ N) (T : ℕ) :
    ∃ b : ℕ → ℤ,
      (∀ i, b (m i)=a i) ∧
      (∀ x : ℤ, ∃ n : ↥(nontrivialDivisors (N*5^T)), (n.val : ℤ) ∣ x-b n.val) ∧
      (∀ n ∈ nontrivialDivisors (N*5^T), 1 < n ∧ Odd n ∧ ¬ 27 ∣ n) ∧
      ∀ u v : ℕ, u ≤ 2 → 1 ≤ v → v ≤ T →
        3^u*5^v ∈ nontrivialDivisors (N*5^T) ∧
        (0 < u → ¬ (3 : ℤ) ∣ b (3^u*5^v)) ∧
        (u=2 → ¬ (9 : ℤ) ∣ b (3^u*5^v)-1) := by
  let pure : Fin 2 → I := ![i3,i9]
  have hg : ∀ j : Fin 2, ¬ (m (pure j) : ℤ) ∣ (-1)-a (pure j) := by
    intro j
    fin_cases j <;> norm_num [pure,hm3,ha3,hm9,ha9]
  have hN' := enlarged_odd_period N 5 T hN hodd (by decide) (by decide)
  obtain ⟨b,hold,hgood,hD,hcov⟩ := irredundant_protected_completion m a hm hgt
    hpriv hc pure (-1) hg (N*5^T) hN'.1 hN'.2.1 (fun i => (hdiv i).trans hN'.2.2)
  refine ⟨b,hold,hcov,?_,?_⟩
  · intro n hn
    have hn' := (mem_nontrivialDivisors _ _ hN'.1).mp hn
    exact ⟨(hD n hn).1,(hD n hn).2,
      fun hd => not_twentyseven_dvd_extended N T h27 (hd.trans hn'.2)⟩
  · intro u v hu hv hvT
    have h9N : 9 ∣ N := by simpa only [hm9] using hdiv i9
    have h5pow : 5 ∣ 5^v := by
      simpa only [pow_one] using pow_dvd_pow 5 hv
    have h5dvd : 5 ∣ 3^u*5^v :=
      h5pow.trans (dvd_mul_left (5^v) (3^u))
    have hn3 : 3 ≠ 3^u*5^v := by intro h; rw [←h] at h5dvd; norm_num at h5dvd
    have hn9 : 9 ≠ 3^u*5^v := by intro h; rw [←h] at h5dvd; norm_num at h5dvd
    refine ⟨current_pattern_mem N T u v hN h9N hu hv hvT,?_,?_⟩
    · intro hu0
      have h3pow : 3 ∣ 3^u := by
        simpa only [pow_one] using pow_dvd_pow 3 hu0
      have hd3 : 3 ∣ 3^u*5^v :=
        h3pow.trans (dvd_mul_right (3^u) (5^v))
      have hh := hgood (3^u*5^v) (0 : Fin 2)
      simp only [pure,Matrix.cons_val_zero,hm3,ha3,sub_zero] at hh
      exact hh hn3 hd3
    · intro hu2
      have hd9 : 9 ∣ 3^u*5^v := by rw [hu2]; exact dvd_mul_right 9 (5^v)
      have hh := hgood (3^u*5^v) (1 : Fin 2)
      simp only [pure,Matrix.cons_val_one,Matrix.cons_val_zero,hm9,ha9] at hh
      exact hh hn9 hd9

#print axioms original_avoids_protected
#print axioms irredundant_protected_completion
#print axioms ternary_five_completions
end Erdos7ProtectedArithmeticCompletion
