import Submission.StationaryEntropyDecrement

/-! Entropy decrement for arbitrary labels on a finite cyclic interval and
actual modular residues. A fixed divisibility condition makes stationarity exact. -/

namespace Erdos371.FiniteInformation
open Finset EntropyScales

lemma mapLaw_uniform_equiv {Ω : Type*} [Fintype Ω] [Nonempty Ω] (e : Equiv.Perm Ω) :
    mapLaw (uniformLaw Ω) e = uniformLaw Ω := by
  classical
  ext x
  change (∑ y, if e y = x then (Fintype.card Ω : ℝ)⁻¹ else 0) = (Fintype.card Ω : ℝ)⁻¹
  simp only [Equiv.apply_eq_iff_eq_symm_apply]
  simp

/-- The usual least-nonnegative-representative residue map. -/
def cyclicResidue (N M : ℕ) : ZMod N → ZMod M := fun x => (x.val : ZMod M)

lemma cyclicResidue_eq_castHom {N M : ℕ} [NeZero N] (h : M ∣ N) (x : ZMod N) :
    cyclicResidue N M x = ZMod.castHom h (ZMod M) x := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rfl

lemma cyclicResidue_semiconj {N M : ℕ} [NeZero N] (h : M ∣ N) :
    Function.Semiconj (cyclicResidue N M) (Equiv.addRight (1 : ZMod N))
      (Equiv.addRight (1 : ZMod M)) := by
  intro x
  change cyclicResidue N M (x+1) = cyclicResidue N M x + 1
  simp only [cyclicResidue_eq_castHom h, map_add, map_one]

/-- A uniform horizon for arbitrary finite labels on a cycle. The residue
moduli need divide the cycle length only at the finitely many relevant scales. -/
theorem cyclic_residue_entropy_decrement {A : Type*} [Fintype A]
    (H₀ : ℕ) (hH₀ : 1 < H₀) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ K > 0, ∀ (M : ℕ → ℕ) [∀ H, NeZero (M H)],
      (∀ n < K, Real.log (M (factorialScale H₀ n) : ℝ) ≤ C * factorialScale H₀ n) →
      ∀ (N : ℕ) [NeZero N],
        (∀ n < K, M (factorialScale H₀ n) ∣ N) → ∀ L : ZMod N → A,
          ∃ n < K, mutualInformation
            (blockJointLaw (uniformLaw (ZMod N)) (Equiv.addRight (1 : ZMod N)) L
              (cyclicResidue N (M (factorialScale H₀ n))) (factorialScale H₀ n)) <
                ε * factorialScale H₀ n / Real.log (factorialScale H₀ n : ℝ) := by
  obtain ⟨K,hK,hdec⟩ := stationary_entropy_decrement (A := A) H₀ hH₀ C ε hC hε
  refine ⟨K,hK,?_⟩
  intro M _ hlog N _ hd L
  apply hdec (ZMod N) (uniformLaw (ZMod N)) (Equiv.addRight 1) (mapLaw_uniform_equiv _)
    L (fun H => ZMod (M H)) (fun H => cyclicResidue N (M H)) (fun _ => Equiv.addRight 1)
  · intro n hn
    exact cyclicResidue_semiconj (hd n hn)
  · intro n hn
    simpa only [ZMod.card] using hlog n hn

lemma log_primorial_le (H : ℕ) : Real.log (primorial H : ℝ) ≤ Real.log 4 * H := by
  have he := Chebyshev.theta_eq_log_primorial (H : ℝ)
  rw [Nat.floor_natCast] at he
  rw [← he]
  exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg H)

instance primorial_neZero (H : ℕ) : NeZero (primorial H) := ⟨(primorial_pos H).ne'⟩

/-- The information estimate for the full small-prime residue, valid for every
labeling of every cyclic interval of a suitable fixed-divisibility length. -/
theorem cyclic_prime_residue_entropy_decrement {A : Type*} [Fintype A]
    (H₀ : ℕ) (hH₀ : 1 < H₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∀ (N : ℕ) [NeZero N],
      (∏ n ∈ range K, primorial (factorialScale H₀ n)) ∣ N → ∀ L : ZMod N → A,
        ∃ n < K, mutualInformation
          (blockJointLaw (uniformLaw (ZMod N)) (Equiv.addRight (1 : ZMod N)) L
            (cyclicResidue N (primorial (factorialScale H₀ n))) (factorialScale H₀ n)) <
              ε * factorialScale H₀ n / Real.log (factorialScale H₀ n : ℝ) := by
  obtain ⟨K,hK,hdec⟩ := cyclic_residue_entropy_decrement (A := A) H₀ hH₀ (Real.log 4) ε
    (Real.log_nonneg (by norm_num)) hε
  refine ⟨K,hK,?_⟩
  intro N _ hd L
  apply hdec primorial (fun n _ => log_primorial_le _) N
    (fun n hn => (dvd_prod_of_mem (fun n => primorial (factorialScale H₀ n))
      (mem_range.mpr hn)).trans hd) L

#print axioms cyclic_residue_entropy_decrement
#print axioms cyclic_prime_residue_entropy_decrement
end Erdos371.FiniteInformation
