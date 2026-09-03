import Submission.CofactorAllModulusMean

/-!
# Maximal primitive cofactor prefixes and lifting

These finite bounds retain the cofactor character sum at large conductors.
No prime-count lower bound is asserted.
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def cofactorPrefixSelector {c : ℕ} (ψ : DirichletCharacter ℂ c) (B : ℕ) : ℕ :=
  Classical.choose (Finset.exists_max_image (range (B+1))
    (fun T => ‖∑ n ∈ Icc 1 T, ψ (n : ZMod c)‖) ⟨0,by simp⟩)

lemma cofactorPrefixSelector_spec {c : ℕ} (ψ : DirichletCharacter ℂ c) (B : ℕ) :
    cofactorPrefixSelector ψ B ≤ B ∧ ∀ T ≤ B,
      ‖∑ n ∈ Icc 1 T, ψ (n : ZMod c)‖ ≤
        ‖∑ n ∈ Icc 1 (cofactorPrefixSelector ψ B), ψ (n : ZMod c)‖ := by
  have h := Classical.choose_spec (Finset.exists_max_image (range (B+1))
    (fun T => ‖∑ n ∈ Icc 1 T, ψ (n : ZMod c)‖) ⟨0,by simp⟩)
  exact ⟨by have := mem_range.mp h.1; exact Nat.le_of_lt_succ this,
    fun T hT => h.2 T (mem_range.mpr (by omega))⟩

noncomputable def cofactorMaxPrefix {c : ℕ} (ψ : DirichletCharacter ℂ c) (B : ℕ) : ℝ :=
  ‖∑ n ∈ Icc 1 (cofactorPrefixSelector ψ B), ψ (n : ZMod c)‖

lemma cofactorMaxPrefix_nonneg {c : ℕ} (ψ : DirichletCharacter ℂ c) (B : ℕ) :
    0 ≤ cofactorMaxPrefix ψ B := norm_nonneg _

lemma cofactor_prefix_le_max {c : ℕ} (ψ : DirichletCharacter ℂ c) (B T : ℕ) (hT : T ≤ B) :
    ‖∑ n ∈ Icc 1 T, ψ (n : ZMod c)‖ ≤ cofactorMaxPrefix ψ B :=
  (cofactorPrefixSelector_spec ψ B).2 T hT

lemma cofactorMaxPrefix_le {c : ℕ} (ψ : DirichletCharacter ℂ c) (B : ℕ) :
    cofactorMaxPrefix ψ B ≤ B := by
  have h := cofactor_character_sum_trivial ψ 0 (cofactorPrefixSelector ψ B)
  simp only [zero_add,Nat.sub_zero] at h
  exact h.trans (by exact_mod_cast (cofactorPrefixSelector_spec ψ B).1)

lemma primeSiftedCharacter_prefix_bound {c : ℕ} (ψ : DirichletCharacter ℂ c)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (B T : ℕ) (hT : T ≤ B) :
    ‖∑ n ∈ Icc 1 T, primeSiftedCharacter ψ P n‖ ≤
      (2 : ℝ)^P.card*cofactorMaxPrefix ψ B := by
  induction P using Finset.induction generalizing T with
  | empty => simpa [primeSiftedCharacter] using cofactor_prefix_le_max ψ B T hT
  | @insert p P hpP ih =>
    have hp : p.Prime := hP p (mem_insert_self _ _)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have he : (∑ n ∈ Icc 1 T, primeSiftedCharacter ψ (insert p P) n) =
        (∑ n ∈ Icc 1 T, primeSiftedCharacter ψ P n)-
          ψ (p : ZMod c)*(∑ n ∈ Icc 1 (T/p), primeSiftedCharacter ψ P n) := by
      simp_rw [primeSiftedCharacter_insert]
      rw [sum_sub_distrib,← sum_filter]
      rw [show Icc 1 T = Icc (0+1) T by rfl,
        sum_multiples_natural_interval _ 0 T p hp.pos]
      simp only [Nat.zero_div,zero_add,primeSiftedCharacter_prime_mul ψ P hP' p hp hpP]
      rw [← mul_sum]
    rw [he,card_insert_of_notMem hpP,pow_succ]
    calc
      _ ≤ ‖∑ n ∈ Icc 1 T, primeSiftedCharacter ψ P n‖+
          ‖ψ (p : ZMod c)*(∑ n ∈ Icc 1 (T/p), primeSiftedCharacter ψ P n)‖ := norm_sub_le _ _
      _ ≤ (2 : ℝ)^P.card*cofactorMaxPrefix ψ B+1*((2 : ℝ)^P.card*cofactorMaxPrefix ψ B) := by
        apply _root_.add_le_add (ih hP' T hT)
        rw [norm_mul]
        exact mul_le_mul (ψ.norm_le_one _) (ih hP' (T/p) ((Nat.div_le_self T p).trans hT))
          (norm_nonneg _) (by norm_num)
      _ = _ := by ring

lemma changeLevel_prefix_le_max {c d : ℕ} (hcd : c ∣ d) (hd : d ≠ 0)
    (ψ : DirichletCharacter ℂ c) (B : ℕ) :
    ‖∑ n ∈ Icc 1 B, (DirichletCharacter.changeLevel hcd ψ) (n : ZMod d)‖ ≤
      (2 : ℝ)^d.primeFactors.card*cofactorMaxPrefix ψ B := by
  simp_rw [changeLevel_eq_primeSiftedCharacter hcd hd ψ]
  exact primeSiftedCharacter_prefix_bound ψ d.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) B B le_rfl

end Erdos821.AnalyticSieve
