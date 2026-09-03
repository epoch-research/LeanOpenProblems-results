import Submission.HigherPhaseRepresentation

/-! Exact polynomial extension from a finite interval. A local vanishing
finite-difference hypothesis suffices; no assumption is made outside the interval. -/
namespace Erdos3LocalPolynomialPhaseExtension
open Finset Erdos3HigherPhaseDifferences Erdos3HigherPhaseRepresentation
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

lemma diffIter_zero {G : Type*} [AddCommGroup G] (k : ℕ) :
    diffIter k (0 : ℕ → G) = 0 := by
  simpa only [fwdDiff_aux.coe_fwdDiffₗ_pow] using
    map_zero ((fwdDiff_aux.fwdDiffₗ ℕ G 1)^k)

lemma local_higher_difference_zero {G : Type*} [AddCommGroup G]
    (f : ℕ → G) {k N : ℕ} (hf : ∀ n, n+(k+1) ≤ N → diffIter (k+1) f n = 0)
    {l : ℕ} (hl : k+1 ≤ l) (n : ℕ) (hn : n+l ≤ N) : diffIter l f n = 0 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hl
  induction r generalizing n with
  | zero => simpa only [Nat.add_zero] using hf n hn
  | succ r ih =>
    have h0 := ih n (by omega) (by omega)
    have h1 := ih (n+1) (by omega) (by omega)
    rw [show k+1+(r+1) = (k+1+r)+1 by omega]
    rw [diffIter,Function.iterate_succ_apply']
    change fwdDiff (1 : ℕ) (diffIter (k+1+r) f) n = 0
    simp only [fwdDiff,h0,h1,sub_self]

/-- Truncated Newton's formula on a finite interval. -/
theorem local_newton_formula {G : Type*} [AddCommGroup G]
    (f : ℕ → G) {k N : ℕ} (hf : ∀ n, n+(k+1) ≤ N → diffIter (k+1) f n = 0)
    (n : ℕ) (hn : n ≤ N) :
    f n = ∑ j ∈ range (k+1), n.choose j • diffIter j f 0 := by
  have hnewton : f n = ∑ j ∈ range (n+1), n.choose j • diffIter j f 0 := by
    simpa only [nsmul_eq_mul,mul_one,zero_add] using shift_eq_sum_fwdDiff_iter (1 : ℕ) f n 0
  rw [hnewton]
  by_cases hnk : n ≤ k
  · apply sum_subset (range_mono (by omega))
    intro j hj hnot
    have hnj : n < j := by simp only [mem_range] at hj hnot; omega
    rw [Nat.choose_eq_zero_of_lt hnj,zero_smul]
  · symm
    apply sum_subset (range_mono (by omega))
    intro j hj hnot
    have hjk : k+1 ≤ j := by simpa only [mem_range,not_lt] using hnot
    have hjN : 0+j ≤ N := by simp only [mem_range] at hj; omega
    rw [local_higher_difference_zero f hf hjk 0 hjN,nsmul_zero]

lemma diffIter_choose_zero {j k : ℕ} (hj : j < k) :
    diffIter k (fun n : ℕ ↦ (n.choose j : ℤ)) = 0 := by
  have hh : diffIter j (fun n : ℕ ↦ (n.choose j : ℤ)) = fun _ ↦ (1 : ℤ) := by
    simpa only [Nat.add_zero,Nat.choose_zero_right,Nat.cast_one] using fwdDiff_iter_choose 0 j
  have hz : diffIter (j+1) (fun n : ℕ ↦ (n.choose j : ℤ)) = 0 := by
    rw [diffIter,Function.iterate_succ_apply']
    change fwdDiff (1 : ℕ) (diffIter j (fun n : ℕ ↦ (n.choose j : ℤ))) = 0
    rw [hh,fwdDiff_const]
    rfl
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le (by omega : j+1 ≤ k)
  rw [show k = r+(j+1) by omega]
  rw [diffIter,Function.iterate_add_apply]
  change diffIter r (diffIter (j+1) (fun n : ℕ ↦ (n.choose j : ℤ))) = 0
  rw [hz,diffIter_zero]

lemma diffIter_choose_smul_zero {G : Type*} [AddCommGroup G]
    (z : G) {j k : ℕ} (hj : j < k) :
    diffIter k (fun n : ℕ ↦ n.choose j • z) = 0 := by
  let φ : ℤ →+ G := zmultiplesHom G z
  have he : (fun n : ℕ ↦ n.choose j • z) = fun n : ℕ ↦ φ (n.choose j : ℤ) := by
    funext n
    exact (natCast_zsmul _ _).symm
  rw [he,diffIter_map,diffIter_choose_zero hj]
  funext n
  exact map_zero φ

noncomputable def newtonExtension {G : Type*} [AddCommGroup G] (k : ℕ) (f : ℕ → G) (n : ℕ) : G :=
  ∑ j ∈ range (k+1), n.choose j • diffIter j f 0

lemma newtonExtension_difference_zero {G : Type*} [AddCommGroup G] (k : ℕ) (f : ℕ → G) :
    diffIter (k+1) (newtonExtension k f) = 0 := by
  have he : newtonExtension k f = ∑ j ∈ range (k+1), (fun n : ℕ ↦ n.choose j • diffIter j f 0) := by
    funext n
    simp only [newtonExtension,sum_apply]
  rw [he]
  change (fwdDiff (1 : ℕ))^[k+1] _ = 0
  rw [fwdDiff_iter_finset_sum]
  apply sum_eq_zero
  intro j hj
  exact diffIter_choose_smul_zero _ (mem_range.mp hj)

lemma newtonExtension_eq {G : Type*} [AddCommGroup G] (f : ℕ → G) {k N : ℕ}
    (hf : ∀ n, n+(k+1) ≤ N → diffIter (k+1) f n = 0) (n : ℕ) (hn : n ≤ N) :
    newtonExtension k f n = f n := (local_newton_formula f hf n hn).symm

/-- Exact monomial coordinates valid on the entire prescribed finite interval. -/
theorem local_polynomial_phase_representation (f : ℕ → Additive Circle) (k N : ℕ)
    (hf : ∀ n, n+(k+1) ≤ N → diffIter (k+1) f n = 0) :
    ∃ c : Fin (k+1) → Additive Circle, ∀ n ≤ N, f n = ∑ j, (n^j.val) • c j := by
  obtain ⟨c,hc⟩ := polynomial_phase_representation k (newtonExtension k f)
    (newtonExtension_difference_zero k f)
  exact ⟨c,fun n hn ↦ (newtonExtension_eq f hf n hn).symm.trans (hc n)⟩

/-- Unit-complex coordinates, with no implicit global polynomiality assumption. -/
theorem local_polynomial_phase_product (f : ℕ → Additive Circle) (k N : ℕ)
    (hf : ∀ n, n+(k+1) ≤ N → diffIter (k+1) f n = 0) :
    ∃ c : Fin (k+1) → ℂ, (∀ j, ‖c j‖ = 1) ∧
      ∀ n ≤ N, phase (f n) = ∏ j, (c j)^(n^j.val) := by
  obtain ⟨c,hc⟩ := local_polynomial_phase_representation f k N hf
  refine ⟨fun j ↦ phase (c j),fun j ↦ phase_norm _,?_⟩
  intro n hn
  rw [hc n hn,phase_sum]
  simp only [phase_nsmul]

#print axioms local_newton_formula
#print axioms local_polynomial_phase_product
end Erdos3LocalPolynomialPhaseExtension
