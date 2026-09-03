import Submission.RecurrentAdmissibleReduction
import Submission.ReturnDisplacementObstruction

/-! In a uniformly recurrent admissible ray, sufficiently long increment
blocks determine both coordinate residues at every finite split-prime cutoff.
The detection length and recurrence bounds remain uncontrolled. -/
namespace Erdos952Investigation
namespace UniformReturnRecognition
open MinimalWordLimit AdmissibleRay SievePeriodicDrift ReturnDisplacementObstruction
open RecurrentAdmissibleReduction (increment)
set_option maxHeartbeats 0

lemma matching_block_displacement (x : ℕ → GaussianInt) (a b L : ℕ)
    (h : ∀ i < L, increment x (a+i) = increment x (b+i)) :
    ∀ i ≤ L, x (b+i)-x (a+i) = x b-x a := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have hs := h i (by omega)
    have hh := ih (by omega)
    dsimp [increment] at hs
    simp only [Nat.add_assoc] at hs
    linear_combination hh-hs

/-- Uniform recurrence upgrades recognition at one fixed prefix to a
uniform residue-recognition length for every pair of positions. -/
theorem uniform_splitPrimorial_recognition (x : ℕ → GaussianInt)
    (hr : UniformlyRecurrent (increment x)) (S : ℕ)
    (ha : ∀ p ≤ S, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (x n)) :
    ∃ T : ℕ, ∀ a b : ℕ,
      (∀ i < T, increment x (a+i) = increment x (b+i)) →
      (splitPrimorial S : ℤ) ∣ (x b-x a).re ∧
        (splitPrimorial S : ℤ) ∣ (x b-x a).im := by
  obtain ⟨L,hL⟩ := splitPrimorial_divides_long_return x S ha
  obtain ⟨R,hR⟩ := hr L
  refine ⟨R+L,?_⟩
  intro a b hmatch
  obtain ⟨n,han,hnR,hn⟩ := hR a
  let t := n-a
  have ht : t ≤ R := by dsimp [t]; omega
  have hat : a+t = n := by dsimp [t]; omega
  have hbn : ∀ i < L, increment x (b+t+i) = increment x i := by
    intro i hi
    have he := hmatch (t+i) (by omega)
    have he' : increment x (a+(t+i)) = increment x i := by
      simpa only [← Nat.add_assoc,hat] using hn i hi
    simpa only [Nat.add_assoc] using he.symm.trans he'
  have hdA := hL n hn
  have hdB := hL (b+t) hbn
  have hd := matching_block_displacement x a b (R+L) hmatch t (by omega)
  rw [hat] at hd
  have hrdiv := dvd_sub hdB.1 hdA.1
  have hidiv := dvd_sub hdB.2 hdA.2
  have her : (x (b+t)-x 0).re-(x n-x 0).re = (x b-x a).re := by
    rw [← hd]
    simp only [Zsqrtd.re_sub]
    ring
  have hei : (x (b+t)-x 0).im-(x n-x 0).im = (x b-x a).im := by
    rw [← hd]
    simp only [Zsqrtd.im_sub]
    ring
  exact ⟨her ▸ hrdiv,hei ▸ hidiv⟩

/-- Equal long blocks are separated in displacement by the split primorial. -/
theorem uniform_return_taxicab_separation (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hr : UniformlyRecurrent (increment x))
    (S : ℕ)
    (ha : ∀ p ≤ S, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (x n)) :
    ∃ T : ℕ, ∀ a b : ℕ, a ≠ b →
      (∀ i < T, increment x (a+i) = increment x (b+i)) →
      (splitPrimorial S : ℤ) ≤ |(x b-x a).re|+|(x b-x a).im| := by
  obtain ⟨T,hT⟩ := uniform_splitPrimorial_recognition x hr S ha
  refine ⟨T,?_⟩
  intro a b hab hmatch
  obtain ⟨hre,him⟩ := hT a b hmatch
  exact le_taxicab_of_dvd_coordinates
    (fun he => hab (hx (sub_eq_zero.mp he)).symm) hre him

/-- The same separation in time, for a bounded-step ray. -/
theorem uniform_return_time_separation (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x) (hs : ∀ n, (increment x n).norm < C)
    (hr : UniformlyRecurrent (increment x)) (S : ℕ)
    (ha : ∀ p ≤ S, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (x n)) :
    ∃ T : ℕ, ∀ a b : ℕ, a < b →
      (∀ i < T, increment x (a+i) = increment x (b+i)) →
      (splitPrimorial S : ℤ) ≤ ((b-a : ℕ) : ℤ)*C := by
  obtain ⟨T,hT⟩ := uniform_return_taxicab_separation x hx hr S ha
  refine ⟨T,?_⟩
  intro a b hab hmatch
  have hh := taxicab_drift_le x C hs a (b-a)
  rw [Nat.add_sub_of_le hab.le] at hh
  exact (hT a b hab.ne hmatch).trans hh

/-- A recurrence bound must dominate the arithmetic return separation.
This is not a contradiction: both the recognized block length `T` and its
recurrence bound `R` are allowed to grow with the cutoff. -/
theorem recurrence_gap_lower_bound (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x) (hs : ∀ n, (increment x n).norm < C)
    (hr : UniformlyRecurrent (increment x)) (S : ℕ)
    (ha : ∀ p ≤ S, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (x n)) :
    ∃ T : ℕ, ∀ R : ℕ,
      (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ n ≤ N+R ∧
        ∀ i < T, increment x (n+i) = increment x i) →
      (splitPrimorial S : ℤ) ≤ ((R+1 : ℕ) : ℤ)*C := by
  obtain ⟨T,hT⟩ := uniform_return_time_separation x C hx hs hr S ha
  refine ⟨T,?_⟩
  intro R hR
  obtain ⟨n,hn,hnR,hmatch⟩ := hR 1
  have hbound := hT 0 n (by omega) (by simpa using fun i hi => (hmatch i hi).symm)
  simp only [Nat.sub_zero] at hbound
  have hC : 0 ≤ C := (GaussianInt.norm_nonneg _).trans (hs 0).le
  have hcast : (n : ℤ) ≤ (R+1 : ℕ) := by exact_mod_cast (show n ≤ R+1 by omega)
  exact hbound.trans (mul_le_mul_of_nonneg_right hcast hC)

#print axioms uniform_splitPrimorial_recognition
#print axioms uniform_return_time_separation
#print axioms recurrence_gap_lower_bound
end UniformReturnRecognition
end Erdos952Investigation
