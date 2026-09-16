import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma I2_subset (p : ℕ) (hp : 5 ≤ p) (M : ℕ) (hM : p ≤ M) :
  let n := p * (p - 2)
  let L2 := p * M + 1
  let R2 := p * M + n
  let S2 := (Icc L2 R2).filter (fun k => 1 < k ∧ ¬ k.Prime)
  (Icc (M + 1) (M + p - 2)).image (fun x => p * x) ⊆ S2 := by
  intro n L2 R2 S2 y
  dsimp [S2]
  simp only [mem_image, mem_filter, mem_Icc]
  rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · dsimp [L2]
    nlinarith
  · dsimp [R2, n]
    have hp2 : 2 ≤ p := by omega
    have H : (p * x : ℤ) ≤ (p : ℤ) * M + (p : ℤ) * (p - 2) := by
      have hx2_z : (x : ℤ) ≤ (M : ℤ) + (p : ℤ) - 2 := by
        have : (M + p - 2 : ℤ) = (M : ℤ) + (p : ℤ) - 2 := by omega
        have H_le : (x : ℤ) ≤ ((M + p - 2 : ℕ) : ℤ) := by exact_mod_cast hx2
        omega
      nlinarith
    exact_mod_cast H
  · have hx_gt1 : 1 < x := by omega
    nlinarith
  · intro h_prime
    have hdvd : p ∣ p * x := dvd_mul_right p x
    have hx_gt1 : 1 < x := by omega
    have hp_gt1 : 1 < p := by omega
    have := h_prime.eq_one_or_self_of_dvd p hdvd
    rcases this with h1 | h2
    · omega
    · have : x = 1 := by nlinarith
      omega
