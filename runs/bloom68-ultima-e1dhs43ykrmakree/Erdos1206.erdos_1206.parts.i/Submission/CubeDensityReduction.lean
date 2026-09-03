import Submission.SidonExtraction

/-! A checked reduction of the cube-Sidon density target to an explicit sparse-collision bound. -/

namespace CubeDensityReduction

open SidonExtraction

/-- The roots, rather than their cubes, are used for the arithmetic input. -/
def CubeImage (A : Finset ℕ) : Finset ℕ := A.image (fun a => a ^ 3)

theorem cube_injective : Function.Injective (fun a : ℕ => a ^ 3) := by
  intro a b h
  exact (Nat.pow_left_injective (by norm_num : 3 ≠ 0)) h

@[simp]
theorem card_cubeImage (A : Finset ℕ) : (CubeImage A).card = A.card := by
  exact Finset.card_image_of_injective A cube_injective

theorem cubeImage_mono {A B : Finset ℕ} (h : A ⊆ B) : CubeImage A ⊆ CubeImage B :=
  Finset.image_subset_image h

/-- A natural-number bound sufficient for the exact real-valued density target. -/
theorem exists_sidon_of_sparse_roots (N d k : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N) (hcard : N ≤ d * A.card)
    (hedges : (badSupports (CubeImage A)).card ≤ k * N) :
    ∃ S : Finset ℕ, S ⊆ CubeImage (Finset.Icc 1 N) ∧
      IsSidon (S : Set ℕ) ∧ N ≤ (2 * d * (k * d + 2)) * S.card := by
  have he : (badSupports (CubeImage A)).card ≤ (k * d) * (CubeImage A).card := by
    rw [card_cubeImage]
    exact hedges.trans (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left k hcard)
  obtain ⟨S, hSA, hs, hc⟩ := exists_sidon_subset_linear (CubeImage A) (k * d) he
  rw [card_cubeImage] at hc
  refine ⟨S, hSA.trans (cubeImage_mono hA), hs, ?_⟩
  apply hcard.trans
  simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (Nat.mul_le_mul_left d hc)

/-- A complete, checked reduction of the stated conjecture to a uniform arithmetic
sparsification bound. The arithmetic hypothesis is explicit and is not asserted here. -/
theorem density_of_eventually_sparse_roots (d k : ℕ) (hd : 0 < d)
    (h : ∀ᶠ N : ℕ in Filter.atTop, ∃ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N ∧ N ≤ d * A.card ∧
      (badSupports (CubeImage A)).card ≤ k * N) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N in Filter.atTop, ∃ S : Finset ℕ,
      S ⊆ (Finset.Icc 1 N).image (fun n => n ^ 3) ∧
      IsSidon (S : Set ℕ) ∧ c * (N : ℝ) ≤ (S.card : ℝ) := by
  let C : ℕ := 2 * d * (k * d + 2)
  have hC : 0 < C := by dsimp [C]; positivity
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  refine ⟨1 / (C : ℝ), by positivity, ?_⟩
  filter_upwards [h] with N hN
  obtain ⟨A, hA, hc, he⟩ := hN
  obtain ⟨S, hS, hs, hsize⟩ := exists_sidon_of_sparse_roots N d k A hA hc he
  refine ⟨S, hS, hs, ?_⟩
  have hsize' : (N : ℝ) ≤ (C : ℝ) * (S.card : ℝ) := by exact_mod_cast hsize
  calc
    (1 / (C : ℝ)) * (N : ℝ) ≤ (1 / (C : ℝ)) * ((C : ℝ) * (S.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hsize' (by positivity)
    _ = (S.card : ℝ) := by field_simp

#print axioms density_of_eventually_sparse_roots

end CubeDensityReduction
