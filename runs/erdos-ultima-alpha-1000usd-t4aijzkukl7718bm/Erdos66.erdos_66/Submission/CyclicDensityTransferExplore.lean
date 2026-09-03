import Submission.CyclicPaddingExplore

/-! Quantitative density control under finite cyclic padding. -/
namespace Erdos66CyclicDensityTransfer
open Erdos66CyclicPadding
open scoped Classical

/-- A source template with nearly the correct density can be repeated and
padded without changing its mean by much. -/
theorem density_transfer (M N : ℕ) [NeZero M] [NeZero N]
    (B : Finset (ZMod M)) (μ ν δ σ ρ : ℝ)
    (hν : 0 ≤ ν) (hδ : 0 ≤ δ) (hσ : 0 ≤ σ) (hρ : 0 ≤ ρ)
    (hB : ∀ z : ZMod M, |(((B.filter (fun a ↦ z-a∈B)).card : ℝ)-ν)| ≤ δ*ν)
    (hlow : (N : ℝ)*ν ≤ M*μ)
    (hupp : (M : ℝ)*μ ≤ (1+σ)*N*ν)
    (hsmall : ν ≤ ρ*μ) :
    ∃ D : Finset (ZMod N), ∀ z : ZMod N,
      |(((D.filter (fun a ↦ z-a∈D)).card : ℝ)-μ)| ≤
        (2*δ+σ+(4+2*δ)*ρ)*μ := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hKM : (M : ℝ)*(N/M : ℕ) ≤ N := by exact_mod_cast Nat.mul_div_le N M
  have hNKM : (N : ℝ) ≤ M*((N/M : ℕ)+1) := by
    have hh := Nat.mod_lt N (NeZero.pos M)
    have hh' := Nat.div_add_mod N M
    have hnat : N ≤ M*(N/M+1) := by nlinarith
    exact_mod_cast hnat
  have hKν : (N/M : ℕ)*ν ≤ μ := by
    apply (mul_le_mul_iff_right₀ hM).mp
    nlinarith [mul_le_mul_of_nonneg_right hKM hν]
  have hσN : σ*((N : ℝ)*ν) ≤ σ*(M*μ) := mul_le_mul_of_nonneg_left hlow hσ
  have hgap : μ-(N/M : ℕ)*ν ≤ σ*μ+ν := by
    have hupper := mul_le_mul_of_nonneg_right hNKM hν
    apply (mul_le_mul_iff_right₀ hM).mp
    nlinarith
  obtain ⟨D,hD⟩ := padding_to_any_modulus M N B ν (δ*ν) hν (mul_nonneg hδ hν) hB
  refine ⟨D,fun z ↦ ?_⟩
  calc
    _ = |((((D.filter (fun a ↦ z-a∈D)).card : ℝ)-(N/M : ℕ)*ν)+
        ((N/M : ℕ)*ν-μ))| := by congr 1; ring
    _ ≤ |(((D.filter (fun a ↦ z-a∈D)).card : ℝ)-(N/M : ℕ)*ν)|+
        |(N/M : ℕ)*ν-μ| := abs_add_le _ _
    _ ≤ (2*(N/M : ℕ)*(δ*ν)+3*ν+2*(δ*ν))+(σ*μ+ν) := by
      exact add_le_add (hD z) (by rw [abs_of_nonpos (sub_nonpos.mpr hKν)]; linarith)
    _ ≤ (2*δ+σ+(4+2*δ)*ρ)*μ := by
      have h₁ := mul_le_mul_of_nonneg_left hKν (show 0 ≤ 2*δ by positivity)
      have h₂ := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 4+2*δ by positivity)
      nlinarith

/-- A convenient numerical version of density transfer. -/
theorem density_transfer_small_error (M N H : ℕ) [NeZero M] [NeZero N]
    (hH : 0 < H) (B : Finset (ZMod M)) (μ ν : ℝ) (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    (hB : ∀ z : ZMod M, |(((B.filter (fun a ↦ z-a∈B)).card : ℝ)-ν)| ≤ (5/(H : ℝ))*ν)
    (hlow : (N : ℝ)*ν ≤ M*μ)
    (hupp : (M : ℝ)*μ ≤ (1+15/(H : ℝ))*N*ν)
    (hsmall : ν ≤ μ/H) :
    ∃ D : Finset (ZMod N), ∀ z : ZMod N,
      |(((D.filter (fun a ↦ z-a∈D)).card : ℝ)-μ)| ≤ (39/(H : ℝ))*μ := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  obtain ⟨D,hD⟩ := density_transfer M N B μ ν (5/H) (15/H) (1/H) hν
    (by positivity) (by positivity) (by positivity) hB hlow hupp
    (by simpa [div_eq_mul_inv,mul_comm] using hsmall)
  refine ⟨D,fun z ↦ (hD z).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ hμ
  field_simp
  nlinarith

end Erdos66CyclicDensityTransfer
