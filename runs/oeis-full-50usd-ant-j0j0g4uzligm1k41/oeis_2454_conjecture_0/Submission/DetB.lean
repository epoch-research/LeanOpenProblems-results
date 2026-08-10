import FormalConjectures.Util.ProblemImports

open Nat
open Matrix Complex
open scoped BigOperators

namespace DetB

/-- Geometric character sum over `Fin N`. -/
theorem char_sum (ζ : ℂ) (N : ℕ) (hζ : IsPrimitiveRoot ζ N) (k : ℕ) :
    ∑ j : Fin N, ζ ^ (k * (j : ℕ)) = if N ∣ k then (N : ℂ) else 0 := by
  have hne : ∀ i : Fin N, ζ ^ (k * (i:ℕ)) = (ζ ^ k) ^ (i:ℕ) := by
    intro i; rw [← pow_mul]
  simp_rw [hne]
  rw [Fin.sum_univ_eq_sum_range (fun i => (ζ ^ k) ^ i)]
  by_cases hdvd : N ∣ k
  · have : ζ ^ k = 1 := by
      obtain ⟨t, rfl⟩ := hdvd
      rw [pow_mul, hζ.pow_eq_one, one_pow]
    simp [this, hdvd]
  · have hk1 : ζ ^ k ≠ 1 := by
      rw [ne_eq, hζ.pow_eq_one_iff_dvd]
      exact hdvd
    rw [geom_sum_eq hk1]
    have : (ζ ^ k) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [this]
    simp [hdvd]

/-- Divisibility characterization: for `p q : Fin N`, `N ∣ (p + (N-1)*q) ↔ p = q`. -/
theorem dvd_iff_eq {N : ℕ} (hN : 0 < N) (p q : Fin N) :
    N ∣ ((p : ℕ) + (N - 1) * (q : ℕ)) ↔ p = q := by
  rw [← ZMod.natCast_eq_zero_iff]
  have key : (((p:ℕ) + (N-1)*(q:ℕ) : ℕ) : ZMod N) = ((p:ℕ) : ZMod N) - ((q:ℕ) : ZMod N) := by
    push_cast [Nat.cast_sub hN, ZMod.natCast_self]
    ring
  rw [key, sub_eq_zero, ZMod.natCast_eq_natCast_iff]
  constructor
  · intro h
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt h p.isLt q.isLt)
  · rintro rfl; rfl

/-- Fourier matrix. -/
def Fmat (ζ : ℂ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun p j => ζ ^ ((p : ℕ) * (j : ℕ))

/-- Inverse Fourier matrix. -/
noncomputable def Finvmat (ζ : ℂ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j p => (N : ℂ)⁻¹ * ζ ^ ((N - 1) * ((j : ℕ) * (p : ℕ)))

theorem Fmat_mul_Finvmat (ζ : ℂ) (N : ℕ) (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) :
    Fmat ζ N * Finvmat ζ N = 1 := by
  ext p q
  rw [Matrix.mul_apply]
  simp only [Fmat, Finvmat, Matrix.of_apply]
  have step : ∀ j : Fin N,
      ζ ^ ((p:ℕ) * (j:ℕ)) * ((N:ℂ)⁻¹ * ζ ^ ((N - 1) * ((j:ℕ) * (q:ℕ))))
        = (N:ℂ)⁻¹ * ζ ^ (((p:ℕ) + (N - 1) * (q:ℕ)) * (j:ℕ)) := by
    intro j
    rw [show (((p:ℕ) + (N - 1) * (q:ℕ)) * (j:ℕ))
          = (p:ℕ) * (j:ℕ) + (N - 1) * ((j:ℕ) * (q:ℕ)) by ring, pow_add]
    ring
  simp_rw [step]
  rw [← Finset.mul_sum, char_sum ζ N hζ ((p:ℕ) + (N - 1) * (q:ℕ)), Matrix.one_apply]
  by_cases hpq : p = q
  · rw [if_pos ((dvd_iff_eq hN p q).mpr hpq), if_pos hpq]
    have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    field_simp
  · rw [if_neg (fun h => hpq ((dvd_iff_eq hN p q).mp h)), if_neg hpq, mul_zero]

theorem Finvmat_mul_Fmat (ζ : ℂ) (N : ℕ) (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) :
    Finvmat ζ N * Fmat ζ N = 1 :=
  Matrix.mul_eq_one_comm.mpr (Fmat_mul_Finvmat ζ N hN hζ)

theorem det_Fmat_unit (ζ : ℂ) (N : ℕ) (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) :
    IsUnit (Fmat ζ N).det := by
  have h : (Fmat ζ N).det * (Finvmat ζ N).det = 1 := by
    rw [← Matrix.det_mul, Fmat_mul_Finvmat ζ N hN hζ, Matrix.det_one]
  exact isUnit_of_mul_eq_one _ h

/-- adjugate of `F` equals `det F • Finv`. -/
theorem adjugate_Fmat (ζ : ℂ) (N : ℕ) (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) :
    (Fmat ζ N).adjugate = (Fmat ζ N).det • Finvmat ζ N := by
  have h1 := Fmat_mul_Finvmat ζ N hN hζ
  calc (Fmat ζ N).adjugate = (Fmat ζ N).adjugate * (Fmat ζ N * Finvmat ζ N) := by rw [h1, mul_one]
    _ = ((Fmat ζ N).adjugate * Fmat ζ N) * Finvmat ζ N := by rw [mul_assoc]
    _ = ((Fmat ζ N).det • (1 : Matrix (Fin N) (Fin N) ℂ)) * Finvmat ζ N := by rw [Matrix.adjugate_mul]
    _ = (Fmat ζ N).det • Finvmat ζ N := by rw [smul_mul_assoc, one_mul]

theorem adjugate_Finvmat (ζ : ℂ) (N : ℕ) (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) :
    (Finvmat ζ N).adjugate = (Finvmat ζ N).det • Fmat ζ N := by
  have h1 := Finvmat_mul_Fmat ζ N hN hζ
  calc (Finvmat ζ N).adjugate = (Finvmat ζ N).adjugate * (Finvmat ζ N * Fmat ζ N) := by rw [h1, mul_one]
    _ = ((Finvmat ζ N).adjugate * Finvmat ζ N) * Fmat ζ N := by rw [mul_assoc]
    _ = ((Finvmat ζ N).det • (1 : Matrix (Fin N) (Fin N) ℂ)) * Fmat ζ N := by rw [Matrix.adjugate_mul]
    _ = (Finvmat ζ N).det • Fmat ζ N := by rw [smul_mul_assoc, one_mul]

/-- The key adjugate-conjugation identity: `adjugate (Finv*Λ*F) = Finv * adjugate Λ * F`. -/
theorem adjugate_conj (ζ : ℂ) (N : ℕ) (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N)
    (Λ : Matrix (Fin N) (Fin N) ℂ) :
    (Finvmat ζ N * Λ * Fmat ζ N).adjugate = Finvmat ζ N * Λ.adjugate * Fmat ζ N := by
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
      adjugate_Fmat ζ N hN hζ, adjugate_Finvmat ζ N hN hζ]
  -- goal: det F • Finv * (adjugate Λ * (det Finv • F)) = Finv * adjugate Λ * F
  have hdet : (Fmat ζ N).det * (Finvmat ζ N).det = 1 := by
    rw [← Matrix.det_mul, Fmat_mul_Finvmat ζ N hN hζ, Matrix.det_one]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hdet, one_smul, mul_assoc]

/-- Core determinant formula via the adjugate of a diagonalized circulant.
The principal `2m × 2m` (i.e. delete last index) submatrix of `Finv · diagonal λ · F`
has determinant `(1/N) ∑_p ∏_{q≠p} λ q`. -/
theorem detG0_abstract (n : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (n+1)) (lam : Fin (n+1) → ℂ) :
    ((Finvmat ζ (n+1) * Matrix.diagonal lam * Fmat ζ (n+1)).submatrix
        Fin.castSucc Fin.castSucc).det
      = ((n+1 : ℕ) : ℂ)⁻¹ * ∑ p : Fin (n+1), ∏ q ∈ Finset.univ.erase p, lam q := by
  have hN : 0 < n + 1 := Nat.succ_pos n
  set Ghat := Finvmat ζ (n+1) * Matrix.diagonal lam * Fmat ζ (n+1) with hGhat
  -- bridge: principal minor = adjugate diagonal entry
  have hbridge : (Ghat.submatrix Fin.castSucc Fin.castSucc).det
      = Ghat.adjugate (Fin.last n) (Fin.last n) := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    have hsign : ((-1 : ℂ)) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) = 1 := by
      rw [Fin.val_last, show n + n = 2 * n by ring, pow_mul, neg_one_sq, one_pow]
    rw [hsign, one_mul, Fin.succAbove_last]
  rw [hbridge, hGhat, adjugate_conj ζ (n+1) hN hζ, Matrix.adjugate_diagonal]
  -- now evaluate (Finv * diagonal μ * F) last last
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Finvmat, Fmat, Matrix.of_apply]
  have e : (n + 1 - 1) * ((Fin.last n : ℕ) * (p : ℕ)) + (p : ℕ) * (Fin.last n : ℕ)
      = (n + 1) * ((Fin.last n : ℕ) * (p : ℕ)) := by
    simp only [Nat.add_sub_cancel]; ring
  calc (((n + 1 : ℕ) : ℂ)⁻¹ * ζ ^ ((n + 1 - 1) * ((Fin.last n : ℕ) * (p : ℕ))))
          * (∏ q ∈ Finset.univ.erase p, lam q) * ζ ^ ((p : ℕ) * (Fin.last n : ℕ))
      = ((n + 1 : ℕ) : ℂ)⁻¹ * (∏ q ∈ Finset.univ.erase p, lam q)
          * (ζ ^ ((n + 1 - 1) * ((Fin.last n : ℕ) * (p : ℕ))) * ζ ^ ((p : ℕ) * (Fin.last n : ℕ))) := by
        ring
    _ = ((n + 1 : ℕ) : ℂ)⁻¹ * (∏ q ∈ Finset.univ.erase p, lam q)
          * ζ ^ ((n + 1) * ((Fin.last n : ℕ) * (p : ℕ))) := by rw [← pow_add, e]
    _ = ((n + 1 : ℕ) : ℂ)⁻¹ * (∏ q ∈ Finset.univ.erase p, lam q) * 1 := by
        rw [pow_mul, hζ.pow_eq_one, one_pow]
    _ = ((n + 1 : ℕ) : ℂ)⁻¹ * ∏ q ∈ Finset.univ.erase p, lam q := by rw [mul_one]

end DetB
