import Submission.NewmanDilatedFactors
import Submission.NewmanQuarticSquare

/-! An exact exclusion of all nontrivial uniform dilations of the known
quartic factor. Other irreducible shapes remain uncontrolled. -/
namespace Erdos406QuarticDilations
open Polynomial Erdos406QuarticSquare Erdos406Cyclotomic Erdos406FactorParity

lemma quartic_square_parameter (t y : ℤ) (ht : 0 ≤ t)
    (he : (2*t+1)^4 - (2*t+1)^3 + (2*t+1)^2 + 1 = y^2) : t = 1 := by
  have hy0 := abs_nonneg y
  by_cases hz : t = 0
  · subst t
    norm_num at he
    have hlo : (1 : ℤ) < |y| := (sq_lt_sq₀ (by norm_num) hy0).mp (by
      rw [sq_abs, ← he]; norm_num)
    have hhi : |y| < (2 : ℤ) := (sq_lt_sq₀ hy0 (by norm_num)).mp (by
      rw [sq_abs, ← he]; norm_num)
    omega
  by_contra hn
  have ht2 : 2 ≤ t := by omega
  let m := 4*t^2+3*t+1
  have hm0 : 0 ≤ m-1 := by dsimp [m]; nlinarith [sq_nonneg t]
  have hm1 : 0 ≤ m := by omega
  have hlow : (m-1)^2 < y^2 := by dsimp [m]; nlinarith [sq_nonneg t]
  have hhigh : y^2 < m^2 := by dsimp [m]; nlinarith
  have hlo : m-1 < |y| := (sq_lt_sq₀ hm0 hy0).mp (by simpa only [sq_abs] using hlow)
  have hhi : |y| < m := (sq_lt_sq₀ hy0 hm1).mp (by simpa only [sq_abs] using hhigh)
  omega

lemma known_quartic_square_odd_input (x : ℕ) (hx : Odd x)
    (hs : IsSquare (qQuartic.eval (x : ℤ))) : x = 3 := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨y, hy⟩ := hs
  have he : (2*(t : ℤ)+1)^4 - (2*(t : ℤ)+1)^3 + (2*(t : ℤ)+1)^2 + 1 = y^2 := by
    simpa [qQuartic, ht, pow_two] using hy
  have h1 := quartic_square_parameter (t : ℤ) y (by omega) he
  have ht1 : t = 1 := by exact_mod_cast h1
  omega

/-- A candidate cannot contain qQuartic(X^L) with any spacing L>1. This
excludes an unbounded-degree family rather than one fixed degree. -/
theorem candidate_quartic_dilation_spacing (k L : ℕ)
    (hg : Nat.digits 3 (2^k) ⊆ [0, 1]) (hL : 0 < L)
    (hd : expand ℤ L qQuartic ∣ digitPoly (Nat.digits 3 (2^k))) : L = 1 := by
  have hm : qQuartic.Monic := by unfold qQuartic; monicity <;> norm_num
  have hM : (expand ℤ L qQuartic).Monic := Monic.expand hL hm
  obtain ⟨_, t, _, ht⟩ := candidate_monic_factor k hg _ hM hd
  have he : qQuartic.eval (((3 : ℕ)^L : ℕ) : ℤ) = (4 : ℤ)^t := by
    simpa only [expand_eq_comp_X_pow, eval_comp, eval_pow, eval_X, Nat.cast_pow, Nat.cast_ofNat]
      using ht
  have hsq : IsSquare (qQuartic.eval (((3 : ℕ)^L : ℕ) : ℤ)) := by
    rw [he]
    exact (show IsSquare (4 : ℤ) from ⟨2, by norm_num⟩).pow t
  have hx := known_quartic_square_odd_input (3^L) ((by decide : Odd (3 : ℕ)).pow) hsq
  exact Nat.pow_right_injective (by decide : 2 ≤ 3) (by simpa using hx)

#print axioms known_quartic_square_odd_input
#print axioms candidate_quartic_dilation_spacing
end Erdos406QuarticDilations
