import FormalConjectures.Util.ProblemImports

open Nat
open Polynomial

def apery_coeff (n k : ℕ) : ℕ := (n.choose k) ^ 2 * ((n + k).choose k)

lemma apery_coeff_coprime (n k p : ℕ) (hp : p.Prime) (hn : n < p) (h : n + k < p) (hk : k ≤ n) :
    p.Coprime (apery_coeff n k) := by
  dsimp [apery_coeff]
  have hc1 : p.Coprime (n.choose k) := Nat.Prime.coprime_choose_of_lt hp hn hk
  have hc2 : p.Coprime (n.choose k ^ 2) := Nat.Coprime.pow_right 2 hc1
  have hc3 : p.Coprime ((n + k).choose k) := Nat.Prime.coprime_choose_of_lt hp h (by linarith)
  exact Nat.Coprime.mul_right hc2 hc3

lemma apery_coeff_dvd (n k p : ℕ) (hp : p.Prime) (hn : n < p) (h : p ≤ n + k) (hk : k ≤ n) :
    p ∣ apery_coeff n k := by
  dsimp [apery_coeff]
  have hk_lt : k < p := by linarith
  have hn_lt : n < p := hn
  have hdvd : p ∣ (n + k).choose k := by
    have h_eq : k + n = n + k := Nat.add_comm k n
    have hd : p ∣ (k + n).choose k := Nat.Prime.dvd_choose_add hp hk_lt hn_lt (by linarith)
    rwa [h_eq] at hd
  exact dvd_mul_of_dvd_right hdvd _

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

#check (inferInstance : Decidable (Irreducible (apery_poly 3)))
#check Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
