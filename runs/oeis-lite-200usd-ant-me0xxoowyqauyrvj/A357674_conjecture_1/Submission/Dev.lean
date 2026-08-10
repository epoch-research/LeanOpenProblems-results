import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

def A357674 (n : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ 4 * S2 ^ 3

noncomputable def S1z (p : ℕ) : ℤ := ∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k : ℤ)
noncomputable def S2z (p : ℕ) : ℤ := ∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k : ℤ) ^ 2

theorem cast_A (p : ℕ) : (A357674 p : ℤ) = (S1z p) ^ 4 * (S2z p) ^ 3 := by
  unfold A357674 S1z S2z; push_cast; ring

theorem lemA (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (S1z p) ≡ 3 [ZMOD (p:ℤ)^3] := by sorry

theorem lemC (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    4 * (S1z p) + 3 * (S2z p) ≡ 21 [ZMOD (p:ℤ)^5] := by sorry

theorem assembly (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (S1z p) ^ 4 * (S2z p) ^ 3 ≡ 2187 [ZMOD (p:ℤ)^5] := by
  set x := S1z p with hxdef
  set y := S2z p with hydef
  have hAdvd : (p:ℤ)^3 ∣ (x - 3) := by
    have := (lemA p hp hp5).dvd; simpa [dvd_sub_comm] using this
  have hCdvd : (p:ℤ)^5 ∣ (4*x + 3*y - 21) := by
    have := (lemC p hp hp5).dvd; simpa [dvd_sub_comm] using this
  have h3y : (p:ℤ)^3 ∣ 3*(y - 3) := by
    have h1 : (p:ℤ)^3 ∣ (4*x + 3*y - 21) :=
      dvd_trans (pow_dvd_pow (p:ℤ) (by norm_num)) hCdvd
    have h2 : (p:ℤ)^3 ∣ 4*(x-3) := Dvd.dvd.mul_left hAdvd 4
    have he : 3*(y-3) = (4*x+3*y-21) - 4*(x-3) := by ring
    rw [he]; exact dvd_sub h1 h2
  have hcop3 : IsCoprime ((p:ℤ)) 3 := by
    have h3 : Nat.Prime 3 := by norm_num
    have : Nat.Coprime p 3 := by rw [Nat.coprime_primes hp h3]; omega
    rw [Int.isCoprime_iff_gcd_eq_one]; simpa [Int.gcd] using this
  have hAydvd : (p:ℤ)^3 ∣ (y - 3) := (hcop3.pow_left).dvd_of_dvd_mul_left h3y
  obtain ⟨a, ha⟩ := hAdvd
  obtain ⟨b, hb⟩ := hAydvd
  have hx : x = (p:ℤ)^3*a + 3 := by linear_combination ha
  have hy : y = (p:ℤ)^3*b + 3 := by linear_combination hb
  have heq : 4*x + 3*y - 21 = (p:ℤ)^3*(4*a+3*b) := by rw [hx, hy]; ring
  have hp2 : (p:ℤ)^2 ∣ (4*a+3*b) := by
    rw [heq] at hCdvd
    obtain ⟨k, hk⟩ := hCdvd
    refine ⟨k, ?_⟩
    have hp3ne : (p:ℤ)^3 ≠ 0 := by positivity
    have hee : (p:ℤ)^3*(4*a+3*b) = (p:ℤ)^3*((p:ℤ)^2*k) := by rw [hk]; ring
    exact mul_left_cancel₀ hp3ne hee
  obtain ⟨k, hk2⟩ := hp2
  rw [Int.modEq_iff_dvd, hx, hy]
  refine ⟨-729*k - (p:ℤ)*(
    (p:ℤ)^15*a^4*b^3 + 9*(p:ℤ)^12*a^4*b^2 + 12*(p:ℤ)^12*a^3*b^3
    + 27*(p:ℤ)^9*a^4*b + 108*(p:ℤ)^9*a^3*b^2 + 54*(p:ℤ)^9*a^2*b^3
    + 27*(p:ℤ)^6*a^4 + 324*(p:ℤ)^6*a^3*b + 486*(p:ℤ)^6*a^2*b^2 + 108*(p:ℤ)^6*a*b^3
    + 324*(p:ℤ)^3*a^3 + 1458*(p:ℤ)^3*a^2*b + 972*(p:ℤ)^3*a*b^2 + 81*(p:ℤ)^3*b^3
    + 1458*a^2 + 2916*a*b + 729*b^2), ?_⟩
  linear_combination (-729*(p:ℤ)^3) * hk2

theorem A357674_conjecture_1 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  have hA1 : A357674 1 = 2187 := by native_decide
  rcases eq_or_lt_of_le hp3 with heq | hlt
  · -- p = 3
    rw [← heq]; native_decide
  · have h4 : p ≠ 4 := by rintro rfl; exact (by decide : ¬ Nat.Prime 4) hp
    have hp5 : 5 ≤ p := by omega
    rw [hA1]
    have key : (A357674 p : ℤ) ≡ 2187 [ZMOD ((p^5 : ℕ) : ℤ)] := by
      rw [cast_A]
      have hc : (((p^5:ℕ)):ℤ) = (p:ℤ)^5 := by push_cast; ring
      rw [hc]; exact assembly p hp hp5
    exact_mod_cast key
