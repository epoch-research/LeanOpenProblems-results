import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  let N := n - 1
  ( (range n).sum fun k => (N.choose k) ^ 2 * ((N + k).choose k) ^ 2 ) ^ 5 *
  ( (range (n + 1)).sum fun k => (n.choose k) ^ 2 * ((n + k).choose k) ) ^ 6

noncomputable def AA (n : ℕ) : ℕ := (range (n+1)).sum fun k => (n.choose k) ^ 2 * ((n + k).choose k) ^ 2
noncomputable def BB (n : ℕ) : ℕ := (range (n + 1)).sum fun k => (n.choose k) ^ 2 * ((n + k).choose k)

-- check a (n) = AA (n-1) ^5 * BB n ^ 6 for n ≥ 1
example (n : ℕ) (hn : 1 ≤ n) : a n = AA (n-1) ^ 5 * BB n ^ 6 := by
  unfold a AA BB
  simp only []
  rw [Nat.sub_add_cancel hn]

-- Reduction lemma over ℤ.
-- pow square-zero helper
example (R : Type) [CommRing R] (A x : R) (hx : x^2 = 0) : (A+x)^5 = A^5 + 5*A^4*x := by
  linear_combination (10*A^3 + 10*A^2*x + 5*A*x^2 + x^3) * hx

example (R : Type) [CommRing R] (B y : R) (hy : y^2 = 0) : (B+y)^6 = B^6 + 6*B^5*y := by
  linear_combination (15*B^4 + 20*B^3*y + 15*B^2*y^2 + 6*B*y^3 + y^4) * hy

-- The core reduction: integers, divisibility hypotheses
theorem reduction (A1 A2 B1 B2 : ℤ) (M : ℕ) (g : ℤ)
    (hMg : (M:ℤ) ∣ g^2) (hgA : g ∣ (A2 - A1)) (hgB : g ∣ (B2 - B1))
    (hstar : (M:ℤ) ∣ (5*B1*(A2-A1) + 6*A1*(B2-B1))) :
    (M:ℤ) ∣ (A2^5 * B2^6 - A1^5 * B1^6) := by
  obtain ⟨eA, heA⟩ := hgA
  obtain ⟨eB, heB⟩ := hgB
  have hA2 : A2 = A1 + g*eA := by linarith [heA]
  have hB2 : B2 = B1 + g*eB := by linarith [heB]
  subst hA2 hB2
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hMg hstar ⊢
  push_cast at hMg hstar ⊢
  set A := (A1 : ZMod M)
  set B := (B1 : ZMod M)
  set G := (g : ZMod M)
  set x := (eA : ZMod M)
  set y := (eB : ZMod M)
  have hg2 : G^2 = 0 := hMg
  have hx2 : (G*x)^2 = 0 := by rw [mul_pow, hg2]; ring
  have hy2 : (G*y)^2 = 0 := by rw [mul_pow, hg2]; ring
  have h5 : (A + G*x)^5 = A^5 + 5*A^4*(G*x) := by
    linear_combination (10*A^3 + 10*A^2*(G*x) + 5*A*(G*x)^2 + (G*x)^3) * hx2
  have h6 : (B + G*y)^6 = B^6 + 6*B^5*(G*y) := by
    linear_combination (15*B^4 + 20*B^3*(G*y) + 15*B^2*(G*y)^2 + 6*B*(G*y)^3 + (G*y)^4) * hy2
  rw [h5, h6]
  linear_combination (A^4*B^5) * hstar + (30*A^4*B^5*x*y) * hg2

-- Main theorem wiring test (with hard lemmas as hypotheses)
theorem main_test (p r : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) (hr_ge_2 : 2 ≤ r)
    (costerA : (p^(3*r) : ℤ) ∣ ((AA (p^r - 1) : ℤ) - (AA (p^(r-1) - 1) : ℤ)))
    (costerB : (p^(3*r) : ℤ) ∣ ((BB (p^r) : ℤ) - (BB (p^(r-1)) : ℤ)))
    (starh : (p^(3*r+3) : ℤ) ∣ (5*(BB (p^(r-1)) : ℤ)*((AA (p^r - 1):ℤ) - (AA (p^(r-1)-1):ℤ))
              + 6*(AA (p^(r-1)-1):ℤ)*((BB (p^r):ℤ) - (BB (p^(r-1)):ℤ)))) :
    a (p^r) ≡ a (p^(r-1)) [MOD p^(3*r + 3)] := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp_ge_3
  have hpr : 1 ≤ p^r := Nat.one_le_pow _ _ (by omega)
  have hprm : 1 ≤ p^(r-1) := Nat.one_le_pow _ _ (by omega)
  have ha_r : a (p^r) = AA (p^r - 1) ^ 5 * BB (p^r) ^ 6 := by
    unfold a AA BB; simp only []; rw [Nat.sub_add_cancel hpr]
  have ha_rm : a (p^(r-1)) = AA (p^(r-1) - 1) ^ 5 * BB (p^(r-1)) ^ 6 := by
    unfold a AA BB; simp only []; rw [Nat.sub_add_cancel hprm]
  rw [Nat.modEq_iff_dvd]
  rw [ha_r, ha_rm]
  push_cast
  have hr1 : 1 ≤ r := by omega
  have hMg : (p^(3*r+3) : ℤ) ∣ (p^(3*r))^2 := by
    rw [← pow_mul]
    exact pow_dvd_pow _ (by omega)
  have := reduction (AA (p^(r-1)-1) : ℤ) (AA (p^r-1) : ℤ) (BB (p^(r-1)) : ℤ) (BB (p^r) : ℤ)
      (p^(3*r+3)) (p^(3*r)) (by push_cast at hMg ⊢; exact hMg) costerA costerB (by
        push_cast; exact starh)
  push_cast at this
  -- goal: p^(3r+3) ∣ (A1^5 B1^6 - A2^5 B2^6); this : p^(3r+3) ∣ (A2^5 B2^6 - A1^5 B1^6)
  have := (dvd_neg).2 this
  convert this using 1
  ring
