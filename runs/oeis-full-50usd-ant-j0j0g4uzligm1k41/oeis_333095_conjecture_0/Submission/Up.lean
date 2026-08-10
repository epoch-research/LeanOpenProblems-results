import FormalConjectures.Util.ProblemImports
open Nat Finset PowerSeries

noncomputable section
variable {R : Type*} [CommRing R]

/-- The `U_p` operator on power series: `coeff n (uop p f) = coeff (p*n) f`. -/
def uop (p : ℕ) (f : PowerSeries R) : PowerSeries R := PowerSeries.mk fun n => coeff (p*n) f

@[simp] theorem coeff_uop (p n : ℕ) (f : PowerSeries R) :
    (coeff n) (uop p f) = (coeff (p*n)) f := by
  unfold uop; rw [coeff_mk]

theorem uop_add (p : ℕ) (f g : PowerSeries R) : uop p (f + g) = uop p f + uop p g := by
  ext n; simp

/-- Freshman's dream for power series over `ZMod p`: `expand p f = f ^ p`. -/
theorem expand_eq_pow_zmod (p : ℕ) [Fact p.Prime] (hp : p ≠ 0)
    (f : PowerSeries (ZMod p)) : expand p hp f = f ^ p := by
  have hfrob : frobenius (ZMod p) p = RingHom.id (ZMod p) := by
    ext x; rw [frobenius_def]; exact ZMod.pow_card x
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod p) p hp (f := f)
  rw [hfrob, MvPowerSeries.map_id, RingHom.id_apply] at h
  exact h

/-- Frobenius divisibility: for an integer power series `g`, every coefficient of
`g^p - expand p g` is divisible by `p`. -/
theorem frob_dvd (p : ℕ) [Fact p.Prime] (hp : p ≠ 0) (g : PowerSeries ℤ) (n : ℕ) :
    (p : ℤ) ∣ (coeff n) (g ^ p - expand p hp g) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have e1 : (((coeff n) (g ^ p - expand p hp g) : ℤ) : ZMod p)
      = (coeff n) (PowerSeries.map (Int.castRingHom (ZMod p)) (g ^ p - expand p hp g)) := by
    rw [coeff_map]; rfl
  rw [e1, map_sub, map_pow, PowerSeries.map_expand, expand_eq_pow_zmod, sub_self, map_zero]

/-- Multiplying by `1/(1-X) = ∑ Xⁿ` computes partial sums of coefficients. -/
theorem coeff_mul_geom (F : PowerSeries R) (n : ℕ) :
    (coeff n) (F * PowerSeries.mk fun _ => (1 : R)) = ∑ k ∈ range (n+1), (coeff k) F := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k _
  rw [coeff_mk, mul_one]

/-- The truncation `E = 1 + X + ... + X^{p-1}`, so that `1/(1-X) = E · (1/(1-X^p))`. -/
def Egeom (p : ℕ) : PowerSeries R := ∑ k ∈ range p, (X : PowerSeries R) ^ k

theorem uop_Egeom (p : ℕ) (hp : 0 < p) : uop p (Egeom (R:=R) p) = 1 := by
  ext n
  rw [coeff_uop, Egeom, map_sum]
  simp only [PowerSeries.coeff_X_pow]
  rw [Finset.sum_ite_eq (range p) (p*n) (fun _ => (1:R))]
  rw [coeff_one]
  by_cases hn : n = 0
  · subst hn; simp [hp]
  · have : ¬ (p * n < p) := by
      rw [not_lt]; calc p = p * 1 := by ring
        _ ≤ p * n := by exact Nat.mul_le_mul_left p (by omega)
    simp [Finset.mem_range, this, hn]

/-- The geometric-series split `1/(1-X) = E · expand p (1/(1-X))`. -/
theorem geom_split (p : ℕ) (hp : p ≠ 0) :
    (PowerSeries.mk fun _ => (1:R)) = Egeom p * expand p hp (PowerSeries.mk fun _ => (1:R)) := by
  have hpp : 0 < p := Nat.pos_of_ne_zero hp
  ext n
  rw [coeff_mk, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hE : ∀ i, (coeff i) (Egeom (R:=R) p) = if i < p then 1 else 0 := by
    intro i; rw [Egeom, map_sum]
    simp only [PowerSeries.coeff_X_pow]
    rw [Finset.sum_ite_eq (range p) i (fun _ => (1:R))]; simp [Finset.mem_range]
  have hEx : ∀ j, (coeff j) (expand p hp (PowerSeries.mk fun _ => (1:R)))
      = if p ∣ j then 1 else 0 := by
    intro j; rw [PowerSeries.coeff_expand]; split <;> simp [coeff_mk]
  simp only [hE, hEx]
  rw [Finset.sum_eq_single_of_mem (n % p)]
  · have h1 : n % p < p := Nat.mod_lt _ hpp
    have h2 : p ∣ (n - n % p) := ⟨n / p, by have := Nat.div_add_mod n p; omega⟩
    rw [if_pos h1, if_pos h2, mul_one]
  · rw [Finset.mem_range]; have := Nat.mod_le n p; omega
  · intro i hi hne
    rw [Finset.mem_range] at hi
    by_cases hip : i < p
    · rw [if_pos hip, one_mul, if_neg]
      intro hdvd
      apply hne
      obtain ⟨c, hc⟩ := hdvd
      have hn : n = p * c + i := by omega
      rw [hn, Nat.mul_add_mod, Nat.mod_eq_of_lt hip]
    · rw [if_neg hip, zero_mul]

/-- Coefficientwise division of an integer power series by `p`. -/
def pdiv (p : ℕ) (h : PowerSeries ℤ) : PowerSeries ℤ := PowerSeries.mk fun n => (coeff n h) / (p : ℤ)

/-- If every coefficient of `h` is divisible by `p`, then `p • (pdiv p h) = h`. -/
theorem smul_pdiv (p : ℕ) (h : PowerSeries ℤ) (H : ∀ n, (p : ℤ) ∣ (coeff n) h) :
    (p : ℤ) • pdiv p h = h := by
  ext n
  rw [map_smul, smul_eq_mul, pdiv, coeff_mk]
  exact Int.mul_ediv_cancel' (H n)

/-- The Frobenius quotient `γ = (g^p - expand p g)/p` for integer series `g`. -/
noncomputable def frobQuot (p : ℕ) (hp : p ≠ 0) (g : PowerSeries ℤ) : PowerSeries ℤ :=
  pdiv p (g ^ p - expand p hp g)

theorem frobQuot_spec (p : ℕ) [Fact p.Prime] (hp : p ≠ 0) (g : PowerSeries ℤ) :
    g ^ p = expand p hp g + (p : ℤ) • frobQuot p hp g := by
  rw [frobQuot, smul_pdiv p _ (frob_dvd p hp g)]
  ring

/-- Binomial split via the Frobenius quotient: `g^(p*m) = ∑_j C(m,j) (expand g)^j (p•γ)^(m-j)`. -/
theorem gpow_split (p : ℕ) [Fact p.Prime] (hp : p ≠ 0) (g : PowerSeries ℤ) (m : ℕ) :
    g ^ (p * m) = ∑ j ∈ range (m+1),
      (expand p hp g) ^ j * ((p : ℤ) • frobQuot p hp g) ^ (m - j) * (m.choose j : PowerSeries ℤ) := by
  rw [pow_mul, frobQuot_spec p hp g, add_pow]

/-- `U_p 1 = 1`. -/
theorem uop_one (p : ℕ) (hp : p ≠ 0) : uop p (1 : PowerSeries R) = 1 := by
  ext n
  rw [coeff_uop, coeff_one, coeff_one]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [if_neg (Nat.mul_ne_zero hp (by omega)), if_neg (by omega)]

/-- `U_p (expand p A) = A`. -/
theorem uop_expand (p : ℕ) (hp : p ≠ 0) (A : PowerSeries R) : uop p (expand p hp A) = A := by
  ext n; rw [coeff_uop, PowerSeries.coeff_expand_mul]

/-- Key multiplicativity: `U_p (expand p A * B) = A * U_p B` when `p ≠ 0`. -/
theorem uop_expand_mul (p : ℕ) (hp : p ≠ 0) (A B : PowerSeries R) :
    uop p (expand p hp A * B) = A * uop p B := by
  ext n
  rw [coeff_uop, coeff_mul, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  -- RHS = ∑_{l∈range(n+1)} coeff l A * coeff (p*(n-l)) B
  have hpp : 0 < p := Nat.pos_of_ne_zero hp
  have hRHS : (∑ l ∈ range (n+1), (coeff l) A * (coeff (n-l)) (uop p B))
      = ∑ l ∈ range (n+1), (coeff l) A * (coeff (p*(n-l))) B := by
    apply Finset.sum_congr rfl; intro l _; rw [coeff_uop]
  rw [hRHS]
  -- LHS: reindex multiples of p
  rw [← Finset.sum_filter_add_sum_filter_not (range (p*n+1)) (fun k => p ∣ k)]
  have hzero : (∑ k ∈ (range (p*n+1)).filter (fun k => ¬ p ∣ k),
      (coeff k) (expand p hp A) * (coeff (p*n-k)) B) = 0 := by
    apply Finset.sum_eq_zero; intro k hk
    rw [Finset.mem_filter] at hk
    rw [PowerSeries.coeff_expand_of_not_dvd p hp A hk.2, zero_mul]
  rw [hzero, add_zero]
  -- now sum over multiples of p in range(pn+1)
  apply Finset.sum_nbij' (fun k => k / p) (fun l => p * l)
  · intro k hk; rw [Finset.mem_filter] at hk
    obtain ⟨l, rfl⟩ := hk.2
    have hb := hk.1; rw [Finset.mem_range] at hb
    have hb2 : p*l ≤ p*n := by omega
    have : l ≤ n := Nat.le_of_mul_le_mul_left hb2 hpp
    simp only [Finset.mem_range, Nat.mul_div_cancel_left _ hpp]; omega
  · intro l hl; simp only [Finset.mem_range] at hl
    have hln : l ≤ n := by omega
    have : p*l ≤ p*n := Nat.mul_le_mul (le_refl p) hln
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Dvd.intro l rfl⟩
  · intro k hk; rw [Finset.mem_filter] at hk
    obtain ⟨l, rfl⟩ := hk.2; rw [Nat.mul_div_cancel_left _ hpp]
  · intro l _; rw [Nat.mul_div_cancel_left _ hpp]
  · intro k hk; rw [Finset.mem_filter] at hk
    obtain ⟨l, rfl⟩ := hk.2
    rw [PowerSeries.coeff_expand_mul p hp A, Nat.mul_div_cancel_left _ hpp,
        Nat.mul_sub]

end
