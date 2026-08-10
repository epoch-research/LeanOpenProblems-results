import FormalConjectures.Util.ProblemImports

open Matrix Nat Finset

namespace Catbert

/-- `mu s = 1 / catalan s`, written via factorials. -/
noncomputable def mu (s : ℕ) : ℚ := (s.factorial * (s+1).factorial : ℚ) / (2*s).factorial

/-- Per-term factor of the coefficient product. -/
noncomputable def fterm (K t : ℕ) : ℚ :=
  (-((t:ℚ)+1)*((t:ℚ)+2)) / (2*((K:ℚ)-(t:ℚ))*(2*(K:ℚ)+2*(t:ℚ)-1))

/-- The (monic) orthogonal polynomial coefficient `c^{(k)}_i`, product form;
zero above the diagonal. -/
noncomputable def cc (k i : ℕ) : ℚ :=
  if i ≤ k then ∏ t ∈ Finset.Ico i k, fterm k t else 0

lemma cc_of_le {k i : ℕ} (h : i ≤ k) : cc k i = ∏ t ∈ Finset.Ico i k, fterm k t := by
  rw [cc, if_pos h]

lemma cc_of_gt {k i : ℕ} (h : k < i) : cc k i = 0 := by
  rw [cc, if_neg (by omega)]

lemma cc_diag (k : ℕ) : cc k k = 1 := by rw [cc_of_le le_rfl]; simp

lemma fterm_ne (K t : ℕ) (h : t < K) : fterm K t ≠ 0 := by
  rw [fterm]
  have h1 : (K:ℚ) - (t:ℚ) > 0 := by
    have : (t:ℚ) < (K:ℚ) := by exact_mod_cast h
    linarith
  have h2 : 2*(K:ℚ)+2*(t:ℚ)-1 > 0 := by
    have : (0:ℚ) ≤ (K:ℚ) := by positivity
    have : (0:ℚ) ≤ (t:ℚ) := by positivity
    have hK : (1:ℚ) ≤ (K:ℚ) := by exact_mod_cast (by omega : 1 ≤ K)
    linarith
  have hnum : (-((t:ℚ)+1)*((t:ℚ)+2)) ≠ 0 := by
    have : (0:ℚ) ≤ (t:ℚ) := by positivity
    have ht1 : ((t:ℚ)+1) > 0 := by linarith
    have ht2 : ((t:ℚ)+2) > 0 := by linarith
    have : (-((t:ℚ)+1)*((t:ℚ)+2)) < 0 := by nlinarith
    linarith
  apply div_ne_zero hnum
  positivity

example : cc 0 0 = 1 := cc_diag 0
example : cc 1 0 = -1 := by rw [cc_of_le (by omega)]; norm_num [fterm, Finset.prod_Ico_succ_top]

/-- Peel the bottom term of the coefficient product: `cc k i = fterm k i * cc k (i+1)` for `i < k`. -/
lemma cc_peel {k i : ℕ} (h : i < k) : cc k i = fterm k i * cc k (i+1) := by
  rw [cc_of_le (by omega), cc_of_le (by omega)]
  rw [Finset.prod_eq_prod_Ico_succ_bot h]

/-- Telescoping product over an interval in `ℚ`. -/
lemma prod_Ico_telescope (g : ℕ → ℚ) {i k : ℕ} (hik : i ≤ k)
    (hg : ∀ t ∈ Finset.Icc i k, g t ≠ 0) :
    ∏ t ∈ Finset.Ico i k, g (t+1) / g t = g k / g i := by
  induction k, hik using Nat.le_induction with
  | base => simp [div_self (hg i (by simp))]
  | succ k hik ih =>
      rw [Finset.prod_Ico_succ_top (by omega)]
      rw [ih (fun t ht => hg t (by simp at ht ⊢; omega))]
      have h1 : g k ≠ 0 := hg k (by simp; omega)
      field_simp

/-- Reverse telescoping product over an interval in `ℚ`. -/
lemma prod_Ico_telescope_inv (g : ℕ → ℚ) {i k : ℕ} (hik : i ≤ k)
    (hg : ∀ t ∈ Finset.Icc i k, g t ≠ 0) :
    ∏ t ∈ Finset.Ico i k, g t / g (t+1) = g i / g k := by
  induction k, hik using Nat.le_induction with
  | base => simp [div_self (hg i (by simp))]
  | succ k hik ih =>
      rw [Finset.prod_Ico_succ_top (by omega)]
      rw [ih (fun t ht => hg t (by simp at ht ⊢; omega))]
      have h1 : g k ≠ 0 := hg k (by simp; omega)
      have h2 : g (k+1) ≠ 0 := hg (k+1) (by simp; omega)
      field_simp

/-- The product of cross-`k` ratios telescopes. -/
lemma ratio_prod {k i : ℕ} (h : i ≤ k) :
    ∏ t ∈ Finset.Ico i k, (fterm (k+1) t / fterm k t)
    = (1/((k:ℚ)-(i:ℚ)+1)) * ((2*(k:ℚ)+2*(i:ℚ)-1)/(4*(k:ℚ)-1)) := by
  set g1 : ℕ → ℚ := fun t => (k:ℚ) - (t:ℚ) + 1 with hg1def
  set g2 : ℕ → ℚ := fun t => 2*(k:ℚ) + 2*(t:ℚ) - 1 with hg2def
  have hg1ne : ∀ t ∈ Finset.Icc i k, g1 t ≠ 0 := by
    intro t ht; simp only [Finset.mem_Icc] at ht
    simp only [hg1def]
    have : (t:ℚ) ≤ (k:ℚ) := by exact_mod_cast ht.2
    intro hc; linarith
  have hg2ne : ∀ t ∈ Finset.Icc i k, g2 t ≠ 0 := by
    intro t ht
    simp only [hg2def]
    have : (0:ℚ) ≤ (t:ℚ) := by positivity
    have hk : (0:ℚ) ≤ (k:ℚ) := by positivity
    intro hc
    have : 2*(k:ℚ) + 2*(t:ℚ) = 1 := by linarith
    -- 2(k+t) = 1 impossible for naturals
    have : (2*(k+t) : ℚ) = 1 := by push_cast; linarith
    have : (2*(k+t) : ℕ) = 1 := by exact_mod_cast this
    omega
  have hsplit : ∏ t ∈ Finset.Ico i k, (fterm (k+1) t / fterm k t)
      = (∏ t ∈ Finset.Ico i k, g1 (t+1) / g1 t)
        * (∏ t ∈ Finset.Ico i k, g2 t / g2 (t+1)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro t ht
    simp only [Finset.mem_Ico] at ht
    have htk : (t:ℚ) < (k:ℚ) := by exact_mod_cast ht.2
    simp only [hg1def, hg2def, fterm]
    push_cast
    have d1 : (k:ℚ) - (t:ℚ) ≠ 0 := by intro hc; linarith
    have d2 : (k:ℚ) - (t:ℚ) + 1 ≠ 0 := by intro hc; linarith
    have d3 : 2*(k:ℚ) + 2*(t:ℚ) - 1 ≠ 0 := by
      have : (0:ℚ) ≤ (t:ℚ) := by positivity
      have hk : (1:ℚ) ≤ (k:ℚ) := by exact_mod_cast (by omega : 1 ≤ k)
      intro hc; linarith
    have d4 : 2*(k:ℚ) + 2*(t:ℚ) + 1 ≠ 0 := by
      have : (0:ℚ) ≤ (t:ℚ) := by positivity
      have hk : (0:ℚ) ≤ (k:ℚ) := by positivity
      intro hc; linarith
    have d5 : ((k:ℚ)+1) - (t:ℚ) ≠ 0 := by intro hc; linarith
    have hnum : (t:ℚ)+1 ≠ 0 := by positivity
    have hnum2 : (t:ℚ)+2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hsplit, prod_Ico_telescope g1 h hg1ne, prod_Ico_telescope_inv g2 h hg2ne]
  simp only [hg1def, hg2def]
  congr 1 <;> ring

/-- The cross-`k` coefficient ratio. -/
lemma cc_succ_ratio {k i : ℕ} (h : i ≤ k) :
    cc (k+1) i = (-((k:ℚ)+1)*((k:ℚ)+2)*(2*(k:ℚ)+2*(i:ℚ)-1)) /
      (2*(4*(k:ℚ)+1)*(4*(k:ℚ)-1)*((k:ℚ)+1-(i:ℚ))) * cc k i := by
  rw [cc_of_le (by omega : i ≤ k+1), cc_of_le h]
  rw [Finset.prod_Ico_succ_top h]
  have hrw : ∀ t ∈ Finset.Ico i k, fterm (k+1) t
      = (fterm (k+1) t / fterm k t) * fterm k t := by
    intro t ht; simp only [Finset.mem_Ico] at ht
    rw [div_mul_cancel₀ _ (fterm_ne k t ht.2)]
  rw [Finset.prod_congr rfl hrw, Finset.prod_mul_distrib, ratio_prod h]
  have e : fterm (k+1) k = (-((k:ℚ)+1)*((k:ℚ)+2))/(2*(4*(k:ℚ)+1)) := by
    rw [fterm]; push_cast; ring
  rw [e]
  have d1 : (k:ℚ)-(i:ℚ)+1 ≠ 0 := by
    have : (i:ℚ) ≤ (k:ℚ) := by exact_mod_cast h
    intro hc; linarith
  have d2 : 4*(k:ℚ)-1 ≠ 0 := by
    intro hc
    have h' : ((4*k:ℕ):ℚ) = 1 := by push_cast; linarith
    have : (4*k:ℕ) = 1 := by exact_mod_cast h'
    omega
  have d3 : 4*(k:ℚ)+1 ≠ 0 := by
    have hk : (0:ℚ) ≤ (k:ℚ) := by positivity
    intro hc; linarith
  have d4 : (k:ℚ)+1-(i:ℚ) ≠ 0 := by
    have : (i:ℚ) ≤ (k:ℚ) := by exact_mod_cast h
    intro hc; linarith
  field_simp
  ring

/-- Cross-`k` ratio coefficient. -/
noncomputable def Acoef (k i : ℕ) : ℚ :=
  (-((k:ℚ)+1)*((k:ℚ)+2)*(2*(k:ℚ)+2*(i:ℚ)-1)) /
    (2*(4*(k:ℚ)+1)*(4*(k:ℚ)-1)*((k:ℚ)+1-(i:ℚ)))

/-- Recurrence coefficient `a_k`. -/
noncomputable def ac (k : ℕ) : ℚ :=
  ((k:ℚ)+1)*(2*(k:ℚ)-3)/((4*(k:ℚ)-3)*(4*(k:ℚ)+1))

/-- Recurrence coefficient `b_k`. -/
noncomputable def bc (k : ℕ) : ℚ :=
  (k:ℚ)*((k:ℚ)+1)*(2*(k:ℚ)-3)*(2*(k:ℚ)-5)/(4*(4*(k:ℚ)-5)*(4*(k:ℚ)-3)^2*(4*(k:ℚ)-1))

lemma cc_succ {k i : ℕ} (h : i ≤ k) : cc (k+1) i = Acoef k i * cc k i := by
  simp only [Acoef]; exact cc_succ_ratio h

-- Nonzero denominator helpers.
lemma fa1 (k : ℕ) : (4*(k:ℚ)+1) ≠ 0 := by positivity
lemma fs1 (k : ℕ) : (4*(k:ℚ)-1) ≠ 0 := by
  intro h; have h2 : ((4*k:ℕ):ℚ) = 1 := by push_cast; linarith
  have : (4*k:ℕ) = 1 := by exact_mod_cast h2
  omega
lemma fs3 (k : ℕ) : (4*(k:ℚ)-3) ≠ 0 := by
  intro h; have h2 : ((4*k:ℕ):ℚ) = 3 := by push_cast; linarith
  have : (4*k:ℕ) = 3 := by exact_mod_cast h2
  omega
lemma fs5 (k : ℕ) : (4*(k:ℚ)-5) ≠ 0 := by
  intro h; have h2 : ((4*k:ℕ):ℚ) = 5 := by push_cast; linarith
  have : (4*k:ℕ) = 5 := by exact_mod_cast h2
  omega

/-- Interior scalar identity for the three-term recurrence. -/
lemma key_interior {k i : ℕ} (hk : 1 ≤ k) (hlt : i + 1 < k) :
    Acoef k (i+1) * Acoef (k-1) (i+1)
      = fterm k i * Acoef (k-1) (i+1) - ac k * Acoef (k-1) (i+1) - bc k := by
  have hk1 : ((k-1:ℕ):ℚ) = (k:ℚ)-1 := by rw [Nat.cast_sub hk, Nat.cast_one]
  have h1 := fa1 k
  have h2 := fs1 k
  have h3 := fs3 k
  have h4 := fs5 k
  have hi1 : (i:ℚ) < (k:ℚ) := by exact_mod_cast (by omega : i < k)
  have hi2 : (i:ℚ) + 1 < (k:ℚ) := by exact_mod_cast (by omega : i + 1 < k)
  have h5 : (2*(k:ℚ)+2*(i:ℚ)-1) ≠ 0 := by
    have : (1:ℚ) ≤ (k:ℚ) := by exact_mod_cast hk
    have : (0:ℚ) ≤ (i:ℚ) := by positivity
    intro h; nlinarith
  have h6 : (k:ℚ) - (i:ℚ) ≠ 0 := by intro h; linarith
  have h7 : (k:ℚ) - (i:ℚ) - 1 ≠ 0 := by intro h; linarith
  have hA1 : Acoef k (i+1)
      = ((-((k:ℚ)+1)*((k:ℚ)+2)*(2*(k:ℚ)+2*(i:ℚ)+1)))
        /(2*(4*(k:ℚ)+1)*(4*(k:ℚ)-1)*((k:ℚ)-(i:ℚ))) := by
    simp only [Acoef]; push_cast; ring
  have hA2 : Acoef (k-1) (i+1)
      = ((-(k:ℚ)*((k:ℚ)+1)*(2*(k:ℚ)+2*(i:ℚ)-1)))
        /(2*(4*(k:ℚ)-3)*(4*(k:ℚ)-5)*((k:ℚ)-(i:ℚ)-1)) := by
    simp only [Acoef]; rw [hk1]; push_cast; ring
  have hF : fterm k i = (-((i:ℚ)+1)*((i:ℚ)+2)) / (2*((k:ℚ)-(i:ℚ))*(2*(k:ℚ)+2*(i:ℚ)-1)) := rfl
  have hC : ac k = ((k:ℚ)+1)*(2*(k:ℚ)-3)/((4*(k:ℚ)-3)*(4*(k:ℚ)+1)) := rfl
  have hB : bc k = (k:ℚ)*((k:ℚ)+1)*(2*(k:ℚ)-3)*(2*(k:ℚ)-5)/(4*(4*(k:ℚ)-5)*(4*(k:ℚ)-3)^2*(4*(k:ℚ)-1)) := rfl
  rw [hA1, hA2, hF, hC, hB]
  have t2 : (2:ℚ) ≠ 0 := by norm_num
  have t4 : (4:ℚ) ≠ 0 := by norm_num
  have DA2 : (2*(4*(k:ℚ)-3)*(4*(k:ℚ)-5)*((k:ℚ)-(i:ℚ)-1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero t2 h3) h4) h7
  have DF : (2*((k:ℚ)-(i:ℚ))*(2*(k:ℚ)+2*(i:ℚ)-1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero t2 h6) h5
  have DC : ((4*(k:ℚ)-3)*(4*(k:ℚ)+1)) ≠ 0 := mul_ne_zero h3 h1
  have DB : (4*(4*(k:ℚ)-5)*(4*(k:ℚ)-3)^2*(4*(k:ℚ)-1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero t4 h4) (pow_ne_zero 2 h3)) h2
  have DA1 : (2*(4*(k:ℚ)+1)*(4*(k:ℚ)-1)*((k:ℚ)-(i:ℚ))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero t2 h1) h2) h6
  simp only [_root_.div_mul_div_comm]
  rw [div_sub_div _ _ (mul_ne_zero DF DA2) (mul_ne_zero DC DA2),
      div_sub_div _ _ (mul_ne_zero (mul_ne_zero DF DA2) (mul_ne_zero DC DA2)) DB,
      div_eq_div_iff (mul_ne_zero DA1 DA2)
        (mul_ne_zero (mul_ne_zero (mul_ne_zero DF DA2) (mul_ne_zero DC DA2)) DB)]
  ring

/-- Boundary scalar identity. -/
lemma key_bd {k : ℕ} (hk : 1 ≤ k) : Acoef k k = fterm k (k-1) - ac k := by
  have hk1 : ((k-1:ℕ):ℚ) = (k:ℚ)-1 := by rw [Nat.cast_sub hk, Nat.cast_one]
  have h1 := fa1 k
  have h2 := fs1 k
  have h3 := fs3 k
  have t2 : (2:ℚ) ≠ 0 := by norm_num
  have hAc : Acoef k k = (-((k:ℚ)+1)*((k:ℚ)+2)*(2*(k:ℚ)+2*(k:ℚ)-1)) / (2*(4*(k:ℚ)+1)*(4*(k:ℚ)-1)*((k:ℚ)+1-(k:ℚ))) := rfl
  have hfb : fterm k (k-1) = (-(((k-1:ℕ):ℚ)+1)*(((k-1:ℕ):ℚ)+2)) / (2*((k:ℚ)-((k-1:ℕ):ℚ))*(2*(k:ℚ)+2*((k-1:ℕ):ℚ)-1)) := rfl
  have hC : ac k = ((k:ℚ)+1)*(2*(k:ℚ)-3)/((4*(k:ℚ)-3)*(4*(k:ℚ)+1)) := rfl
  rw [hAc, hfb, hC, hk1]
  have dA : (2*(4*(k:ℚ)+1)*(4*(k:ℚ)-1)*((k:ℚ)+1-(k:ℚ))) ≠ 0 := by
    have e : (2*(4*(k:ℚ)+1)*(4*(k:ℚ)-1)*((k:ℚ)+1-(k:ℚ))) = 2*(4*(k:ℚ)+1)*(4*(k:ℚ)-1) := by
      ring
    rw [e]; exact mul_ne_zero (mul_ne_zero t2 h1) h2
  have dF : (2*((k:ℚ)-((k:ℚ)-1))*(2*(k:ℚ)+2*((k:ℚ)-1)-1)) ≠ 0 := by
    have e : (2*((k:ℚ)-((k:ℚ)-1))*(2*(k:ℚ)+2*((k:ℚ)-1)-1)) = 2*(4*(k:ℚ)-3) := by ring
    rw [e]; exact mul_ne_zero t2 h3
  have dC : ((4*(k:ℚ)-3)*(4*(k:ℚ)+1)) ≠ 0 := mul_ne_zero h3 h1
  rw [div_sub_div _ _ dF dC, div_eq_div_iff dA (mul_ne_zero dF dC)]
  ring

/-- `i = 0` scalar identity. -/
lemma key_i0 {k : ℕ} (hk : 1 ≤ k) :
    Acoef k 0 * Acoef (k-1) 0 + ac k * Acoef (k-1) 0 + bc k = 0 := by
  have hk1 : ((k-1:ℕ):ℚ) = (k:ℚ)-1 := by rw [Nat.cast_sub hk, Nat.cast_one]
  have h1 := fa1 k
  have h2 := fs1 k
  have h3 := fs3 k
  have h4 := fs5 k
  have hk0 : (k:ℚ) ≠ 0 := by
    have : (1:ℚ) ≤ (k:ℚ) := by exact_mod_cast hk
    intro h; linarith
  have hkp1 : (k:ℚ)+1 ≠ 0 := by positivity
  have h5 : (2*(k:ℚ)-1) ≠ 0 := by
    intro h; have hh : ((2*k:ℕ):ℚ) = 1 := by push_cast; linarith
    have : (2*k:ℕ) = 1 := by exact_mod_cast hh
    omega
  have hA1 : Acoef k 0
      = ((-((k:ℚ)+1)*((k:ℚ)+2)*(2*(k:ℚ)-1)))
        /(2*(4*(k:ℚ)+1)*(4*(k:ℚ)-1)*((k:ℚ)+1)) := by
    simp only [Acoef]; push_cast; ring
  have hA2 : Acoef (k-1) 0
      = ((-(k:ℚ)*((k:ℚ)+1)*(2*(k:ℚ)-3)))
        /(2*(4*(k:ℚ)-3)*(4*(k:ℚ)-5)*(k:ℚ)) := by
    simp only [Acoef]; rw [hk1]; push_cast; ring
  have hC : ac k = ((k:ℚ)+1)*(2*(k:ℚ)-3)/((4*(k:ℚ)-3)*(4*(k:ℚ)+1)) := rfl
  have hB : bc k = (k:ℚ)*((k:ℚ)+1)*(2*(k:ℚ)-3)*(2*(k:ℚ)-5)/(4*(4*(k:ℚ)-5)*(4*(k:ℚ)-3)^2*(4*(k:ℚ)-1)) := rfl
  rw [hA1, hA2, hC, hB]
  have t2 : (2:ℚ) ≠ 0 := by norm_num
  have t4 : (4:ℚ) ≠ 0 := by norm_num
  have DA1 : (2*(4*(k:ℚ)+1)*(4*(k:ℚ)-1)*((k:ℚ)+1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero t2 h1) h2) hkp1
  have DA2 : (2*(4*(k:ℚ)-3)*(4*(k:ℚ)-5)*(k:ℚ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero t2 h3) h4) hk0
  have DC : ((4*(k:ℚ)-3)*(4*(k:ℚ)+1)) ≠ 0 := mul_ne_zero h3 h1
  have DB : (4*(4*(k:ℚ)-5)*(4*(k:ℚ)-3)^2*(4*(k:ℚ)-1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero t4 h4) (pow_ne_zero 2 h3)) h2
  simp only [_root_.div_mul_div_comm]
  rw [div_add_div _ _ (mul_ne_zero DA1 DA2) (mul_ne_zero DC DA2),
      div_add_div _ _ (mul_ne_zero (mul_ne_zero DA1 DA2) (mul_ne_zero DC DA2)) DB,
      div_eq_zero_iff]
  left; ring

/-- `cc (k-1) j ≠ 0` for `j ≤ k-1`. -/
lemma cc_ne {k j : ℕ} (h : j ≤ k) : cc k j ≠ 0 := by
  rw [cc_of_le h]
  apply Finset.prod_ne_zero_iff.mpr
  intro t ht; simp only [Finset.mem_Ico] at ht
  exact fterm_ne k t ht.2

/-- Three-term recurrence for `cc`, shifted form. -/
lemma cc_rec1 {k : ℕ} (hk : 1 ≤ k) (i : ℕ) :
    cc (k+1) (i+1) = cc k i - ac k * cc k (i+1) - bc k * cc (k-1) (i+1) := by
  by_cases hA : i + 1 < k
  · -- interior
    have e1a : cc (k+1) (i+1) = Acoef k (i+1) * cc k (i+1) := cc_succ (by omega)
    have e2a : cc k (i+1) = Acoef (k-1) (i+1) * cc (k-1) (i+1) := by
      have := cc_succ (k := k-1) (i := i+1) (by omega)
      rwa [Nat.sub_add_cancel hk] at this
    have e3a : cc k i = fterm k i * cc k (i+1) := cc_peel (by omega)
    rw [e1a, e3a, e2a]
    linear_combination (cc (k-1) (i+1)) * key_interior hk hA
  · by_cases hB : i + 1 = k
    · -- boundary i = k-1
      subst hB
      simp only [Nat.add_sub_cancel]
      rw [cc_succ (le_refl (i+1)), cc_peel (Nat.lt_succ_self i)]
      simp only [cc_diag, mul_one, cc_of_gt (Nat.lt_succ_self i), mul_zero, sub_zero]
      exact key_bd (Nat.le_add_left 1 i)
    · by_cases hC : i = k
      · subst hC
        rw [cc_diag, cc_diag, cc_of_gt (by omega), cc_of_gt (by omega)]
        ring
      · -- i > k
        rw [cc_of_gt (by omega), cc_of_gt (by omega), cc_of_gt (by omega),
            cc_of_gt (by omega)]
        ring

/-- Three-term recurrence for `cc` at `i = 0`. -/
lemma cc_rec0 {k : ℕ} (hk : 1 ≤ k) :
    cc (k+1) 0 = - ac k * cc k 0 - bc k * cc (k-1) 0 := by
  have e1a : cc (k+1) 0 = Acoef k 0 * cc k 0 := cc_succ (Nat.zero_le k)
  have e2a : cc k 0 = Acoef (k-1) 0 * cc (k-1) 0 := by
    have := cc_succ (k := k-1) (i := 0) (Nat.zero_le _)
    rwa [Nat.sub_add_cancel hk] at this
  rw [e1a, e2a]
  linear_combination (cc (k-1) 0) * key_i0 hk

/-- The orthogonal-polynomial functional `L_m^{(k)} = ∑_i c^{(k)}_i μ_{i+m}`. -/
noncomputable def Lsum (k m : ℕ) : ℚ := ∑ i ∈ Finset.range (k+1), cc k i * mu (i+m)

lemma Lsum_eq_range (k m N : ℕ) (h : k+1 ≤ N) :
    ∑ i ∈ Finset.range N, cc k i * mu (i+m) = Lsum k m := by
  rw [Lsum]
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr h)
  intro i _ hi
  simp only [Finset.mem_range, not_lt] at hi
  rw [cc_of_gt (by omega), zero_mul]

/-- The functional satisfies the same three-term recurrence. -/
lemma Lsum_rec {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    Lsum (k+1) m = Lsum k (m+1) - ac k * Lsum k m - bc k * Lsum (k-1) m := by
  have P1 : (∑ i ∈ Finset.range (k+1), cc k i * mu (i+1+m)) = Lsum k (m+1) := by
    rw [Lsum]; apply Finset.sum_congr rfl; intro i _
    rw [show i+1+m = i+(m+1) from by omega]
  have P2 : (∑ i ∈ Finset.range (k+1), cc k (i+1) * mu (i+1+m)) + cc k 0 * mu m = Lsum k m := by
    have h := Lsum_eq_range k m (k+2) (by omega)
    rw [Finset.sum_range_succ', Nat.zero_add] at h
    exact h
  have P3 : (∑ i ∈ Finset.range (k+1), cc (k-1) (i+1) * mu (i+1+m)) + cc (k-1) 0 * mu m
      = Lsum (k-1) m := by
    have h := Lsum_eq_range (k-1) m (k+2) (by omega)
    rw [Finset.sum_range_succ', Nat.zero_add] at h
    exact h
  have hsum : (∑ i ∈ Finset.range (k+1),
        (cc k i - ac k * cc k (i+1) - bc k * cc (k-1) (i+1)) * mu (i+1+m))
      = (∑ i ∈ Finset.range (k+1), cc k i * mu (i+1+m))
        - ac k * (∑ i ∈ Finset.range (k+1), cc k (i+1) * mu (i+1+m))
        - bc k * (∑ i ∈ Finset.range (k+1), cc (k-1) (i+1) * mu (i+1+m)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [Lsum, Finset.sum_range_succ', cc_rec0 hk]
  simp only [cc_rec1 hk]
  rw [Nat.zero_add, hsum, P1]
  linear_combination (-ac k) * P2 + (-bc k) * P3

/-! ### Closed form `R k m` and the identity `Lsum k m = R k m`. -/

/-- Ratio coefficient `c_{k+1}/c_k`. -/
noncomputable def rho (k : ℕ) : ℚ :=
  (2*(k:ℚ)-3)*(2*(k:ℚ)-1)/((4*(k:ℚ)-1)*(4*(k:ℚ)+1))

/-- The constant `c_k` of the closed form, defined recursively. -/
noncomputable def ck : ℕ → ℚ
  | 0 => 1
  | (k+1) => rho k * ck k

lemma ck_succ (k : ℕ) : ck (k+1) = rho k * ck k := rfl

/-- Falling factorial `∏_{j<k} (m - j)`. -/
noncomputable def pfall (k m : ℕ) : ℚ := ∏ j ∈ Finset.range k, ((m:ℚ) - (j:ℚ))

/-- Factorial factor `(m+1)! (m+k)! / (2m+2k)!`. -/
noncomputable def Gf (k m : ℕ) : ℚ :=
  ((m+1).factorial * (m+k).factorial : ℚ) / (2*m+2*k).factorial

/-- The closed form. -/
noncomputable def R (k m : ℕ) : ℚ := ck k * pfall k m * Gf k m

lemma pfall_succ (k m : ℕ) : pfall (k+1) m = pfall k m * ((m:ℚ) - (k:ℚ)) := by
  unfold pfall; rw [Finset.prod_range_succ]

lemma pfall_shift (k m : ℕ) : pfall (k+1) (m+1) = ((m:ℚ)+1) * pfall k m := by
  unfold pfall
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  · push_cast; ring
  · apply Finset.prod_congr rfl; intro i _; push_cast; ring

lemma Gf_succ (k m : ℕ) :
    Gf (k+1) m = ((m:ℚ)+k+1)/((2*(m:ℚ)+2*k+2)*(2*(m:ℚ)+2*k+1)) * Gf k m := by
  unfold Gf
  have hfac : ((m+(k+1)).factorial : ℚ) = ((m:ℚ)+k+1) * (m+k).factorial := by
    rw [show m+(k+1) = (m+k)+1 from rfl, Nat.factorial_succ]; push_cast; ring
  have hden : ((2*m+2*(k+1)).factorial : ℚ)
      = (2*(m:ℚ)+2*k+2) * ((2*(m:ℚ)+2*k+1) * (2*m+2*k).factorial) := by
    rw [show 2*m+2*(k+1) = 2*m+2*k+1+1 from by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [hfac, hden]
  have h0 : ((2*m+2*k).factorial : ℚ) ≠ 0 := by exact_mod_cast (2*m+2*k).factorial_ne_zero
  have h1 : (2*(m:ℚ)+2*k+2) ≠ 0 := by positivity
  have h2 : (2*(m:ℚ)+2*k+1) ≠ 0 := by positivity
  field_simp

lemma Gf_mshift (k m : ℕ) :
    Gf k (m+1) = ((m:ℚ)+2)*((m:ℚ)+k+1)/((2*(m:ℚ)+2*k+2)*(2*(m:ℚ)+2*k+1)) * Gf k m := by
  unfold Gf
  have ha : (((m+1)+1).factorial : ℚ) = ((m:ℚ)+2) * (m+1).factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hb : (((m+1)+k).factorial : ℚ) = ((m:ℚ)+k+1) * (m+k).factorial := by
    rw [show (m+1)+k = (m+k)+1 from by ring, Nat.factorial_succ]; push_cast; ring
  have hc : ((2*(m+1)+2*k).factorial : ℚ)
      = (2*(m:ℚ)+2*k+2) * ((2*(m:ℚ)+2*k+1) * (2*m+2*k).factorial) := by
    rw [show 2*(m+1)+2*k = 2*m+2*k+1+1 from by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [ha, hb, hc]
  have h0 : ((2*m+2*k).factorial : ℚ) ≠ 0 := by exact_mod_cast (2*m+2*k).factorial_ne_zero
  have h1 : (2*(m:ℚ)+2*k+2) ≠ 0 := by positivity
  have h2 : (2*(m:ℚ)+2*k+1) ≠ 0 := by positivity
  field_simp

lemma rho_succ (j : ℕ) :
    rho (j+1) = (2*(j:ℚ)-1)*(2*(j:ℚ)+1)/((4*(j:ℚ)+3)*(4*(j:ℚ)+5)) := by
  unfold rho; push_cast; ring

lemma ac_succ (j : ℕ) :
    ac (j+1) = ((j:ℚ)+2)*(2*(j:ℚ)-1)/((4*(j:ℚ)+1)*(4*(j:ℚ)+5)) := by
  unfold ac; push_cast; ring

lemma bc_succ (j : ℕ) :
    bc (j+1) = ((j:ℚ)+1)*((j:ℚ)+2)*(2*(j:ℚ)-1)*(2*(j:ℚ)-3)
      /(4*(4*(j:ℚ)-1)*(4*(j:ℚ)+1)^2*(4*(j:ℚ)+3)) := by
  unfold bc; push_cast; ring

/-- `R` satisfies the same three-term recurrence as `Lsum`. -/
lemma R_rec (j m : ℕ) :
    R (j+2) m = R (j+1) (m+1) - ac (j+1) * R (j+1) m - bc (j+1) * R j m := by
  have qm1 : (4*(j:ℚ)-1) ≠ 0 := by
    rcases Nat.eq_zero_or_pos j with h|h
    · subst h; norm_num
    · have : (1:ℚ) ≤ (j:ℚ) := by exact_mod_cast h
      intro hc; linarith
  have e1 : (2*(m:ℚ)+2*j+1) ≠ 0 := by positivity
  have e2 : (2*(m:ℚ)+2*j+2) ≠ 0 := by positivity
  have e3 : (2*(m:ℚ)+2*j+3) ≠ 0 := by positivity
  have e4 : (2*(m:ℚ)+2*j+4) ≠ 0 := by positivity
  have q1 : (4*(j:ℚ)+1) ≠ 0 := by positivity
  have q3 : (4*(j:ℚ)+3) ≠ 0 := by positivity
  have q5 : (4*(j:ℚ)+5) ≠ 0 := by positivity
  unfold R
  rw [show j+2 = (j+1)+1 from rfl]
  simp only [ck_succ]
  rw [pfall_shift]
  simp only [pfall_succ]
  rw [Gf_mshift (j+1) m]
  simp only [Gf_succ]
  rw [rho_succ, ac_succ, bc_succ]
  unfold rho
  push_cast
  field_simp
  ring

lemma R_zero (m : ℕ) : R 0 m = mu m := by
  unfold R
  rw [pfall, Finset.prod_range_zero]
  show ck 0 * 1 * Gf 0 m = mu m
  rw [show ck 0 = 1 from rfl, Gf, mu]
  simp only [Nat.add_zero, Nat.mul_zero, one_mul]
  ring

lemma base0 (m : ℕ) : Lsum 0 m = R 0 m := by
  rw [Lsum, Finset.sum_range_one, cc_diag, Nat.zero_add, one_mul, R_zero]

lemma Gf0 (m : ℕ) : Gf 0 m = mu m := by
  rw [Gf, mu]; simp only [Nat.add_zero, Nat.mul_zero]; ring

lemma base1 (m : ℕ) : Lsum 1 m = R 1 m := by
  have hcc0 : cc 1 0 = -1 := by
    rw [cc_of_le (by omega)]; norm_num [fterm, Finset.prod_Ico_succ_top]
  have hLs : Lsum 1 m = -1 * mu m + 1 * mu (m+1) := by
    rw [Lsum, Finset.sum_range_succ, Finset.sum_range_one, hcc0, cc_diag, Nat.zero_add,
        show (1+m) = (m+1) from by ring]
  have hR1 : R 1 m = rho 0 * (m:ℚ) * Gf 1 m := by
    unfold R
    simp only [pfall, Finset.prod_range_one, Nat.cast_zero, sub_zero]
    show (rho 0 * ck 0) * (m:ℚ) * Gf 1 m = rho 0 * (m:ℚ) * Gf 1 m
    rw [show ck 0 = 1 from rfl]; ring
  have hmu1 : mu (m+1) = ((m:ℚ)+2)*((m:ℚ)+1)/((2*(m:ℚ)+2)*(2*(m:ℚ)+1)) * mu m := by
    rw [← Gf0 (m+1), ← Gf0 m, Gf_mshift 0 m]; push_cast; ring
  have hGf1 : Gf 1 m = ((m:ℚ)+1)/((2*(m:ℚ)+2)*(2*(m:ℚ)+1)) * mu m := by
    rw [← Gf0 m]
    have h := Gf_succ 0 m
    rw [h]; push_cast; ring
  have hrho0 : rho 0 = -3 := by rw [rho]; norm_num
  rw [hLs, hR1, hmu1, hGf1, hrho0]
  have hd1 : (2*(m:ℚ)+2) ≠ 0 := by positivity
  have hd2 : (2*(m:ℚ)+1) ≠ 0 := by positivity
  field_simp
  ring

lemma Lsum_eq_R (k m : ℕ) : Lsum k m = R k m := by
  suffices h : ∀ k, (∀ m, Lsum k m = R k m) ∧ (∀ m, Lsum (k+1) m = R (k+1) m) by
    exact (h k).1 m
  intro k
  induction k with
  | zero => exact ⟨base0, base1⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    intro m
    have hL := Lsum_rec (k := n+1) (by omega) m
    simp only [Nat.add_sub_cancel] at hL
    rw [hL, ih.2 (m+1), ih.2 m, ih.1 m]
    exact (R_rec n m).symm

/-! ### Orthogonality and the connection to Catalan numbers. -/

lemma pfall_eq_zero {k m : ℕ} (h : m < k) : pfall k m = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_range.mpr h); simp

/-- Orthogonality: `L_m^{(k)} = 0` for `m < k`. -/
lemma Lsum_orthogonal {k m : ℕ} (h : m < k) : Lsum k m = 0 := by
  rw [Lsum_eq_R, R, pfall_eq_zero h]; ring

lemma cat_fact (s : ℕ) : catalan s * s.factorial * (s+1).factorial = (2*s).factorial := by
  have h1 : (s+1)*catalan s = (2*s).choose s := by
    rw [succ_mul_catalan_eq_centralBinom, Nat.centralBinom_eq_two_mul_choose]
  have h2 : (2*s).choose s * s.factorial * (2*s - s).factorial = (2*s).factorial :=
    Nat.choose_mul_factorial_mul_factorial (by omega)
  rw [show 2*s - s = s from by omega] at h2
  rw [Nat.factorial_succ]
  calc catalan s * s.factorial * ((s+1)*s.factorial)
      = ((s+1)*catalan s) * s.factorial * s.factorial := by ring
    _ = (2*s).choose s * s.factorial * s.factorial := by rw [h1]
    _ = (2*s).factorial := h2

lemma mu_catalan (s : ℕ) : mu s = 1 / (catalan s : ℚ) := by
  have hcatn : catalan s ≠ 0 := by
    intro h0
    have h := cat_fact s
    rw [h0, zero_mul, zero_mul] at h
    exact (2*s).factorial_ne_zero h.symm
  have hcat : (catalan s : ℚ) ≠ 0 := by exact_mod_cast hcatn
  have hfac : ((2*s).factorial : ℚ) ≠ 0 := by exact_mod_cast (2*s).factorial_ne_zero
  rw [mu, div_eq_div_iff hfac hcat, one_mul]
  have h' : ((catalan s * s.factorial * (s+1).factorial : ℕ) : ℚ) = ((2*s).factorial : ℚ) := by
    exact_mod_cast cat_fact s
  push_cast at h'
  linear_combination h'

/-! ### The determinant factorization. -/

/-- The Catbert matrix as `mu (i+j)`. -/
noncomputable def Amat (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := fun i j => mu (i.val + j.val)

/-- The lower-triangular coefficient matrix. -/
noncomputable def Cmat (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := fun i j => cc i.val j.val

lemma sum_fin_cc (n a b : ℕ) (ha : a < n) :
    ∑ q : Fin n, cc a q.val * mu (q.val + b) = Lsum a b := by
  rw [Fin.sum_univ_eq_sum_range (fun q => cc a q * mu (q + b))]
  exact Lsum_eq_range a b n (by omega)

lemma Amat_symm (n : ℕ) : (Amat n)ᵀ = Amat n := by
  ext i j; simp only [Matrix.transpose_apply, Amat, Nat.add_comm]

lemma CAC_symm (n : ℕ) :
    (Cmat n * Amat n * (Cmat n)ᵀ)ᵀ = Cmat n * Amat n * (Cmat n)ᵀ := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Amat_symm, Matrix.mul_assoc]

lemma CAC_entry (n : ℕ) (i j : Fin n) :
    (Cmat n * Amat n * (Cmat n)ᵀ) i j = ∑ p : Fin n, cc j.val p.val * Lsum i.val p.val := by
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [Matrix.mul_apply, Matrix.transpose_apply, Cmat, mul_comm]
  congr 1
  rw [← sum_fin_cc n i.val p.val i.isLt]
  apply Finset.sum_congr rfl
  intro q _
  rw [Cmat, Amat]

lemma CAC_entry_symm (n : ℕ) (i j : Fin n) :
    (Cmat n * Amat n * (Cmat n)ᵀ) i j = (Cmat n * Amat n * (Cmat n)ᵀ) j i := by
  calc (Cmat n * Amat n * (Cmat n)ᵀ) i j
      = (Cmat n * Amat n * (Cmat n)ᵀ)ᵀ i j := by rw [CAC_symm]
    _ = (Cmat n * Amat n * (Cmat n)ᵀ) j i := Matrix.transpose_apply _ i j

lemma entry_offdiag (n : ℕ) (i j : Fin n) (h : j.val < i.val) :
    ∑ p : Fin n, cc j.val p.val * Lsum i.val p.val = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : p.val ≤ j.val
  · rw [Lsum_orthogonal (by omega : p.val < i.val), mul_zero]
  · rw [cc_of_gt (by omega : j.val < p.val), zero_mul]

lemma CAC_eq (n : ℕ) :
    Cmat n * Amat n * (Cmat n)ᵀ = Matrix.diagonal (fun i : Fin n => Lsum i.val i.val) := by
  ext i j
  rw [Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, CAC_entry, Finset.sum_eq_single i]
    · rw [cc_diag, one_mul]
    · intro p _ hp
      rcases lt_or_gt_of_ne (fun hh => hp (Fin.ext hh)) with hh | hh
      · rw [Lsum_orthogonal hh, mul_zero]
      · rw [cc_of_gt hh, zero_mul]
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  · rw [if_neg hij]
    rcases lt_or_gt_of_ne (fun hh => hij (Fin.ext hh)) with hh | hh
    · rw [CAC_entry_symm, CAC_entry]; exact entry_offdiag n j i hh
    · rw [CAC_entry]; exact entry_offdiag n i j hh

lemma det_Cmat (n : ℕ) : (Cmat n).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [Cmat, cc_diag]
  · intro i j hij
    rw [Cmat]
    exact cc_of_gt (by exact hij)

lemma det_Amat (n : ℕ) : (Amat n).det = ∏ i : Fin n, Lsum i.val i.val := by
  have h1 : (Cmat n * Amat n * (Cmat n)ᵀ).det = (Amat n).det := by
    simp only [Matrix.det_mul, Matrix.det_transpose, det_Cmat, one_mul, mul_one]
  rw [CAC_eq, Matrix.det_diagonal] at h1
  exact h1.symm

/-! ### Integrality and assembly. -/

lemma pfall_diag (k : ℕ) : pfall k k = (k.factorial : ℚ) := by
  unfold pfall
  have hcong : ∀ j ∈ Finset.range k, ((k:ℚ) - (j:ℚ)) = (((k - j : ℕ)) : ℚ) := by
    intro j hj; rw [Finset.mem_range] at hj
    rw [Nat.cast_sub hj.le]
  rw [Finset.prod_congr rfl hcong, ← Nat.cast_prod]
  congr 1
  rw [← Finset.prod_range_reflect (fun j => k - j) k]
  rw [← Finset.prod_range_add_one_eq_factorial]
  apply Finset.prod_congr rfl
  intro i hi; rw [Finset.mem_range] at hi; omega

/-- The reciprocal of the determinant is the product of the reciprocals `w_k = 1/h_k`. -/
lemma prod_inv_int (n : ℕ) (w : ℕ → ℤ) (hw : ∀ k, Lsum k k * (w k : ℚ) = 1) :
    (∏ i : Fin n, Lsum i.val i.val)⁻¹ = ((∏ i : Fin n, w i.val : ℤ) : ℚ) := by
  push_cast
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact inv_eq_of_mul_eq_one_right (hw i.val)

lemma cb_succ (n : ℕ) :
    ((Nat.centralBinom (n+1)) : ℚ) = 2*(2*(n:ℚ)+1)/((n:ℚ)+1) * (Nat.centralBinom n) := by
  have hn : ((n:ℚ)+1) ≠ 0 := by positivity
  have hc : ((n:ℚ)+1)*(Nat.centralBinom (n+1)) = 2*(2*(n:ℚ)+1)*(Nat.centralBinom n) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  field_simp
  linear_combination hc

lemma two_k_ne1 (k : ℕ) : (2*(k:ℚ)-1) ≠ 0 := by
  intro h; have : (2*(k:ℕ):ℚ) = 1 := by push_cast; linarith
  have : (2*k:ℕ) = 1 := by exact_mod_cast this
  omega

lemma two_k_ne3 (k : ℕ) : (2*(k:ℚ)-3) ≠ 0 := by
  intro h; have : (2*(k:ℕ):ℚ) = 3 := by push_cast; linarith
  have : (2*k:ℕ) = 3 := by exact_mod_cast this
  omega

/-- Closed form for `ck k` (cleared denominators) via central binomials. -/
lemma ck_closed (k : ℕ) :
    ck k * ((2*(k:ℚ)-1)^2*(2*(k:ℚ)-3)*((Nat.centralBinom (2*k)) : ℚ))
      = 3*(4*(k:ℚ)-1)*((Nat.centralBinom k) : ℚ) := by
  induction k with
  | zero => simp [ck, Nat.centralBinom]
  | succ n ih =>
    have hcbk : ((Nat.centralBinom (n+1)) : ℚ) = 2*(2*(n:ℚ)+1)/((n:ℚ)+1) * (Nat.centralBinom n) :=
      cb_succ n
    have hcb2 : ((Nat.centralBinom (2*(n+1))) : ℚ)
        = 4*(4*(n:ℚ)+1)*(4*(n:ℚ)+3)/((2*(n:ℚ)+1)*(2*(n:ℚ)+2)) * (Nat.centralBinom (2*n)) := by
      have e1 := cb_succ (2*n)
      have e2 := cb_succ (2*n+1)
      rw [show 2*(n+1) = (2*n+1)+1 from by ring, e2]
      rw [show 2*n+1 = (2*n)+1 from rfl] at e1 ⊢
      rw [e1]
      push_cast
      have h1 : (2*(n:ℚ)+1) ≠ 0 := by positivity
      have h2 : (2*(n:ℚ)+1+1) ≠ 0 := by positivity
      field_simp
      ring
    have hpos1 : ((n:ℚ)+1) ≠ 0 := by positivity
    have hd1 : (2*(n:ℚ)+1) ≠ 0 := by positivity
    have hd2 : (2*(n:ℚ)+2) ≠ 0 := by positivity
    have hcbpos : ((Nat.centralBinom (2*n)) : ℚ) ≠ 0 := by
      have := Nat.centralBinom_pos (2*n); positivity
    have hr1 : (4*(n:ℚ)-1) ≠ 0 := by
      intro h; have : (4*(n:ℕ):ℚ) = 1 := by push_cast; linarith
      have : (4*n:ℕ) = 1 := by exact_mod_cast this
      omega
    have hr2 : (4*(n:ℚ)+1) ≠ 0 := by positivity
    have hne : (4*(n:ℚ)-1)*(4*(n:ℚ)+1) ≠ 0 := mul_ne_zero hr1 hr2
    rw [ck_succ, rho, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hne]
    rw [hcb2, hcbk]
    push_cast
    field_simp
    linear_combination (4*(2*(n:ℚ)+1)^2*(4*(n:ℚ)+3)) * ih

/-- `centralBinom m * (m!)^2 = (2m)!` over `ℚ`. -/
lemma cbfact (m : ℕ) :
    ((Nat.centralBinom m : ℚ)) * (m.factorial : ℚ)^2 = ((2*m).factorial : ℚ) := by
  have h : Nat.centralBinom m * (m.factorial)^2 = (2*m).factorial := by
    have hh := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2*m by omega)
    rw [show 2*m - m = m from by omega] at hh
    show (2*m).choose m * (m.factorial)^2 = (2*m).factorial
    rw [sq, ← mul_assoc]; exact hh
  exact_mod_cast h

/-- `(2k+1)·catalan(2k) = centralBinom(2k)`. -/
lemma catA (k : ℕ) :
    (2*(k:ℚ)+1) * (catalan (2*k) : ℚ) = (Nat.centralBinom (2*k) : ℚ) := by
  exact_mod_cast succ_mul_catalan_eq_centralBinom (2*k)

/-- `2(4k-1)·catalan(2k-1) = centralBinom(2k)` for `k ≥ 1`. -/
lemma catBk (k : ℕ) (hk : 1 ≤ k) :
    2*(4*(k:ℚ)-1)*(catalan (2*k-1):ℚ) = (Nat.centralBinom (2*k):ℚ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j+1 := ⟨k-1, by omega⟩
  have hcb : 2*(4*(j:ℚ)+3)*(catalan (2*j+1):ℚ) = (Nat.centralBinom (2*j+2):ℚ) := by
    have h2 : (2*j+2) * catalan (2*j+1) = Nat.centralBinom (2*j+1) := by
      have h := succ_mul_catalan_eq_centralBinom (2*j+1)
      rwa [show (2*j+1)+1 = 2*j+2 from by ring] at h
    have h1 : (2*j+2) * Nat.centralBinom (2*j+2) = 2*(4*j+3) * Nat.centralBinom (2*j+1) := by
      have h := Nat.succ_mul_centralBinom_succ (2*j+1)
      rw [show (2*j+1)+1 = 2*j+2 from by ring,
          show 2*(2*(2*j+1)+1) = 2*(4*j+3) from by ring] at h
      exact h
    have hk2 : (2*(j:ℚ)+2) ≠ 0 := by positivity
    apply mul_left_cancel₀ hk2
    have e2 : (2*(j:ℚ)+2) * (catalan (2*j+1):ℚ) = (Nat.centralBinom (2*j+1):ℚ) := by
      exact_mod_cast h2
    have e1 : (2*(j:ℚ)+2) * (Nat.centralBinom (2*j+2):ℚ)
        = 2*(4*(j:ℚ)+3)*(Nat.centralBinom (2*j+1):ℚ) := by exact_mod_cast h1
    rw [e1]
    linear_combination (2*(4*(j:ℚ)+3))*e2
  rw [show 2*(j+1)-1 = 2*j+1 from by omega, show 2*(j+1) = 2*j+2 from by ring]
  push_cast
  linear_combination hcb

/-- The catalan recurrence `(k+1)·catalan(2k+1) = (4k+1)·catalan(2k)`. -/
lemma crecQ (k : ℕ) :
    ((k:ℚ)+1)*(catalan (2*k+1):ℚ) = (4*(k:ℚ)+1)*(catalan (2*k):ℚ) := by
  have catA1 : (2*(k:ℚ)+2)*(catalan (2*k+1):ℚ) = (Nat.centralBinom (2*k+1):ℚ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom (2*k+1)
  have cbrec : (2*(k:ℚ)+1)*(Nat.centralBinom (2*k+1):ℚ)
      = 2*(4*(k:ℚ)+1)*(Nat.centralBinom (2*k):ℚ) := by
    have h := Nat.succ_mul_centralBinom_succ (2*k)
    have h2 : ((2*k+1)*Nat.centralBinom (2*k+1):ℚ) = (2*(2*(2*k)+1)*Nat.centralBinom (2*k):ℚ) := by
      exact_mod_cast h
    push_cast at h2; linear_combination h2
  have catA0 : (2*(k:ℚ)+1)*(catalan (2*k):ℚ) = (Nat.centralBinom (2*k):ℚ) := catA k
  have h21 : (2*(k:ℚ)+1) ≠ 0 := by positivity
  have hclear : (2*(k:ℚ)+2)*(catalan (2*k+1):ℚ) = 2*(4*(k:ℚ)+1)*(catalan (2*k):ℚ) := by
    apply mul_left_cancel₀ h21
    linear_combination (2*(k:ℚ)+1)*catA1 + cbrec - 2*(4*(k:ℚ)+1)*catA0
  linear_combination (1/2:ℚ)*hclear

/-- Closed form for the diagonal `Lsum k k`, cleared of denominators. -/
lemma Lsum_diag (k : ℕ) :
    Lsum k k * ((2*(k:ℚ)-1)^2*(2*(k:ℚ)-3)*((4*k).factorial:ℚ)^2)
      = 3*(4*(k:ℚ)-1)*((k:ℚ)+1)*((2*k).factorial:ℚ)^4 := by
  have hF4 : ((4*k).factorial:ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (4*k)).ne'
  have hb2 : (Nat.centralBinom (2*k):ℚ)*((2*k).factorial:ℚ)^2 = ((4*k).factorial:ℚ) := by
    have := cbfact (2*k); rwa [show 2*(2*k) = 4*k from by ring] at this
  have hb1 : (Nat.centralBinom k:ℚ)*((k.factorial:ℚ))^2 = ((2*k).factorial:ℚ) := cbfact k
  have hcc := ck_closed k
  have hckf : ck k * (2*(k:ℚ)-1)^2*(2*(k:ℚ)-3)*((4*k).factorial:ℚ)*((k.factorial:ℚ))^2
      = 3*(4*(k:ℚ)-1)*((2*k).factorial:ℚ)^3 := by
    linear_combination ((k.factorial:ℚ)^2*((2*k).factorial:ℚ)^2)*hcc
      + (3*(4*(k:ℚ)-1)*((2*k).factorial:ℚ)^2)*hb1
      + (-(ck k)*(2*(k:ℚ)-1)^2*(2*(k:ℚ)-3)*((k.factorial:ℚ))^2)*hb2
  have hGe : Gf k k = (((k+1).factorial:ℚ)*((2*k).factorial:ℚ))/((4*k).factorial:ℚ) := by
    rw [Gf, show k+k = 2*k from by ring, show 2*k+2*k = 4*k from by ring]
  have hG' : Gf k k * ((4*k).factorial:ℚ) = ((k+1).factorial:ℚ)*((2*k).factorial:ℚ) := by
    rw [hGe]; field_simp
  have hF1 : ((k+1).factorial:ℚ) = ((k:ℚ)+1)*(k.factorial:ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hLeq : Lsum k k * ((4*k).factorial:ℚ)
      = ck k*(k.factorial:ℚ)*((k+1).factorial:ℚ)*((2*k).factorial:ℚ) := by
    rw [Lsum_eq_R, R, pfall_diag,
        mul_assoc (ck k * (k.factorial:ℚ)) (Gf k k) ((4*k).factorial:ℚ), hG']
    ring
  linear_combination ((2*(k:ℚ)-1)^2*(2*(k:ℚ)-3)*((4*k).factorial:ℚ))*hLeq
    + (ck k*(k.factorial:ℚ)*((2*k).factorial:ℚ)*(2*(k:ℚ)-1)^2*(2*(k:ℚ)-3)*((4*k).factorial:ℚ))*hF1
    + (((k:ℚ)+1)*((2*k).factorial:ℚ))*hckf

/-- The integer `A_k = catalan(2k+1) - 2·catalan(2k)`. -/
def Aint (k : ℕ) : ℤ := (catalan (2*k+1) : ℤ) - 2*(catalan (2*k):ℤ)

/-- The integer `B_k = 2(2k-1)(2k-3)(2k+1)·catalan(2k-1) / 3`. -/
def Bint (k : ℕ) : ℤ :=
  (2*(2*(k:ℤ)-1)*(2*(k:ℤ)-3)*(2*(k:ℤ)+1)*(catalan (2*k-1):ℤ))/3

/-- The reciprocal integer `w_k`. -/
def wfun (k : ℕ) : ℤ := if k = 0 then 1 else Aint k * Bint k

/-- The integrality core: each `h_k = Lsum k k` is the reciprocal of an integer. -/
lemma exists_w : ∃ w : ℕ → ℤ, ∀ k, Lsum k k * (w k : ℚ) = 1 := by
  refine ⟨wfun, fun k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · -- k = 0
    simp only [wfun, if_pos rfl, Int.cast_one, mul_one]
    rw [Lsum_eq_R, R_zero]
    simp [mu]
  · -- 1 ≤ k
    have hk : 1 ≤ k := hk0
    simp only [wfun, if_neg (show k ≠ 0 by omega), Int.cast_mul]
    -- goal: Lsum k k * (↑(Aint k) * ↑(Bint k)) = 1
    have hA : ((k:ℚ)+1) * (Aint k:ℚ) = (2*(k:ℚ)-1) * (catalan (2*k):ℚ) := by
      have hrec := crecQ k
      have hAc : (Aint k:ℚ) = (catalan (2*k+1):ℚ) - 2*(catalan (2*k):ℚ) := by
        simp only [Aint]; push_cast; ring
      rw [hAc]; linear_combination hrec
    have hB : 3 * (Bint k:ℚ)
        = 2*(2*(k:ℚ)-1)*(2*(k:ℚ)-3)*(2*(k:ℚ)+1)*(catalan (2*k-1):ℚ) := by
      have hap : (3:ℤ) ∣ (2*(k:ℤ)-1)*(2*(k:ℤ)-3)*(2*(k:ℤ)+1) := by
        have h3 : (k:ℤ)%3 = 0 ∨ (k:ℤ)%3 = 1 ∨ (k:ℤ)%3 = 2 := by omega
        rcases h3 with h|h|h
        · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (show (3:ℤ) ∣ (2*(k:ℤ)-3) by omega) _) _
        · exact dvd_mul_of_dvd_right (show (3:ℤ) ∣ (2*(k:ℤ)+1) by omega) _
        · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (show (3:ℤ) ∣ (2*(k:ℤ)-1) by omega) _) _
      have hdvd : (3:ℤ) ∣ 2*(2*(k:ℤ)-1)*(2*(k:ℤ)-3)*(2*(k:ℤ)+1)*(catalan (2*k-1):ℤ) := by
        have he : 2*(2*(k:ℤ)-1)*(2*(k:ℤ)-3)*(2*(k:ℤ)+1)*(catalan (2*k-1):ℤ)
            = ((2*(k:ℤ)-1)*(2*(k:ℤ)-3)*(2*(k:ℤ)+1)) * (2*(catalan (2*k-1):ℤ)) := by ring
        rw [he]; exact hap.mul_right _
      have hBc : Bint k * 3 = 2*(2*(k:ℤ)-1)*(2*(k:ℤ)-3)*(2*(k:ℤ)+1)*(catalan (2*k-1):ℤ) := by
        simp only [Bint]; exact Int.ediv_mul_cancel hdvd
      have hBcQ : (Bint k:ℚ) * 3
          = 2*(2*(k:ℚ)-1)*(2*(k:ℚ)-3)*(2*(k:ℚ)+1)*(catalan (2*k-1):ℚ) := by
        exact_mod_cast hBc
      linear_combination hBcQ
    have hb2 : (Nat.centralBinom (2*k):ℚ)*((2*k).factorial:ℚ)^2 = ((4*k).factorial:ℚ) := by
      have := cbfact (2*k); rwa [show 2*(2*k) = 4*k from by ring] at this
    have hf1 : (2*(k:ℚ)+1)*(catalan (2*k):ℚ)*((2*k).factorial:ℚ)^2 = ((4*k).factorial:ℚ) := by
      linear_combination ((2*k).factorial:ℚ)^2 * catA k + hb2
    have hf2 : 2*(4*(k:ℚ)-1)*(catalan (2*k-1):ℚ)*((2*k).factorial:ℚ)^2 = ((4*k).factorial:ℚ) := by
      linear_combination ((2*k).factorial:ℚ)^2 * catBk k hk + hb2
    have hLd := Lsum_diag k
    have hAB_raw : (((k:ℚ)+1)*(Aint k:ℚ)) * (3*(Bint k:ℚ))
        = ((2*(k:ℚ)-1)*(catalan (2*k):ℚ))
          * (2*(2*(k:ℚ)-1)*(2*(k:ℚ)-3)*(2*(k:ℚ)+1)*(catalan (2*k-1):ℚ)) := by
      rw [hA, hB]
    have hCC_raw : ((2*(k:ℚ)+1)*(catalan (2*k):ℚ)*((2*k).factorial:ℚ)^2)
          * (2*(4*(k:ℚ)-1)*(catalan (2*k-1):ℚ)*((2*k).factorial:ℚ)^2)
        = ((4*k).factorial:ℚ) * ((4*k).factorial:ℚ) := by
      rw [hf1, hf2]
    have hK : (3*((k:ℚ)+1)*(4*(k:ℚ)-1)*((2*k).factorial:ℚ)^4) ≠ 0 := by
      have e1 : ((k:ℚ)+1) ≠ 0 := by positivity
      have e2 : (4*(k:ℚ)-1) ≠ 0 := by
        have : (1:ℚ) ≤ (k:ℚ) := by exact_mod_cast hk
        intro hc; linarith
      have e4 : ((2*k).factorial:ℚ)^4 ≠ 0 := by
        have := Nat.factorial_pos (2*k); positivity
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) e1) e2) e4
    have key : Lsum k k * (Aint k:ℚ) * (Bint k:ℚ)
          * (3*((k:ℚ)+1)*(4*(k:ℚ)-1)*((2*k).factorial:ℚ)^4)
        = 3*(4*(k:ℚ)-1)*((k:ℚ)+1)*((2*k).factorial:ℚ)^4 := by
      linear_combination (Lsum k k*(4*(k:ℚ)-1)*((2*k).factorial:ℚ)^4)*hAB_raw
        + (Lsum k k*(2*(k:ℚ)-1)^2*(2*(k:ℚ)-3))*hCC_raw + hLd
    have hfin : (Lsum k k * (Aint k:ℚ) * (Bint k:ℚ))
          * (3*((k:ℚ)+1)*(4*(k:ℚ)-1)*((2*k).factorial:ℚ)^4)
        = 1 * (3*((k:ℚ)+1)*(4*(k:ℚ)-1)*((2*k).factorial:ℚ)^4) := by
      rw [one_mul]; linear_combination key
    have hres := mul_right_cancel₀ hK hfin
    linear_combination hres

theorem catbert_det_inv_int (n : ℕ) :
    (Amat n).det⁻¹ ∈ Set.range (Int.cast : ℤ → ℚ) := by
  rw [det_Amat]
  obtain ⟨w, hw⟩ := exists_w
  exact ⟨∏ i : Fin n, w i.val, (prod_inv_int n w hw).symm⟩

end Catbert
