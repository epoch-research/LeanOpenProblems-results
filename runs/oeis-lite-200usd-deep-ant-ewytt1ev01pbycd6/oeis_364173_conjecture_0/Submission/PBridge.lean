import FormalConjectures.Util.ProblemImports
import Submission.PLog
import Submission.PKaz
import Submission.VonStaudt
import Submission.PSigma
import Submission.PStrong

open scoped Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

namespace PBridge

open PLog PKaz PSigma PStrong

variable {p : ℕ} [Fact p.Prime]

lemma prod_Icc_eq_fact (n : ℕ) : ∏ j ∈ Finset.Icc 1 n, j = n.factorial := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]; ring

/-- Natural-number version of `Wfac`: `∏_{1 ≤ j ≤ m, p ∤ j} j`. -/
def WfacN (m : ℕ) : ℕ := ∏ j ∈ (Finset.Icc 1 m).filter (fun j => ¬ p ∣ j), j

lemma WfacN_cast (m : ℕ) : ((WfacN (p := p) m : ℕ) : ℤ_[p]) = Wfac m := by
  rw [WfacN, Wfac, Nat.cast_prod]

/-- The block decomposition of a factorial: `(pL)! = WfacN(pL) · p^L · L!`. -/
lemma factorial_block (L : ℕ) :
    (p * L).factorial = WfacN (p := p) (p * L) * p ^ L * L.factorial := by
  have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
  -- `(pL)! = ∏_{j ∈ Icc 1 (pL)} j`
  have hfac : (p * L).factorial = ∏ j ∈ Finset.Icc 1 (p * L), j :=
    (prod_Icc_eq_fact (p * L)).symm
  -- split the product by divisibility by `p`
  have hsplit : (∏ j ∈ Finset.Icc 1 (p * L), j)
      = (∏ j ∈ (Finset.Icc 1 (p * L)).filter (fun j => ¬ p ∣ j), j)
        * (∏ j ∈ (Finset.Icc 1 (p * L)).filter (fun j => p ∣ j), j) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (p * L)) (fun j => p ∣ j)
        (fun j => j), mul_comm]
  -- the `p ∣ j` part is `∏_{k ∈ Icc 1 L} (p k) = p^L · L!`
  have hdvd : (∏ j ∈ (Finset.Icc 1 (p * L)).filter (fun j => p ∣ j), j)
      = p ^ L * L.factorial := by
    have hbij : (∏ j ∈ (Finset.Icc 1 (p * L)).filter (fun j => p ∣ j), j)
        = ∏ k ∈ Finset.Icc 1 L, (p * k) := by
      refine Finset.prod_nbij' (fun j => j / p) (fun k => p * k) ?_ ?_ ?_ ?_ ?_
      · rintro j hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨⟨hj1, hj2⟩, hd⟩ := hj
        obtain ⟨k, rfl⟩ := hd
        show (p * k) / p ∈ Finset.Icc 1 L
        rw [Nat.mul_div_cancel_left k hp0, Finset.mem_Icc]
        constructor
        · rcases Nat.eq_zero_or_pos k with hk | hk
          · simp [hk] at hj1
          · exact hk
        · exact le_of_mul_le_mul_left hj2 hp0
      · rintro k hk
        simp only [Finset.mem_Icc] at hk
        simp only [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨?_, ?_⟩, Dvd.intro k rfl⟩
        · have : 1 ≤ k := hk.1
          nlinarith [hp0]
        · exact Nat.mul_le_mul_left p hk.2
      · rintro j hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨_, hd⟩ := hj
        show p * (j / p) = j
        exact Nat.mul_div_cancel' hd
      · rintro k _
        show (p * k) / p = k
        exact Nat.mul_div_cancel_left k hp0
      · rintro j hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨_, hd⟩ := hj
        show j = p * (j / p)
        exact (Nat.mul_div_cancel' hd).symm
    rw [hbij, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
    simp only [Nat.add_sub_cancel]
    congr 1
    rw [← prod_Icc_eq_fact]
  rw [hfac, hsplit, hdvd, WfacN, ← mul_assoc]

/-- Cast of `factorial_block` into `ℤ_[p]`. -/
lemma factorial_block_cast (L : ℕ) :
    ((p * L).factorial : ℤ_[p]) = Wfac (p * L) * (p : ℤ_[p]) ^ L * (L.factorial : ℤ_[p]) := by
  have := factorial_block (p := p) L
  have h2 : ((p * L).factorial : ℤ_[p]) = ((WfacN (p := p) (p * L) * p ^ L * L.factorial : ℕ) : ℤ_[p]) := by
    rw [← this]
  rw [h2]; push_cast [WfacN_cast]; ring

/-- The even-case reduction of `a` to a factorial ratio. -/
lemma a_even (M : ℕ) :
    _root_.a (2 * M) =
      ((18 * M).factorial * (4 * M).factorial * (3 * M).factorial : ℝ) /
      ((9 * M).factorial * (8 * M).factorial * (6 * M).factorial * (2 * M).factorial : ℝ) := by
  unfold _root_.a
  simp only
  have h2M : ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) := by push_cast; ring
  rw [h2M]
  have e1 : (9 : ℝ) * (2 * M) + 1 = ((18 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  have e2 : (2 : ℝ) * (2 * M) + 1 = ((4 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  have e3 : (3 / 2 : ℝ) * (2 * M) + 1 = ((3 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  have e4 : (9 / 2 : ℝ) * (2 * M) + 1 = ((9 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  have e5 : (4 : ℝ) * (2 * M) + 1 = ((8 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  have e6 : (3 : ℝ) * (2 * M) + 1 = ((6 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  have e7 : (2 * (M:ℝ)) + 1 = ((2 * M : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [e1, e2, e3, e4, e5, e6, e7, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
      Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
      Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]

/-- Numerator factorial product for the even case (at `2·M`). -/
def Neven (M : ℕ) : ℕ := (18 * M).factorial * (4 * M).factorial * (3 * M).factorial
/-- Denominator factorial product for the even case (at `2·M`). -/
def Deven (M : ℕ) : ℕ := (9 * M).factorial * (8 * M).factorial * (6 * M).factorial * (2 * M).factorial

lemma Deven_pos (M : ℕ) : 0 < Deven M := by
  unfold Deven
  positivity

/-- The integer identity `cA · Deven M = Neven M`, from `cA = a(2M)`. -/
lemma int_identity (M : ℕ) (cA : ℤ) (hA : (cA : ℝ) = _root_.a (2 * M)) :
    cA * (Deven M : ℤ) = (Neven M : ℤ) := by
  have hD : (Deven M : ℝ) ≠ 0 := by exact_mod_cast (Deven_pos M).ne'
  have hreal : (cA : ℝ) * (Deven M : ℝ) = (Neven M : ℝ) := by
    rw [hA, a_even]
    simp only [Neven, Deven]
    push_cast
    field_simp
  have : ((cA * (Deven M : ℤ) : ℤ) : ℝ) = ((Neven M : ℤ) : ℝ) := by push_cast; push_cast at hreal; linarith [hreal]
  exact_mod_cast this

/-- `Wfac` is a `p`-adic unit. -/
lemma isUnit_Wfac (m : ℕ) : IsUnit (Wfac (p := p) m) := by
  rw [PadicInt.isUnit_iff, Wfac, norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_Icc] at hi
  exact norm_cast_eq_one hi.2

/-- Per-factor block decomposition inside `ℤ_[p]`. -/
lemma fact_term (i M M' : ℕ) (hM : M = p * M') :
    ((i * M).factorial : ℤ_[p]) = Wfac (i * M) * (p : ℤ_[p]) ^ (i * M') * ((i * M').factorial : ℤ_[p]) := by
  have hiM : i * M = p * (i * M') := by rw [hM]; ring
  rw [hiM, factorial_block_cast]

/-- Numerator block decomposition. -/
lemma Neven_block (M M' : ℕ) (hM : M = p * M') :
    (Neven M : ℤ_[p]) =
      (Wfac (18 * M) * Wfac (4 * M) * Wfac (3 * M)) * (p : ℤ_[p]) ^ (25 * M') * (Neven M' : ℤ_[p]) := by
  simp only [Neven]
  push_cast
  rw [fact_term 18 M M' hM, fact_term 4 M M' hM, fact_term 3 M M' hM,
      show 25 * M' = 18 * M' + 4 * M' + 3 * M' from by ring, pow_add, pow_add]
  ring

/-- Denominator block decomposition. -/
lemma Deven_block (M M' : ℕ) (hM : M = p * M') :
    (Deven M : ℤ_[p]) =
      (Wfac (9 * M) * Wfac (8 * M) * Wfac (6 * M) * Wfac (2 * M)) * (p : ℤ_[p]) ^ (25 * M') * (Deven M' : ℤ_[p]) := by
  simp only [Deven]
  push_cast
  rw [fact_term 9 M M' hM, fact_term 8 M M' hM, fact_term 6 M M' hM, fact_term 2 M M' hM,
      show 25 * M' = 9 * M' + 8 * M' + 6 * M' + 2 * M' from by ring, pow_add, pow_add, pow_add]
  ring

/-- Finset expansion for the numerator coefficient set. -/
lemma prod_num (f : ℕ → ℤ_[p]) :
    (∏ i ∈ ({18, 4, 3} : Finset ℕ), f i) = f 18 * f 4 * f 3 := by
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  ring

/-- Finset expansion for the denominator coefficient set. -/
lemma prod_den (f : ℕ → ℤ_[p]) :
    (∏ i ∈ ({9, 8, 6, 2} : Finset ℕ), f i) = f 9 * f 8 * f 6 * f 2 := by
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton]
  ring

/-- **The even-case bridge.** If `cA = a(2·m·pʳ)` and `cB = a(2·m·pʳ⁻¹)` are the
integer values of `a`, then `p^{3r} ∣ (cA - cB)`. -/
lemma even_bridge (hp5 : 5 ≤ p) (m r : ℕ) (hm : 0 < m) (hr : 1 ≤ r)
    (cA cB : ℤ) (hA : (cA : ℝ) = _root_.a (2 * (m * p ^ r)))
    (hB : (cB : ℝ) = _root_.a (2 * (m * p ^ (r - 1)))) :
    (p : ℤ) ^ (3 * r) ∣ (cA - cB) := by
  have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
  set M := m * p ^ r with hMdef
  set M' := m * p ^ (r - 1) with hM'def
  have hMM' : M = p * M' := by
    rw [hMdef, hM'def]
    have hpr : p ^ r = p * p ^ (r - 1) := by
      conv_lhs => rw [show r = 1 + (r - 1) from by omega]
      rw [pow_add, pow_one]
    rw [hpr]; ring
  -- integer identities from the real reduction
  have hidA : cA * (Deven M : ℤ) = (Neven M : ℤ) := int_identity M cA hA
  have hidB : cB * (Deven M' : ℤ) = (Neven M' : ℤ) := int_identity M' cB hB
  -- cast into `ℤ_[p]`
  have hidA' : (cA : ℤ_[p]) * (Deven M : ℤ_[p]) = (Neven M : ℤ_[p]) := by exact_mod_cast hidA
  have hidB' : (cB : ℤ_[p]) * (Deven M' : ℤ_[p]) = (Neven M' : ℤ_[p]) := by exact_mod_cast hidB
  rw [Neven_block M M' hMM', Deven_block M M' hMM', ← hidB'] at hidA'
  set An := Wfac (p:=p) (18 * M) * Wfac (p:=p) (4 * M) * Wfac (p:=p) (3 * M) with hAndef
  set Ad := Wfac (p:=p) (9 * M) * Wfac (p:=p) (8 * M) * Wfac (p:=p) (6 * M) * Wfac (p:=p) (2 * M) with hAddef
  set P := (p : ℤ_[p]) ^ (25 * M') with hPdef
  set Dd := (Deven M' : ℤ_[p]) with hDddef
  -- `hidA' : cA * (Ad * P * Dd) = An * P * (cB * Dd)`
  have hPne : P ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp0.ne')
  have hDdne : Dd ≠ 0 := by rw [hDddef]; exact_mod_cast (Deven_pos M').ne'
  have hPDd : P * Dd ≠ 0 := mul_ne_zero hPne hDdne
  have key : (cA : ℤ_[p]) * Ad = An * (cB : ℤ_[p]) := by
    have h2 : ((cA : ℤ_[p]) * Ad) * (P * Dd) = (An * (cB : ℤ_[p])) * (P * Dd) := by
      linear_combination hidA'
    exact mul_right_cancel₀ hPDd h2
  -- reduction `m = m₀ · p^e` with `¬ p ∣ m₀`
  obtain ⟨m₀, e, hnp, hmfac⟩ : ∃ m₀ e, ¬ p ∣ m₀ ∧ m = m₀ * p ^ e := by
    refine ⟨ordCompl[p] m, m.factorization p, Nat.not_dvd_ordCompl (Fact.out (p := p.Prime)) hm.ne', ?_⟩
    rw [mul_comm]; exact (Nat.ordProj_mul_ordCompl_eq_self m p).symm
  have hMval : M = m₀ * p ^ (r + e) := by rw [hMdef, hmfac]; ring
  -- apply the strong supercongruence
  have hstrong := strong_supercongruence (p := p) hp5 ({18, 4, 3} : Finset ℕ)
    ({9, 8, 6, 2} : Finset ℕ) id m₀ (r + e) hnp (by omega) (by decide)
  have hAn : (∏ i ∈ ({18, 4, 3} : Finset ℕ), Wfac (id i * (m₀ * p ^ (r + e)))) = An := by
    rw [prod_num]; simp only [id_eq]; rw [← hMval, hAndef]
  have hAd : (∏ i ∈ ({9, 8, 6, 2} : Finset ℕ), Wfac (id i * (m₀ * p ^ (r + e)))) = Ad := by
    rw [prod_den]; simp only [id_eq]; rw [← hMval, hAddef]
  rw [hAn, hAd] at hstrong
  -- `p^{3r} ∣ (An - Ad)`
  have hpow_dvd : (p : ℤ_[p]) ^ (3 * r) ∣ (An - Ad) :=
    dvd_trans (pow_dvd_pow (p : ℤ_[p]) (by omega)) hstrong
  -- combine
  have hrel : ((cA : ℤ_[p]) - (cB : ℤ_[p])) * Ad = (cB : ℤ_[p]) * (An - Ad) := by
    rw [sub_mul, mul_sub]; rw [key]; ring
  have hAdunit : IsUnit Ad := by
    rw [hAddef]
    exact (((isUnit_Wfac _).mul (isUnit_Wfac _)).mul (isUnit_Wfac _)).mul (isUnit_Wfac _)
  have hp3r : (p : ℤ_[p]) ^ (3 * r) ∣ ((cA : ℤ_[p]) - (cB : ℤ_[p])) := by
    rw [← IsUnit.dvd_mul_right hAdunit, hrel]
    exact hpow_dvd.mul_left _
  -- convert back to `ℤ`
  have hcast : ((cA - cB : ℤ) : ℤ_[p]) = (cA : ℤ_[p]) - (cB : ℤ_[p]) := by push_cast; ring
  rw [← hcast] at hp3r
  have hnorm : ‖((cA - cB : ℤ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(3 * r : ℕ) : ℤ) :=
    (dvd_iff_norm_le _ (3 * r)).mp hp3r
  have hfin := (PadicInt.norm_int_le_pow_iff_dvd (k := cA - cB) (n := 3 * r)).mp hnorm
  exact_mod_cast hfin

end PBridge
