/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports
import Submission.PLog
import Submission.PKaz
import Submission.VonStaudt
import Submission.PSigma
import Submission.PStrong
import Submission.PBridge

open scoped Real

namespace PBridgeOdd

open PLog PKaz PSigma PStrong PBridge

variable {p : ℕ} [Fact p.Prime]

/-! ## Generalized factorial block for arbitrary `m`. -/

/-- The block decomposition of a factorial for arbitrary `m`:
`m! = WfacN(m) · p^{⌊m/p⌋} · ⌊m/p⌋!`. -/
lemma factorial_block_gen (m : ℕ) :
    m.factorial = WfacN (p := p) m * p ^ (m / p) * (m / p).factorial := by
  have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
  have hfac : m.factorial = ∏ j ∈ Finset.Icc 1 m, j := (prod_Icc_eq_fact m).symm
  have hsplit : (∏ j ∈ Finset.Icc 1 m, j)
      = (∏ j ∈ (Finset.Icc 1 m).filter (fun j => ¬ p ∣ j), j)
        * (∏ j ∈ (Finset.Icc 1 m).filter (fun j => p ∣ j), j) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 m) (fun j => p ∣ j)
        (fun j => j), mul_comm]
  have hdvd : (∏ j ∈ (Finset.Icc 1 m).filter (fun j => p ∣ j), j)
      = p ^ (m / p) * (m / p).factorial := by
    have hbij : (∏ j ∈ (Finset.Icc 1 m).filter (fun j => p ∣ j), j)
        = ∏ k ∈ Finset.Icc 1 (m / p), (p * k) := by
      refine Finset.prod_nbij' (fun j => j / p) (fun k => p * k) ?_ ?_ ?_ ?_ ?_
      · rintro j hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨⟨hj1, hj2⟩, hd⟩ := hj
        obtain ⟨c, rfl⟩ := hd
        show (p * c) / p ∈ Finset.Icc 1 (m / p)
        rw [Nat.mul_div_cancel_left c hp0, Finset.mem_Icc]
        refine ⟨?_, ?_⟩
        · rcases Nat.eq_zero_or_pos c with hk | hk
          · simp [hk] at hj1
          · exact hk
        · exact Nat.le_div_iff_mul_le hp0 |>.mpr (by rw [mul_comm]; exact hj2)
      · rintro k hk
        simp only [Finset.mem_Icc] at hk
        simp only [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨?_, ?_⟩, Dvd.intro k rfl⟩
        · have : 1 ≤ k := hk.1
          nlinarith [hp0]
        · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hp0).mp hk.2
      · rintro j hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨_, hd⟩ := hj
        exact Nat.mul_div_cancel' hd
      · rintro k _
        exact Nat.mul_div_cancel_left k hp0
      · rintro j hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨_, hd⟩ := hj
        exact (Nat.mul_div_cancel' hd).symm
    rw [hbij, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
    simp only [Nat.add_sub_cancel]
    congr 1
    rw [← prod_Icc_eq_fact]
  rw [hfac, hsplit, hdvd, WfacN, ← mul_assoc]

/-! ## Part 0: the real reduction of `a n` for odd `n`. -/

/-- Legendre duplication packaged for a natural half-integer point:
`Γ((m+1)+1/2) = (2m+1)! · 2^{-1-2m} · √π / m!`. -/
lemma Gamma_half_nat (m : ℕ) :
    Real.Gamma ((m : ℝ) + 1 + 1 / 2)
      = ((2 * m + 1).factorial : ℝ) * (2 : ℝ) ^ (-1 - 2 * (m : ℝ)) * Real.sqrt π
        / (m.factorial : ℝ) := by
  have hdup := Real.Gamma_mul_Gamma_add_half ((m : ℝ) + 1)
  have hGm1 : Real.Gamma ((m : ℝ) + 1) = (m.factorial : ℝ) := by
    rw [Real.Gamma_nat_eq_factorial]
  have h2s : Real.Gamma (2 * ((m : ℝ) + 1)) = ((2 * m + 1).factorial : ℝ) := by
    have : (2 : ℝ) * ((m : ℝ) + 1) = ((2 * m + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [this, Real.Gamma_nat_eq_factorial]
  have hexp : (1 : ℝ) - 2 * ((m : ℝ) + 1) = -1 - 2 * (m : ℝ) := by ring
  rw [hGm1, h2s, hexp] at hdup
  have hfac_ne : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  field_simp at hdup ⊢
  linarith [hdup]

/-- `A = (9N-1)/2`. -/
def Aidx (N : ℕ) : ℕ := (9 * N - 1) / 2
/-- `B = (3N-1)/2`. -/
def Bidx (N : ℕ) : ℕ := (3 * N - 1) / 2

lemma two_Aidx (N : ℕ) (hodd : Odd N) : 2 * Aidx N + 1 = 9 * N := by
  obtain ⟨m, hm⟩ := hodd; subst hm; unfold Aidx; omega

lemma two_Bidx (N : ℕ) (hodd : Odd N) : 2 * Bidx N + 1 = 3 * N := by
  obtain ⟨m, hm⟩ := hodd; subst hm; unfold Bidx; omega

/-- The odd-case reduction of `a` to a factorial ratio.
For `n = 2k+1`, `A = 9k+4 = (9n-1)/2`, `B = 3k+1 = (3n-1)/2`. -/
lemma a_odd (k : ℕ) :
    _root_.a (2 * k + 1) =
      ((2 : ℝ) ^ (6 * (2 * k + 1)) * ((2 * (2 * k + 1)).factorial : ℝ) * ((9 * k + 4).factorial : ℝ)) /
      (((4 * (2 * k + 1)).factorial : ℝ) * ((2 * k + 1).factorial : ℝ) * ((3 * k + 1).factorial : ℝ)) := by
  set n := 2 * k + 1 with hn
  unfold _root_.a
  simp only
  have hπ : Real.sqrt π > 0 := Real.sqrt_pos.mpr Real.pi_pos
  have hπne : Real.sqrt π ≠ 0 := ne_of_gt hπ
  -- integer Gammas
  have e1 : (9 : ℝ) * (n : ℝ) + 1 = ((9 * n : ℕ) : ℝ) + 1 := by push_cast; ring
  have e2 : (2 : ℝ) * (n : ℝ) + 1 = ((2 * n : ℕ) : ℝ) + 1 := by push_cast; ring
  have e5 : (4 : ℝ) * (n : ℝ) + 1 = ((4 * n : ℕ) : ℝ) + 1 := by push_cast; ring
  have e6 : (3 : ℝ) * (n : ℝ) + 1 = ((3 * n : ℕ) : ℝ) + 1 := by push_cast; ring
  have e7 : (n : ℝ) + 1 = ((n : ℕ) : ℝ) + 1 := by push_cast; ring
  -- half Gammas
  have hB : (3 / 2 : ℝ) * (n : ℝ) + 1 = ((3 * k + 1 : ℕ) : ℝ) + 1 + 1 / 2 := by
    rw [hn]; push_cast; ring
  have hA : (9 / 2 : ℝ) * (n : ℝ) + 1 = ((9 * k + 4 : ℕ) : ℝ) + 1 + 1 / 2 := by
    rw [hn]; push_cast; ring
  rw [e1, e2, e5, e6, e7, hB, hA,
      Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
      Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
      Gamma_half_nat (3 * k + 1), Gamma_half_nat (9 * k + 4)]
  -- reduce the factorials appearing after duplication
  have hB1 : 2 * (3 * k + 1) + 1 = 3 * n := by rw [hn]; ring
  have hA1 : 2 * (9 * k + 4) + 1 = 9 * n := by rw [hn]; ring
  rw [hB1, hA1]
  -- now combine 2-power terms and cancel √π, (9n)!, (3n)!
  have hfac9 : ((9 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast (9 * n).factorial_ne_zero
  have hfac3 : ((3 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast (3 * n).factorial_ne_zero
  have hfacB : (((3 * k + 1).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (3 * k + 1).factorial_ne_zero
  have hfacA : (((9 * k + 4).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (9 * k + 4).factorial_ne_zero
  have hfac4 : ((4 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast (4 * n).factorial_ne_zero
  have hfacn : ((n).factorial : ℝ) ≠ 0 := by exact_mod_cast (n).factorial_ne_zero
  -- 2-power identity: 2^(-1-2B) = 2^(6n) · 2^(-1-2A)
  have hpow : (2 : ℝ) ^ (-1 - 2 * ((3 * k + 1 : ℕ) : ℝ))
      = (2 : ℝ) ^ (6 * n) * (2 : ℝ) ^ (-1 - 2 * ((9 * k + 4 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast (2 : ℝ) (6 * n), ← Real.rpow_add (by norm_num)]
    congr 1
    rw [hn]; push_cast; ring
  rw [hpow]
  have hcne : (2 : ℝ) ^ (-1 - 2 * ((9 * k + 4 : ℕ) : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  field_simp

/-! ## Part 1: the integer identity and its `ℤ_[p]` block decomposition. -/

/-- Numerator factorial product for the odd case. -/
def Numo (N : ℕ) : ℕ := 2 ^ (6 * N) * (2 * N).factorial * (Aidx N).factorial
/-- Denominator factorial product for the odd case. -/
def Deno (N : ℕ) : ℕ := (4 * N).factorial * N.factorial * (Bidx N).factorial

lemma Deno_pos (N : ℕ) : 0 < Deno N := by unfold Deno; positivity

/-- `cA · Deno N = Numo N`, from `cA = a N`, for odd `N`. -/
lemma int_identity_odd (N : ℕ) (hodd : Odd N) (cA : ℤ) (hA : (cA : ℝ) = _root_.a N) :
    cA * (Deno N : ℤ) = (Numo N : ℤ) := by
  obtain ⟨k, hk⟩ := hodd
  have hN : N = 2 * k + 1 := by omega
  subst hN
  have hAi : Aidx (2 * k + 1) = 9 * k + 4 := by unfold Aidx; omega
  have hBi : Bidx (2 * k + 1) = 3 * k + 1 := by unfold Bidx; omega
  have hD : (Deno (2 * k + 1) : ℝ) ≠ 0 := by exact_mod_cast (Deno_pos _).ne'
  have hreal : (cA : ℝ) * (Deno (2 * k + 1) : ℝ) = (Numo (2 * k + 1) : ℝ) := by
    rw [hA, a_odd k]
    unfold Numo Deno
    rw [hAi, hBi]
    push_cast
    field_simp
  have : ((cA * (Deno (2 * k + 1) : ℤ) : ℤ) : ℝ) = ((Numo (2 * k + 1) : ℤ) : ℝ) := by
    push_cast; push_cast at hreal; linarith [hreal]
  exact_mod_cast this

/-- Per-factor block decomposition, keyed on the floor `m / p = m'`. -/
lemma fact_term_div (m m' : ℕ) (h : m / p = m') :
    ((m.factorial : ℕ) : ℤ_[p]) = Wfac m * (p : ℤ_[p]) ^ m' * ((m'.factorial : ℕ) : ℤ_[p]) := by
  have := factorial_block_gen (p := p) m
  have h2 : ((m.factorial : ℕ) : ℤ_[p])
      = ((WfacN (p := p) m * p ^ (m / p) * (m / p).factorial : ℕ) : ℤ_[p]) := by rw [← this]
  rw [h2]; push_cast [WfacN_cast, h]; ring

/-- Division/quotient fact for the half indices. -/
lemma idx_div (a a' t : ℕ) (hp : p = 2 * t + 1) (hkey : 2 * a + 1 = p * (2 * a' + 1)) :
    a = p * a' + t ∧ a / p = a' := by
  have hp0 : 0 < p := by omega
  have heq2 : 2 * (p * a' + t) + 1 = 2 * a + 1 := by rw [hkey, hp]; ring
  have hae : p * a' + t = a := by
    have := Nat.add_right_cancel heq2
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  refine ⟨hae.symm, ?_⟩
  rw [← hae, Nat.mul_add_div hp0, Nat.div_eq_of_lt (by omega), Nat.add_zero]

/-- Numerator block decomposition into level `N'`. -/
lemma Numo_block (Nr N' t : ℕ) (hp : p = 2 * t + 1) (hodd : Odd Nr) (hNr : Nr = p * N') :
    (Numo Nr : ℤ_[p]) =
      (2 : ℤ_[p]) ^ (6 * (Nr - N'))
        * (Wfac (2 * Nr) * Wfac (Aidx Nr))
        * (p : ℤ_[p]) ^ (2 * N' + Aidx N') * (Numo N' : ℤ_[p]) := by
  have hp0 : 0 < p := by omega
  have hoddN' : Odd N' := by
    have hh : Odd (p * N') := hNr ▸ hodd
    exact (Nat.odd_mul.mp hh).2
  -- divisions
  have hd2 : (2 * Nr) / p = 2 * N' := by rw [hNr]; rw [show 2 * (p * N') = p * (2 * N') from by ring, Nat.mul_div_cancel_left _ hp0]
  have hdA := (idx_div (Aidx Nr) (Aidx N') t hp (by
    rw [two_Aidx Nr hodd, hNr, two_Aidx N' hoddN']; ring)).2
  have hNrge : N' ≤ Nr := by rw [hNr]; nlinarith [hp0]
  unfold Numo
  push_cast
  rw [fact_term_div (2 * Nr) (2 * N') hd2, fact_term_div (Aidx Nr) (Aidx N') hdA]
  rw [show 6 * Nr = 6 * (Nr - N') + 6 * N' from by omega, pow_add]
  ring

/-- Denominator block decomposition into level `N'`. -/
lemma Deno_block (Nr N' t : ℕ) (hp : p = 2 * t + 1) (hodd : Odd Nr) (hNr : Nr = p * N') :
    (Deno Nr : ℤ_[p]) =
      (Wfac (4 * Nr) * Wfac Nr * Wfac (Bidx Nr))
        * (p : ℤ_[p]) ^ (4 * N' + N' + Bidx N') * (Deno N' : ℤ_[p]) := by
  have hp0 : 0 < p := by omega
  have hoddN' : Odd N' := by
    have hh : Odd (p * N') := hNr ▸ hodd
    exact (Nat.odd_mul.mp hh).2
  have hd4 : (4 * Nr) / p = 4 * N' := by rw [hNr]; rw [show 4 * (p * N') = p * (4 * N') from by ring, Nat.mul_div_cancel_left _ hp0]
  have hd1 : Nr / p = N' := by rw [hNr, Nat.mul_div_cancel_left _ hp0]
  have hdB := (idx_div (Bidx Nr) (Bidx N') t hp (by
    rw [two_Bidx Nr hodd, hNr, two_Bidx N' hoddN']; ring)).2
  unfold Deno
  push_cast
  rw [fact_term_div (4 * Nr) (4 * N') hd4, fact_term_div Nr N' hd1, fact_term_div (Bidx Nr) (Bidx N') hdB]
  rw [pow_add, pow_add]
  ring

/-- Abbreviation: the analytic unit `U = 2^{6ΔN}·Wnum·Wden⁻¹`, which is `≡ 1 (mod p)`. -/
noncomputable def Ucore (n r : ℕ) : ℤ_[p] :=
  (2 : ℤ_[p]) ^ (6 * (n * p ^ r - n * p ^ (r - 1)))
      * (Wfac (2 * (n * p ^ r)) * Wfac (Aidx (n * p ^ r)))
      * PadicInt.inv (Wfac (4 * (n * p ^ r)) * Wfac (n * p ^ r) * Wfac (Bidx (n * p ^ r)))

/- **The analytic heart of the odd core (the p-adic Legendre duplication, to all orders).**

This states that the block-correction unit `Ucore` is `≡ 1 (mod p)` and that its `p`-adic
logarithm has norm `≤ p^{-3r}`.  Numerically (`p ∈ {5,7,11,13}`, various `n,r`) the log equals
`∑ₛ Σₛ · (n·2⁻¹·pʳ⁻¹)ˢ · ((18ˢ+4ˢ+3ˢ) − (9ˢ+8ˢ+6ˢ+2ˢ))`, i.e. exactly the even-case
`Sig`-series with the *half-integer* count base `h·pʳ⁻¹`, `h = n/2 ∈ ℤ_[p]`.  Since `Σ₀ = Σ₂ = 0`
and `18+4+3 = 9+8+6+2 = 25`, the `s = 0,1,2` terms vanish and each `s ≥ 3` term is bounded by
`‖Σₛ‖·‖h pʳ⁻¹‖ˢ ≤ p^{-3}·p^{-3(r-1)} = p^{-3r}`, exactly as in `PStrong.logdiff_le`.  Proving the
identity connecting `padicLog Ucore` to that series is the `p`-adic Legendre duplication formula
for Morita's `Γ_p`; this is the one remaining gap. -/
/-- The half-integer count base `M'' = n·2⁻¹·pʳ⁻¹ ∈ ℤ_[p]`. -/
noncomputable def Mbase (n r : ℕ) : ℤ_[p] := (n : ℤ_[p]) * iv 2 * (p : ℤ_[p]) ^ (r - 1)

/-- Two consecutive blocks combine into a single product over `[1,2p-1] \ {p}`. -/
lemma pblock_combined (m : ℕ) :
    Pblock (2 * m) * Pblock (2 * m + 1)
      = ∏ k ∈ Finset.Icc 1 (p - 1) ∪ Finset.Icc (p + 1) (2 * p - 1),
          ((2 * m * p + k : ℕ) : ℤ_[p]) := by
  have hdisj : Disjoint (Finset.Icc 1 (p - 1)) (Finset.Icc (p + 1) (2 * p - 1)) := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_Icc] at ha hb; omega
  have h2 : (∏ i ∈ Finset.Icc 1 (p - 1), (((2 * m + 1) * p + i : ℕ) : ℤ_[p]))
      = ∏ k ∈ Finset.Icc (p + 1) (2 * p - 1), ((2 * m * p + k : ℕ) : ℤ_[p]) := by
    refine Finset.prod_nbij' (fun i => p + i) (fun k => k - p) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_Icc] at hi ⊢; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro i hi; dsimp only; simp only [Finset.mem_Icc] at hi; omega
    · intro k hk; dsimp only; simp only [Finset.mem_Icc] at hk; omega
    · intro i hi; dsimp only; push_cast; ring
  rw [Finset.prod_union hdisj, Pblock, Pblock, h2]

/-- The even coprime residues in the double-block `(2mp, 2mp+2p)` give `2^{p-1}·Pblock m`. -/
lemma even_block (m : ℕ) :
    ∏ i ∈ Finset.Icc 1 (p - 1), ((2 * m * p + 2 * i : ℕ) : ℤ_[p])
      = (2 : ℤ_[p]) ^ (p - 1) * Pblock m := by
  have hstep : ∀ i, ((2 * m * p + 2 * i : ℕ) : ℤ_[p]) = 2 * ((m * p + i : ℕ) : ℤ_[p]) := by
    intro i; push_cast; ring
  simp_rw [hstep]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Pblock, Nat.card_Icc]
  congr 2

/-- Logarithm of a quotient of two units close to `1`: `log(x·y⁻¹) = log x − log y`. -/
lemma padicLog_div (hp3 : 3 ≤ p) (x y : ℤ_[p]) (hy : ‖y‖ = 1)
    (hx1 : ‖x - 1‖ < 1) (hxy1 : ‖x * PadicInt.inv y - 1‖ < 1) (hy1 : ‖y - 1‖ < 1) :
    padicLog (x * PadicInt.inv y - 1) = padicLog (x - 1) - padicLog (y - 1) := by
  have hyv : y * PadicInt.inv y = 1 := PadicInt.mul_inv hy
  have hmul := padicLog_mul hp3 (x * PadicInt.inv y - 1) (y - 1) hxy1 hy1
  have key : (x * PadicInt.inv y - 1) + (y - 1) + (x * PadicInt.inv y - 1) * (y - 1) = x - 1 := by
    have h1 : x * PadicInt.inv y * y = x := by
      rw [mul_assoc, mul_comm (PadicInt.inv y) y, hyv, mul_one]
    linear_combination h1
  rw [key] at hmul
  linear_combination -hmul

/-- **The p-adic Legendre duplication series identity** (verified numerically for
`p ∈ {5,7,11,13}`).  The `p`-adic log of the odd-core unit `Ucore - 1` expands as the
even-case `Sig`-series evaluated at the *half-integer* count base `M'' = n·2⁻¹·pʳ⁻¹`, with
count differences `Δₛ = (18ˢ+4ˢ+3ˢ) − (9ˢ+8ˢ+6ˢ+2ˢ)`. -/
lemma Ucore_log_series (hp5 : 5 ≤ p) (n r : ℕ) (hodd : Odd n) (hn : 0 < n) (hr : 1 ≤ r) :
    ‖(Ucore (p := p) n r) - 1‖ < 1 ∧
    padicLog ((Ucore (p := p) n r) - 1)
      = ∑' s : ℕ, Sig (p := p) s
          * ((Mbase (p := p) n r : ℚ_[p]) ^ s
              * (((18 : ℚ_[p]) ^ s + 4 ^ s + 3 ^ s) - (9 ^ s + 8 ^ s + 6 ^ s + 2 ^ s))) := by
  sorry

lemma Ucore_log_bound (hp5 : 5 ≤ p) (n r : ℕ) (hodd : Odd n) (hn : 0 < n) (hr : 1 ≤ r) :
    ‖(Ucore (p := p) n r) - 1‖ < 1 ∧
    ‖padicLog ((Ucore (p := p) n r) - 1)‖ ≤ (p : ℝ) ^ (-(3 * r : ℕ) : ℤ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hinv_le_one : (p : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hp0]; exact_mod_cast (by omega : 1 ≤ p)
  obtain ⟨hlt, hser⟩ := Ucore_log_series hp5 n r hodd hn hr
  refine ⟨hlt, ?_⟩
  rw [hser]
  set MQ : ℚ_[p] := (Mbase (p := p) n r : ℚ_[p]) with hMQ
  -- `‖MQ‖ ≤ p^{-(r-1)}`.
  have h2nd : ¬ p ∣ 2 := by
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  have hiv2norm : ‖(iv (p := p) 2 : ℤ_[p])‖ = 1 := by
    have h := mul_iv_cancel (p := p) (i := 2) h2nd
    have hc := congrArg norm h
    rw [norm_mul, norm_one, norm_cast_eq_one h2nd, one_mul] at hc
    exact hc
  have hMnorm : ‖MQ‖ ≤ ((p : ℝ)⁻¹) ^ (r - 1) := by
    rw [hMQ, PadicInt.padic_norm_e_of_padicInt, Mbase, norm_mul, norm_mul, norm_pow,
      PadicInt.norm_p, hiv2norm, mul_one]
    calc ‖(n : ℤ_[p])‖ * ((p : ℝ)⁻¹) ^ (r - 1)
        ≤ 1 * ((p : ℝ)⁻¹) ^ (r - 1) := by
          gcongr; exact PadicInt.norm_le_one _
      _ = ((p : ℝ)⁻¹) ^ (r - 1) := one_mul _
  -- `‖Δ s‖ ≤ 1` since the count difference is an integer.
  have hΔle : ∀ s : ℕ,
      ‖((18 : ℚ_[p]) ^ s + 4 ^ s + 3 ^ s) - (9 ^ s + 8 ^ s + 6 ^ s + 2 ^ s)‖ ≤ 1 := by
    intro s
    have hcast : ((18 : ℚ_[p]) ^ s + 4 ^ s + 3 ^ s) - (9 ^ s + 8 ^ s + 6 ^ s + 2 ^ s)
        = ((((18 ^ s + 4 ^ s + 3 ^ s) - (9 ^ s + 8 ^ s + 6 ^ s + 2 ^ s)) : ℤ) : ℚ_[p]) := by
      push_cast; ring
    rw [hcast, ← PadicInt.coe_intCast, PadicInt.padic_norm_e_of_padicInt]
    exact PadicInt.norm_le_one _
  -- the per-term bound
  have key : ∀ s : ℕ,
      ‖Sig (p := p) s
          * (MQ ^ s * (((18 : ℚ_[p]) ^ s + 4 ^ s + 3 ^ s) - (9 ^ s + 8 ^ s + 6 ^ s + 2 ^ s)))‖
        ≤ (p : ℝ) ^ (-((3 * r : ℕ) : ℤ)) := by
    intro s
    rcases Nat.lt_or_ge s 3 with hs | hs
    · interval_cases s
      · rw [Sig_zero]; simp only [zero_mul, norm_zero]; positivity
      · have hd1 : ((18 : ℚ_[p]) ^ 1 + 4 ^ 1 + 3 ^ 1) - (9 ^ 1 + 8 ^ 1 + 6 ^ 1 + 2 ^ 1) = 0 := by
          norm_num
        rw [hd1, mul_zero, mul_zero, norm_zero]; positivity
      · rw [Sig_two_eq_zero hp5]; simp only [zero_mul, norm_zero]; positivity
    · rw [norm_mul, norm_mul, norm_pow]
      have hSig : ‖Sig (p := p) s‖ ≤ ((p : ℝ)⁻¹) ^ 3 := by
        have hz3 : ((p : ℝ)⁻¹) ^ 3 = (p : ℝ) ^ (-3 : ℤ) := by rw [rpow_neg]; norm_num
        rw [hz3]; exact norm_Sig_le3 hp5 s (by omega)
      have hDs := hΔle s
      calc ‖Sig (p := p) s‖
              * (‖MQ‖ ^ s * ‖((18 : ℚ_[p]) ^ s + 4 ^ s + 3 ^ s) - (9 ^ s + 8 ^ s + 6 ^ s + 2 ^ s)‖)
          ≤ ((p : ℝ)⁻¹) ^ 3 * ((((p : ℝ)⁻¹) ^ (r - 1)) ^ s * 1) := by
            gcongr
        _ = ((p : ℝ)⁻¹) ^ (3 + (r - 1) * s) := by rw [mul_one, ← pow_mul, ← pow_add]
        _ ≤ ((p : ℝ)⁻¹) ^ (3 * r) := by
            apply pow_le_pow_of_le_one (by positivity) hinv_le_one
            have hle : (r - 1) * 3 ≤ (r - 1) * s := Nat.mul_le_mul (le_refl (r - 1)) (by omega)
            omega
        _ = (p : ℝ) ^ (-((3 * r : ℕ) : ℤ)) := rpow_neg (3 * r)
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) key

/-- **The hard `p`-adic core (odd case).**  Fully reduced to `Ucore_log_bound`. -/
lemma odd_core (hp5 : 5 ≤ p) (n r : ℕ) (hodd : Odd n) (hn : 0 < n) (hr : 1 ≤ r) :
    (p : ℤ_[p]) ^ (3 * r) ∣
      ((2 : ℤ_[p]) ^ (6 * (n * p ^ r - n * p ^ (r - 1)))
          * (Wfac (2 * (n * p ^ r)) * Wfac (Aidx (n * p ^ r)))
        - (Wfac (4 * (n * p ^ r)) * Wfac (n * p ^ r) * Wfac (Bidx (n * p ^ r)))) := by
  have hp3 : 3 ≤ p := by omega
  set Wnum := (2 : ℤ_[p]) ^ (6 * (n * p ^ r - n * p ^ (r - 1)))
      * (Wfac (2 * (n * p ^ r)) * Wfac (Aidx (n * p ^ r))) with hWnum
  set Wden := Wfac (p := p) (4 * (n * p ^ r)) * Wfac (p := p) (n * p ^ r)
      * Wfac (p := p) (Bidx (n * p ^ r)) with hWden
  have hWdenunit : IsUnit Wden :=
    ((isUnit_Wfac _).mul (isUnit_Wfac _)).mul (isUnit_Wfac _)
  have hWnorm : ‖Wden‖ = 1 := PadicInt.isUnit_iff.mp hWdenunit
  set vinv := PadicInt.inv Wden with hvinv
  have hvv : Wden * vinv = 1 := PadicInt.mul_inv hWnorm
  set U := Wnum * vinv with hU
  have hUcore : U = Ucore (p := p) n r := by
    rw [hU, hvinv, hWden, hWnum, Ucore]
  -- Wnum - Wden = (U - 1) * Wden
  have hfact : Wnum - Wden = (U - 1) * Wden := by
    rw [hU, sub_mul, one_mul, mul_assoc, mul_comm vinv Wden, hvv, mul_one]
  have hbnd := Ucore_log_bound hp5 n r hodd hn hr
  rw [← hUcore] at hbnd
  have hdvd : (p : ℤ_[p]) ^ (3 * r) ∣ (U - 1) :=
    sub_one_dvd_of_padicLog hp3 U hbnd.1 (3 * r) (by
      simpa using hbnd.2)
  rw [hfact]
  exact hdvd.mul_right _

/-- **The odd-case bridge.** -/
lemma odd_bridge (hp5 : 5 ≤ p) (n r : ℕ) (hodd : Odd n) (hn : 0 < n) (hr : 1 ≤ r)
    (cA cB : ℤ) (hA : (cA : ℝ) = _root_.a (n * p ^ r)) (hB : (cB : ℝ) = _root_.a (n * p ^ (r - 1))) :
    (p : ℤ) ^ (3 * r) ∣ (cA - cB) := by
  have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
  obtain ⟨t, hpt⟩ : ∃ t, p = 2 * t + 1 := by
    obtain ⟨t, ht⟩ := (Fact.out (p := p.Prime)).odd_of_ne_two (by omega); exact ⟨t, ht⟩
  set Nr := n * p ^ r with hNrdef
  set N' := n * p ^ (r - 1) with hN'def
  have hNrN' : Nr = p * N' := by
    rw [hNrdef, hN'def]
    have hpr : p ^ r = p * p ^ (r - 1) := by
      conv_lhs => rw [show r = 1 + (r - 1) from by omega]; rw [pow_add, pow_one]
    rw [hpr]; ring
  have hoddNr : Odd Nr := by
    rw [hNrdef]; exact hodd.mul (by
      have : Odd p := ⟨t, by omega⟩
      exact this.pow)
  have hoddN' : Odd N' := by
    rw [hN'def]; exact hodd.mul (by
      have : Odd p := ⟨t, by omega⟩
      exact this.pow)
  -- integer identities
  have hidA : cA * (Deno Nr : ℤ) = (Numo Nr : ℤ) := int_identity_odd Nr hoddNr cA hA
  have hidB : cB * (Deno N' : ℤ) = (Numo N' : ℤ) := int_identity_odd N' hoddN' cB hB
  have hidA' : (cA : ℤ_[p]) * (Deno Nr : ℤ_[p]) = (Numo Nr : ℤ_[p]) := by exact_mod_cast hidA
  have hidB' : (cB : ℤ_[p]) * (Deno N' : ℤ_[p]) = (Numo N' : ℤ_[p]) := by exact_mod_cast hidB
  -- balance of exponents
  have hbal : 2 * N' + Aidx N' = 4 * N' + N' + Bidx N' := by
    have hA' := two_Aidx N' hoddN'
    have hB' := two_Bidx N' hoddN'
    omega
  rw [Numo_block Nr N' t hpt hoddNr hNrN', Deno_block Nr N' t hpt hoddNr hNrN', hbal, ← hidB'] at hidA'
  set Wnum := Wfac (p := p) (2 * Nr) * Wfac (p := p) (Aidx Nr) with hWnum
  set Wden := Wfac (p := p) (4 * Nr) * Wfac (p := p) Nr * Wfac (p := p) (Bidx Nr) with hWden
  set P := (p : ℤ_[p]) ^ (4 * N' + N' + Bidx N') with hPdef
  set Dd := (Deno N' : ℤ_[p]) with hDddef
  set pw := (2 : ℤ_[p]) ^ (6 * (Nr - N')) with hpwdef
  -- hidA' : cA * (Wden * P * Dd) = pw * Wnum * P * (cB * Dd)
  have hPne : P ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp0.ne')
  have hDdne : Dd ≠ 0 := by rw [hDddef]; exact_mod_cast (Deno_pos N').ne'
  have hPDd : P * Dd ≠ 0 := mul_ne_zero hPne hDdne
  have key : (cA : ℤ_[p]) * Wden = pw * Wnum * (cB : ℤ_[p]) := by
    have h2 : ((cA : ℤ_[p]) * Wden) * (P * Dd) = (pw * Wnum * (cB : ℤ_[p])) * (P * Dd) := by
      ring_nf
      ring_nf at hidA'
      linear_combination hidA'
    exact mul_right_cancel₀ hPDd h2
  -- core divisibility
  have hcore : (p : ℤ_[p]) ^ (3 * r) ∣ (pw * Wnum - Wden) := by
    have := odd_core hp5 n r hodd hn hr
    rw [← hNrdef, ← hN'def] at this
    exact this
  have hrel : ((cA : ℤ_[p]) - (cB : ℤ_[p])) * Wden = (cB : ℤ_[p]) * (pw * Wnum - Wden) := by
    rw [sub_mul, mul_sub, key]; ring
  have hWdenunit : IsUnit Wden := by
    rw [hWden]; exact ((isUnit_Wfac _).mul (isUnit_Wfac _)).mul (isUnit_Wfac _)
  have hp3r : (p : ℤ_[p]) ^ (3 * r) ∣ ((cA : ℤ_[p]) - (cB : ℤ_[p])) := by
    rw [← IsUnit.dvd_mul_right hWdenunit, hrel]
    exact hcore.mul_left _
  have hcast : ((cA - cB : ℤ) : ℤ_[p]) = (cA : ℤ_[p]) - (cB : ℤ_[p]) := by push_cast; ring
  rw [← hcast] at hp3r
  have hnorm : ‖((cA - cB : ℤ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(3 * r : ℕ) : ℤ) :=
    (dvd_iff_norm_le _ (3 * r)).mp hp3r
  have hfin := (PadicInt.norm_int_le_pow_iff_dvd (k := cA - cB) (n := 3 * r)).mp hnorm
  exact_mod_cast hfin

/-- **Assembly: the full conjecture** (test version; the final inlined `Spec.lean` uses the
verbatim statement at top level). -/
theorem final_thm
    (h_int : ∀ m : ℕ, _root_.a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  intro p hp h5 n r hn hr
  haveI : Fact p.Prime := ⟨hp⟩
  set cA : ℤ := Classical.choose (h_int (n * p ^ r)) with hcAdef
  set cB : ℤ := Classical.choose (h_int (n * p ^ (r - 1))) with hcBdef
  have hA : (cA : ℝ) = _root_.a (n * p ^ r) := Classical.choose_spec (h_int (n * p ^ r))
  have hB : (cB : ℝ) = _root_.a (n * p ^ (r - 1)) := Classical.choose_spec (h_int (n * p ^ (r - 1)))
  have hr1 : 1 ≤ r := hr
  have hdvd : (p : ℤ) ^ (3 * r) ∣ (cA - cB) := by
    rcases Nat.even_or_odd n with hev | hodd
    · -- even case
      obtain ⟨m, hm2⟩ := hev
      have hmpos : 0 < m := by omega
      have hne : n = 2 * m := by omega
      have hAe : (cA : ℝ) = _root_.a (2 * (m * p ^ r)) := by
        rw [hA, hne]; congr 1; ring
      have hBe : (cB : ℝ) = _root_.a (2 * (m * p ^ (r - 1))) := by
        rw [hB, hne]; congr 1; ring
      exact PBridge.even_bridge h5 m r hmpos hr1 cA cB hAe hBe
    · -- odd case
      exact odd_bridge h5 n r hodd hn hr1 cA cB hA hB
  exact (Int.modEq_iff_dvd.mpr (dvd_sub_comm.mp hdvd))

end PBridgeOdd

