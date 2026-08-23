import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset
open scoped Nat

/-- The generalized coefficient $c_{m} (k) = \frac{(m k)!}{(k!)^m}$ in $\mathbb{N}$. -/
def coeff_of_log_gf_gen (m k : ℕ) : ℕ :=
  (m * k).factorial / (k.factorial ^ m)

/--
A generalized recursive definition for the coefficients of any exponential series $\exp(\sum d_k \frac{x^k}{k})$.
The coefficients $a_k$ satisfy $k \cdot a_k = \sum_{j=1}^k d_j \cdot a_{k-j}$.
This is a local helper function inside `b_m_int`.
-/
private noncomputable def generalized_exp_coeff (d : ℕ → ℕ) : ℕ → ℕ
| 0 => 1
| k' + 1 =>
  let k := k' + 1
  (Finset.sum (Finset.range k) fun j =>
    (d (j + 1)) * (generalized_exp_coeff d (k - (j + 1)))) / k

/--
The sequence $b_m(n)$ is defined by $b_m(n) := [x^n] A_m(x)^n$ for $n \ge 1$.
We define $b_m(n)$ as the $n$-th coefficient of the series $\exp(L_{m,n}(x))$, where the driving coefficients are $d_k = n \cdot c_m(k)$.
Since this sequence is in $\mathbb{N}$, we define it in $\mathbb{Z}$ for the congruence.
-/
noncomputable def b_m_int (m n : ℕ) : ℤ :=
  if n = 0 then 0 -- Not in the domain of the conjecture, but required for total function.
  else
    let d (k : ℕ) : ℕ := n * coeff_of_log_gf_gen m k
    (generalized_exp_coeff d n : ℤ)

/-! ## Helper lemmas -/

variable {p : ℕ}

lemma mem_Icc_pred_lt {k : ℕ} (hp : 0 < p) (hk : k ∈ Icc 1 (p - 1)) : k < p := by
  have := (mem_Icc.mp hk).2
  exact lt_of_le_of_lt this (Nat.pred_lt hp.ne')

lemma not_dvd_of_mem_Icc_pred {k : ℕ} (hp : p.Prime) (hk : k ∈ Icc 1 (p - 1)) :
    ¬ p ∣ k :=
  Nat.not_dvd_of_pos_of_lt (mem_Icc.mp hk).1 (mem_Icc_pred_lt hp.pos hk)

lemma isUnit_natCast_pow {t k : ℕ} (hp : p.Prime) (hk : k ∈ Icc 1 (p - 1)) :
    IsUnit (k : ZMod (p ^ t)) := by
  rw [ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  exact ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_of_mem_Icc_pred hp hk)).symm

lemma ZMod.natCast_ne_zero_of_not_dvd {k : ℕ} [hp : Fact p.Prime] (hk : ¬ p ∣ k) :
    (k : ZMod p) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  exact hk

lemma inv_eq_pow_sub_one {k : ℕ} [hp : Fact p.Prime] (hk : ¬ p ∣ k) :
    (k : ZMod p)⁻¹ = (k : ZMod p) ^ (p - 2) := by
  have hk0 : (k : ZMod p) ≠ 0 := ZMod.natCast_ne_zero_of_not_dvd hk
  have hF : (k : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hk0
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpow : (k : ZMod p) ^ (p - 1) = (k : ZMod p) * (k : ZMod p) ^ (p - 2) := by
    have : p - 1 = (p - 2) + 1 := by omega
    rw [this, pow_succ, mul_comm]
  exact inv_eq_of_mul_eq_one_right (hpow.symm.trans hF)

lemma inv_pow_eq_pow_fermat {k i : ℕ} [hp : Fact p.Prime] (hk : ¬ p ∣ k) :
    ((k : ZMod p)⁻¹) ^ i = (k : ZMod p) ^ (i * (p - 2)) := by
  rw [inv_eq_pow_sub_one hk, ← pow_mul, mul_comm]

/-- The image of `Icc 1 (p-1)` under `natCast` is exactly the units of `ZMod p`. -/
lemma sum_Icc_eq_sum_units {ι : Type*} [AddCommMonoid ι] (f : ZMod p → ι)
    [hp : Fact p.Prime] :
    (∑ k ∈ Icc 1 (p - 1), f (k : ZMod p)) = ∑ x : (ZMod p)ˣ, f x := by
  let emb : (ZMod p)ˣ ↪ ZMod p :=
    ⟨fun u => (u : ZMod p), Units.val_injective⟩
  have hset : (Icc 1 (p - 1)).image (fun k : ℕ => (k : ZMod p)) = univ.map emb := by
    ext x
    simp only [mem_image, mem_Icc, mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, emb]
    constructor
    · rintro ⟨k, ⟨hk1, hkp⟩, rfl⟩
      refine ⟨Units.mk0 (k : ZMod p) ?_, rfl⟩
      exact ZMod.natCast_ne_zero_of_not_dvd
        (Nat.not_dvd_of_pos_of_lt hk1 (lt_of_le_of_lt hkp (Nat.pred_lt hp.out.ne_zero)))
    · rintro ⟨u, rfl⟩
      refine ⟨(u : ZMod p).val, ?_, ?_⟩
      · have hval := ZMod.val_lt (u : ZMod p)
        have hpos : 0 < (u : ZMod p).val := by
          rw [Nat.pos_iff_ne_zero]
          intro h
          have : (u : ZMod p) = 0 := by
            have hcast := ZMod.natCast_zmod_val (u : ZMod p)
            rw [h] at hcast
            simpa using hcast.symm
          exact Units.ne_zero u this
        exact ⟨hpos, Nat.le_pred_of_lt hval⟩
      · exact ZMod.natCast_zmod_val (u : ZMod p)
  have h1 : (∑ k ∈ Icc 1 (p - 1), f (k : ZMod p)) =
      ∑ x ∈ (Icc 1 (p - 1)).image (fun k : ℕ => (k : ZMod p)), f x := by
    rw [sum_image]
    intro a ha b hb hab
    have ha' : a < p := mem_Icc_pred_lt hp.out.pos ha
    have hb' : b < p := mem_Icc_pred_lt hp.out.pos hb
    have := congrArg ZMod.val hab
    simpa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using this
  rw [h1, hset, sum_map]
  simp [emb]

lemma sum_pow_Icc_eq_zero {i : ℕ} [hp : Fact p.Prime] [DecidableEq (ZMod p)]
    (hdiv : ¬ (p - 1) ∣ i) :
    (∑ k ∈ Icc 1 (p - 1), (k : ZMod p) ^ i) = 0 := by
  rw [sum_Icc_eq_sum_units (fun x => x ^ i)]
  have hsum := FiniteField.sum_pow_units (K := ZMod p) (i := i)
  simp only [ZMod.card, hdiv, ite_false] at hsum
  convert hsum

lemma gcd_sub_two_sub_one (hp : 2 ≤ p) : Nat.gcd (p - 2) (p - 1) = 1 := by
  have h : p - 1 = (p - 2) + 1 := by omega
  have : Nat.Coprime ((p - 2) + 1) (p - 2) := by
    rw [Nat.coprime_self_add_left]
    exact Nat.coprime_one_left _
  rw [h]
  exact Nat.coprime_iff_gcd_eq_one.mp this.symm

lemma sum_inv_pow_eq_zero_mod_p {j : ℕ} [hp : Fact p.Prime] [DecidableEq (ZMod p)]
    (hj : 1 ≤ j) (hj2 : j ≤ p - 2) :
    (∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ j) = 0 := by
  rw [sum_congr rfl (fun k hk => inv_pow_eq_pow_fermat (not_dvd_of_mem_Icc_pred hp.out hk))]
  refine sum_pow_Icc_eq_zero ?_
  intro h
  have hcop : Nat.Coprime (p - 2) (p - 1) := gcd_sub_two_sub_one hp.out.two_le
  have hcop' : Nat.Coprime (p - 1) (p - 2) := hcop.symm
  have : (p - 1) ∣ j :=
    Nat.Coprime.dvd_of_dvd_mul_right hcop' (by simpa [mul_comm] using h)
  have := Nat.le_of_dvd (by omega : 0 < j) this
  omega

lemma wolstenholme_H1_mod_p [hp : Fact p.Prime] [DecidableEq (ZMod p)] (hp3 : 3 ≤ p) :
    (∑ k ∈ Icc 1 (p - 1), (k : ZMod p)⁻¹) = 0 := by
  simpa using sum_inv_pow_eq_zero_mod_p (p := p) (j := 1) (by omega) (by omega)

lemma wolstenholme_H2_mod_p [hp : Fact p.Prime] [DecidableEq (ZMod p)] (hp5 : 5 ≤ p) :
    (∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2) = 0 := by
  exact sum_inv_pow_eq_zero_mod_p (p := p) (j := 2) (by omega) (by omega)

lemma wolstenholme_H3_mod_p [hp : Fact p.Prime] [DecidableEq (ZMod p)] (hp5 : 5 ≤ p) :
    (∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 3) = 0 := by
  exact sum_inv_pow_eq_zero_mod_p (p := p) (j := 3) (by omega) (by omega)

/-- In `ZMod (p^3)`, `(1 - p * a)⁻¹ = 1 + p a + p² a²`. -/
lemma inv_one_sub_p_mul (a : ZMod (p ^ 3)) (_hp : 2 ≤ p) :
    (1 - (p : ZMod (p ^ 3)) * a)⁻¹ =
      1 + (p : ZMod (p ^ 3)) * a + (p : ZMod (p ^ 3)) ^ 2 * a ^ 2 := by
  have hp3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self _
  set x := (p : ZMod (p ^ 3)) * a
  have hx3 : x ^ 3 = 0 := by
    calc x ^ 3 = ((p : ZMod (p ^ 3)) * a) ^ 3 := rfl
      _ = (p : ZMod (p ^ 3)) ^ 3 * a ^ 3 := by ring
      _ = 0 * a ^ 3 := by rw [hp3]
      _ = 0 := by ring
  have hid : (1 - x) * (1 + x + x ^ 2) = 1 := by
    ring_nf
    simp [hx3]
  have hunit : IsUnit (1 - x) := IsUnit.of_mul_eq_one (1 + x + x ^ 2) hid
  have hinv : (1 - x) * (1 - x)⁻¹ = 1 := ZMod.mul_inv_of_unit (1 - x) hunit
  have hresult : (1 - x)⁻¹ = 1 + x + x ^ 2 :=
    (IsUnit.mul_left_cancel hunit (hid.trans hinv.symm)).symm
  convert hresult using 1
  simp [x]
  ring

lemma isUnit_p_sub_of_mem {k : ℕ} (hp : p.Prime) (hk : k ∈ Icc 1 (p - 1)) :
    IsUnit (((p - k : ℕ) : ZMod (p ^ 3))) := by
  have hpk : p - k ∈ Icc 1 (p - 1) := by
    rw [mem_Icc] at hk ⊢; omega
  exact isUnit_natCast_pow (t := 3) hp hpk

/-- Pairing in `ZMod (p³)`: `k⁻¹ + (p-k)⁻¹ = -p k⁻² - p² k⁻³`. -/
lemma inv_add_inv_sub {k : ℕ} (hp : p.Prime) (hk : k ∈ Icc 1 (p - 1)) :
    (k : ZMod (p ^ 3))⁻¹ + (((p - k : ℕ) : ZMod (p ^ 3)))⁻¹ =
      - (p : ZMod (p ^ 3)) * ((k : ZMod (p ^ 3))⁻¹) ^ 2
      - (p : ZMod (p ^ 3)) ^ 2 * ((k : ZMod (p ^ 3))⁻¹) ^ 3 := by
  have hklt : k < p := mem_Icc_pred_lt hp.pos hk
  have uk : IsUnit (k : ZMod (p ^ 3)) := isUnit_natCast_pow (t := 3) hp hk
  have upk : IsUnit (((p - k : ℕ) : ZMod (p ^ 3))) := isUnit_p_sub_of_mem hp hk
  -- Clear denominators by multiplying by the unit `k^3 * (p-k)`.
  set K := (k : ZMod (p ^ 3))
  set PK := ((p - k : ℕ) : ZMod (p ^ 3))
  have hPK : PK = (p : ZMod (p ^ 3)) - K := Nat.cast_sub hklt.le
  have hcleared :
      (K⁻¹ + PK⁻¹) * (K ^ 3 * PK) =
        (- (p : ZMod (p ^ 3)) * K⁻¹ ^ 2 - (p : ZMod (p ^ 3)) ^ 2 * K⁻¹ ^ 3) * (K ^ 3 * PK) := by
    have hKinv : K * K⁻¹ = 1 := ZMod.mul_inv_of_unit _ uk
    have hPKinv : PK * PK⁻¹ = 1 := ZMod.mul_inv_of_unit _ upk
    have hp3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
      rw [← Nat.cast_pow]; exact ZMod.natCast_self _
    -- LHS = K^2 * PK + K^3
    have hL : (K⁻¹ + PK⁻¹) * (K ^ 3 * PK) = K ^ 2 * PK + K ^ 3 := by
      calc (K⁻¹ + PK⁻¹) * (K ^ 3 * PK)
          = K⁻¹ * K ^ 3 * PK + PK⁻¹ * K ^ 3 * PK := by ring
        _ = K ^ 2 * (K * K⁻¹) * PK + K ^ 3 * (PK * PK⁻¹) := by ring
        _ = K ^ 2 * 1 * PK + K ^ 3 * 1 := by rw [hKinv, hPKinv]
        _ = K ^ 2 * PK + K ^ 3 := by ring
    -- RHS = -p K * PK - p^2 * PK
    have hR : (- (p : ZMod (p ^ 3)) * K⁻¹ ^ 2 - (p : ZMod (p ^ 3)) ^ 2 * K⁻¹ ^ 3) * (K ^ 3 * PK) =
        - (p : ZMod (p ^ 3)) * K * PK - (p : ZMod (p ^ 3)) ^ 2 * PK := by
      calc _ = - (p : ZMod (p ^ 3)) * K⁻¹ ^ 2 * K ^ 3 * PK
                - (p : ZMod (p ^ 3)) ^ 2 * K⁻¹ ^ 3 * K ^ 3 * PK := by ring
        _ = - (p : ZMod (p ^ 3)) * K * (K * K⁻¹) ^ 2 * PK
                - (p : ZMod (p ^ 3)) ^ 2 * (K * K⁻¹) ^ 3 * PK := by ring
        _ = - (p : ZMod (p ^ 3)) * K * 1 ^ 2 * PK
                - (p : ZMod (p ^ 3)) ^ 2 * 1 ^ 3 * PK := by rw [hKinv]
        _ = - (p : ZMod (p ^ 3)) * K * PK - (p : ZMod (p ^ 3)) ^ 2 * PK := by ring
    rw [hL, hR, hPK]
    -- p K^2 = -p K (p-K) - p^2 (p-K)   since p^3 = 0
    ring_nf
    simp [hp3]
  -- Now cancel the unit `K^3 * PK`
  have hunit : IsUnit (K ^ 3 * PK) := (uk.pow 3).mul upk
  exact IsUnit.mul_right_cancel hunit hcleared

/- ## Recurrence unfolding -/

lemma generalized_exp_coeff_zero (d : ℕ → ℕ) : generalized_exp_coeff d 0 = 1 := by
  simp [generalized_exp_coeff]

lemma generalized_exp_coeff_succ (d : ℕ → ℕ) (k : ℕ) :
    generalized_exp_coeff d (k + 1) =
      (∑ j ∈ range (k + 1), d (j + 1) * generalized_exp_coeff d (k - j)) / (k + 1) := by
  simp [generalized_exp_coeff]

lemma coeff_of_log_gf_gen_one (k : ℕ) : coeff_of_log_gf_gen 1 k = 1 := by
  simp [coeff_of_log_gf_gen]
  exact Nat.div_self (Nat.factorial_pos k)

lemma coeff_of_log_gf_gen_zero (m : ℕ) : coeff_of_log_gf_gen m 0 = 1 := by
  simp [coeff_of_log_gf_gen]

/-- `(k!)^m ∣ (m k)!`, so `coeff_of_log_gf_gen` is the exact quotient. -/
lemma factorial_pow_dvd_factorial_mul (m k : ℕ) :
    k.factorial ^ m ∣ (m * k).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul]
    have hadd : (m * k + k).factorial = (m * k + k).factorial := rfl
    exact dvd_trans (mul_dvd_mul ih (dvd_refl _))
      (Nat.factorial_mul_factorial_dvd_factorial_add (m * k) k)

lemma coeff_of_log_gf_gen_mul_factorial (m k : ℕ) :
    coeff_of_log_gf_gen m k * k.factorial ^ m = (m * k).factorial := by
  simpa [coeff_of_log_gf_gen] using
    Nat.div_mul_cancel (factorial_pow_dvd_factorial_mul m k)

/- ## The m = 1 closed form `b_1(n) = C(2n-1, n)` -/

/-- ∑_{t < k} C(n+t-1, n-1) = C(n+k-1, n). -/
lemma sum_choose_offset (n k : ℕ) (hn : 1 ≤ n) :
    ∑ t ∈ Finset.range k, (n + t - 1).choose (n - 1) = (n + k - 1).choose n := by
  induction k with
  | zero =>
    simp [choose_eq_zero_of_lt (show n - 1 < n by omega)]
  | succ k ih =>
    rw [sum_range_succ, ih]
    have hN : n + k.succ - 1 = n + k := by omega
    rw [hN]
    -- C(n+k-1, n) + C(n+k-1, n-1) = C(n+k, n)
    have hpascal := choose_succ_succ (n + k - 1) (n - 1)
    simp only [Nat.succ_eq_add_one] at hpascal
    have hn1 : n - 1 + 1 = n := by omega
    have hnk : n + k - 1 + 1 = n + k := by omega
    rw [hn1, hnk] at hpascal
    linarith [hpascal]

lemma choose_n_mul_eq_k_mul {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    n * (n + k - 1).choose n = k * (n + k - 1).choose k := by
  have hsym : (n + k - 1).choose n = (n + k - 1).choose (k - 1) := by
    refine choose_symm_of_eq_add ?_
    omega
  have hk1 : k - 1 + 1 = k := by omega
  have hsucc := choose_succ_right_eq (n + k - 1) (k - 1)
  rw [hk1] at hsucc
  have hsub : n + k - 1 - (k - 1) = n := by omega
  rw [hsub] at hsucc
  -- hsucc : C(N,k) * k = C(N, k-1) * n
  rw [hsym]
  linarith

/-- For driving coefficients constantly `n`, the `k`-th exp-coefficient is `C(n+k-1, k)`. -/
lemma generalized_exp_coeff_const (n k : ℕ) (hn : 1 ≤ n) :
    generalized_exp_coeff (fun _ => n) k = (n + k - 1).choose k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      simp [generalized_exp_coeff_zero]
    | succ k =>
      rw [generalized_exp_coeff_succ]
      -- Reindex the convolution to a prefix sum.
      have hreindex :
          ∑ j ∈ Finset.range (k + 1), generalized_exp_coeff (fun _ => n) (k - j) =
            ∑ t ∈ Finset.range (k + 1), generalized_exp_coeff (fun _ => n) t := by
        refine sum_nbij (fun j => k - j) ?_ ?_ ?_ ?_
        · intro j hj
          have hj' := mem_range.mp hj
          exact mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le k j))
        · intro a ha b hb hab
          have ha' := mem_range.mp ha
          have hb' := mem_range.mp hb
          have ha_le : a ≤ k := Nat.lt_succ_iff.mp ha'
          have hb_le : b ≤ k := Nat.lt_succ_iff.mp hb'
          calc a = k - (k - a) := (Nat.sub_sub_self ha_le).symm
            _ = k - (k - b) := by
                have : k - a = k - b := hab
                rw [this]
            _ = b := Nat.sub_sub_self hb_le
        · intro t ht
          have ht' := mem_range.mp ht
          have ht_le : t ≤ k := Nat.lt_succ_iff.mp ht'
          refine ⟨k - t, mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le k t)),
            Nat.sub_sub_self ht_le⟩
        · intro j hj; rfl
      have hsum :
          ∑ j ∈ Finset.range (k + 1), n * generalized_exp_coeff (fun _ => n) (k - j) =
            n * ∑ t ∈ Finset.range (k + 1), (n + t - 1).choose t := by
        rw [← mul_sum, hreindex]
        refine congrArg (fun s => n * s) ?_
        refine sum_congr rfl fun t ht => ?_
        have ht' := mem_range.mp ht
        rw [ih t (by omega)]
      rw [hsum]
      have hshift :
          ∑ t ∈ Finset.range (k + 1), (n + t - 1).choose t =
            ∑ t ∈ Finset.range (k + 1), (n + t - 1).choose (n - 1) := by
        refine sum_congr rfl fun t _ => ?_
        refine choose_symm_of_eq_add ?_
        omega
      rw [hshift, sum_choose_offset n (k + 1) hn]
      have heq : n + (k + 1) - 1 = n + k := by omega
      rw [heq]
      have hid : n * (n + k).choose n = (k + 1) * (n + k).choose (k + 1) := by
        have h := choose_n_mul_eq_k_mul (n := n) (k := k + 1) hn (by omega)
        simpa [heq] using h
      exact Nat.div_eq_of_eq_mul_left (by omega) (by linarith [hid])

lemma b_m_int_one (n : ℕ) (hn : 1 ≤ n) :
    b_m_int 1 n = (2 * n - 1).choose n := by
  have hne : n ≠ 0 := by omega
  unfold b_m_int
  simp only [hne, ↓reduceIte]
  have hd : (fun k => n * coeff_of_log_gf_gen 1 k) = fun _ => n := by
    funext k
    simp [coeff_of_log_gf_gen_one]
  rw [hd, generalized_exp_coeff_const n n hn]
  congr 2
  omega

lemma two_mul_choose_two_mul_sub_one (n : ℕ) (hn : 1 ≤ n) :
    2 * (2 * n - 1).choose n = (2 * n).choose n := by
  have h' := Nat.add_one_mul_choose_eq (2 * n - 1) (n - 1)
  have hN : 2 * n - 1 + 1 = 2 * n := by omega
  have hk : n - 1 + 1 = n := by omega
  rw [hN, hk] at h'
  -- h' : (2n) * C(2n-1, n-1) = C(2n, n) * n
  have hsym : (2 * n - 1).choose (n - 1) = (2 * n - 1).choose n := by
    refine choose_symm_of_eq_add ?_
    omega
  rw [hsym] at h'
  -- (2n) * C(2n-1, n) = C(2n, n) * n
  have hn0 : 0 < n := hn
  have hmul : n * (2 * (2 * n - 1).choose n) = n * (2 * n).choose n := by
    linarith [h']
  exact Nat.mul_left_cancel hn0 hmul

lemma choose_two_mul_sub_one (n : ℕ) (hn : 1 ≤ n) :
    (2 * n - 1).choose n = (2 * n).choose n / 2 := by
  have h := two_mul_choose_two_mul_sub_one n hn
  exact Nat.eq_div_of_mul_eq_left (by decide : 2 ≠ 0) (mul_comm 2 _ ▸ h)

/- ## Polynomials for the binomial supercongruence -/

/-- Integer coefficients `g_j = C(p, j) / p` for `1 ≤ j ≤ p-1`. -/
def gcoeff (p j : ℕ) : ℤ :=
  (p.choose j : ℤ) / p

lemma gcoeff_eq (p j : ℕ) (hp : p.Prime) (hj : 1 ≤ j) (hjp : j ≤ p - 1) :
    (p : ℤ) * gcoeff p j = p.choose j := by
  have hdiv : (p : ℤ) ∣ (p.choose j : ℤ) := by
    have : p ∣ p.choose j := by
      refine hp.dvd_choose_self ?_ ?_
      · omega
      · have : j < p := by
          have := hp.pos
          omega
        exact this
    exact Int.natCast_dvd_natCast.mpr this
  simp [gcoeff]
  exact Int.mul_ediv_cancel' hdiv

lemma choose_prime_dvd (hp : p.Prime) {j : ℕ} (hj : 0 < j) (hjp : j < p) :
    p ∣ p.choose j :=
  hp.dvd_choose_self hj.ne' hjp

/-- Intermediate polynomial in `(1 + X)^p = 1 + X^p + p • G`. -/
noncomputable def G_int (q : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.Icc 1 (q - 1), Polynomial.monomial j (gcoeff q j)

lemma G_int_coeff_eq (q j : ℕ) :
    (G_int q).coeff j = if 1 ≤ j ∧ j ≤ q - 1 then gcoeff q j else 0 := by
  simp only [G_int, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  split_ifs with h
  · have hjmem : j ∈ Icc 1 (q - 1) := mem_Icc.mpr h
    rw [Finset.sum_eq_single_of_mem j hjmem]
    · simp
    · intro i hi hne
      exact if_neg hne
  · refine Finset.sum_eq_zero fun i hi => ?_
    exact if_neg (by
      intro hij
      have := mem_Icc.mp hi
      subst hij
      exact h this)

lemma one_add_X_pow_prime (hp : p.Prime) :
    (1 + Polynomial.X : Polynomial ℤ) ^ p =
      1 + Polynomial.X ^ p + Polynomial.C (p : ℤ) * G_int p := by
  classical
  -- (X + 1)^p = ∑ C(p,j) X^j
  have hbin :
      (Polynomial.X + 1 : Polynomial ℤ) ^ p =
        ∑ j ∈ Finset.range (p + 1),
          Polynomial.monomial j (p.choose j : ℤ) := by
    rw [add_pow]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [one_pow, mul_one]
    rw [mul_comm, ← Polynomial.C_eq_natCast, Polynomial.C_mul_X_pow_eq_monomial]
  rw [show (1 + Polynomial.X : Polynomial ℤ) = Polynomial.X + 1 by ring, hbin]
  have h0 : Polynomial.monomial 0 (p.choose 0 : ℤ) = 1 := by
    simp
  have hpterm : Polynomial.monomial p (p.choose p : ℤ) = Polynomial.X ^ p := by
    simp [p.choose_self, ← Polynomial.C_mul_X_pow_eq_monomial]
  have hmid : ∑ j ∈ Icc 1 (p - 1), Polynomial.monomial j (p.choose j : ℤ) =
      Polynomial.C (p : ℤ) * G_int p := by
    simp only [G_int, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := mem_Icc.mp hj
    have hjeq := gcoeff_eq p j hp hj'.1 hj'.2
    rw [← hjeq, Polynomial.C_mul_monomial, mul_comm]
  have hdisj1 : Disjoint ({0} : Finset ℕ) (Icc 1 (p - 1)) := by
    simp [Finset.disjoint_singleton_left, mem_Icc]
  have hdisj2 : Disjoint ({0} ∪ Icc 1 (p - 1) : Finset ℕ) ({p} : Finset ℕ) := by
    simp [Finset.disjoint_singleton_right, mem_Icc]
    have := hp.pos
    omega
  have hunion : ({0} ∪ Icc 1 (p - 1) ∪ {p} : Finset ℕ) = Finset.range (p + 1) := by
    ext j
    simp only [Finset.mem_union, Finset.mem_singleton, mem_Icc, Finset.mem_range]
    have := hp.pos
    omega
  rw [← hunion, Finset.sum_union hdisj2, Finset.sum_union hdisj1]
  simp only [Finset.sum_singleton, h0, hpterm, hmid]
  ring

/- ## Product formula for binomial coefficients -/

lemma prod_range_succ_eq_factorial (k : ℕ) :
    ∏ i ∈ Finset.range k, (i + 1) = k.factorial :=
  Finset.prod_range_add_one_eq_factorial k

/-- `n.choose k * k! = ∏_{i < k} (n - i)`. -/
lemma choose_mul_factorial_eq_prod_range (n k : ℕ) :
    n.choose k * k.factorial = ∏ i ∈ Finset.range k, (n - i) := by
  rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]

/-- Rational product formula: `n.choose k = ∏_{i < k} (n - i) / (i + 1)`. -/
lemma choose_eq_prod_rat (n k : ℕ) (_hk : k ≤ n) :
    (n.choose k : ℚ) =
      ∏ i ∈ Finset.range k, ((n - i : ℕ) : ℚ) / (i + 1 : ℚ) := by
  have hprod := choose_mul_factorial_eq_prod_range n k
  have hfact := prod_range_succ_eq_factorial k
  have hk0 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hcast : (n.choose k : ℚ) * (k.factorial : ℚ) =
      ∏ i ∈ Finset.range k, ((n - i : ℕ) : ℚ) := by
    simpa [Nat.cast_mul, Nat.cast_prod] using congrArg (fun x : ℕ => (x : ℚ)) hprod
  have hdiv : (n.choose k : ℚ) =
      (∏ i ∈ Finset.range k, ((n - i : ℕ) : ℚ)) / (k.factorial : ℚ) := by
    field_simp [hk0]
    linarith [hcast]
  rw [hdiv, ← hfact, Nat.cast_prod]
  simp [Finset.prod_div_distrib]

lemma choose_mul_prod_eq (n k : ℕ) :
    (n.choose k : ℤ) * ∏ i ∈ Finset.range k, ((i + 1 : ℕ) : ℤ) =
      ∏ i ∈ Finset.range k, ((n - i : ℕ) : ℤ) := by
  have h := choose_mul_factorial_eq_prod_range n k
  have hf := prod_range_succ_eq_factorial k
  have h' : (n.choose k : ℤ) * (k.factorial : ℤ) =
      ∏ i ∈ Finset.range k, ((n - i : ℕ) : ℤ) := by
    simpa [Nat.cast_mul, Nat.cast_prod] using congrArg (fun x : ℕ => (x : ℤ)) h
  rw [← hf, Nat.cast_prod] at h'
  exact h'

/- ## Weak binomial congruence -/

lemma isUnit_of_not_dvd_zmod (t : ℕ) (hp : p.Prime) {k : ℕ} (h : ¬ p ∣ k) :
    IsUnit ((k : ZMod (p ^ t))) := by
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right t ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm

/-- Numbers `1, …, n` split into multiples of `q` and the rest. -/
lemma range_succ_disj (n q : ℕ) :
    Disjoint ((Finset.range n).filter (fun j => q ∣ j + 1))
      ((Finset.range n).filter (fun j => ¬ q ∣ j + 1)) :=
  disjoint_filter_filter_neg _ _ _

lemma range_succ_union (n q : ℕ) :
    ((Finset.range n).filter (fun j => q ∣ j + 1)) ∪
      ((Finset.range n).filter (fun j => ¬ q ∣ j + 1)) = Finset.range n :=
  filter_union_filter_not_eq _ _

/-- Multiples of `q` in `1..k*q` are `q, 2q, …, kq`. -/
lemma filter_dvd_succ_eq_image (k q : ℕ) (hq : 0 < q) :
    (Finset.range (k * q)).filter (fun j => q ∣ j + 1) =
      (Finset.range k).image (fun u => q * (u + 1) - 1) := by
  ext j
  constructor
  · intro hj
    have hjt : j < k * q := mem_range.mp (mem_filter.mp hj).1
    have hdvd : q ∣ j + 1 := (mem_filter.mp hj).2
    obtain ⟨u, hu⟩ := hdvd
    have hu0 : 0 < u := by
      apply Nat.pos_of_ne_zero
      rintro rfl
      omega
    have hu_le : u ≤ k := by
      have : q * u ≤ k * q := by
        have : j + 1 ≤ k * q := Nat.succ_le_of_lt hjt
        rwa [hu] at this
      exact Nat.le_of_mul_le_mul_left (mul_comm k q ▸ this) hq
    have hu_lt : u - 1 < k := by omega
    refine mem_image.mpr ⟨u - 1, mem_range.mpr hu_lt, ?_⟩
    have : q * (u - 1 + 1) - 1 = q * u - 1 := by
      rw [Nat.sub_add_cancel hu0]
    rw [this, ← hu]
    exact Nat.succ_sub_one j
  · intro hj
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hj
    have hu' : u < k := mem_range.mp hu
    refine mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩
    · have hlt : q * (u + 1) - 1 < q * (u + 1) :=
        Nat.sub_lt (Nat.mul_pos hq (Nat.succ_pos _)) (by omega)
      have hle : q * (u + 1) ≤ q * k := Nat.mul_le_mul_left q (Nat.succ_le_of_lt hu')
      calc q * (u + 1) - 1 < q * (u + 1) := hlt
        _ ≤ q * k := hle
        _ = k * q := mul_comm _ _
    · refine ⟨u + 1, ?_⟩
      exact Nat.sub_add_cancel (Nat.mul_pos hq (Nat.succ_pos _))

/-- `C(p,j) * j! = p * ∏_{i=1}^{j-1} (p-i)`. -/
lemma choose_prime_eq_prod (hp : p.Prime) {j : ℕ} (hj : 1 ≤ j) (hjp : j < p) :
    (p.choose j : ℤ) * (j.factorial : ℤ) =
      (p : ℤ) * ∏ i ∈ Finset.range (j - 1), ((p - (i + 1) : ℕ) : ℤ) := by
  have hmul := Nat.descFactorial_eq_factorial_mul_choose p j
  have : (p.choose j * j.factorial : ℤ) = (p.descFactorial j : ℤ) := by
    rw [mul_comm, ← Nat.cast_mul, hmul]
  rw [this, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  -- ∏_{i < j} (p-i) = p * ∏_{i < j-1} (p-(i+1))
  have hsplit : ∏ i ∈ Finset.range j, ((p - i : ℕ) : ℤ) =
      (p : ℤ) * ∏ i ∈ Finset.range (j - 1), ((p - (i + 1) : ℕ) : ℤ) := by
    have hjpos : 0 < j := hj
    have hrange : Finset.range j =
        insert 0 ((Finset.range (j - 1)).image (fun i => i + 1)) := by
      ext x
      simp only [mem_range, mem_insert, mem_image]
      constructor
      · intro hx
        cases x with
        | zero => simp
        | succ x =>
          right
          exact ⟨x, by omega, rfl⟩
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · omega
        · omega
    have hdisj : 0 ∉ (Finset.range (j - 1)).image (fun i => i + 1) := by
      simp [mem_image]
    rw [hrange, Finset.prod_insert hdisj]
    simp only [Nat.sub_zero]
    rw [Finset.prod_image (fun a _ b _ hab => Nat.succ_injective hab)]
  exact hsplit

lemma gcoeff_eq_prod (hp : p.Prime) {j : ℕ} (hj : 1 ≤ j) (hjp : j < p) :
    gcoeff p j * (j.factorial : ℤ) =
      ∏ i ∈ Finset.range (j - 1), ((p - (i + 1) : ℕ) : ℤ) := by
  have h := choose_prime_eq_prod hp hj hjp
  have hg := gcoeff_eq p j hp hj (by omega)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have : (p : ℤ) * (gcoeff p j * (j.factorial : ℤ)) =
      (p : ℤ) * ∏ i ∈ Finset.range (j - 1), ((p - (i + 1) : ℕ) : ℤ) := by
    rw [← mul_assoc, hg, h]
  exact Int.eq_of_mul_eq_mul_left hp0 this

lemma cast_sub_mod_p [Fact p.Prime] {a : ℕ} (ha : a ≤ p) :
    ((p - a : ℕ) : ZMod p) = - (a : ZMod p) := by
  rw [Nat.cast_sub ha]
  simp

lemma gcoeff_mod_p [Fact p.Prime] {j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p - 1) :
    (gcoeff p j : ZMod p) = (-1 : ZMod p) ^ (j - 1) * (j : ZMod p)⁻¹ := by
  have hp := Fact.out (p := p.Prime)
  have hjlt : j < p := by have := hp.pos; omega
  have hprod := gcoeff_eq_prod hp hj hjlt
  have hj0 : (j : ZMod p) ≠ 0 :=
    ZMod.natCast_ne_zero_of_not_dvd (not_dvd_of_mem_Icc_pred hp (mem_Icc.mpr ⟨hj, hjp⟩))
  have hcast : (gcoeff p j : ZMod p) * (j.factorial : ZMod p) =
      ∏ i ∈ Finset.range (j - 1), ((p - (i + 1) : ℕ) : ZMod p) := by
    apply_fun (fun z : ℤ => (z : ZMod p)) at hprod
    simpa [Int.cast_mul, Int.cast_prod, Int.cast_natCast] using hprod
  have hneg_term : ∀ i ∈ Finset.range (j - 1),
      ((p - (i + 1) : ℕ) : ZMod p) = - ((i + 1 : ℕ) : ZMod p) := by
    intro i hi
    have : i + 1 ≤ p := by
      have := mem_range.mp hi; omega
    exact cast_sub_mod_p this
  have hleft : (gcoeff p j : ZMod p) * (j.factorial : ZMod p) =
      ∏ i ∈ Finset.range (j - 1), (-((i + 1 : ℕ) : ZMod p)) := by
    rw [hcast]
    exact Finset.prod_congr rfl hneg_term
  have hneg : ∏ i ∈ Finset.range (j - 1), (-((i + 1 : ℕ) : ZMod p)) =
      (-1 : ZMod p) ^ (j - 1) * ∏ i ∈ Finset.range (j - 1), ((i + 1 : ℕ) : ZMod p) := by
    rw [show (fun i : ℕ => -((i + 1 : ℕ) : ZMod p)) =
          (fun i => (-1 : ZMod p) * ((i + 1 : ℕ) : ZMod p)) by funext; ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hfact : ∏ i ∈ Finset.range (j - 1), ((i + 1 : ℕ) : ZMod p) =
      ((j - 1).factorial : ZMod p) := by
    rw [← Nat.cast_prod, prod_range_succ_eq_factorial]
  have hfacj : (j.factorial : ZMod p) = (j : ZMod p) * ((j - 1).factorial : ZMod p) := by
    cases j with
    | zero => omega
    | succ j' =>
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.succ_sub_one]
  have hfac_ne : ((j - 1).factorial : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ (j - 1).factorial := (ZMod.natCast_eq_zero_iff (j - 1).factorial p).mp h0
    have : p ≤ j - 1 := (Nat.Prime.dvd_factorial hp).mp hdvd
    omega
  rw [hneg, hfact] at hleft
  have hmul : (gcoeff p j : ZMod p) * (j : ZMod p) * ((j - 1).factorial : ZMod p) =
      (-1 : ZMod p) ^ (j - 1) * ((j - 1).factorial : ZMod p) := by
    rw [mul_assoc, ← hfacj]
    exact hleft
  have hgj : (gcoeff p j : ZMod p) * (j : ZMod p) = (-1 : ZMod p) ^ (j - 1) :=
    mul_right_cancel₀ hfac_ne hmul
  calc (gcoeff p j : ZMod p)
      = (gcoeff p j : ZMod p) * (j : ZMod p) * (j : ZMod p)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hj0, mul_one]
    _ = (-1 : ZMod p) ^ (j - 1) * (j : ZMod p)⁻¹ := by rw [hgj]

lemma G_int_natDegree_le (q : ℕ) : (G_int q).natDegree ≤ q - 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  have hj' := mem_Icc.mp hj
  rw [Polynomial.natDegree_monomial]
  split_ifs with hg
  · exact Nat.zero_le _
  · exact hj'.2

lemma one_add_X_pow_eq_expand (n q : ℕ) :
    (1 + Polynomial.X ^ q : Polynomial ℤ) ^ n =
      Polynomial.expand ℤ q ((1 + Polynomial.X) ^ n) := by
  rw [Polynomial.expand_eq_comp_X_pow, Polynomial.comp, Polynomial.eval₂_pow]
  change _ = ((1 + Polynomial.X).comp (Polynomial.X ^ q)) ^ n
  rw [Polynomial.add_comp, Polynomial.one_comp, Polynomial.X_comp]

lemma coeff_one_add_X_pow_mul (n t q : ℕ) (hq : 0 < q) :
    ((1 + Polynomial.X ^ q : Polynomial ℤ) ^ n).coeff (q * t) = (n.choose t : ℤ) := by
  rw [one_add_X_pow_eq_expand, mul_comm q t, Polynomial.coeff_expand_mul hq,
    Polynomial.coeff_one_add_X_pow]

lemma coeff_one_add_X_pow_of_not_dvd {n d q : ℕ} (hq : 0 < q) (h : ¬ q ∣ d) :
    ((1 + Polynomial.X ^ q : Polynomial ℤ) ^ n).coeff d = 0 := by
  rw [one_add_X_pow_eq_expand, Polynomial.coeff_expand hq]
  simp [h]

lemma G_int_sq_coeff (q n : ℕ) :
    ((G_int q) ^ 2).coeff n =
      ∑ i ∈ Finset.range (n + 1), (G_int q).coeff i * (G_int q).coeff (n - i) := by
  rw [pow_two, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    fun i j => (G_int q).coeff i * (G_int q).coeff j]

lemma G_int_sq_coeff_p (hp : p.Prime) :
    ((G_int p) ^ 2).coeff p =
      ∑ j ∈ Icc 1 (p - 1), gcoeff p j * gcoeff p (p - j) := by
  have hppos := hp.pos
  rw [G_int_sq_coeff]
  have hss : Icc 1 (p - 1) ⊆ Finset.range (p + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (by have := mem_Icc.mp hi; omega)
  have hsub :
      ∑ i ∈ Finset.range (p + 1), (G_int p).coeff i * (G_int p).coeff (p - i) =
        ∑ i ∈ Icc 1 (p - 1), (G_int p).coeff i * (G_int p).coeff (p - i) := by
    refine (Finset.sum_subset hss ?_).symm
    intro i _ hi'
    rw [G_int_coeff_eq]
    split_ifs with h
    · exact (hi' (mem_Icc.mpr h)).elim
    · simp
  rw [hsub]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := mem_Icc.mp hj
  have hjp1 : 1 ≤ p - j := by omega
  have hjp : p - j ≤ p - 1 := by omega
  rw [G_int_coeff_eq, G_int_coeff_eq, if_pos ⟨hj'.1, hj'.2⟩, if_pos ⟨hjp1, hjp⟩]

lemma G_int_sq_natDegree_le (hp : p.Prime) :
    ((G_int p) ^ 2).natDegree ≤ 2 * (p - 1) := by
  have h := G_int_natDegree_le p
  calc ((G_int p) ^ 2).natDegree
      ≤ (G_int p).natDegree + (G_int p).natDegree := by
        rw [pow_two]; exact Polynomial.natDegree_mul_le
    _ ≤ (p - 1) + (p - 1) := Nat.add_le_add h h
    _ = 2 * (p - 1) := by ring

/-- `[X^p] G^{2}` is divisible by `p` for `p ≥ 5`. -/
lemma G_int_sq_coeff_p_dvd (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ) ∣ ((G_int p) ^ 2).coeff p := by
  have : Fact p.Prime := ⟨hp⟩
  have hsum := G_int_sq_coeff_p hp
  have hprod : ∀ j ∈ Icc 1 (p - 1),
      (gcoeff p j * gcoeff p (p - j) : ZMod p) = ((j : ZMod p)⁻¹) ^ 2 := by
    intro j hj
    have hj' := mem_Icc.mp hj
    have hjlt : j < p := by have := hp.pos; omega
    have h1 : 1 ≤ p - j := by omega
    have h2 : p - j ≤ p - 1 := by omega
    have hg1 := gcoeff_mod_p (p := p) hj'.1 hj'.2
    have hg2 := gcoeff_mod_p (p := p) h1 h2
    have hneg : ((p - j : ℕ) : ZMod p) = -(j : ZMod p) := cast_sub_mod_p hjlt.le
    have hpow : (-1 : ZMod p) ^ (j - 1) * (-1 : ZMod p) ^ (p - j - 1) =
        (-1 : ZMod p) ^ (p - 2) := by
      rw [← pow_add]; congr 1; omega
    have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
    have hsign : (-1 : ZMod p) ^ (p - 2) = -1 := by
      have hpmod : p % 2 = 1 := (Nat.odd_iff.mp hp_odd)
      have hodd : Odd (p - 2) := Nat.odd_iff.mpr (by omega)
      obtain ⟨k, hk⟩ := hodd
      rw [hk, pow_add, pow_mul, pow_one]
      simp
    have hinv : (((p - j : ℕ) : ZMod p))⁻¹ = -((j : ZMod p)⁻¹) := by
      rw [hneg, inv_neg]
    rw [hg1, hg2, hinv]
    have hsign' : (-1 : ZMod p) ^ (j - 1) * (-1 : ZMod p) ^ (p - j - 1) = -1 :=
      hpow.trans hsign
    rw [mul_mul_mul_comm, hsign']
    ring
  have hcast : (((G_int p) ^ 2).coeff p : ZMod p) =
      ∑ j ∈ Icc 1 (p - 1), ((j : ZMod p)⁻¹) ^ 2 := by
    rw [hsum, Int.cast_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    simpa using hprod j hj
  have h0 := wolstenholme_H2_mod_p (p := p) hp5
  have : (((G_int p) ^ 2).coeff p : ZMod p) = 0 := by
    rw [hcast, h0]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this

lemma coeff_mul_G_multiple (a b : ℕ) (hp : p.Prime) :
    ((1 + Polynomial.X ^ p : Polynomial ℤ) ^ a * G_int p).coeff (b * p) = 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    fun i j => ((1 + Polynomial.X ^ p : Polynomial ℤ) ^ a).coeff i * (G_int p).coeff j]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : i ≤ b * p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hdiv : p ∣ i
  · rw [G_int_coeff_eq]
    split_ifs with h
    · have hjlt : b * p - i < p := by have := hp.pos; omega
      have pdvd : p ∣ b * p - i := by
        have hbp : p ∣ b * p := dvd_mul_left p b
        exact Nat.dvd_sub hbp hdiv
      exact (Nat.not_dvd_of_pos_of_lt h.1 hjlt pdvd).elim
    · simp
  · rw [coeff_one_add_X_pow_of_not_dvd hp.pos hdiv]
    simp

lemma wolstenholme_term_zero (a b : ℕ) (hp : p.Prime) :
    ((1 + Polynomial.X ^ p : Polynomial ℤ) ^ a).coeff (b * p) = (a.choose b : ℤ) := by
  simpa [mul_comm b p] using coeff_one_add_X_pow_mul a b p hp.pos

lemma wolstenholme_inner_two (a b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ) ∣ ((1 + Polynomial.X ^ p : Polynomial ℤ) ^ a * (G_int p) ^ 2).coeff (b * p) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    fun i j => ((1 + Polynomial.X ^ p : Polynomial ℤ) ^ a).coeff i * ((G_int p) ^ 2).coeff j]
  refine Finset.dvd_sum fun i hi => ?_
  have hi' : i ≤ b * p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hdiv : p ∣ i
  · obtain ⟨t, ht⟩ := hdiv
    have htle : t ≤ b := by
      have : p * t ≤ p * b := by
        have : i ≤ b * p := hi'
        rwa [ht, mul_comm b] at this
      exact Nat.le_of_mul_le_mul_left this hp.pos
    have hjEq : b * p - i = p * (b - t) := by
      rw [ht, mul_comm b p, ← Nat.mul_sub]
    by_cases hjp : b * p - i = p
    · have : (p : ℤ) ∣ ((G_int p) ^ 2).coeff (b * p - i) := by
        rw [hjp]; exact G_int_sq_coeff_p_dvd hp hp5
      exact dvd_mul_of_dvd_right this _
    · have hcases : b * p - i = 0 ∨ 2 * p ≤ b * p - i := by
        have pd : p ∣ b * p - i := Nat.dvd_sub (dvd_mul_left p b) ⟨t, ht⟩
        obtain ⟨s, hs⟩ := pd
        match s with
        | 0 => exact Or.inl (by simp [hs])
        | 1 => exact (hjp (by simp [hs])).elim
        | s + 2 =>
          right
          nlinarith [hp.pos, hs]
      cases hcases with
      | inl h0 =>
        have hG0 : (G_int p).coeff 0 = 0 := by rw [G_int_coeff_eq]; simp
        have : ((G_int p) ^ 2).coeff 0 = 0 := by
          rw [G_int_sq_coeff]; simp [hG0]
        simp [h0, this]
      | inr h2p =>
        have : ((G_int p) ^ 2).coeff (b * p - i) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          have hdeg := G_int_sq_natDegree_le hp
          have : 2 * (p - 1) < b * p - i := by
            have : 2 * (p - 1) < 2 * p := by have := hp.pos; omega
            omega
          exact lt_of_le_of_lt hdeg this
        simp [this]
  · rw [coeff_one_add_X_pow_of_not_dvd hp.pos hdiv]
    simp

lemma wolstenholme_expand_coeff (a b : ℕ) :
    ((1 + Polynomial.X ^ p + Polynomial.C (p : ℤ) * G_int p : Polynomial ℤ) ^ a).coeff (b * p) =
      ∑ m ∈ Finset.range (a + 1),
        (a.choose m : ℤ) * (p : ℤ) ^ (a - m) *
          ((1 + Polynomial.X ^ p : Polynomial ℤ) ^ m * (G_int p) ^ (a - m)).coeff (b * p) := by
  have hbin := add_pow (1 + Polynomial.X ^ p : Polynomial ℤ)
    (Polynomial.C (p : ℤ) * G_int p) a
  rw [show 1 + Polynomial.X ^ p + Polynomial.C (p : ℤ) * G_int p =
      (1 + Polynomial.X ^ p) + Polynomial.C (p : ℤ) * G_int p by ac_rfl]
  rw [hbin, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hC : (a.choose m : Polynomial ℤ) = Polynomial.C (a.choose m : ℤ) := by simp
  have hpG : (Polynomial.C (p : ℤ) * G_int p) ^ (a - m) =
      Polynomial.C ((p : ℤ) ^ (a - m)) * (G_int p) ^ (a - m) := by
    rw [mul_pow, Polynomial.C_pow]
  rw [hC, hpG]
  have hcomm : (1 + Polynomial.X ^ p : Polynomial ℤ) ^ m *
        (Polynomial.C ((p : ℤ) ^ (a - m)) * (G_int p) ^ (a - m)) *
        Polynomial.C (a.choose m : ℤ) =
      Polynomial.C ((a.choose m : ℤ) * (p : ℤ) ^ (a - m)) *
        ((1 + Polynomial.X ^ p) ^ m * (G_int p) ^ (a - m)) := by
    simp [Polynomial.C_mul]
    ring
  rw [hcomm, Polynomial.coeff_C_mul]

/-- Wolstenholme for binomial coefficients, `r = 1`. -/
lemma wolstenholme_choose_r1 (a b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ((a * p).choose (b * p) : ℤ) ≡ (a.choose b : ℤ) [ZMOD (p ^ 3 : ℤ)] := by
  by_cases hba : b ≤ a
  · have hpow := one_add_X_pow_prime (p := p) hp
    have hleft : ((1 + Polynomial.X : Polynomial ℤ) ^ (a * p)).coeff (b * p) =
        ((a * p).choose (b * p) : ℤ) :=
      Polynomial.coeff_one_add_X_pow _ _ _
    have hexp : (1 + Polynomial.X : Polynomial ℤ) ^ (a * p) =
        (1 + Polynomial.X ^ p + Polynomial.C (p : ℤ) * G_int p) ^ a := by
      rw [mul_comm a p, pow_mul, hpow]
    rw [Int.modEq_iff_dvd, ← hleft, hexp, wolstenholme_expand_coeff]
    -- Isolate the m = a term, which equals C(a,b)
    have hamem : a ∈ Finset.range (a + 1) := by simp
    have hsplit :
        (a.choose b : ℤ) -
            ∑ m ∈ Finset.range (a + 1),
              (a.choose m : ℤ) * (p : ℤ) ^ (a - m) *
                ((1 + Polynomial.X ^ p : Polynomial ℤ) ^ m *
                  (G_int p) ^ (a - m)).coeff (b * p) =
          - ∑ m ∈ (Finset.range (a + 1)).erase a,
              (a.choose m : ℤ) * (p : ℤ) ^ (a - m) *
                ((1 + Polynomial.X ^ p : Polynomial ℤ) ^ m *
                  (G_int p) ^ (a - m)).coeff (b * p) := by
      rw [← Finset.sum_erase_add _ _ hamem]
      simp only [Nat.sub_self, pow_zero, one_mul, Nat.choose_self, Nat.cast_one, mul_one]
      rw [wolstenholme_term_zero a b hp]
      ring
    rw [hsplit, dvd_neg]
    refine Finset.dvd_sum fun m hm => ?_
    have hne : m ≠ a := (Finset.mem_erase.mp hm).1
    have hmr : m ∈ Finset.range (a + 1) := (Finset.mem_erase.mp hm).2
    have hmle : m ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmr)
    have hkm : 1 ≤ a - m := Nat.sub_pos_of_lt (lt_of_le_of_ne hmle hne)
    have hk : a - m = 1 ∨ a - m = 2 ∨ 3 ≤ a - m := by omega
    rcases hk with hk1 | hk2 | hk3
    · -- power of pG is 1
      have : ((1 + Polynomial.X ^ p : Polynomial ℤ) ^ m * (G_int p) ^ (a - m)).coeff (b * p) = 0 := by
        rw [hk1, pow_one]
        exact coeff_mul_G_multiple m b hp
      simp [this]
    · -- power of pG is 2
      have hinner := wolstenholme_inner_two m b hp hp5
      have hpow2 : (p : ℤ) ^ (a - m) = (p : ℤ) ^ 2 := by rw [hk2]
      have hG : (G_int p) ^ (a - m) = (G_int p) ^ 2 := by rw [hk2]
      rw [hpow2, hG]
      have h1 : (p : ℤ) ^ 3 ∣
          (p : ℤ) ^ 2 * ((1 + Polynomial.X ^ p : Polynomial ℤ) ^ m * (G_int p) ^ 2).coeff (b * p) := by
        have : (p : ℤ) ^ 3 = (p : ℤ) ^ 2 * p := by ring
        rw [this]
        exact mul_dvd_mul_left _ hinner
      rw [mul_assoc]
      exact dvd_mul_of_dvd_right h1 _
    · -- power of pG ≥ 3
      refine dvd_mul_of_dvd_left ?_ _
      exact dvd_mul_of_dvd_right (pow_dvd_pow (p : ℤ) hk3) _
  · have : a < b := Nat.lt_of_not_ge hba
    have hb1 : a * p < b * p := Nat.mul_lt_mul_of_pos_right this hp.pos
    simp [Nat.choose_eq_zero_of_lt this, Nat.choose_eq_zero_of_lt hb1]

lemma two_mul_b_m_int_one (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℤ) * b_m_int 1 n = (2 * n).choose n := by
  rw [b_m_int_one n hn]
  exact_mod_cast two_mul_choose_two_mul_sub_one n hn

lemma b_m_int_one_congr_of_central (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M) {q : ℤ}
    (h : ((2 * N).choose N : ℤ) ≡ ((2 * M).choose M : ℤ) [ZMOD q])
    (h2 : IsCoprime (2 : ℤ) q) :
    b_m_int 1 N ≡ b_m_int 1 M [ZMOD q] := by
  have hN' := two_mul_b_m_int_one N hN
  have hM' := two_mul_b_m_int_one M hM
  have hmul : (2 : ℤ) * b_m_int 1 N ≡ (2 : ℤ) * b_m_int 1 M [ZMOD q] := by
    rwa [hN', hM']
  rw [Int.modEq_iff_dvd] at hmul ⊢
  have : q ∣ 2 * (b_m_int 1 M - b_m_int 1 N) := by
    convert hmul using 1; ring
  exact h2.symm.dvd_of_dvd_mul_left this

lemma prod_range_split_dvd (n q : ℕ) :
    (∏ i ∈ Finset.range n, (i + 1)) =
      (∏ i ∈ (Finset.range n).filter (fun j => q ∣ j + 1), (i + 1)) *
      (∏ i ∈ (Finset.range n).filter (fun j => ¬ q ∣ j + 1), (i + 1)) := by
  rw [← Finset.prod_union (range_succ_disj n q), range_succ_union]

lemma prod_filter_dvd_factorial (k q : ℕ) (hq : 0 < q) :
    ∏ i ∈ (Finset.range (k * q)).filter (fun j => q ∣ j + 1), (i + 1) =
      q ^ k * k.factorial := by
  rw [filter_dvd_succ_eq_image k q hq]
  have hinj : Set.InjOn (fun u : ℕ => q * (u + 1) - 1) (Finset.range k) := by
    intro u _ v _ h
    have hu : 1 ≤ q * (u + 1) := Nat.mul_pos hq (Nat.succ_pos _)
    have hv : 1 ≤ q * (v + 1) := Nat.mul_pos hq (Nat.succ_pos _)
    have h' : q * (u + 1) - 1 = q * (v + 1) - 1 := by
      simpa using h
    have heq : q * (u + 1) - 1 + 1 = q * (v + 1) - 1 + 1 := by rw [h']
    rw [Nat.sub_add_cancel hu, Nat.sub_add_cancel hv] at heq
    exact Nat.succ_injective (Nat.mul_left_cancel hq heq)
  rw [Finset.prod_image hinj]
  have hcancel : ∀ u ∈ Finset.range k, q * (u + 1) - 1 + 1 = q * (u + 1) := fun u _ =>
    Nat.sub_add_cancel (Nat.mul_pos hq (Nat.succ_pos _))
  refine Eq.trans (Finset.prod_congr rfl hcancel) ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← prod_range_succ_eq_factorial]

lemma wolstenholme_choose_of_mul (a b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ((a * p).choose (b * p) : ℤ) ≡ (a.choose b : ℤ) [ZMOD (p ^ 3 : ℤ)] :=
  wolstenholme_choose_r1 a b hp hp5

/-- The case `m = 1`, `r = 1` of the main conjecture. -/
lemma general_supercongruence_m_one_r_one (n p : ℕ) (hp : Nat.Prime p)
    (hp5 : p ≥ 5) (hn : n ≥ 1) :
    b_m_int 1 (n * p) ≡ b_m_int 1 n [ZMOD (p ^ 3 : ℤ)] := by
  have hN : 1 ≤ n * p := Nat.mul_pos hn hp.pos
  have hcent : ((2 * (n * p)).choose (n * p) : ℤ) ≡ ((2 * n).choose n : ℤ) [ZMOD (p ^ 3 : ℤ)] := by
    have := wolstenholme_choose_r1 (2 * n) n hp hp5
    convert this using 2 <;> ring
  have h2 : IsCoprime (2 : ℤ) (p ^ 3 : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    have hcop : Nat.Coprime 2 p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (by
        intro h2p
        have : p ≤ 2 := Nat.le_of_dvd (by decide : (0 : ℕ) < 2) h2p
        omega)).symm
    have hcop3 : Nat.Coprime 2 (p ^ 3) := hcop.pow_right 3
    simpa using hcop3
  simpa using b_m_int_one_congr_of_central (n * p) n hN hn hcent h2



/-! ## Pairing on `Icc 1 (p-1)` and Wolstenholme `H₁` modulo `p²` -/

lemma p_sub_of_mem_Icc (hp : 0 < p) {k : ℕ} (hk : k ∈ Icc 1 (p - 1)) :
    p - k ∈ Icc 1 (p - 1) := by
  have h := mem_Icc.mp hk
  have hklt : k < p := mem_Icc_pred_lt hp hk
  refine mem_Icc.mpr ⟨?_, ?_⟩
  · exact Nat.sub_pos_of_lt hklt
  · have : 1 ≤ k := h.1
    exact Nat.sub_le_sub_left this _

lemma p_sub_p_sub (hp : 0 < p) {k : ℕ} (hk : k ∈ Icc 1 (p - 1)) :
    p - (p - k) = k := by
  have hklt : k < p := mem_Icc_pred_lt hp hk
  exact Nat.sub_sub_self (Nat.le_of_lt hklt)

lemma injOn_p_sub (hp : 0 < p) :
    Set.InjOn (fun k : ℕ => p - k) (Icc 1 (p - 1)) := by
  intro a ha b hb h
  have ha' := mem_Icc_pred_lt hp ha
  have hb' := mem_Icc_pred_lt hp hb
  have h' : p - a = p - b := by simpa using h
  have : p - (p - a) = p - (p - b) := by rw [h']
  rw [Nat.sub_sub_self (Nat.le_of_lt ha'), Nat.sub_sub_self (Nat.le_of_lt hb')] at this
  exact this

lemma image_p_sub (hp : 0 < p) :
    (Icc 1 (p - 1)).image (fun k => p - k) = Icc 1 (p - 1) := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    exact p_sub_of_mem_Icc hp hk
  · intro hx
    refine mem_image.mpr ⟨p - x, p_sub_of_mem_Icc hp hx, p_sub_p_sub hp hx⟩

lemma sum_comp_p_sub (hp : 0 < p) {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    ∑ k ∈ Icc 1 (p - 1), f (p - k) = ∑ k ∈ Icc 1 (p - 1), f k := by
  refine sum_nbij (fun k => p - k) ?_ ?_ ?_ ?_
  · intro k hk; exact p_sub_of_mem_Icc hp hk
  · exact injOn_p_sub hp
  · intro k hk; exact ⟨p - k, p_sub_of_mem_Icc hp hk, p_sub_p_sub hp hk⟩
  · intro k hk; rfl

lemma two_mul_sum_inv (hp : 0 < p) {R : Type*} [CommRing R] (f : ℕ → R) :
    2 * ∑ k ∈ Icc 1 (p - 1), f k =
      ∑ k ∈ Icc 1 (p - 1), (f k + f (p - k)) := by
  rw [two_mul, sum_add_distrib, sum_comp_p_sub hp f]

lemma pair_inv_mod_p2 (hp : p.Prime) {k : ℕ} (hk : k ∈ Icc 1 (p - 1)) :
    (k : ZMod (p ^ 2))⁻¹ + (((p - k : ℕ) : ZMod (p ^ 2)))⁻¹ =
      - (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 2 := by
  have hklt : k < p := mem_Icc_pred_lt hp.pos hk
  have uk : IsUnit (k : ZMod (p ^ 2)) := isUnit_natCast_pow (t := 2) hp hk
  have hpkmem : p - k ∈ Icc 1 (p - 1) := p_sub_of_mem_Icc hp.pos hk
  have upk : IsUnit (((p - k : ℕ) : ZMod (p ^ 2))) :=
    isUnit_natCast_pow (t := 2) hp hpkmem
  set K := (k : ZMod (p ^ 2))
  set PK := ((p - k : ℕ) : ZMod (p ^ 2))
  have hPK : PK = (p : ZMod (p ^ 2)) - K := Nat.cast_sub hklt.le
  have hp2z : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  have hKinv : K * K⁻¹ = 1 := ZMod.mul_inv_of_unit _ uk
  have hPKinv : PK * PK⁻¹ = 1 := ZMod.mul_inv_of_unit _ upk
  have hcleared :
      (K⁻¹ + PK⁻¹) * (K ^ 2 * PK) =
        (- (p : ZMod (p ^ 2)) * K⁻¹ ^ 2) * (K ^ 2 * PK) := by
    have hL : (K⁻¹ + PK⁻¹) * (K ^ 2 * PK) = K * PK + K ^ 2 := by
      calc (K⁻¹ + PK⁻¹) * (K ^ 2 * PK)
          = K⁻¹ * K ^ 2 * PK + PK⁻¹ * K ^ 2 * PK := by ring
        _ = K * (K * K⁻¹) * PK + K ^ 2 * (PK * PK⁻¹) := by ring
        _ = K * 1 * PK + K ^ 2 * 1 := by rw [hKinv, hPKinv]
        _ = K * PK + K ^ 2 := by ring
    have hR : (- (p : ZMod (p ^ 2)) * K⁻¹ ^ 2) * (K ^ 2 * PK) =
        - (p : ZMod (p ^ 2)) * PK := by
      calc _ = - (p : ZMod (p ^ 2)) * (K⁻¹ * K) ^ 2 * PK := by ring
        _ = - (p : ZMod (p ^ 2)) * (K * K⁻¹) ^ 2 * PK := by ring
        _ = - (p : ZMod (p ^ 2)) * (1 : ZMod (p ^ 2)) ^ 2 * PK := by rw [hKinv]
        _ = - (p : ZMod (p ^ 2)) * PK := by ring
    rw [hL, hR, hPK]
    ring_nf
    simp [hp2z]
  have hunit : IsUnit (K ^ 2 * PK) := (uk.pow 2).mul upk
  exact IsUnit.mul_right_cancel hunit hcleared

lemma two_unit_zmod_p2 (hp : p.Prime) (hp5 : 5 ≤ p) :
    IsUnit (2 : ZMod (p ^ 2)) := by
  have h : IsUnit ((2 : ℕ) : ZMod (p ^ 2)) := by
    rw [ZMod.isUnit_iff_coprime]
    refine Nat.Coprime.pow_right 2 ?_
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 (by
      intro hd
      have : p ≤ 2 := Nat.le_of_dvd (by decide : (0 : ℕ) < 2) hd
      omega)).symm
  exact h

lemma p_dvd_p_sq : p ∣ p ^ 2 :=
  dvd_pow_self p (by decide : 2 ≠ 0)

lemma castHom_inv_sq (hp : p.Prime) {k : ℕ} (hk : k ∈ Icc 1 (p - 1)) :
    (ZMod.castHom p_dvd_p_sq (ZMod p)) (((k : ZMod (p ^ 2))⁻¹) ^ 2) =
      ((k : ZMod p)⁻¹) ^ 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have uk : IsUnit (k : ZMod (p ^ 2)) := isUnit_natCast_pow (t := 2) hp hk
  have hmapk :
      (ZMod.castHom p_dvd_p_sq (ZMod p)) (k : ZMod (p ^ 2)) = (k : ZMod p) := by
    simp [ZMod.castHom_apply]
  have hcu :
      (ZMod.castHom p_dvd_p_sq (ZMod p)) (k : ZMod (p ^ 2))⁻¹ = (k : ZMod p)⁻¹ := by
    have hmul :
        (k : ZMod p) *
          (ZMod.castHom p_dvd_p_sq (ZMod p)) (k : ZMod (p ^ 2))⁻¹ = 1 := by
      rw [← hmapk, ← map_mul, ZMod.mul_inv_of_unit _ uk, map_one]
    exact (inv_eq_of_mul_eq_one_right hmul).symm
  rw [map_pow, hcu]

lemma wolstenholme_H1_mod_p2 (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ k ∈ Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hsum := two_mul_sum_inv (R := ZMod (p ^ 2)) hp.pos
    (fun k => (k : ZMod (p ^ 2))⁻¹)
  have hpair :
      ∑ k ∈ Icc 1 (p - 1),
        ((k : ZMod (p ^ 2))⁻¹ + (((p - k : ℕ) : ZMod (p ^ 2)))⁻¹) =
      ∑ k ∈ Icc 1 (p - 1),
        (- (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 2) :=
    sum_congr rfl fun k hk => pair_inv_mod_p2 hp hk
  rw [hpair, ← mul_sum] at hsum
  -- The inverse-square sum reduces to H₂ ≡ 0 (mod p), hence is a multiple of p.
  have hcast :
      (ZMod.castHom p_dvd_p_sq (ZMod p))
        (∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2) = 0 := by
    rw [map_sum]
    have : ∑ k ∈ Icc 1 (p - 1),
        (ZMod.castHom p_dvd_p_sq (ZMod p)) (((k : ZMod (p ^ 2))⁻¹) ^ 2) =
        ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2 :=
      sum_congr rfl fun k hk => castHom_inv_sq hp hk
    rw [this]
    exact wolstenholme_H2_mod_p hp5
  have hsval :
      p ∣ (∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2).val := by
    set s := ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2
    have hx : (ZMod.castHom p_dvd_p_sq (ZMod p)) (s.val : ZMod (p ^ 2)) = (s.val : ZMod p) :=
      map_natCast _ s.val
    have hs' : (s.val : ZMod (p ^ 2)) = s := ZMod.natCast_zmod_val s
    rw [hs'] at hx
    rw [hx] at hcast
    exact (ZMod.natCast_eq_zero_iff s.val p).mp hcast
  obtain ⟨t, ht⟩ := hsval
  have hsmul :
      (∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2) =
        (p : ZMod (p ^ 2)) * (t : ZMod (p ^ 2)) := by
    have := congrArg (fun n : ℕ => (n : ZMod (p ^ 2))) ht
    simpa [ZMod.natCast_zmod_val, Nat.cast_mul] using this
  have hp2z : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  have hp_sum0 : (p : ZMod (p ^ 2)) * ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2 = 0 := by
    rw [hsmul, ← mul_assoc, ← pow_two, hp2z, zero_mul]
  have hsum0 : 2 * ∑ k ∈ Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ = 0 := by
    rw [hsum, neg_mul, hp_sum0, neg_zero]
  rw [mul_comm] at hsum0
  exact (IsUnit.mul_left_eq_zero (two_unit_zmod_p2 hp hp5)).mp hsum0

/-! ## Product formula for the binomial ratio -/

lemma prod_Icc_one_eq_factorial (n : ℕ) :
    ∏ i ∈ Icc 1 n, i = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
      ext x
      simp only [mem_Icc, mem_insert]
      omega
    have hmem : (n + 1) ∉ Icc 1 n := by
      simp [mem_Icc]
    rw [hsplit, prod_insert hmem, ih, factorial_succ, mul_comm]

/-- `n! * ∏_{j=1}^q (n+j) = (n+q)!`. -/
lemma factorial_mul_prod_Icc (n q : ℕ) :
    n.factorial * ∏ j ∈ Icc 1 q, (n + j) = (n + q).factorial := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : Icc 1 (q + 1) = insert (q + 1) (Icc 1 q) := by
      ext x; simp [mem_Icc]; omega
    have hmem : (q + 1) ∉ Icc 1 q := by simp [mem_Icc]
    rw [hsplit, prod_insert hmem]
    have : n.factorial * ((n + (q + 1)) * ∏ x ∈ Icc 1 q, (n + x)) =
        (n.factorial * ∏ x ∈ Icc 1 q, (n + x)) * (n + q + 1) := by
      ring
    rw [this, ih]
    have : (n + q).factorial * (n + q + 1) = (n + (q + 1)).factorial := by
      rw [show n + (q + 1) = n + q + 1 by ring, factorial_succ, mul_comm]
    exact this

/-- `(qA)! = q^A · A! · ∏_{i=1}^{q-1} ∏_{t=0}^{A-1} (t q + i)`. -/
lemma factorial_mul_eq_prod_blocks (q A : ℕ) (hq : 0 < q) :
    (q * A).factorial =
      q ^ A * A.factorial *
        ∏ i ∈ Icc 1 (q - 1), ∏ t ∈ range A, (t * q + i) := by
  induction A with
  | zero => simp
  | succ A ih =>
    have hAq : q * (A + 1) = q * A + q := by ring
    rw [hAq]
    have hstep : (q * A + q).factorial =
        (q * A).factorial * ∏ j ∈ Icc 1 q, (q * A + j) :=
      (factorial_mul_prod_Icc (q * A) q).symm
    have hsplit : Icc 1 q = insert q (Icc 1 (q - 1)) := by
      ext x; simp [mem_Icc]; omega
    have hmem : q ∉ Icc 1 (q - 1) := by simp [mem_Icc]; omega
    have hinner : ∏ j ∈ Icc 1 q, (q * A + j) =
        (q * A + q) * ∏ j ∈ Icc 1 (q - 1), (q * A + j) := by
      rw [hsplit, prod_insert hmem, mul_comm]
    rw [hstep, hinner, ih]
    have hrange :
        ∏ i ∈ Icc 1 (q - 1), ∏ t ∈ range (A + 1), (t * q + i) =
          (∏ i ∈ Icc 1 (q - 1), ∏ t ∈ range A, (t * q + i)) *
            ∏ i ∈ Icc 1 (q - 1), (q * A + i) := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      rw [prod_range_succ]
      ring
    rw [pow_succ, factorial_succ, hrange]
    ring

lemma range_add_split {A B : ℕ} (hBA : B ≤ A) :
    range A = range B ∪ (range (A - B)).map ⟨fun t => B + t, add_right_injective B⟩ := by
  ext t
  simp only [mem_union, mem_range, mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro ht
    by_cases htb : t < B
    · exact Or.inl htb
    · refine Or.inr ⟨t - B, ?_, ?_⟩
      · omega
      · omega
  · rintro (h | ⟨u, hu, rfl⟩) <;> omega

lemma range_add_disjoint {A B : ℕ} :
    Disjoint (range B)
      ((range (A - B)).map ⟨fun t => B + t, add_right_injective B⟩) := by
  refine disjoint_left.mpr ?_
  intro x hxB hxA
  simp only [mem_range, mem_map, Function.Embedding.coeFn_mk] at hxB hxA
  obtain ⟨u, hu, rfl⟩ := hxA
  omega

lemma prod_range_add_split {α : Type*} [CommMonoid α] (f : ℕ → α) {A B : ℕ}
    (hBA : B ≤ A) :
    ∏ t ∈ range A, f t =
      (∏ t ∈ range B, f t) * ∏ t ∈ range (A - B), f (B + t) := by
  rw [range_add_split hBA, prod_union range_add_disjoint, prod_map]
  simp

/-- The binomial ratio equals the double product over residue classes. -/
lemma choose_ratio_eq_prod (q A B : ℕ) (hq : 0 < q) (hBA : B ≤ A) :
    ((q * A).choose (q * B) : ℚ) / (A.choose B : ℚ) =
      ∏ i ∈ Icc 1 (q - 1),
        ∏ t ∈ range (A - B),
          (((B + t) * q + i : ℕ) : ℚ) / ((t * q + i : ℕ) : ℚ) := by
  have hA := factorial_mul_eq_prod_blocks q A hq
  have hB := factorial_mul_eq_prod_blocks q B hq
  have hC := factorial_mul_eq_prod_blocks q (A - B) hq
  have hle : q * B ≤ q * A := Nat.mul_le_mul_left q hBA
  have hchA : ((q * A).choose (q * B) : ℚ) =
      ((q * A).factorial : ℚ) /
        (((q * B).factorial : ℚ) * ((q * (A - B)).factorial : ℚ)) := by
    have : q * A - q * B = q * (A - B) := (Nat.mul_sub q A B).symm
    rw [Nat.cast_choose ℚ (show q * B ≤ q * A from hle)]
    simp [this]
  have hchB : (A.choose B : ℚ) =
      (A.factorial : ℚ) / ((B.factorial : ℚ) * ((A - B).factorial : ℚ)) :=
    Nat.cast_choose ℚ hBA
  have hAne : (A.choose B : ℚ) ≠ 0 := by
    have : 0 < A.choose B := Nat.choose_pos hBA
    exact Nat.cast_ne_zero.mpr this.ne'
  have hqA : ((q * A).factorial : ℚ) =
      (q : ℚ) ^ A * (A.factorial : ℚ) *
        ∏ i ∈ Icc 1 (q - 1), ∏ t ∈ range A, ((t * q + i : ℕ) : ℚ) := by
    apply_fun (fun n : ℕ => (n : ℚ)) at hA
    simpa [Nat.cast_mul, Nat.cast_pow, Nat.cast_prod] using hA
  have hqB : ((q * B).factorial : ℚ) =
      (q : ℚ) ^ B * (B.factorial : ℚ) *
        ∏ i ∈ Icc 1 (q - 1), ∏ t ∈ range B, ((t * q + i : ℕ) : ℚ) := by
    apply_fun (fun n : ℕ => (n : ℚ)) at hB
    simpa [Nat.cast_mul, Nat.cast_pow, Nat.cast_prod] using hB
  have hqC : ((q * (A - B)).factorial : ℚ) =
      (q : ℚ) ^ (A - B) * ((A - B).factorial : ℚ) *
        ∏ i ∈ Icc 1 (q - 1), ∏ t ∈ range (A - B), ((t * q + i : ℕ) : ℚ) := by
    apply_fun (fun n : ℕ => (n : ℚ)) at hC
    simpa [Nat.cast_mul, Nat.cast_pow, Nat.cast_prod] using hC
  have hsplitA :
      ∏ i ∈ Icc 1 (q - 1), ∏ t ∈ range A, ((t * q + i : ℕ) : ℚ) =
        (∏ i ∈ Icc 1 (q - 1), ∏ t ∈ range B, ((t * q + i : ℕ) : ℚ)) *
          ∏ i ∈ Icc 1 (q - 1), ∏ t ∈ range (A - B),
            (((B + t) * q + i : ℕ) : ℚ) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    simpa using prod_range_add_split (fun t => ((t * q + i : ℕ) : ℚ)) hBA
  have hprod_div :
      ∏ i ∈ Icc 1 (q - 1), ∏ t ∈ range (A - B),
          (((B + t) * q + i : ℕ) : ℚ) / ((t * q + i : ℕ) : ℚ) =
        (∏ i ∈ Icc 1 (q - 1), ∏ t ∈ range (A - B),
            (((B + t) * q + i : ℕ) : ℚ)) /
        (∏ i ∈ Icc 1 (q - 1), ∏ t ∈ range (A - B),
            ((t * q + i : ℕ) : ℚ)) := by
    simp [Finset.prod_div_distrib]
  set PB := ∏ i ∈ Icc 1 (q - 1), ∏ t ∈ range B, ((t * q + i : ℕ) : ℚ)
  set PC := ∏ i ∈ Icc 1 (q - 1), ∏ t ∈ range (A - B), ((t * q + i : ℕ) : ℚ)
  set Pshift := ∏ i ∈ Icc 1 (q - 1), ∏ t ∈ range (A - B),
      (((B + t) * q + i : ℕ) : ℚ)
  have hsplitA' : ∏ i ∈ Icc 1 (q - 1), ∏ t ∈ range A, ((t * q + i : ℕ) : ℚ) =
      PB * Pshift := hsplitA
  have hprod_div' :
      ∏ i ∈ Icc 1 (q - 1), ∏ t ∈ range (A - B),
          (((B + t) * q + i : ℕ) : ℚ) / ((t * q + i : ℕ) : ℚ) =
        Pshift / PC := hprod_div
  have hterm_ne : ∀ t i : ℕ, 1 ≤ i → ((t * q + i : ℕ) : ℚ) ≠ 0 := by
    intro t i hi
    exact Nat.cast_ne_zero.mpr (Nat.add_pos_right _ hi).ne'
  have hPCne : PC ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro t ht
    exact hterm_ne t i (mem_Icc.mp hi).1
  have hPBne : PB ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro t ht
    exact hterm_ne t i (mem_Icc.mp hi).1
  have hAne' : (A.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (factorial_ne_zero _)
  have hBne' : (B.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (factorial_ne_zero _)
  have hCne' : ((A - B).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (factorial_ne_zero _)
  have hqne : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq)
  rw [hchA, hchB, hprod_div', hqA, hqB, hqC, hsplitA']
  have hqpow : (q : ℚ) ^ A = (q : ℚ) ^ B * (q : ℚ) ^ (A - B) := by
    rw [← pow_add, Nat.add_sub_of_le hBA]
  rw [hqpow]
  field_simp [hAne, hAne', hBne', hCne', hPCne, hPBne, hqne, pow_ne_zero]

/-! ## p-adic valuation helpers -/

lemma padicValRat_natCast (n : ℕ) :
    padicValRat p (n : ℚ) = padicValNat p n :=
  padicValRat.of_nat

lemma padicValRat_intCast (z : ℤ) :
    padicValRat p (z : ℚ) = padicValInt p z :=
  padicValRat.of_int

lemma padicValRat_sum_ge {ι : Type*} [Fact p.Prime] (s : Finset ι) (f : ι → ℚ) (K : ℤ)
    (hf0 : ∀ i ∈ s, f i ≠ 0 → K ≤ padicValRat p (f i))
    (hsum0 : (∑ i ∈ s, f i) ≠ 0) :
    K ≤ padicValRat p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp at hsum0
  | insert a s has ih =>
    rw [sum_insert has] at hsum0 ⊢
    by_cases hf : f a = 0
    · simp only [hf, zero_add] at hsum0 ⊢
      exact ih (fun i hi => hf0 i (mem_insert_of_mem hi)) hsum0
    · by_cases hs0 : (∑ i ∈ s, f i) = 0
      · simp only [hs0, add_zero] at hsum0 ⊢
        exact hf0 a (mem_insert_self _ _) hf
      · have hfa := hf0 a (mem_insert_self _ _) hf
        have hfs := ih (fun i hi => hf0 i (mem_insert_of_mem hi)) hs0
        exact le_trans (le_min hfa hfs) (padicValRat.min_le_padicValRat_add hsum0)

lemma padicValInt_one_le_of_dvd {z : ℤ} [Fact p.Prime] (hz : z ≠ 0)
    (hdiv : (p : ℤ) ∣ z) : 1 ≤ padicValInt p z := by
  have := (padicValInt_dvd_iff (p := p) 1 z).mp (by simpa using hdiv)
  exact this.resolve_left hz

lemma padicValRat_int_one_le {z : ℤ} [Fact p.Prime] (hz : z ≠ 0)
    (hdiv : (p : ℤ) ∣ z) : (1 : ℤ) ≤ padicValRat p (z : ℚ) := by
  have := padicValInt_one_le_of_dvd hz hdiv
  simpa [padicValRat.of_int] using this

lemma padicValNat_le_of_dvd {n s : ℕ} [Fact p.Prime] (hn : n ≠ 0)
    (hdiv : p ^ s ∣ n) : s ≤ padicValNat p n := by
  have := (padicValNat_dvd_iff (p := p) s n).mp hdiv
  exact this.resolve_left hn

lemma padicValRat_pow_p (t : ℕ) [Fact p.Prime] :
    padicValRat p ((p : ℚ) ^ t) = t := by
  rw [padicValRat.pow (Nat.cast_ne_zero.mpr (NeZero.ne p)), padicValRat_natCast,
    padicValNat.self (Nat.Prime.one_lt (Fact.out (p := p.Prime)))]
  simp

lemma padicValRat_of_dvd_pow {z : ℤ} {s : ℕ} [Fact p.Prime] (hz : z ≠ 0)
    (hdiv : (p : ℤ) ^ s ∣ z) : (s : ℤ) ≤ padicValRat p (z : ℚ) := by
  have h := (padicValInt_dvd_iff (p := p) s z).mp hdiv
  have := h.resolve_left hz
  simpa [padicValRat.of_int] using this

/-! ## Pairing product and the binomial ratio squared -/

/-- `α t = t(t+1)`. -/
def alphaN (t : ℕ) : ℤ := (t : ℤ) * (t + 1)

/-- `β_q(i) = i(q-i)`. -/
def pbeta (q i : ℕ) : ℤ := (i : ℤ) * ((q - i : ℕ) : ℤ)

lemma pair_prod_eq (q i t : ℕ) (hi : i ≤ q) :
    ((i + t * q : ℕ) : ℤ) * (((q - i) + t * q : ℕ) : ℤ) =
      pbeta q i + alphaN t * (q : ℤ) ^ 2 := by
  unfold pbeta alphaN
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, Nat.cast_sub hi, Nat.cast_mul]
  ring

lemma prod_comp_p_sub_int (t : ℕ) (hp0 : 0 < p) :
    ∏ i ∈ Icc 1 (p - 1), (((p - i) + t * p : ℕ) : ℤ) =
      ∏ i ∈ Icc 1 (p - 1), ((i + t * p : ℕ) : ℤ) := by
  refine prod_nbij (fun i => p - i) (fun i hi => p_sub_of_mem_Icc hp0 hi)
    (injOn_p_sub hp0) ?_ ?_
  · intro i hi
    exact ⟨p - i, p_sub_of_mem_Icc hp0 hi, p_sub_p_sub hp0 hi⟩
  · intro i hi; rfl

lemma prod_pair_sq (t : ℕ) (hp0 : 0 < p) :
    (∏ i ∈ Icc 1 (p - 1), ((i + t * p : ℕ) : ℤ)) ^ 2 =
      ∏ i ∈ Icc 1 (p - 1), (pbeta p i + alphaN t * (p : ℤ) ^ 2) := by
  have hmul :
      (∏ i ∈ Icc 1 (p - 1), ((i + t * p : ℕ) : ℤ)) *
        (∏ i ∈ Icc 1 (p - 1), (((p - i) + t * p : ℕ) : ℤ)) =
      ∏ i ∈ Icc 1 (p - 1), (pbeta p i + alphaN t * (p : ℤ) ^ 2) := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun i hi =>
      pair_prod_eq p i t (mem_Icc_pred_lt hp0 hi).le
  calc (∏ i ∈ Icc 1 (p - 1), ((i + t * p : ℕ) : ℤ)) ^ 2
      = (∏ i ∈ Icc 1 (p - 1), ((i + t * p : ℕ) : ℤ)) *
          (∏ i ∈ Icc 1 (p - 1), ((i + t * p : ℕ) : ℤ)) := by rw [pow_two]
    _ = (∏ i ∈ Icc 1 (p - 1), ((i + t * p : ℕ) : ℤ)) *
          (∏ i ∈ Icc 1 (p - 1), (((p - i) + t * p : ℕ) : ℤ)) := by
        rw [prod_comp_p_sub_int t hp0]
    _ = ∏ i ∈ Icc 1 (p - 1), (pbeta p i + alphaN t * (p : ℤ) ^ 2) := hmul

lemma alphaN_shift (B t : ℕ) :
    alphaN (B + t) - alphaN t = (B : ℤ) * (2 * (t : ℤ) + B + 1) := by
  simp [alphaN]
  ring

lemma pair_ratio_num_sub (q B t i : ℕ) :
    (pbeta q i + alphaN (B + t) * (q : ℤ) ^ 2) - (pbeta q i + alphaN t * (q : ℤ) ^ 2) =
      (B : ℤ) * (2 * (t : ℤ) + B + 1) * (q : ℤ) ^ 2 := by
  rw [add_sub_add_left_eq_sub, ← sub_mul, alphaN_shift]

/-! ## Closed forms for the weighted power sums `U_j` -/

/-- `U_j(B,C) = ∑_{t < C} (2t+B+1) (t(t+1))^j`. -/
def Usum (j B C : ℕ) : ℤ :=
  ∑ t ∈ range C, (2 * (t : ℤ) + B + 1) * (alphaN t) ^ j

lemma two_dvd_mul_pred (C : ℕ) : 2 ∣ C * (C - 1) := by
  rcases Nat.even_or_odd C with hE | hO
  · exact dvd_mul_of_dvd_left (even_iff_two_dvd.mp hE) _
  · have : Even (C - 1) := Nat.Odd.sub_odd hO odd_one
    exact dvd_mul_of_dvd_right (even_iff_two_dvd.mp this) _

lemma two_mul_sum_range_id (C : ℕ) :
    2 * ∑ t ∈ range C, t = C * (C - 1) := by
  rw [sum_range_id, Nat.mul_div_cancel' (two_dvd_mul_pred C)]

lemma two_mul_sum_range_id_int (C : ℕ) :
    (2 : ℤ) * ∑ t ∈ range C, (t : ℤ) = (C : ℤ) * ((C : ℤ) - 1) := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) (two_mul_sum_range_id C)
  cases C with
  | zero => simp
  | succ C =>
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_succ,
      Nat.succ_sub_one] at h
    simpa [Nat.cast_sum, Nat.cast_succ] using h

lemma Usum_zero (B C : ℕ) :
    Usum 0 B C = (C : ℤ) * ((B : ℤ) + C) := by
  simp only [Usum, pow_zero, mul_one]
  have hsplit :
      ∑ t ∈ range C, (2 * (t : ℤ) + ((B : ℤ) + 1)) =
        (2 : ℤ) * ∑ t ∈ range C, (t : ℤ) +
          ((C : ℤ) * ((B : ℤ) + 1)) := by
    rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  -- rewrite 2t+B+1 as 2t+(B+1)
  have hterm : ∀ t, (2 * (t : ℤ) + B + 1) = 2 * (t : ℤ) + ((B : ℤ) + 1) := by
    intro t; ring
  simp_rw [hterm]
  rw [hsplit, two_mul_sum_range_id_int]
  ring

lemma six_mul_Usum_one (B C : ℕ) :
    (6 : ℤ) * Usum 1 B C = (C : ℤ) * (2 * (B : ℤ) + 3 * C) * ((C : ℤ) ^ 2 - 1) := by
  induction C with
  | zero => simp [Usum]
  | succ C ih =>
    unfold Usum at ih ⊢
    rw [sum_range_succ, mul_add, pow_one, ih]
    simp only [alphaN, pow_one, Nat.cast_add, Nat.cast_one]
    ring

lemma Usum_one (B C : ℕ) :
    Usum 1 B C = (C : ℤ) * (2 * (B : ℤ) + 3 * C) * ((C : ℤ) ^ 2 - 1) / 6 := by
  have h := six_mul_Usum_one B C
  have hdiv : (6 : ℤ) ∣ (C : ℤ) * (2 * (B : ℤ) + 3 * C) * ((C : ℤ) ^ 2 - 1) := by
    rw [← h]; exact dvd_mul_right _ _
  have h' : (C : ℤ) * (2 * (B : ℤ) + 3 * C) * ((C : ℤ) ^ 2 - 1) = Usum 1 B C * 6 := by
    rw [mul_comm (Usum 1 B C), h]
  exact ((Int.ediv_eq_iff_eq_mul_left (by decide : (6 : ℤ) ≠ 0) hdiv).2 h').symm

lemma harmInv_def_eq (q : ℕ) :
    (∑ k ∈ Icc 1 (q - 1), (1 : ℚ) / k) =
      ∑ k ∈ Icc 1 (q - 1), (k : ℚ)⁻¹ := by
  simp

/-- `∑_{i=1}^{p-1} 1/(i(p-i)) = 2 H_{p-1} / p`. -/
lemma sum_inv_pbeta (hp0 : 0 < p) :
    ∑ i ∈ Icc 1 (p - 1), (1 : ℚ) / (pbeta p i) =
      (2 : ℚ) / p * ∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / k := by
  have hterm : ∀ i ∈ Icc 1 (p - 1),
      (1 : ℚ) / (pbeta p i) =
        (1 / (p : ℚ)) * (1 / (i : ℚ) + 1 / ((p - i : ℕ) : ℚ)) := by
    intro i hi
    have hilt : i < p := mem_Icc_pred_lt hp0 hi
    have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (mem_Icc.mp hi).1)
    have hpi0 : ((p - i : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt hilt))
    have hp0' : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp0.ne'
    have hcast : ((p - i : ℕ) : ℚ) = (p : ℚ) - i := Nat.cast_sub hilt.le
    unfold pbeta
    have hpb : (pbeta p i : ℚ) = (i : ℚ) * ((p - i : ℕ) : ℚ) := by
      simp [pbeta]
    -- rewrite using the explicit product
    have : (1 : ℚ) / ((i : ℚ) * ((p - i : ℕ) : ℚ)) =
        (1 / (p : ℚ)) * (1 / (i : ℚ) + 1 / ((p - i : ℕ) : ℚ)) := by
      have hsum : (i : ℚ) + ((p - i : ℕ) : ℚ) = p := by
        rw [hcast]; ring
      field_simp [hp0', hi0, hpi0]
      linarith [hsum]
    simpa [pbeta] using this
  have hsum := sum_congr rfl hterm
  rw [hsum, ← mul_sum, sum_add_distrib]
  have hre : ∑ i ∈ Icc 1 (p - 1), (1 : ℚ) / ((p - i : ℕ) : ℚ) =
      ∑ i ∈ Icc 1 (p - 1), (1 : ℚ) / i :=
    sum_comp_p_sub hp0 (fun i => (1 : ℚ) / i)
  rw [hre]
  ring

/-- Faulhaber's polynomial: its value at `n` is `∑_{t<n} t^k`. -/
noncomputable def faulhaberPoly (k : ℕ) : Polynomial ℚ :=
  ∑ i ∈ range (k + 1),
    Polynomial.C (bernoulli i * ((k + 1).choose i : ℚ) / (k + 1)) *
      Polynomial.X ^ (k + 1 - i)

lemma faulhaberPoly_eval (n k : ℕ) :
    (faulhaberPoly k).eval (n : ℚ) = ∑ t ∈ range n, (t : ℚ) ^ k := by
  rw [faulhaberPoly, Polynomial.eval_finset_sum, eq_comm, sum_range_pow n k]
  refine sum_congr rfl fun i hi => ?_
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

lemma poly_eq_of_eval_nat {f g : Polynomial ℚ}
    (h : ∀ n : ℕ, f.eval (n : ℚ) = g.eval (n : ℚ)) : f = g := by
  refine Polynomial.eq_of_infinite_eval_eq f g ?_
  have hInf : (Set.range fun n : ℕ => (n : ℚ)).Infinite :=
    Set.infinite_range_of_injective Nat.cast_injective
  refine hInf.mono ?_
  intro x hx
  rcases hx with ⟨n, rfl⟩
  exact h n

/-- Discrete antiderivative of a polynomial, as a polynomial. -/
noncomputable def sumPoly (g : Polynomial ℚ) : Polynomial ℚ :=
  ∑ k ∈ range (g.natDegree + 1), Polynomial.C (g.coeff k) * faulhaberPoly k

lemma sumPoly_eval (g : Polynomial ℚ) (n : ℕ) :
    (sumPoly g).eval (n : ℚ) = ∑ t ∈ range n, g.eval (t : ℚ) := by
  have ht : ∀ t : ℕ, g.eval (t : ℚ) =
      ∑ k ∈ range (g.natDegree + 1), g.coeff k * (t : ℚ) ^ k := by
    intro t
    exact Polynomial.eval_eq_sum_range (t : ℚ)
  rw [sumPoly, Polynomial.eval_finset_sum, sum_congr rfl (fun t _ => ht t),
    Finset.sum_comm]
  refine sum_congr rfl fun k hk => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, faulhaberPoly_eval, mul_sum]

lemma sumPoly_eval_zero (g : Polynomial ℚ) : (sumPoly g).eval 0 = 0 := by
  simpa using sumPoly_eval g 0

lemma sumPoly_succ (g : Polynomial ℚ) (n : ℕ) :
    (sumPoly g).eval ((n + 1 : ℕ) : ℚ) - (sumPoly g).eval (n : ℚ) = g.eval (n : ℚ) := by
  rw [sumPoly_eval, sumPoly_eval, sum_range_succ]
  abel

lemma sumPoly_diff (g : Polynomial ℚ) :
    (sumPoly g).comp (Polynomial.X + 1) - sumPoly g = g := by
  refine poly_eq_of_eval_nat fun n => ?_
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  simpa using sumPoly_succ g n

/-- The weight `g_j(t) = (2t+1) (t(t+1))^j` as a polynomial. -/
noncomputable def gOddPoly (j : ℕ) : Polynomial ℚ :=
  (Polynomial.C 2 * Polynomial.X + 1) * (Polynomial.X * (Polynomial.X + 1)) ^ j

lemma gOddPoly_eval (j t : ℕ) :
    (gOddPoly j).eval (t : ℚ) = (2 * (t : ℚ) + 1) * ((t : ℚ) * (t + 1)) ^ j := by
  simp [gOddPoly]

/-- Reflection of the argument through `-1`: `g_j(-1-t) = -g_j(t)`. -/
lemma gOddPoly_reflect (j : ℕ) :
    (gOddPoly j).comp (-(Polynomial.X + 1)) = - gOddPoly j := by
  refine Polynomial.funext fun x => ?_
  simp [gOddPoly]
  ring

/-- `Q_j(C) = ∑_{t<C} (2t+1)(t(t+1))^j` as a polynomial. -/
noncomputable def QsumPoly (j : ℕ) : Polynomial ℚ :=
  sumPoly (gOddPoly j)

lemma poly_antideriv_unique (F G g : Polynomial ℚ)
    (hF : F.comp (Polynomial.X + 1) - F = g)
    (hG : G.comp (Polynomial.X + 1) - G = g)
    (hF0 : F.eval 0 = 0) (hG0 : G.eval 0 = 0) : F = G := by
  have hper : (F - G).comp (Polynomial.X + 1) = F - G := by
    apply sub_eq_zero.mp
    calc (F - G).comp (Polynomial.X + 1) - (F - G)
        = (F.comp (Polynomial.X + 1) - G.comp (Polynomial.X + 1)) - (F - G) := by
            simp [Polynomial.sub_comp]
      _ = (F.comp (Polynomial.X + 1) - F) - (G.comp (Polynomial.X + 1) - G) := by ring
      _ = g - g := by rw [hF, hG]
      _ = 0 := sub_self _
  refine poly_eq_of_eval_nat fun n => ?_
  have hconst : ∀ n : ℕ, (F - G).eval (n : ℚ) = (F - G).eval 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := congrArg (fun p => p.eval (n : ℚ)) hper
      simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_one] at this
      simpa [this] using ih
  have : (F - G).eval (n : ℚ) = 0 := by
    simpa [hF0, hG0] using hconst n
  simpa [sub_eq_zero] using this

lemma QsumPoly_even (j : ℕ) :
    (QsumPoly j).comp (-Polynomial.X) = QsumPoly j := by
  set Q := QsumPoly j
  set S := Q.comp (-Polynomial.X)
  have hQdiff : Q.comp (Polynomial.X + 1) - Q = gOddPoly j := sumPoly_diff _
  have hSdiff : S.comp (Polynomial.X + 1) - S = gOddPoly j := by
    -- Identify both sides by evaluating at every rational.
    refine Polynomial.funext fun x => ?_
    have hx :
        Polynomial.eval (x + 1) S - Polynomial.eval x S =
          Polynomial.eval x (gOddPoly j) := by
      have hQat : ∀ y : ℚ,
          Polynomial.eval (y + 1) Q - Polynomial.eval y Q =
            Polynomial.eval y (gOddPoly j) := by
        intro y
        have := congrArg (fun p => Polynomial.eval y p) hQdiff
        simpa [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_one] using this
      -- Q(-x) - Q(-x-1) = g(-x-1) = -g(x), so Q(-x-1) - Q(-x) = g(x)
      have hneg := hQat (-x - 1)
      have hrefl : Polynomial.eval (-x - 1) (gOddPoly j) =
          - Polynomial.eval x (gOddPoly j) := by
        have hx : (-x - 1 : ℚ) = -(x + 1) := by ring
        rw [hx]
        have := congrArg (fun p => Polynomial.eval x p) (gOddPoly_reflect j)
        simpa [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_one] using this
      have hSeval : ∀ y : ℚ, Polynomial.eval y S = Polynomial.eval (-y) Q := by
        intro y
        simp [S, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]
      rw [hSeval (x + 1), hSeval x]
      have : Polynomial.eval (-(x + 1)) Q - Polynomial.eval (-x) Q =
          Polynomial.eval x (gOddPoly j) := by
        have hx' : -(x + 1) = -x - 1 := by ring
        rw [hx']
        have hneg' : Polynomial.eval (-x) Q - Polynomial.eval (-x - 1) Q =
            Polynomial.eval (-x - 1) (gOddPoly j) := by
          convert hneg using 2
          ring
        rw [hrefl] at hneg'
        linarith
      exact this
    simpa [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one] using hx
  have hS0 : S.eval 0 = 0 := by
    simp [S, Q, QsumPoly, sumPoly_eval_zero]
  have hQ0 : Q.eval 0 = 0 := sumPoly_eval_zero _
  exact poly_antideriv_unique S Q (gOddPoly j) hSdiff hQdiff hS0 hQ0

lemma QsumPoly_eval (j n : ℕ) :
    (QsumPoly j).eval (n : ℚ) =
      ∑ t ∈ range n, (gOddPoly j).eval (t : ℚ) :=
  sumPoly_eval _ _

lemma QsumPoly_eval_neg (j : ℕ) (x : ℚ) :
    (QsumPoly j).eval (-x) = (QsumPoly j).eval x := by
  have := congrArg (fun p => p.eval x) (QsumPoly_even j)
  simpa [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X] using this

lemma QsumPoly_isRoot_zero (j : ℕ) : (QsumPoly j).eval 0 = 0 :=
  sumPoly_eval_zero _

lemma QsumPoly_isRoot_one {j : ℕ} (hj : 1 ≤ j) : (QsumPoly j).eval 1 = 0 := by
  have h := QsumPoly_eval j 1
  have hz : (gOddPoly j).eval (0 : ℚ) = 0 := by
    simp [gOddPoly, zero_pow (Nat.pos_iff_ne_zero.mp hj)]
  simpa [sum_range_one, hz] using h

lemma QsumPoly_isRoot_neg_one {j : ℕ} (hj : 1 ≤ j) : (QsumPoly j).eval (-1) = 0 := by
  rw [QsumPoly_eval_neg, QsumPoly_isRoot_one hj]

lemma dvd_X_of_eval_zero (p : Polynomial ℚ) (h : p.eval 0 = 0) :
    Polynomial.X ∣ p := by
  rw [Polynomial.X_dvd_iff]
  simpa [Polynomial.eval] using h

lemma dvd_X_sub_C_of_eval (p : Polynomial ℚ) (a : ℚ) (h : p.eval a = 0) :
    (Polynomial.X - Polynomial.C a) ∣ p :=
  Polynomial.dvd_iff_isRoot.mpr h

lemma X_sub_one_dvd_of_eval_one (p : Polynomial ℚ) (h : p.eval 1 = 0) :
    (Polynomial.X - 1) ∣ p := by
  simpa using dvd_X_sub_C_of_eval p 1 h

lemma X_add_one_dvd_of_eval_neg_one (p : Polynomial ℚ) (h : p.eval (-1) = 0) :
    (Polynomial.X + 1) ∣ p := by
  have := dvd_X_sub_C_of_eval p (-1) h
  simpa [sub_eq_add_neg] using this

lemma isCoprime_X_sub_one_X_add_one :
    IsCoprime (Polynomial.X - 1 : Polynomial ℚ) (Polynomial.X + 1) := by
  simpa using
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (a := (1 : ℚ)) (b := (-1 : ℚ))
      (by norm_num : IsUnit ((1 : ℚ) - (-1))))

lemma neg_X_pow (k : ℕ) :
    (-Polynomial.X : Polynomial ℚ) ^ k = Polynomial.C ((-1 : ℚ) ^ k) * Polynomial.X ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ, pow_succ]
    simp [mul_assoc, mul_left_comm, mul_comm]

lemma coeff_comp_neg_X (q : Polynomial ℚ) (n : ℕ) :
    (q.comp (-Polynomial.X)).coeff n = (-1 : ℚ) ^ n * q.coeff n := by
  induction q using Polynomial.induction_on' with
  | add f g hf hg =>
    simp [hf, hg, mul_add]
  | monomial k a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.pow_comp, Polynomial.X_comp, neg_X_pow]
    rw [← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X_pow]
    split_ifs with h
    · simp [h, mul_comm]
    · simp

/-- Even + vanishing at `0` implies `X² ∣ p`. -/
lemma even_and_eval_zero_dvd_X_sq {p : Polynomial ℚ}
    (heven : p.comp (-Polynomial.X) = p) (h0 : p.eval 0 = 0) :
    Polynomial.X ^ 2 ∣ p := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  interval_cases k
  · simpa [Polynomial.eval] using h0
  · have hcmp : (p.comp (-Polynomial.X)).coeff 1 = p.coeff 1 := by rw [heven]
    have := coeff_comp_neg_X p 1
    have : p.coeff 1 = - p.coeff 1 := by
      simpa [this] using hcmp.symm
    linarith

lemma isCoprime_X_X_sub_one :
    IsCoprime (Polynomial.X : Polynomial ℚ) (Polynomial.X - 1) := by
  simpa using
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (a := (0 : ℚ)) (b := (1 : ℚ)) (by norm_num))

lemma isCoprime_X_X_add_one :
    IsCoprime (Polynomial.X : Polynomial ℚ) (Polynomial.X + 1) := by
  simpa [sub_eq_add_neg] using
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (a := (0 : ℚ)) (b := (-1 : ℚ)) (by norm_num))

/-- `X²(X²-1)` divides `Q_j` for `j ≥ 1`. -/
lemma X_sq_mul_X_sq_sub_one_dvd_Qsum {j : ℕ} (hj : 1 ≤ j) :
    Polynomial.X ^ 2 * (Polynomial.X ^ 2 - 1) ∣ QsumPoly j := by
  have hX2 := even_and_eval_zero_dvd_X_sq (QsumPoly_even j) (QsumPoly_isRoot_zero j)
  have h1 := X_sub_one_dvd_of_eval_one _ (QsumPoly_isRoot_one hj)
  have hm1 := X_add_one_dvd_of_eval_neg_one _ (QsumPoly_isRoot_neg_one hj)
  have h11 : (Polynomial.X - 1) * (Polynomial.X + 1) ∣ QsumPoly j :=
    isCoprime_X_sub_one_X_add_one.mul_dvd h1 hm1
  have hfac : (Polynomial.X ^ 2 - 1 : Polynomial ℚ) =
      (Polynomial.X - 1) * (Polynomial.X + 1) := by ring
  rw [hfac]
  have hcop : IsCoprime (Polynomial.X ^ 2 : Polynomial ℚ)
      ((Polynomial.X - 1) * (Polynomial.X + 1)) := by
    refine IsCoprime.mul_right ?_ ?_
    · exact isCoprime_X_X_sub_one.pow_left
    · exact isCoprime_X_X_add_one.pow_left
  exact hcop.mul_dvd hX2 h11

/-- The unweighted sum `P_j(C) = ∑_{t<C} (t(t+1))^j`. -/
noncomputable def gEvenPoly (j : ℕ) : Polynomial ℚ :=
  (Polynomial.X * (Polynomial.X + 1)) ^ j

noncomputable def PsumPoly (j : ℕ) : Polynomial ℚ :=
  sumPoly (gEvenPoly j)

lemma gEvenPoly_reflect (j : ℕ) :
    (gEvenPoly j).comp (-(Polynomial.X + 1)) = gEvenPoly j := by
  refine Polynomial.funext fun x => ?_
  simp [gEvenPoly]
  ring

lemma PsumPoly_odd (j : ℕ) :
    (PsumPoly j).comp (-Polynomial.X) = - PsumPoly j := by
  set P := PsumPoly j
  set S := - P.comp (-Polynomial.X)
  have hPdiff : P.comp (Polynomial.X + 1) - P = gEvenPoly j := sumPoly_diff _
  have hSdiff : S.comp (Polynomial.X + 1) - S = gEvenPoly j := by
    refine Polynomial.funext fun x => ?_
    have hPat : ∀ y : ℚ,
        Polynomial.eval (y + 1) P - Polynomial.eval y P =
          Polynomial.eval y (gEvenPoly j) := by
      intro y
      have := congrArg (fun p => Polynomial.eval y p) hPdiff
      simpa [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_one] using this
    have hSeval : ∀ y : ℚ, Polynomial.eval y S = - Polynomial.eval (-y) P := by
      intro y
      simp [S, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]
    have hneg := hPat (-x - 1)
    have hrefl : Polynomial.eval (-x - 1) (gEvenPoly j) =
        Polynomial.eval x (gEvenPoly j) := by
      have hx : (-x - 1 : ℚ) = -(x + 1) := by ring
      rw [hx]
      have := congrArg (fun p => Polynomial.eval x p) (gEvenPoly_reflect j)
      simpa [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_one] using this
    have hneg' : Polynomial.eval (-x) P - Polynomial.eval (-x - 1) P =
        Polynomial.eval (-x - 1) (gEvenPoly j) := by
      have : (-x - 1 + 1 : ℚ) = -x := by ring
      simpa [this] using hneg
    rw [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, hSeval (x + 1), hSeval x]
    have hx' : -(x + 1) = -x - 1 := by ring
    rw [hx']
    linarith [hneg', hrefl]
  have hS0 : S.eval 0 = 0 := by
    simp [S, P, PsumPoly, sumPoly_eval_zero]
  have hP0 : P.eval 0 = 0 := sumPoly_eval_zero _
  have hSP : S = P := poly_antideriv_unique S P (gEvenPoly j) hSdiff hPdiff hS0 hP0
  have : - P.comp (-Polynomial.X) = P := hSP
  exact neg_eq_iff_eq_neg.mp this

lemma PsumPoly_eval_zero (j : ℕ) : (PsumPoly j).eval 0 = 0 :=
  sumPoly_eval_zero _

lemma PsumPoly_eval_one {j : ℕ} (hj : 1 ≤ j) : (PsumPoly j).eval 1 = 0 := by
  have h := sumPoly_eval (gEvenPoly j) 1
  have hz : (gEvenPoly j).eval (0 : ℚ) = 0 := by
    simp [gEvenPoly, zero_pow (Nat.pos_iff_ne_zero.mp hj)]
  simpa [PsumPoly, sum_range_one, hz] using h

lemma PsumPoly_eval_neg_one {j : ℕ} (hj : 1 ≤ j) : (PsumPoly j).eval (-1) = 0 := by
  have := congrArg (fun p => p.eval 1) (PsumPoly_odd j)
  simpa [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X,
    PsumPoly_eval_one hj] using this

lemma X_mul_X_sq_sub_one_dvd_Psum {j : ℕ} (hj : 1 ≤ j) :
    Polynomial.X * (Polynomial.X ^ 2 - 1) ∣ PsumPoly j := by
  have hX := dvd_X_of_eval_zero _ (PsumPoly_eval_zero j)
  have h1 := X_sub_one_dvd_of_eval_one _ (PsumPoly_eval_one hj)
  have hm1 := X_add_one_dvd_of_eval_neg_one _ (PsumPoly_eval_neg_one hj)
  have h11 : (Polynomial.X - 1) * (Polynomial.X + 1) ∣ PsumPoly j :=
    isCoprime_X_sub_one_X_add_one.mul_dvd h1 hm1
  have hfac : (Polynomial.X ^ 2 - 1 : Polynomial ℚ) =
      (Polynomial.X - 1) * (Polynomial.X + 1) := by ring
  rw [hfac]
  have hcop : IsCoprime (Polynomial.X : Polynomial ℚ)
      ((Polynomial.X - 1) * (Polynomial.X + 1)) :=
    isCoprime_X_X_sub_one.mul_right isCoprime_X_X_add_one
  exact hcop.mul_dvd hX h11

lemma Usum_as_rat (j B C : ℕ) :
    (Usum j B C : ℚ) =
      ∑ t ∈ range C, (2 * (t : ℚ) + (B : ℚ) + 1) * ((t : ℚ) * (t + 1)) ^ j := by
  simp [Usum, alphaN]

lemma Usum_eq_Q_add_B_mul_P (j B C : ℕ) :
    (Usum j B C : ℚ) =
      (QsumPoly j).eval (C : ℚ) + (B : ℚ) * (PsumPoly j).eval (C : ℚ) := by
  rw [Usum_as_rat, QsumPoly_eval]
  have hP : (PsumPoly j).eval (C : ℚ) =
      ∑ t ∈ range C, (gEvenPoly j).eval (t : ℚ) :=
    sumPoly_eval _ _
  rw [hP]
  have hterm : ∀ t, (2 * (t : ℚ) + (B : ℚ) + 1) * ((t : ℚ) * (t + 1)) ^ j =
      (gOddPoly j).eval (t : ℚ) + (B : ℚ) * (gEvenPoly j).eval (t : ℚ) := by
    intro t
    simp [gOddPoly, gEvenPoly]
    ring
  simp_rw [hterm, sum_add_distrib, mul_sum]

lemma QsumPoly_eval_eq_mul {j : ℕ} (hj : 1 ≤ j) (C : ℕ) :
    ∃ R : Polynomial ℚ,
      (QsumPoly j).eval (C : ℚ) =
        (C : ℚ) ^ 2 * ((C : ℚ) ^ 2 - 1) * R.eval (C : ℚ) := by
  obtain ⟨R, hR⟩ := X_sq_mul_X_sq_sub_one_dvd_Qsum hj
  refine ⟨R, ?_⟩
  rw [hR]
  simp [pow_two, mul_assoc, mul_left_comm, mul_comm]

lemma PsumPoly_eval_eq_mul {j : ℕ} (hj : 1 ≤ j) (C : ℕ) :
    ∃ R : Polynomial ℚ,
      (PsumPoly j).eval (C : ℚ) =
        (C : ℚ) * ((C : ℚ) ^ 2 - 1) * R.eval (C : ℚ) := by
  obtain ⟨R, hR⟩ := X_mul_X_sq_sub_one_dvd_Psum hj
  refine ⟨R, ?_⟩
  rw [hR]
  simp [pow_two, mul_assoc, mul_left_comm, mul_comm]

/-! ## Additional coefficient lemmas -/

lemma generalized_exp_coeff_one (d : ℕ → ℕ) : generalized_exp_coeff d 1 = d 1 := by
  rw [generalized_exp_coeff_succ (k := 0)]
  simp [generalized_exp_coeff_zero]


/-! ## Binomial ratio as a paired product -/

lemma choose_ratio_sq (q A B : ℕ) (hq : 0 < q) (hBA : B ≤ A) :
    (((q * A).choose (q * B) : ℚ) / (A.choose B : ℚ)) ^ 2 =
      ∏ i ∈ Icc 1 (q - 1),
        ∏ t ∈ range (A - B),
          ((pbeta q i + alphaN (B + t) * (q : ℤ) ^ 2 : ℤ) : ℚ) /
          ((pbeta q i + alphaN t * (q : ℤ) ^ 2 : ℤ) : ℚ) := by
  have hprod := choose_ratio_eq_prod q A B hq hBA
  have hp0 : 0 < q := hq
  -- square both sides and pair i with q-i
  have hsq :
      (((q * A).choose (q * B) : ℚ) / (A.choose B : ℚ)) ^ 2 =
        (∏ i ∈ Icc 1 (q - 1),
          ∏ t ∈ range (A - B),
            (((B + t) * q + i : ℕ) : ℚ) / ((t * q + i : ℕ) : ℚ)) *
        (∏ i ∈ Icc 1 (q - 1),
          ∏ t ∈ range (A - B),
            (((B + t) * q + (q - i) : ℕ) : ℚ) / ((t * q + (q - i) : ℕ) : ℚ)) := by
    have hre :
        ∏ i ∈ Icc 1 (q - 1),
            ∏ t ∈ range (A - B),
              (((B + t) * q + (q - i) : ℕ) : ℚ) / ((t * q + (q - i) : ℕ) : ℚ) =
          ∏ i ∈ Icc 1 (q - 1),
            ∏ t ∈ range (A - B),
              (((B + t) * q + i : ℕ) : ℚ) / ((t * q + i : ℕ) : ℚ) := by
      -- reindex i ↦ q-i on the outer product
      refine prod_nbij (fun i => q - i) (fun i hi => p_sub_of_mem_Icc hp0 hi)
        (injOn_p_sub hp0) ?_ ?_
      · intro i hi
        exact ⟨q - i, p_sub_of_mem_Icc hp0 hi, p_sub_p_sub hp0 hi⟩
      · intro i hi
        rfl
    rw [hprod, pow_two, hre]
  rw [hsq, ← prod_mul_distrib]
  refine prod_congr rfl fun i hi => ?_
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun t ht => ?_
  have hiq : i ≤ q := (mem_Icc.mp hi).2.trans (Nat.pred_le _)
  have hilt : i < q := mem_Icc_pred_lt hp0 hi
  have hnum := pair_prod_eq q i (B + t) hiq
  have hden := pair_prod_eq q i t hiq
  have h1 : (((B + t) * q + i : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.add_pos_right _ (mem_Icc.mp hi).1).ne'
  have h2 : ((t * q + i : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.add_pos_right _ (mem_Icc.mp hi).1).ne'
  have h3 : (((B + t) * q + (q - i) : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.add_pos_right _ (Nat.sub_pos_of_lt hilt)).ne'
  have h4 : ((t * q + (q - i) : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.add_pos_right _ (Nat.sub_pos_of_lt hilt)).ne'
  have hL : ((i + (B + t) * q : ℕ) : ℚ) = ((B + t) * q + i : ℕ) := by
    simp [add_comm]
  have hR : (((q - i) + (B + t) * q : ℕ) : ℚ) = ((B + t) * q + (q - i) : ℕ) := by
    simp [add_comm]
  have hL' : ((i + t * q : ℕ) : ℚ) = ((t * q + i : ℕ) : ℚ) := by
    simp [add_comm]
  have hR' : (((q - i) + t * q : ℕ) : ℚ) = ((t * q + (q - i) : ℕ) : ℚ) := by
    simp [add_comm]
  have hcast_num :
      (((B + t) * q + i : ℕ) : ℚ) * (((B + t) * q + (q - i) : ℕ) : ℚ) =
        ((pbeta q i + alphaN (B + t) * (q : ℤ) ^ 2 : ℤ) : ℚ) := by
    have := congrArg (fun z : ℤ => (z : ℚ)) hnum
    simp only [Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_natCast] at this
    simpa [hL, hR] using this
  have hcast_den :
      ((t * q + i : ℕ) : ℚ) * ((t * q + (q - i) : ℕ) : ℚ) =
        ((pbeta q i + alphaN t * (q : ℤ) ^ 2 : ℤ) : ℚ) := by
    have := congrArg (fun z : ℤ => (z : ℚ)) hden
    simp only [Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_natCast] at this
    simpa [hL', hR'] using this
  have hden0 : ((pbeta q i + alphaN t * (q : ℤ) ^ 2 : ℤ) : ℚ) ≠ 0 := by
    rw [← hcast_den]
    exact mul_ne_zero h2 h4
  field_simp [h1, h2, h3, h4, hden0]
  rw [hcast_num, hcast_den]
  ring

/-! ## p-adic valuations of harmonic sums -/

lemma padicValRat_inv_nat [Fact p.Prime] (k : ℕ) :
    padicValRat p (k : ℚ)⁻¹ = - padicValRat p (k : ℚ) :=
  padicValRat.inv (k : ℚ)

lemma padicValNat_of_lt_prime {k : ℕ} [hp : Fact p.Prime] (hk : 0 < k) (hkl : k < p) :
    padicValNat p k = 0 :=
  padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hk hkl)

lemma factorial_div_mem (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    ((n.factorial / k : ℕ) : ℚ) = (n.factorial : ℚ) / k :=
  Nat.cast_div (Nat.dvd_factorial hk hkn) (Nat.cast_ne_zero.mpr hk.ne')

lemma sum_factorial_div_eq (q : ℕ) :
    ∑ k ∈ Icc 1 q, ((q.factorial / k : ℕ) : ℚ) =
      (q.factorial : ℚ) * ∑ k ∈ Icc 1 q, (1 : ℚ) / k := by
  rw [mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hkpos : 0 < k := (mem_Icc.mp hk).1
  have hkl : k ≤ q := (mem_Icc.mp hk).2
  rw [factorial_div_mem q k hkpos hkl]
  ring

lemma zmod_div_eq_mul_inv {q t : ℕ} (hp : p.Prime) {k : ℕ}
    (hk : k ∈ Icc 1 (p - 1)) (hkdvd : k ∣ q) :
    ((q / k : ℕ) : ZMod (p ^ t)) =
      (q : ZMod (p ^ t)) * (k : ZMod (p ^ t))⁻¹ := by
  have hku : IsUnit (k : ZMod (p ^ t)) := isUnit_natCast_pow (t := t) hp hk
  have hprod : (q / k) * k = q := Nat.div_mul_cancel hkdvd
  have hcast := congrArg (fun n : ℕ => (n : ZMod (p ^ t))) hprod
  simp only [Nat.cast_mul] at hcast
  have hcancel : (k : ZMod (p ^ t)) * (k : ZMod (p ^ t))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hku
  rw [← mul_one ((q / k : ℕ) : ZMod (p ^ t)), ← hcancel, ← mul_assoc, hcast]

lemma padicValRat_harmonic_ge_two (hp : p.Prime) (hp5 : 5 ≤ p) :
    (2 : ℤ) ≤ padicValRat p (∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / k) ∨
      (∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / k) = 0 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  set H := ∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / k
  by_cases h0 : H = 0
  · exact Or.inr h0
  · left
    let N : ℤ := ∑ k ∈ Icc 1 (p - 1), ((p - 1).factorial / k : ℕ)
    have hden : ((p - 1).factorial : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (factorial_ne_zero _)
    have hNeq : H * ((p - 1).factorial : ℚ) = (N : ℚ) := by
      simp only [N, Int.cast_sum, Int.cast_natCast]
      have := sum_factorial_div_eq (p - 1)
      rw [mul_comm] at this
      simpa [H, div_eq_mul_inv] using this.symm
    have hpfact : padicValRat p ((p - 1).factorial : ℚ) = 0 := by
      rw [padicValRat_natCast]
      norm_cast
      refine padicValNat.eq_zero_of_not_dvd ?_
      intro hdiv
      have : p ≤ p - 1 := (Nat.Prime.dvd_factorial hp).mp hdiv
      omega
    have hNneZ : N ≠ 0 := by
      intro hN0
      have : H * ((p - 1).factorial : ℚ) = 0 := by
        rw [hNeq, hN0, Int.cast_zero]
      exact h0 ((mul_eq_zero.mp this).resolve_right hden)
    have hNne : (N : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hNneZ
    have hHval : padicValRat p H = padicValRat p (N : ℚ) := by
      have := congrArg (padicValRat p) hNeq
      rw [padicValRat.mul h0 hden, hpfact, add_zero] at this
      simpa using this
    have hsumZ := wolstenholme_H1_mod_p2 hp hp5
    have hpdvd : (p : ℤ) ^ 2 ∣ N := by
      have hmap :
          (∑ k ∈ Icc 1 (p - 1), (((p - 1).factorial / k : ℕ) : ZMod (p ^ 2))) = 0 := by
        have hfac :
            ∑ k ∈ Icc 1 (p - 1), (((p - 1).factorial / k : ℕ) : ZMod (p ^ 2)) =
              ((p - 1).factorial : ZMod (p ^ 2)) *
                ∑ k ∈ Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ := by
          rw [mul_sum]
          refine sum_congr rfl fun k hk => ?_
          have hkdvd : k ∣ (p - 1).factorial :=
            Nat.dvd_factorial (mem_Icc.mp hk).1 (mem_Icc.mp hk).2
          exact zmod_div_eq_mul_inv hp hk hkdvd
        rw [hfac, hsumZ, mul_zero]
      have : (N : ZMod (p ^ 2)) = 0 := by
        simp only [N, Int.cast_sum, Int.cast_natCast]
        exact hmap
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd N (p ^ 2)).mp this
    have : (2 : ℤ) ≤ padicValRat p (N : ℚ) :=
      padicValRat_of_dvd_pow hNneZ hpdvd
    rwa [hHval]

lemma pbeta_ne_zero {i : ℕ} (hp0 : 0 < p) (hi : i ∈ Icc 1 (p - 1)) :
    (pbeta p i : ℚ) ≠ 0 := by
  have hilt : i < p := mem_Icc_pred_lt hp0 hi
  have hi0 : 0 < i := (mem_Icc.mp hi).1
  have hpi : 0 < p - i := Nat.sub_pos_of_lt hilt
  unfold pbeta
  simp only [Int.cast_mul, Int.cast_natCast]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hi0.ne') (Nat.cast_ne_zero.mpr hpi.ne')

lemma padicValRat_pbeta (hp : p.Prime) {i : ℕ} (hi : i ∈ Icc 1 (p - 1)) :
    padicValRat p (pbeta p i : ℚ) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hilt : i < p := mem_Icc_pred_lt hp.pos hi
  have hi0 : 0 < i := (mem_Icc.mp hi).1
  have hpi : 0 < p - i := Nat.sub_pos_of_lt hilt
  have hi' : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hi0.ne'
  have hpi' : ((p - i : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpi.ne'
  simp only [pbeta, Int.cast_mul, Int.cast_natCast]
  rw [padicValRat.mul hi' hpi', padicValRat_natCast, padicValRat_natCast]
  have h1 : padicValNat p i = 0 :=
    padicValNat_of_lt_prime hi0 hilt
  have h2 : padicValNat p (p - i) = 0 :=
    padicValNat_of_lt_prime hpi (Nat.sub_lt hp.pos hi0)
  norm_cast
  rw [h1, h2]

lemma padicValRat_sum_inv_pbeta (hp : p.Prime) (hp5 : 5 ≤ p) :
    (1 : ℤ) ≤ padicValRat p (∑ i ∈ Icc 1 (p - 1), (1 : ℚ) / pbeta p i) ∨
      (∑ i ∈ Icc 1 (p - 1), (1 : ℚ) / pbeta p i) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hform := sum_inv_pbeta (p := p) hp.pos
  set S := ∑ i ∈ Icc 1 (p - 1), (1 : ℚ) / pbeta p i
  set H := ∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / k
  have hSH : S = (2 : ℚ) / p * H := hform
  by_cases hS0 : S = 0
  · exact Or.inr hS0
  · left
    have hH0 : H ≠ 0 := by
      intro h
      exact hS0 (by simp [hSH, h])
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have h2 : (2 : ℚ) ≠ 0 := by norm_num
    rw [hSH, padicValRat.mul, padicValRat.div h2 hp0]
    · have h2v : padicValRat p (2 : ℚ) = 0 := by
        rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from rfl, padicValRat_natCast]
        exact_mod_cast padicValNat.eq_zero_of_not_dvd (fun hdiv => by
          have : p ≤ 2 := Nat.le_of_dvd (by decide) hdiv
          omega)
      have hpv : padicValRat p (p : ℚ) = 1 := by
        rw [padicValRat_natCast, padicValNat.self hp.one_lt]
        norm_cast
      have hHv := padicValRat_harmonic_ge_two hp hp5
      rcases hHv with hH | hH0'
      · linarith [h2v, hpv, hH]
      · exact (hH0 hH0').elim
    · exact div_ne_zero h2 hp0
    · exact hH0

/-- Central binomial form of Wolstenholme, one prime step. -/
lemma wolstenholme_central_step (N : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ((2 * N * p).choose (N * p) : ℤ) ≡ ((2 * N).choose N : ℤ) [ZMOD (p : ℤ) ^ 3] := by
  have := wolstenholme_choose_r1 (2 * N) N hp hp5
  convert this using 2 <;> ring

lemma two_coprime_p_pow (hp : p.Prime) (hp5 : 5 ≤ p) (t : ℕ) :
    IsCoprime (2 : ℤ) (p ^ t : ℤ) := by
  rw [Int.isCoprime_iff_nat_coprime]
  have hcop : Nat.Coprime 2 p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (by
      intro h2p
      have : p ≤ 2 := Nat.le_of_dvd (by decide) h2p
      omega)).symm
  simpa using hcop.pow_right t

lemma coeff_of_log_gf_gen_succ (m k : ℕ) :
    coeff_of_log_gf_gen (m + 1) k =
      ((m + 1) * k).choose k * coeff_of_log_gf_gen m k := by
  have hle : k ≤ (m + 1) * k := Nat.le_mul_of_pos_left k (Nat.succ_pos m)
  have hsub : (m + 1) * k - k = m * k := by
    rw [Nat.succ_mul, Nat.add_sub_cancel]
  have hch :
      ((m + 1) * k).choose k * k.factorial * (m * k).factorial =
        ((m + 1) * k).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := (m + 1) * k) (k := k) hle
    rwa [hsub] at h
  have hcm := coeff_of_log_gf_gen_mul_factorial m k
  have hcm1 := coeff_of_log_gf_gen_mul_factorial (m + 1) k
  have hmul :
      coeff_of_log_gf_gen (m + 1) k * k.factorial ^ (m + 1) =
        ((m + 1) * k).choose k * coeff_of_log_gf_gen m k * k.factorial ^ (m + 1) := by
    rw [hcm1, ← hch, ← hcm]
    ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (n := m + 1) (Nat.factorial_pos k)) hmul

/-- `c_m(k) = ∏_{s=2}^{m} C(s k, k)` (empty product is 1 when `m ≤ 1`). -/
lemma coeff_of_log_gf_gen_eq_prod_choose (m k : ℕ) :
    coeff_of_log_gf_gen m k = ∏ s ∈ Icc 2 m, (s * k).choose k := by
  induction m with
  | zero =>
    simp [coeff_of_log_gf_gen]
  | succ m ih =>
    by_cases hm : m = 0
    · subst hm
      simp [coeff_of_log_gf_gen, Nat.div_self (Nat.factorial_pos k)]
    · have hIcc : Icc 2 (m + 1) = insert (m + 1) (Icc 2 m) := by
        ext s
        simp only [mem_insert, mem_Icc]
        constructor <;> omega
      have hnot : m + 1 ∉ Icc 2 m := by
        simp [mem_Icc]
      rw [hIcc, prod_insert hnot, coeff_of_log_gf_gen_succ, ih, mul_comm]


/-! ## Carry lemma for central binomials -/

lemma add_mod_pow_cases {x y i : ℕ} (hp0 : 0 < p) :
    x % p ^ i + y % p ^ i = (x + y) % p ^ i ∨
      x % p ^ i + y % p ^ i = (x + y) % p ^ i + p ^ i := by
  have hmod : (x % p ^ i + y % p ^ i) % p ^ i = (x + y) % p ^ i := by
    rw [← Nat.add_mod]
  have hx : x % p ^ i < p ^ i := Nat.mod_lt _ (Nat.pow_pos hp0)
  have hy : y % p ^ i < p ^ i := Nat.mod_lt _ (Nat.pow_pos hp0)
  have hsumlt : x % p ^ i + y % p ^ i < 2 * p ^ i := by
    have := Nat.add_lt_add hx hy
    simpa [two_mul] using this
  have hle : x % p ^ i + y % p ^ i < p ^ i ∨ p ^ i ≤ x % p ^ i + y % p ^ i :=
    lt_or_ge _ _
  rcases hle with hlt | hge
  · left
    rwa [Nat.mod_eq_of_lt hlt] at hmod
  · right
    have hsub : x % p ^ i + y % p ^ i - p ^ i < p ^ i := by omega
    have : (x % p ^ i + y % p ^ i) % p ^ i = x % p ^ i + y % p ^ i - p ^ i :=
      Nat.mod_eq_sub_mod hge ▸ Nat.mod_eq_of_lt hsub
    have : x % p ^ i + y % p ^ i - p ^ i = (x + y) % p ^ i := this.symm.trans hmod
    omega

lemma two_mul_mod_cover {x y i : ℕ} (hp0 : 0 < p)
    (hdvd : p ^ i ∣ x + y) (hx : ¬ p ∣ x) (hi : 1 ≤ i) :
    p ^ i ≤ 2 * (x % p ^ i) ∨ p ^ i ≤ 2 * (y % p ^ i) := by
  have hmod0 : (x + y) % p ^ i = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  rcases add_mod_pow_cases (x := x) (y := y) (i := i) hp0 with h | h
  · -- x% + y% = (x+y)% = 0 ⇒ both residues 0 ⇒ p^i ∣ x
    have hsum0 : x % p ^ i + y % p ^ i = 0 := by
      rw [h, hmod0]
    have hx0 : x % p ^ i = 0 := Nat.eq_zero_of_add_eq_zero_right hsum0
    have : p ^ i ∣ x := Nat.dvd_iff_mod_eq_zero.mpr hx0
    have : p ∣ x := (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hi)).trans this
    exact (hx this).elim
  · -- x% + y% = (x+y)% + p^i = p^i
    have hsum : x % p ^ i + y % p ^ i = p ^ i := by
      rw [h, hmod0, zero_add]
    by_contra hnot
    push_neg at hnot
    have hx2 : 2 * (x % p ^ i) < p ^ i := hnot.1
    have hy2 : 2 * (y % p ^ i) < p ^ i := hnot.2
    have : 2 * p ^ i = 2 * (x % p ^ i) + 2 * (y % p ^ i) := by
      rw [← Nat.mul_add, hsum]
    omega

lemma padicValNat_central_eq (x b : ℕ) [hp : Fact p.Prime]
    (hb : Nat.log p (2 * x) < b) :
    padicValNat p ((2 * x).choose x) =
      #{i ∈ Ico 1 b | p ^ i ≤ 2 * (x % p ^ i)} := by
  have h := padicValNat_choose' (p := p) (n := x) (k := x) (b := b)
    (by simpa [two_mul] using hb)
  simpa [two_mul] using h

lemma carry_central {x y r : ℕ} [hp : Fact p.Prime]
    (hxy : p ^ r ∣ x + y) (hx : ¬ p ∣ x) (hy : ¬ p ∣ y) :
    r ≤ padicValNat p ((2 * x).choose x) + padicValNat p ((2 * y).choose y) := by
  classical
  rcases r with _ | r0
  · exact Nat.zero_le _
  set r := r0 + 1
  have hr0 : r = r0 + 1 := rfl
  have hp0 := hp.out.pos
  let b := Nat.log p (2 * x) + Nat.log p (2 * y) + r + 2
  have hbx : Nat.log p (2 * x) < b := by omega
  have hby : Nat.log p (2 * y) < b := by omega
  have hxeq := padicValNat_central_eq (p := p) x b hbx
  have hyeq := padicValNat_central_eq (p := p) y b hby
  rw [hxeq, hyeq]
  -- Every i ∈ Icc 1 r belongs to at least one of the two filter sets.
  let Sx := (Ico 1 b).filter (fun i => p ^ i ≤ 2 * (x % p ^ i))
  let Sy := (Ico 1 b).filter (fun i => p ^ i ≤ 2 * (y % p ^ i))
  have hcover : (Icc 1 r : Finset ℕ) ⊆ Sx ∪ Sy := by
    intro i hi
    have hi' := mem_Icc.mp hi
    have hile : i ≤ r := hi'.2
    have hige : 1 ≤ i := hi'.1
    have hibo : i ∈ Ico 1 b := mem_Ico.mpr ⟨hige, by omega⟩
    have hdvd : p ^ i ∣ x + y := (pow_dvd_pow p hile).trans hxy
    have hcov := two_mul_mod_cover (p := p) hp0 hdvd hx hige
    refine mem_union.mpr ?_
    rcases hcov with hx2 | hy2
    · exact Or.inl (mem_filter.mpr ⟨hibo, hx2⟩)
    · exact Or.inr (mem_filter.mpr ⟨hibo, hy2⟩)
  have hcard := Finset.card_le_card hcover
  have hunion : #(Sx ∪ Sy) ≤ #Sx + #Sy := card_union_le _ _
  have hrcc : #(Icc 1 r) = r := by simp [Nat.card_Icc]
  have : r ≤ #Sx + #Sy := by
    have := hcard.trans hunion
    rwa [hrcc] at this
  simpa [Sx, Sy] using this

/-! ## Stirling second kind identities -/

/-- `S(n+1, k+1) = ∑_j C(n,j) S(j,k)`. -/
lemma stirlingSecond_succ_eq_sum_choose (n k : ℕ) :
    stirlingSecond (n + 1) (k + 1) =
      ∑ j ∈ range (n + 1), n.choose j * stirlingSecond j k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [stirlingSecond]
    | succ k => simp [stirlingSecond]
  | succ n ih =>
    cases k with
    | zero =>
      have hS : stirlingSecond (n + 2) 1 = 1 := by
        simpa using stirlingSecond_one_right (n + 1)
      rw [hS]
      have h0 : ∀ j ∈ range (n + 2),
          j ≠ 0 → stirlingSecond j 0 = 0 := fun j _ hj => by
        cases j with
        | zero => exact (hj rfl).elim
        | succ j => exact stirlingSecond_succ_zero j
      rw [sum_eq_single 0]
      · simp [stirlingSecond]
      · intro j hj hj0
        simp [h0 j hj hj0]
      · simp
    | succ k =>
      have hterm : ∀ j ∈ range (n + 2),
          (n + 1).choose j * stirlingSecond j (k + 1) =
            n.choose j * stirlingSecond j (k + 1) +
              (if j = 0 then 0 else n.choose (j - 1) * stirlingSecond j (k + 1)) := by
        intro j hj
        cases j with
        | zero => simp
        | succ j =>
          rw [choose_succ_left (n := n) (k := j + 1) (Nat.succ_pos _)]
          simp [add_mul, add_comm]
      rw [sum_congr rfl hterm, sum_add_distrib]
      have hextra : n.choose (n + 1) = 0 := choose_eq_zero_of_lt (Nat.lt_succ_self n)
      have hsum1 :
          (∑ j ∈ range (n + 2), n.choose j * stirlingSecond j (k + 1)) =
            stirlingSecond (n + 1) (k + 2) := by
        rw [sum_range_succ, hextra, zero_mul, add_zero, ← ih (k := k + 1)]
      have hshift :
          (∑ j ∈ range (n + 2),
              if j = 0 then 0 else n.choose (j - 1) * stirlingSecond j (k + 1)) =
            ∑ i ∈ range (n + 1), n.choose i * stirlingSecond (i + 1) (k + 1) := by
        rw [sum_range_succ']; simp
      rw [hsum1, hshift]
      have hsplit :
          (∑ i ∈ range (n + 1), n.choose i * stirlingSecond (i + 1) (k + 1)) =
            (k + 1) * ∑ i ∈ range (n + 1), n.choose i * stirlingSecond i (k + 1) +
              ∑ i ∈ range (n + 1), n.choose i * stirlingSecond i k := by
        have hrec : ∀ i, stirlingSecond (i + 1) (k + 1) =
            (k + 1) * stirlingSecond i (k + 1) + stirlingSecond i k :=
          fun i => stirlingSecond_succ_succ i k
        simp only [hrec, mul_add]
        rw [sum_add_distrib]
        congr 1
        simp [mul_sum, mul_left_comm]
      rw [hsplit, ← ih (k := k + 1), ← ih (k := k)]
      rw [stirlingSecond_succ_succ (n + 1) (k + 1)]
      ring

/-- `I(k,n) = ∑_{j=0}^k (-1)^j C(k,j) j^n`. -/
def stirlingSum (k n : ℕ) : ℤ :=
  ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * (k.choose j : ℤ) * (j : ℤ) ^ n

lemma stirlingSum_zero_right (k : ℕ) :
    stirlingSum k 0 = if k = 0 then 1 else 0 := by
  unfold stirlingSum
  simp only [pow_zero, mul_one]
  simpa [mul_comm] using Int.alternating_sum_range_choose (n := k)

lemma stirlingSum_zero_left (n : ℕ) :
    stirlingSum 0 n = if n = 0 then 1 else 0 := by
  unfold stirlingSum
  cases n with
  | zero => simp
  | succ n => simp [zero_pow (Nat.succ_ne_zero n)]

lemma choose_mul_eq_succ_mul {k j : ℕ} (hj : 1 ≤ j) :
    (k + 1).choose j * j = (k + 1) * k.choose (j - 1) := by
  obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le' hj
  simpa [Nat.succ_eq_add_one] using (Nat.add_one_mul_choose_eq k j').symm

/-- `I(k, n+1) = -k ∑_m C(n,m) I(k-1, m)` for `k ≥ 1`. -/
lemma stirlingSum_succ_right {k n : ℕ} (hk : 1 ≤ k) :
    stirlingSum k (n + 1) =
      - (k : ℤ) * ∑ m ∈ range (n + 1), (n.choose m : ℤ) * stirlingSum (k - 1) m := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk
  have hpow : ∀ j : ℕ, (j : ℤ) ^ (n + 1) = (j : ℤ) * (j : ℤ) ^ n := fun j => by
    rw [pow_succ, mul_comm]
  have hLHS : stirlingSum (k' + 1) (n + 1) =
      ∑ j ∈ range (k' + 2),
        (-1 : ℤ) ^ j * ((k' + 1).choose j : ℤ) * (j : ℤ) * (j : ℤ) ^ n := by
    unfold stirlingSum
    refine sum_congr rfl fun j _ => ?_
    rw [hpow]; ring
  have h0 :
      ∑ j ∈ range (k' + 2),
          (-1 : ℤ) ^ j * ((k' + 1).choose j : ℤ) * (j : ℤ) * (j : ℤ) ^ n =
        ∑ j ∈ range (k' + 1),
          (-1 : ℤ) ^ (j + 1) * ((k' + 1).choose (j + 1) : ℤ) *
            ((j + 1 : ℕ) : ℤ) * ((j + 1 : ℕ) : ℤ) ^ n := by
    rw [sum_range_succ']; simp
  have hch : ∀ j,
      ((k' + 1).choose (j + 1) : ℤ) * ((j + 1 : ℕ) : ℤ) =
        (k' + 1 : ℤ) * (k'.choose j : ℤ) := fun j => by
    exact_mod_cast choose_mul_eq_succ_mul (j := j + 1) (Nat.succ_pos _)
  have hterm : ∀ j ∈ range (k' + 1),
      (-1 : ℤ) ^ (j + 1) * ((k' + 1).choose (j + 1) : ℤ) *
          ((j + 1 : ℕ) : ℤ) * ((j + 1 : ℕ) : ℤ) ^ n =
        - (k' + 1 : ℤ) *
          ((-1 : ℤ) ^ j * (k'.choose j : ℤ) * ((j + 1 : ℕ) : ℤ) ^ n) := by
    intro j _
    calc
      (-1 : ℤ) ^ (j + 1) * ((k' + 1).choose (j + 1) : ℤ) *
          ((j + 1 : ℕ) : ℤ) * ((j + 1 : ℕ) : ℤ) ^ n =
        (-1 : ℤ) ^ (j + 1) *
          (((k' + 1).choose (j + 1) : ℤ) * ((j + 1 : ℕ) : ℤ)) *
          ((j + 1 : ℕ) : ℤ) ^ n := by ring
      _ = (-1 : ℤ) ^ (j + 1) * ((k' + 1 : ℤ) * (k'.choose j : ℤ)) *
          ((j + 1 : ℕ) : ℤ) ^ n := by rw [hch]
      _ = - (k' + 1 : ℤ) *
          ((-1 : ℤ) ^ j * (k'.choose j : ℤ) * ((j + 1 : ℕ) : ℤ) ^ n) := by
        rw [pow_succ]; ring
  have hLHS' : stirlingSum (k' + 1) (n + 1) =
      - (k' + 1 : ℤ) *
        ∑ j ∈ range (k' + 1),
          (-1 : ℤ) ^ j * (k'.choose j : ℤ) * ((j + 1 : ℕ) : ℤ) ^ n := by
    rw [hLHS, h0, sum_congr rfl hterm, ← mul_sum]
  have hbin : ∀ j : ℕ, ((j + 1 : ℕ) : ℤ) ^ n =
      ∑ m ∈ range (n + 1), (n.choose m : ℤ) * (j : ℤ) ^ m := by
    intro j
    have h := add_pow (j : ℤ) (1 : ℤ) n
    simpa [one_pow, mul_one, Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm,
      mul_assoc] using h
  have hswap :
      ∑ j ∈ range (k' + 1),
          (-1 : ℤ) ^ j * (k'.choose j : ℤ) * ((j + 1 : ℕ) : ℤ) ^ n =
        ∑ m ∈ range (n + 1), (n.choose m : ℤ) * stirlingSum k' m := by
    simp only [hbin, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun m _ => ?_
    unfold stirlingSum
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [hLHS', hswap]
  simp

lemma stirlingSum_eq : ∀ n k,
    stirlingSum k n = (-1 : ℤ) ^ k * (k.factorial : ℤ) * (stirlingSecond n k : ℤ) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k
    cases n with
    | zero =>
      rw [stirlingSum_zero_right]
      cases k with
      | zero => simp [stirlingSecond]
      | succ k => simp [stirlingSecond]
    | succ n =>
      cases k with
      | zero =>
        rw [stirlingSum_zero_left]
        simp [stirlingSecond]
      | succ k =>
        rw [stirlingSum_succ_right (k := k + 1) (Nat.succ_pos _)]
        simp only [Nat.add_sub_cancel]
        have hih : ∀ m ∈ range (n + 1),
            stirlingSum k m =
              (-1 : ℤ) ^ k * (k.factorial : ℤ) * (stirlingSecond m k : ℤ) := by
          intro m hm
          exact ih m (by have := mem_range.mp hm; omega) k
        have hsum :
            ∑ m ∈ range (n + 1), (n.choose m : ℤ) * stirlingSum k m =
              (-1 : ℤ) ^ k * (k.factorial : ℤ) *
                ∑ m ∈ range (n + 1), (n.choose m : ℤ) * (stirlingSecond m k : ℤ) := by
          rw [mul_sum]
          refine sum_congr rfl fun m hm => ?_
          rw [hih m hm]
          ring
        rw [hsum]
        have hS := stirlingSecond_succ_eq_sum_choose n k
        have hScast :
            ∑ m ∈ range (n + 1), (n.choose m : ℤ) * (stirlingSecond m k : ℤ) =
              (stirlingSecond (n + 1) (k + 1) : ℤ) := by
          exact_mod_cast hS.symm
        rw [hScast, Nat.factorial_succ]
        push_cast
        ring

lemma sum_choose_stirlingSecond (n k : ℕ) :
    ∑ i ∈ range n, (n.choose i : ℤ) * (stirlingSecond i k : ℤ) =
      (k + 1 : ℤ) * (stirlingSecond n (k + 1) : ℤ) := by
  have hfull := congrArg (fun z : ℕ => (z : ℤ))
    (stirlingSecond_succ_eq_sum_choose n k).symm
  have hcast : ∑ i ∈ range (n + 1), (n.choose i : ℤ) * (stirlingSecond i k : ℤ) =
      (stirlingSecond (n + 1) (k + 1) : ℤ) := by
    simpa using hfull
  have hsplit :
      ∑ i ∈ range (n + 1), (n.choose i : ℤ) * (stirlingSecond i k : ℤ) =
        ∑ i ∈ range n, (n.choose i : ℤ) * (stirlingSecond i k : ℤ) +
          (stirlingSecond n k : ℤ) := by
    rw [sum_range_succ]
    simp
  have hrec : (stirlingSecond (n + 1) (k + 1) : ℤ) =
      (k + 1 : ℤ) * (stirlingSecond n (k + 1) : ℤ) + (stirlingSecond n k : ℤ) := by
    exact_mod_cast stirlingSecond_succ_succ n k
  linarith

/-- `∑_k (-1)^k k! S(n, k+1) = 0` for `n ≥ 2`. -/
lemma sum_signed_factorial_stirling {n : ℕ} (hn : 2 ≤ n) :
    ∑ k ∈ range n,
      (-1 : ℤ) ^ k * (k.factorial : ℤ) * (stirlingSecond n (k + 1) : ℤ) = 0 := by
  let f : ℕ → ℤ := fun j =>
    (-1 : ℤ) ^ j * (j.factorial : ℤ) * (stirlingSecond (n - 1) j : ℤ)
  have hS0 : (stirlingSecond (n - 1) 0 : ℤ) = 0 := by
    have : n - 1 = n - 2 + 1 := by omega
    rw [this]
    exact_mod_cast stirlingSecond_succ_zero (n - 2)
  have hf0 : f 0 = 0 := by simp [f, hS0]
  have hfn : f n = 0 := by
    have : (stirlingSecond (n - 1) n : ℤ) = 0 := by
      exact_mod_cast stirlingSecond_eq_zero_of_lt (show n - 1 < n by omega)
    simp [f, this]
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hrec : ∀ k, (stirlingSecond n (k + 1) : ℤ) =
      (k + 1 : ℤ) * (stirlingSecond (n - 1) (k + 1) : ℤ) +
        (stirlingSecond (n - 1) k : ℤ) := by
    intro k
    have h := congrArg (fun z : ℕ => (z : ℤ)) (stirlingSecond_succ_succ (n - 1) k)
    rwa [hn1] at h
  have hfac : ∀ k : ℕ, (k.factorial : ℤ) * (k + 1 : ℤ) = ((k + 1).factorial : ℤ) := by
    intro k
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hterm : ∀ k : ℕ,
      (-1 : ℤ) ^ k * (k.factorial : ℤ) * (stirlingSecond n (k + 1) : ℤ) =
        (-1 : ℤ) ^ k * ((k + 1).factorial : ℤ) *
            (stirlingSecond (n - 1) (k + 1) : ℤ) + f k := by
    intro k
    rw [hrec k]
    unfold f
    have hf := hfac k
    calc
      (-1 : ℤ) ^ k * (k.factorial : ℤ) *
          ((k + 1 : ℤ) * (stirlingSecond (n - 1) (k + 1) : ℤ) +
            (stirlingSecond (n - 1) k : ℤ)) =
        (-1 : ℤ) ^ k * ((k.factorial : ℤ) * (k + 1 : ℤ)) *
            (stirlingSecond (n - 1) (k + 1) : ℤ) +
          (-1 : ℤ) ^ k * (k.factorial : ℤ) * (stirlingSecond (n - 1) k : ℤ) := by ring
      _ = (-1 : ℤ) ^ k * ((k + 1).factorial : ℤ) *
            (stirlingSecond (n - 1) (k + 1) : ℤ) +
          (-1 : ℤ) ^ k * (k.factorial : ℤ) * (stirlingSecond (n - 1) k : ℤ) := by
        rw [hf]
  have hsplit :
      ∑ k ∈ range n,
          (-1 : ℤ) ^ k * (k.factorial : ℤ) * (stirlingSecond n (k + 1) : ℤ) =
        ∑ k ∈ range n, (-1 : ℤ) ^ k * ((k + 1).factorial : ℤ) *
            (stirlingSecond (n - 1) (k + 1) : ℤ) +
          ∑ k ∈ range n, f k := by
    rw [sum_congr rfl (fun k _ => hterm k), sum_add_distrib]
  rw [hsplit]
  have hfirst :
      ∑ k ∈ range n, (-1 : ℤ) ^ k * ((k + 1).factorial : ℤ) *
          (stirlingSecond (n - 1) (k + 1) : ℤ) =
        - ∑ k ∈ range n, f (k + 1) := by
    have hneg : ∀ k,
        (-1 : ℤ) ^ k * ((k + 1).factorial : ℤ) *
            (stirlingSecond (n - 1) (k + 1) : ℤ) =
          - f (k + 1) := by
      intro k
      simp only [f]
      rw [pow_succ]
      ring
    rw [sum_congr rfl (fun k _ => hneg k), ← sum_neg_distrib]
  have hshift : ∑ k ∈ range n, f (k + 1) = ∑ j ∈ range n, f j := by
    have h1 : ∑ k ∈ range n, f (k + 1) = ∑ j ∈ range (n + 1), f j - f 0 := by
      rw [sum_range_succ' (f := f)]
      ring
    rw [h1, sum_range_succ, hfn, add_zero, hf0, sub_zero]
  rw [hfirst, hshift]
  ring

/-- Explicit formula `B_n = ∑_{k=0}^n I(k,n)/(k+1)`. -/
noncomputable def bernoulliExplicit (n : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1), (stirlingSum k n : ℚ) / (k + 1 : ℚ)

lemma bernoulliExplicit_zero : bernoulliExplicit 0 = 1 := by
  unfold bernoulliExplicit
  simp [stirlingSum]

lemma bernoulliExplicit_one : bernoulliExplicit 1 = -1 / 2 := by
  unfold bernoulliExplicit
  simp [stirlingSum, sum_range_succ, range_one]
  norm_num

lemma stirlingSum_eq_zero_of_lt {k n : ℕ} (h : n < k) : stirlingSum k n = 0 := by
  rw [stirlingSum_eq, stirlingSecond_eq_zero_of_lt h]
  simp

lemma bernoulliExplicit_sum_extend {n N : ℕ} (h : n ≤ N) :
    bernoulliExplicit n =
      ∑ k ∈ range (N + 1), (stirlingSum k n : ℚ) / (k + 1 : ℚ) := by
  unfold bernoulliExplicit
  have hsub : range (n + 1) ⊆ range (N + 1) := by
    intro x hx
    exact mem_range.mpr (lt_of_lt_of_le (mem_range.mp hx) (Nat.succ_le_succ h))
  have hsplit : range (N + 1) = range (n + 1) ∪ (range (N + 1) \ range (n + 1)) :=
    (union_sdiff_of_subset hsub).symm
  rw [hsplit, sum_union disjoint_sdiff]
  have htail :
      ∑ k ∈ range (N + 1) \ range (n + 1), (stirlingSum k n : ℚ) / (k + 1 : ℚ) = 0 := by
    refine sum_eq_zero fun k hk => ?_
    have hk' : n + 1 ≤ k := by
      have : k ∉ range (n + 1) := (mem_sdiff.mp hk).2
      exact Nat.le_of_not_lt (fun hlt => this (mem_range.mpr hlt))
    have : stirlingSum k n = 0 := stirlingSum_eq_zero_of_lt (lt_of_lt_of_le (Nat.lt_succ_self n) hk')
    simp [this]
  rw [htail, add_zero]

lemma sum_choose_bernoulliExplicit (n : ℕ) :
    ∑ i ∈ range n, (n.choose i : ℚ) * bernoulliExplicit i =
      if n = 1 then 1 else 0 := by
  rcases n with _ | n
  · simp
  rcases n with _ | n
  · simp [bernoulliExplicit_zero]
  have hn2 : 2 ≤ n + 2 := by omega
  have hI : ∀ k i, (stirlingSum k i : ℚ) =
      ((-1 : ℤ) ^ k : ℚ) * (k.factorial : ℚ) * (stirlingSecond i k : ℚ) := by
    intro k i
    have h := congrArg (fun z : ℤ => (z : ℚ)) (stirlingSum_eq i k)
    simpa [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast] using h
  have hexpand :
      ∑ i ∈ range (n + 2), ((n + 2).choose i : ℚ) * bernoulliExplicit i =
        ∑ k ∈ range (n + 2), (1 / (k + 1 : ℚ)) *
          ∑ i ∈ range (n + 2), ((n + 2).choose i : ℚ) * (stirlingSum k i : ℚ) := by
    have hrew : ∀ i ∈ range (n + 2),
        ((n + 2).choose i : ℚ) * bernoulliExplicit i =
          ∑ k ∈ range (n + 2),
            (1 / (k + 1 : ℚ)) * (((n + 2).choose i : ℚ) * (stirlingSum k i : ℚ)) := by
      intro i hi
      have hile : i ≤ n + 1 := Nat.lt_succ_iff.mp (mem_range.mp hi)
      rw [bernoulliExplicit_sum_extend hile, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      field_simp
    rw [sum_congr rfl hrew, sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [← mul_sum]
  have hinner : ∀ k,
      ∑ i ∈ range (n + 2), ((n + 2).choose i : ℚ) * (stirlingSum k i : ℚ) =
        ((-1 : ℤ) ^ k : ℚ) * (k.factorial : ℚ) * (k + 1 : ℚ) *
          (stirlingSecond (n + 2) (k + 1) : ℚ) := by
    intro k
    simp only [hI]
    have hfactor :
        ∑ i ∈ range (n + 2), ((n + 2).choose i : ℚ) *
            (((-1 : ℤ) ^ k : ℚ) * (k.factorial : ℚ) * (stirlingSecond i k : ℚ)) =
          ((-1 : ℤ) ^ k : ℚ) * (k.factorial : ℚ) *
            ∑ i ∈ range (n + 2), ((n + 2).choose i : ℚ) * (stirlingSecond i k : ℚ) := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      ring
    rw [hfactor]
    have hZ := sum_choose_stirlingSecond (n + 2) k
    have hcast :
        ∑ i ∈ range (n + 2), ((n + 2).choose i : ℚ) * (stirlingSecond i k : ℚ) =
          (k + 1 : ℚ) * (stirlingSecond (n + 2) (k + 1) : ℚ) := by
      exact_mod_cast hZ
    rw [hcast]
    ring
  rw [hexpand]
  have hrew :
      ∑ k ∈ range (n + 2), (1 / (k + 1 : ℚ)) *
          ∑ i ∈ range (n + 2), ((n + 2).choose i : ℚ) * (stirlingSum k i : ℚ) =
        ∑ k ∈ range (n + 2),
          ((-1 : ℤ) ^ k : ℚ) * (k.factorial : ℚ) *
            (stirlingSecond (n + 2) (k + 1) : ℚ) := by
    refine sum_congr rfl fun k _ => ?_
    rw [hinner]
    have hk0 : (k + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    field_simp [hk0]
  rw [hrew]
  have hvan := sum_signed_factorial_stirling (n := n + 2) hn2
  have : (∑ k ∈ range (n + 2),
      ((-1 : ℤ) ^ k : ℚ) * (k.factorial : ℚ) *
        (stirlingSecond (n + 2) (k + 1) : ℚ)) = 0 := by
    have h' := congrArg (fun z : ℤ => (z : ℚ)) hvan
    simpa [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast] using h'
  simpa using this

lemma bernoulliExplicit_eq (n : ℕ) : bernoulliExplicit n = bernoulli n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases n with _ | n
    · simp [bernoulliExplicit_zero, bernoulli_zero]
    rcases n with _ | n
    · simp [bernoulliExplicit_one, bernoulli_one]
    have hT := sum_choose_bernoulliExplicit (n + 3)
    have hB := sum_bernoulli (n + 3)
    have hn3 : n + 3 ≠ 1 := by omega
    simp only [hn3, ↓reduceIte] at hT hB
    have hprev : ∀ i < n + 2, bernoulliExplicit i = bernoulli i :=
      fun i hi => ih i (by omega)
    have hsum_eq :
        ∑ i ∈ range (n + 2), ((n + 3).choose i : ℚ) * bernoulliExplicit i =
          ∑ i ∈ range (n + 2), ((n + 3).choose i : ℚ) * bernoulli i :=
      sum_congr rfl fun i hi => by rw [hprev i (mem_range.mp hi)]
    have hlastT :
        ∑ i ∈ range (n + 3), ((n + 3).choose i : ℚ) * bernoulliExplicit i =
          ∑ i ∈ range (n + 2), ((n + 3).choose i : ℚ) * bernoulliExplicit i +
            ((n + 3 : ℕ) : ℚ) * bernoulliExplicit (n + 2) := by
      rw [sum_range_succ, show (n + 3).choose (n + 2) = n + 3 from
        choose_succ_self_right (n + 2)]
    have hlastB :
        ∑ i ∈ range (n + 3), ((n + 3).choose i : ℚ) * bernoulli i =
          ∑ i ∈ range (n + 2), ((n + 3).choose i : ℚ) * bernoulli i +
            ((n + 3 : ℕ) : ℚ) * bernoulli (n + 2) := by
      rw [sum_range_succ, show (n + 3).choose (n + 2) = n + 3 from
        choose_succ_self_right (n + 2)]
    have hne : ((n + 3 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : n + 3 ≠ 0)
    have : bernoulliExplicit (n + 2) = bernoulli (n + 2) := by
      apply mul_left_cancel₀ hne
      linarith
    exact this

/-- `(p^s - 1) / p = p^{s-1} - 1` for `s ≥ 1`. -/
lemma pow_sub_one_div_p [hp : Fact p.Prime] {s : ℕ} (hs : 1 ≤ s) :
    (p ^ s - 1) / p = p ^ (s - 1) - 1 := by
  have hp0 := hp.out.pos
  have hpow : p * p ^ (s - 1) = p ^ s := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hs]
  have hdecomp : p * (p ^ (s - 1) - 1) + (p - 1) = p ^ s - 1 := by
    have h1 : 1 ≤ p ^ (s - 1) := Nat.one_le_pow _ _ hp0
    have h2 : 1 ≤ p := hp.out.one_le
    have h3 : 1 ≤ p ^ s := Nat.one_le_pow _ _ hp0
    zify [h1, h2, h3]
    have hpowZ : (p : ℤ) * (p ^ (s - 1) : ℤ) = (p ^ s : ℤ) := by exact_mod_cast hpow
    linear_combination hpowZ
  have hlt : p - 1 < p := Nat.sub_lt hp0 (by omega)
  rw [← hdecomp, Nat.mul_add_div hp0, Nat.div_eq_of_lt hlt, add_zero]

lemma two_pow_sub_one_ge (s : ℕ) : s ≤ 2 ^ s - 1 := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h2 : 1 ≤ 2 ^ s := Nat.one_le_pow _ _ (by decide)
    have : 2 ^ (s + 1) - 1 = 2 ^ s + (2 ^ s - 1) := by
      rw [pow_succ]
      omega
    rw [this]
    omega

lemma padicValNat_factorial_pow_sub_one [hp : Fact p.Prime] (s : ℕ) :
    s - 1 ≤ padicValNat p (p ^ s - 1).factorial := by
  rcases s with _ | s
  · simp
  have hp0 := hp.out.pos
  have hp2 : 2 ≤ p := hp.out.two_le
  rcases s with _ | s
  · exact Nat.zero_le _
  have hne : p ^ (s + 1 + 1) - 1 ≠ 0 := by
    have hle : p ≤ p ^ (s + 1 + 1) :=
      le_self_pow (show 1 ≤ p from hp.out.one_le) (by omega)
    have : 2 ≤ p ^ (s + 2) := hp2.trans (by simpa [Nat.succ_eq_add_one, add_assoc] using hle)
    omega
  have hlog : Nat.log p (p ^ (s + 2) - 1) < s + 2 :=
    Nat.log_lt_of_lt_pow hne (Nat.sub_lt (Nat.pow_pos hp0) (by omega))
  rw [padicValNat_factorial hlog]
  have hone : 1 ∈ Ico 1 (s + 2) := mem_Ico.mpr ⟨le_rfl, by omega⟩
  refine le_trans ?_ (single_le_sum (fun _ _ => Nat.zero_le _) hone)
  have hdiv : (p ^ (s + 2) - 1) / p ^ 1 = p ^ (s + 1) - 1 := by
    simpa [pow_one] using pow_sub_one_div_p (p := p) (s := s + 2) (by omega)
  rw [hdiv]
  have : s + 1 ≤ p ^ (s + 1) - 1 :=
    le_trans (two_pow_sub_one_ge (s + 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hp2 (s + 1)) 1)
  exact this

lemma padicValNat_succ_le_factorial [hp : Fact p.Prime] (k : ℕ) :
    padicValNat p (k + 1) ≤ padicValNat p k.factorial + 1 := by
  set s := padicValNat p (k + 1) with hs
  rcases Nat.eq_zero_or_pos s with hs0 | hspos
  · omega
  have hdiv : p ^ s ∣ k + 1 := by
    simpa [hs] using (pow_padicValNat_dvd (p := p) (n := k + 1))
  have hge : p ^ s ≤ k + 1 := Nat.le_of_dvd (Nat.succ_pos k) hdiv
  have hk : p ^ s - 1 ≤ k := by omega
  have hmono : padicValNat p (p ^ s - 1).factorial ≤ padicValNat p k.factorial := by
    have hdvd : p ^ padicValNat p (p ^ s - 1).factorial ∣ k.factorial :=
      pow_padicValNat_dvd.trans (factorial_dvd_factorial hk)
    exact padicValNat_le_of_dvd (factorial_ne_zero _) hdvd
  have := padicValNat_factorial_pow_sub_one (p := p) s
  omega

lemma padicValRat_of_int_nonneg (z : ℤ) :
    (0 : ℤ) ≤ padicValRat p (z : ℚ) := by
  rw [padicValRat_intCast]
  exact Nat.cast_nonneg _

lemma padicValRat_of_nat_nonneg (n : ℕ) :
    (0 : ℤ) ≤ padicValRat p (n : ℚ) := by
  rw [padicValRat_natCast]
  exact Nat.cast_nonneg _

lemma padicValRat_neg_one_pow (k : ℕ) :
    padicValRat p ((-1 : ℚ) ^ k) = 0 := by
  have h : ((-1 : ℚ) ^ k) = 1 ∨ ((-1 : ℚ) ^ k) = -1 := by
    rcases Nat.even_or_odd k with h | h
    · left; exact Even.neg_one_pow h
    · right; exact Odd.neg_one_pow h
  rcases h with h | h
  · simp [h]
  · rw [h, padicValRat.neg, padicValRat.one]

lemma padicValRat_stirlingSum_ge_factorial [hp : Fact p.Prime] {k n : ℕ}
    (hz : (stirlingSum k n : ℚ) ≠ 0) :
    padicValRat p (k.factorial : ℚ) ≤ padicValRat p (stirlingSum k n : ℚ) := by
  have hform : (stirlingSum k n : ℚ) =
      ((-1 : ℚ) ^ k) * (k.factorial : ℚ) * (stirlingSecond n k : ℚ) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) (stirlingSum_eq n k)
    simpa [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast] using h
  have hfac0 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (factorial_ne_zero _)
  have hsign0 : ((-1 : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hS0 : (stirlingSecond n k : ℚ) ≠ 0 := by
    intro h
    exact hz (by simp [hform, h])
  rw [hform, padicValRat.mul (mul_ne_zero hsign0 hfac0) hS0,
    padicValRat.mul hsign0 hfac0, padicValRat_neg_one_pow]
  have hSn : (0 : ℤ) ≤ padicValRat p (stirlingSecond n k : ℚ) :=
    padicValRat_of_nat_nonneg _
  linarith

lemma padicValRat_bernoulli_ge [hp : Fact p.Prime] (n : ℕ) :
    bernoulli n = 0 ∨ (-1 : ℤ) ≤ padicValRat p (bernoulli n) := by
  rw [← bernoulliExplicit_eq]
  by_cases h0 : bernoulliExplicit n = 0
  · exact Or.inl h0
  · right
    have hterm : ∀ k ∈ range (n + 1),
        (fun k => (stirlingSum k n : ℚ) / (k + 1 : ℚ)) k ≠ 0 →
          (-1 : ℤ) ≤ padicValRat p ((stirlingSum k n : ℚ) / (k + 1 : ℚ)) := by
      intro k hk hnz
      have hz : (stirlingSum k n : ℚ) ≠ 0 := by
        intro h; exact hnz (by simp [h])
      have hk0 : (k + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      rw [padicValRat.div hz hk0]
      have hI := padicValRat_stirlingSum_ge_factorial (p := p) hz
      have hden : padicValRat p (k + 1 : ℚ) ≤ padicValRat p (k.factorial : ℚ) + 1 := by
        have hk1 : (k + 1 : ℚ) = ((k + 1 : ℕ) : ℚ) := by norm_cast
        rw [hk1, padicValRat_natCast, padicValRat_natCast]
        exact_mod_cast padicValNat_succ_le_factorial (p := p) k
      linarith
    simpa [bernoulliExplicit] using
      padicValRat_sum_ge (range (n + 1))
        (fun k => (stirlingSum k n : ℚ) / (k + 1 : ℚ)) (-1) hterm (by
          simpa [bernoulliExplicit] using h0)

lemma Usum_zero_diag (N : ℕ) : Usum 0 N N = 2 * (N : ℤ) ^ 2 := by
  rw [Usum_zero]; ring

lemma Usum_one_diag (N : ℕ) :
    Usum 1 N N = (5 : ℤ) * (N : ℤ) ^ 2 * ((N : ℤ) ^ 2 - 1) / 6 := by
  rw [Usum_one]; ring

lemma padicValRat_Usum_zero [hp : Fact p.Prime] (hp5 : 5 ≤ p) {N : ℕ}
    (hN : N ≠ 0) :
    (2 : ℤ) * padicValNat p N ≤ padicValRat p (Usum 0 N N : ℚ) ∨ Usum 0 N N = 0 := by
  rw [Usum_zero_diag]
  have h2 : padicValRat p (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from rfl, padicValRat_natCast]
    exact_mod_cast padicValNat.eq_zero_of_not_dvd (fun hdiv => by
      have : p ≤ 2 := Nat.le_of_dvd (by decide) hdiv
      omega)
  have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have h20 : (2 : ℚ) ≠ 0 := by norm_num
  have hform : ((2 * (N : ℤ) ^ 2 : ℤ) : ℚ) = (2 : ℚ) * (N : ℚ) ^ 2 := by
    push_cast; rfl
  by_cases h0 : (2 : ℚ) * (N : ℚ) ^ 2 = 0
  · exact Or.inr (by
      have : (2 * (N : ℤ) ^ 2 : ℤ) = 0 := by exact_mod_cast h0
      simpa [Usum_zero_diag] using this)
  · left
    rw [hform, padicValRat.mul h20 (pow_ne_zero 2 hN0), padicValRat.pow hN0, h2,
      padicValRat_natCast]
    simp

lemma padicValRat_two_eq_zero [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    padicValRat p (2 : ℚ) = 0 := by
  rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from rfl, padicValRat_natCast]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd (fun hdiv => by
    have : p ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    omega)

lemma padicValRat_six_eq_zero [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    padicValRat p (6 : ℚ) = 0 := by
  rw [show (6 : ℚ) = ((6 : ℕ) : ℚ) from rfl, padicValRat_natCast]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd (fun hdiv => by
    have hp6 : p ≤ 6 := Nat.le_of_dvd (by decide) hdiv
    have hprime := hp.out
    have hcases : p = 5 := by
      rcases hprime.eq_or_lt_of_le hp6 with h | h
      · exact h
      · have : p = 2 ∨ p = 3 := by
          have := hprime.eq_two_or_odd
          omega
        omega
    subst hcases
    exact (by decide : ¬(5 ∣ 6)) hdiv)

lemma zmod_of_val_sub [hp : Fact p.Prime] {a b : ℤ} {s : ℕ}
    (h : a = b ∨ (s : ℤ) ≤ padicValRat p ((a - b : ℤ) : ℚ)) :
    a ≡ b [ZMOD (p : ℤ) ^ s] := by
  rcases h with h | hval
  · simp [h]
  · by_cases hab : a = b
    · simp [hab]
    · have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
      have hcast : padicValRat p ((a - b : ℤ) : ℚ) = padicValInt p (a - b) :=
        padicValRat_intCast (z := a - b)
      have hs : s ≤ padicValInt p (a - b) := by
        have : (s : ℤ) ≤ (padicValInt p (a - b) : ℤ) := by
          rwa [hcast] at hval
        exact_mod_cast this
      have hdvd : (p : ℤ) ^ s ∣ a - b :=
        (padicValInt_dvd_iff (p := p) s (a - b)).mpr (Or.inr hs)
      rw [Int.modEq_iff_dvd, ← neg_sub]
      exact dvd_neg.mpr hdvd

lemma geometric_sum_neg (z : ℚ) (K : ℕ) (hz : z ≠ -1) :
    (1 + z) * ∑ k ∈ range K, (-z) ^ k = 1 - (-z) ^ K := by
  have hz1 : 1 + z ≠ 0 := fun h => hz (by linarith)
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, mul_add, ih, pow_succ]
    ring

lemma geometric_inv_partial (z : ℚ) (K : ℕ) (hz : z ≠ -1) :
    (1 + z)⁻¹ = ∑ k ∈ range K, (-z) ^ k + (-z) ^ K * (1 + z)⁻¹ := by
  have hz1 : 1 + z ≠ 0 := fun h => hz (by linarith)
  have hsum := geometric_sum_neg z K hz
  apply mul_left_cancel₀ hz1
  rw [mul_add, hsum]
  have hrem : (1 + z) * ((-z) ^ K * (1 + z)⁻¹) = (-z) ^ K := by
    rw [← mul_assoc, mul_comm (1 + z), mul_assoc, mul_inv_cancel₀ hz1, mul_one]
  rw [hrem]
  exact (mul_inv_cancel₀ hz1).trans (sub_add_cancel _ _).symm

noncomputable def faulhaber_term (k i : ℕ) : ℚ :=
  bernoulli i * ((k + 1).choose i : ℚ) / (k + 1 : ℚ)

lemma faulhaberPoly_coeff (k m : ℕ) :
    (faulhaberPoly k).coeff m =
      ∑ i ∈ range (k + 1),
        if m = k + 1 - i then faulhaber_term k i else 0 := by
  unfold faulhaberPoly
  rw [Polynomial.finset_sum_coeff]
  refine sum_congr rfl fun i hi => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, faulhaber_term]
  split_ifs <;> ring

lemma faulhaberPoly_coeff_val [hp : Fact p.Prime] (k m : ℕ) :
    (faulhaberPoly k).coeff m = 0 ∨
      (-1 : ℤ) - padicValRat p ((k + 1 : ℕ) : ℚ) ≤
        padicValRat p ((faulhaberPoly k).coeff m) := by
  rw [faulhaberPoly_coeff]
  set f : ℕ → ℚ := fun i => if m = k + 1 - i then faulhaber_term k i else 0
  by_cases h0 : ∑ i ∈ range (k + 1), f i = 0
  · exact Or.inl h0
  · right
    refine padicValRat_sum_ge (range (k + 1)) f
      ((-1 : ℤ) - padicValRat p ((k + 1 : ℕ) : ℚ)) ?_ h0
    intro i hi hfi
    have hm : m = k + 1 - i := by
      by_contra hne
      simp [f, hne] at hfi
    have hfi' : faulhaber_term k i ≠ 0 := by
      simpa [f, hm] using hfi
    unfold faulhaber_term at hfi'
    have hk10 : (k + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hB0 : bernoulli i ≠ 0 := by
      intro h; exact hfi' (by simp [h])
    have hC0 : ((k + 1).choose i : ℚ) ≠ 0 := by
      intro h; exact hfi' (by simp [h])
    have hBge : (-1 : ℤ) ≤ padicValRat p (bernoulli i) :=
      (padicValRat_bernoulli_ge (p := p) i).resolve_left hB0
    have hf : f i = faulhaber_term k i := by simp [f, hm]
    rw [hf, faulhaber_term, padicValRat.div (mul_ne_zero hB0 hC0) hk10,
      padicValRat.mul hB0 hC0]
    have hCge : (0 : ℤ) ≤ padicValRat p ((k + 1).choose i : ℚ) :=
      padicValRat_of_nat_nonneg _
    have hk1 : (k + 1 : ℚ) = ((k + 1 : ℕ) : ℚ) := by norm_cast
    rw [hk1]
    linarith

lemma natDegree_X_mul_X_add_one :
    (Polynomial.X * (Polynomial.X + 1) : Polynomial ℚ).natDegree = 2 := by
  have h : (Polynomial.X * (Polynomial.X + 1) : Polynomial ℚ) =
      (Polynomial.X ^ 2 + Polynomial.X : Polynomial ℚ) := by ring
  rw [h]
  have hlt : (Polynomial.X : Polynomial ℚ).natDegree <
      (Polynomial.X ^ 2 : Polynomial ℚ).natDegree := by
    rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]; norm_num
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt,
    Polynomial.natDegree_X_pow]

lemma gOddPoly_natDegree_le (j : ℕ) : (gOddPoly j).natDegree ≤ 2 * j + 1 := by
  have h1 : (Polynomial.C 2 * Polynomial.X + 1 : Polynomial ℚ).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    have : (Polynomial.C 2 * Polynomial.X : Polynomial ℚ).natDegree ≤ 1 := by
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      simp
    simp [this]
  have hpow : ((Polynomial.X * (Polynomial.X + 1) : Polynomial ℚ) ^ j).natDegree ≤ 2 * j := by
    refine (Polynomial.natDegree_pow_le).trans ?_
    rw [natDegree_X_mul_X_add_one, Nat.mul_comm]
  unfold gOddPoly
  refine (Polynomial.natDegree_mul_le).trans ?_
  linarith [h1, hpow]

lemma gEvenPoly_natDegree_le (j : ℕ) : (gEvenPoly j).natDegree ≤ 2 * j := by
  unfold gEvenPoly
  refine (Polynomial.natDegree_pow_le).trans ?_
  rw [natDegree_X_mul_X_add_one, Nat.mul_comm]

lemma coeff_X_mul_X_add_one_pow (j i : ℕ) :
    ((Polynomial.X * (Polynomial.X + 1) : Polynomial ℚ) ^ j).coeff i =
      if j ≤ i then ((j.choose (i - j) : ℕ) : ℚ) else 0 := by
  rw [mul_pow, Polynomial.coeff_X_pow_mul']
  split_ifs with hji
  · rw [Polynomial.coeff_X_add_one_pow]
  · rfl

lemma gEvenPoly_coeff (j i : ℕ) :
    (gEvenPoly j).coeff i =
      if j ≤ i then ((j.choose (i - j) : ℕ) : ℚ) else 0 := by
  simpa [gEvenPoly] using coeff_X_mul_X_add_one_pow j i

lemma gOddPoly_coeff (j i : ℕ) :
    (gOddPoly j).coeff i =
      (2 : ℚ) * (if 1 ≤ i then (gEvenPoly j).coeff (i - 1) else 0) +
        (gEvenPoly j).coeff i := by
  simp only [gOddPoly, gEvenPoly]
  rw [add_mul, one_mul, Polynomial.coeff_add, mul_assoc, Polynomial.coeff_C_mul]
  rcases i with _ | i
  · simp [Polynomial.coeff_X_mul_zero]
  · rw [Polynomial.coeff_X_mul]
    simp [Nat.succ_eq_add_one]

lemma gEvenPoly_coeff_eq_nat (j i : ℕ) :
    ∃ n : ℕ, (gEvenPoly j).coeff i = (n : ℚ) := by
  rw [gEvenPoly_coeff]
  split_ifs
  · exact ⟨j.choose (i - j), rfl⟩
  · exact ⟨0, by simp⟩

lemma gOddPoly_coeff_eq_int (j i : ℕ) :
    ∃ z : ℤ, (gOddPoly j).coeff i = (z : ℚ) := by
  obtain ⟨n1, h1⟩ := gEvenPoly_coeff_eq_nat j (i - 1)
  obtain ⟨n2, h2⟩ := gEvenPoly_coeff_eq_nat j i
  rw [gOddPoly_coeff, h1, h2]
  split_ifs
  · refine ⟨2 * (n1 : ℤ) + n2, by push_cast; ring⟩
  · refine ⟨n2, by simp⟩

lemma padicValRat_gEven_coeff [hp : Fact p.Prime] (j i : ℕ) :
    (gEvenPoly j).coeff i = 0 ∨
      (0 : ℤ) ≤ padicValRat p ((gEvenPoly j).coeff i) := by
  obtain ⟨n, hn⟩ := gEvenPoly_coeff_eq_nat j i
  by_cases h0 : (gEvenPoly j).coeff i = 0
  · exact Or.inl h0
  · right; rw [hn]; exact padicValRat_of_nat_nonneg n

lemma padicValRat_gOdd_coeff [hp : Fact p.Prime] (j i : ℕ) :
    (gOddPoly j).coeff i = 0 ∨
      (0 : ℤ) ≤ padicValRat p ((gOddPoly j).coeff i) := by
  obtain ⟨z, hz⟩ := gOddPoly_coeff_eq_int j i
  by_cases h0 : (gOddPoly j).coeff i = 0
  · exact Or.inl h0
  · right; rw [hz]; exact padicValRat_of_int_nonneg z

lemma sumPoly_coeff (g : Polynomial ℚ) (m : ℕ) :
    (sumPoly g).coeff m =
      ∑ k ∈ range (g.natDegree + 1), g.coeff k * (faulhaberPoly k).coeff m := by
  unfold sumPoly
  rw [Polynomial.finset_sum_coeff]
  refine sum_congr rfl fun k hk => ?_
  rw [Polynomial.coeff_C_mul]

lemma padicValRat_mul_ge_add [hp : Fact p.Prime] {a b : ℚ} {A B : ℤ}
    (ha : a = 0 ∨ A ≤ padicValRat p a) (hb : b = 0 ∨ B ≤ padicValRat p b) :
    a * b = 0 ∨ A + B ≤ padicValRat p (a * b) := by
  by_cases ha0 : a = 0
  · exact Or.inl (by simp [ha0])
  · by_cases hb0 : b = 0
    · exact Or.inl (by simp [hb0])
    · right
      rw [padicValRat.mul ha0 hb0]
      have hA : A ≤ padicValRat p a := ha.resolve_left ha0
      have hB : B ≤ padicValRat p b := hb.resolve_left hb0
      linarith

lemma padicValRat_nat_le_log (n : ℕ) :
    padicValRat p (n : ℚ) ≤ Nat.log p n := by
  rw [padicValRat_natCast]
  exact_mod_cast padicValNat_le_nat_log n

lemma padicValRat_sumPoly_coeff_ge [hp : Fact p.Prime] (g : Polynomial ℚ) (m : ℕ)
    (hg : ∀ k, g.coeff k = 0 ∨ (0 : ℤ) ≤ padicValRat p (g.coeff k)) :
    (sumPoly g).coeff m = 0 ∨
      (-1 : ℤ) - (Nat.log p (g.natDegree + 1) : ℤ) ≤
        padicValRat p ((sumPoly g).coeff m) := by
  rw [sumPoly_coeff]
  set f : ℕ → ℚ := fun k => g.coeff k * (faulhaberPoly k).coeff m
  by_cases h0 : ∑ k ∈ range (g.natDegree + 1), f k = 0
  · exact Or.inl h0
  · right
    refine padicValRat_sum_ge (range (g.natDegree + 1)) f
      ((-1 : ℤ) - (Nat.log p (g.natDegree + 1) : ℤ)) ?_ h0
    intro k hk hf0
    have hmul := padicValRat_mul_ge_add (A := 0)
      (B := (-1 : ℤ) - padicValRat p ((k + 1 : ℕ) : ℚ))
      (hg k) (faulhaberPoly_coeff_val (p := p) k m)
    have hne : f k ≠ 0 := hf0
    have hge := hmul.resolve_left (by simpa [f] using hne)
    have hkle : k ≤ g.natDegree := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hk1le : k + 1 ≤ g.natDegree + 1 := Nat.add_le_add_right hkle 1
    have hvlog : padicValRat p ((k + 1 : ℕ) : ℚ) ≤ Nat.log p (g.natDegree + 1) := by
      refine (padicValRat_nat_le_log (k + 1)).trans ?_
      exact_mod_cast Nat.log_mono_right hk1le
    linarith

lemma QsumPoly_coeff_lt_two {j m : ℕ} (hj : 1 ≤ j) (hm : m < 2) :
    (QsumPoly j).coeff m = 0 := by
  have hdiv := even_and_eval_zero_dvd_X_sq (QsumPoly_even j) (QsumPoly_isRoot_zero j)
  exact (Polynomial.X_pow_dvd_iff.mp hdiv) m hm

lemma padicValRat_eval_ge [hp : Fact p.Prime] (f : Polynomial ℚ) {N d : ℕ}
    (K : ℤ) (hN : N ≠ 0)
    (hlow : ∀ m < d, f.coeff m = 0)
    (hcoeff : ∀ m, f.coeff m = 0 ∨ K ≤ padicValRat p (f.coeff m))
    (hsum : f.eval (N : ℚ) ≠ 0) :
    K + d * (padicValNat p N : ℤ) ≤ padicValRat p (f.eval (N : ℚ)) := by
  have heval : f.eval (N : ℚ) =
      ∑ m ∈ range (f.natDegree + 1), f.coeff m * (N : ℚ) ^ m :=
    Polynomial.eval_eq_sum_range _
  rw [heval] at hsum ⊢
  refine padicValRat_sum_ge (range (f.natDegree + 1))
    (fun m => f.coeff m * (N : ℚ) ^ m)
    (K + d * (padicValNat p N : ℤ)) ?_ hsum
  intro m hm hterm
  have hc0 : f.coeff m ≠ 0 := by
    intro h; exact hterm (by simp [h])
  have hge := (hcoeff m).resolve_left hc0
  have hmge : d ≤ m := by
    by_contra hlt
    exact hc0 (hlow m (lt_of_not_ge hlt))
  have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [padicValRat.mul hc0 (pow_ne_zero _ hN0), padicValRat.pow hN0, padicValRat_natCast]
  have : (m : ℤ) * padicValNat p N ≥ (d : ℤ) * padicValNat p N :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hmge) (Nat.cast_nonneg _)
  linarith

lemma gOdd_natDegree_succ (j : ℕ) : (gOddPoly j).natDegree + 1 ≤ 2 * j + 2 := by
  have := gOddPoly_natDegree_le j
  omega

lemma gEven_natDegree_succ (j : ℕ) : (gEvenPoly j).natDegree + 1 ≤ 2 * j + 1 := by
  have := gEvenPoly_natDegree_le j
  omega

lemma log_le_of_le {a b : ℕ} (h : a ≤ b) : Nat.log p a ≤ Nat.log p b :=
  Nat.log_mono_right h

lemma padicValRat_Qsum_eval [hp : Fact p.Prime] {j N : ℕ} (hj : 1 ≤ j) (hN : N ≠ 0) :
    (QsumPoly j).eval (N : ℚ) = 0 ∨
      (2 : ℤ) * padicValNat p N - 1 - Nat.log p (2 * j + 2) ≤
        padicValRat p ((QsumPoly j).eval (N : ℚ)) := by
  by_cases h0 : (QsumPoly j).eval (N : ℚ) = 0
  · exact Or.inl h0
  · right
    have hcoeff : ∀ m, (QsumPoly j).coeff m = 0 ∨
        (-1 : ℤ) - Nat.log p ((gOddPoly j).natDegree + 1) ≤
          padicValRat p ((QsumPoly j).coeff m) := by
      intro m
      simpa [QsumPoly] using
        padicValRat_sumPoly_coeff_ge (p := p) (gOddPoly j) m
          (fun k => padicValRat_gOdd_coeff (p := p) j k)
    have hcoeff' : ∀ m, (QsumPoly j).coeff m = 0 ∨
        (-1 : ℤ) - Nat.log p (2 * j + 2) ≤
          padicValRat p ((QsumPoly j).coeff m) := by
      intro m
      rcases hcoeff m with h | h
      · exact Or.inl h
      · right
        have : (Nat.log p ((gOddPoly j).natDegree + 1) : ℤ) ≤ Nat.log p (2 * j + 2) :=
          Nat.cast_le.mpr (log_le_of_le (p := p) (gOdd_natDegree_succ j))
        linarith
    have := padicValRat_eval_ge (p := p) (QsumPoly j) (K := (-1 : ℤ) - Nat.log p (2 * j + 2))
      (d := 2) hN (fun m hm => QsumPoly_coeff_lt_two hj hm) hcoeff' h0
    convert this using 1
    ring

lemma PsumPoly_X_dvd {j : ℕ} (hj : 1 ≤ j) : Polynomial.X ∣ PsumPoly j :=
  dvd_X_of_eval_zero _ (PsumPoly_eval_zero j)

lemma PsumPoly_coeff_lt_one {j m : ℕ} (hj : 1 ≤ j) (hm : m < 1) :
    (PsumPoly j).coeff m = 0 := by
  have hdiv := PsumPoly_X_dvd hj
  have : m = 0 := by omega
  subst this
  simpa [Polynomial.eval] using PsumPoly_eval_zero j

lemma padicValRat_Psum_eval [hp : Fact p.Prime] {j N : ℕ} (hj : 1 ≤ j) (hN : N ≠ 0) :
    (PsumPoly j).eval (N : ℚ) = 0 ∨
      (1 : ℤ) * padicValNat p N - 1 - Nat.log p (2 * j + 1) ≤
        padicValRat p ((PsumPoly j).eval (N : ℚ)) := by
  by_cases h0 : (PsumPoly j).eval (N : ℚ) = 0
  · exact Or.inl h0
  · right
    have hcoeff : ∀ m, (PsumPoly j).coeff m = 0 ∨
        (-1 : ℤ) - Nat.log p ((gEvenPoly j).natDegree + 1) ≤
          padicValRat p ((PsumPoly j).coeff m) := by
      intro m
      simpa [PsumPoly] using
        padicValRat_sumPoly_coeff_ge (p := p) (gEvenPoly j) m
          (fun k => padicValRat_gEven_coeff (p := p) j k)
    have hcoeff' : ∀ m, (PsumPoly j).coeff m = 0 ∨
        (-1 : ℤ) - Nat.log p (2 * j + 1) ≤
          padicValRat p ((PsumPoly j).coeff m) := by
      intro m
      rcases hcoeff m with h | h
      · exact Or.inl h
      · right
        have : (Nat.log p ((gEvenPoly j).natDegree + 1) : ℤ) ≤ Nat.log p (2 * j + 1) :=
          Nat.cast_le.mpr (log_le_of_le (p := p) (gEven_natDegree_succ j))
        linarith
    have := padicValRat_eval_ge (p := p) (PsumPoly j) (K := (-1 : ℤ) - Nat.log p (2 * j + 1))
      (d := 1) hN (fun m hm => PsumPoly_coeff_lt_one hj hm) hcoeff' h0
    convert this using 1
    ring

lemma padicValRat_Usum_ge [hp : Fact p.Prime] {j N : ℕ} (hj : 1 ≤ j) (hN : N ≠ 0) :
    (Usum j N N : ℚ) = 0 ∨
      (2 : ℤ) * padicValNat p N - 1 - Nat.log p (2 * j + 2) ≤
        padicValRat p (Usum j N N : ℚ) := by
  rw [Usum_eq_Q_add_B_mul_P]
  set Qv := (QsumPoly j).eval (N : ℚ)
  set Pv := (PsumPoly j).eval (N : ℚ)
  set S := Qv + (N : ℚ) * Pv
  by_cases hS : S = 0
  · exact Or.inl hS
  · right
    have hQ := padicValRat_Qsum_eval (p := p) hj hN
    have hP := padicValRat_Psum_eval (p := p) hj hN
    have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    have hlog : (Nat.log p (2 * j + 1) : ℤ) ≤ Nat.log p (2 * j + 2) :=
      Nat.cast_le.mpr (log_le_of_le (p := p) (Nat.le_succ _))
    by_cases hQ0 : Qv = 0
    · by_cases hP0 : Pv = 0
      · exact (hS (by simp [S, hQ0, hP0])).elim
      · have hPge := hP.resolve_left hP0
        have : S = (N : ℚ) * Pv := by simp [S, hQ0]
        rw [this, padicValRat.mul hN0 hP0, padicValRat_natCast]
        linarith
    · have hQge := hQ.resolve_left hQ0
      by_cases hP0 : Pv = 0
      · have : S = Qv := by simp [S, hP0]
        rwa [this]
      · have hPge := hP.resolve_left hP0
        have hNPv : (N : ℚ) * Pv ≠ 0 := mul_ne_zero hN0 hP0
        have hvNP : (2 : ℤ) * padicValNat p N - 1 - Nat.log p (2 * j + 2) ≤
            padicValRat p ((N : ℚ) * Pv) := by
          rw [padicValRat.mul hN0 hP0, padicValRat_natCast]
          linarith
        exact le_trans (le_min hQge hvNP) (padicValRat.min_le_padicValRat_add hS)

lemma two_mul_b_m_int_one_nat (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℕ) * (2 * n - 1).choose n = (2 * n).choose n :=
  two_mul_choose_two_mul_sub_one n hn

/-- Central binomial form of the `m = 1` sequence. -/
lemma b_m_int_one_eq_central_div (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℤ) * b_m_int 1 n = ((2 * n).choose n : ℤ) :=
  two_mul_b_m_int_one n hn

lemma choose_two_mul_pos (N : ℕ) (hN : 1 ≤ N) : 0 < (2 * N).choose N :=
  Nat.choose_pos (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 2))

lemma central_ratio (N : ℕ) (hp0 : 0 < p) (hN : 1 ≤ N) :
    (((2 * N * p).choose (N * p) : ℚ) / ((2 * N).choose N : ℚ)) ^ 2 =
      ∏ i ∈ Icc 1 (p - 1),
        ∏ t ∈ range N,
          ((pbeta p i + alphaN (N + t) * (p : ℤ) ^ 2 : ℤ) : ℚ) /
          ((pbeta p i + alphaN t * (p : ℤ) ^ 2 : ℤ) : ℚ) := by
  have hBA : N ≤ 2 * N := by omega
  have h := choose_ratio_sq (q := p) (A := 2 * N) (B := N) hp0 hBA
  have hA : p * (2 * N) = 2 * N * p := by ring
  have hB : p * N = N * p := by ring
  have hC : 2 * N - N = N := by omega
  simpa [hA, hB, hC] using h

/-- The paired increment `y_{i,t}`. -/
noncomputable def yterm (N i t : ℕ) : ℚ :=
  ((N : ℚ) * (2 * (t : ℚ) + N + 1) * (p : ℚ) ^ 2) /
    ((pbeta p i : ℚ) + (alphaN t : ℚ) * (p : ℚ) ^ 2)

lemma pair_den_ne_zero (i t : ℕ) (hp0 : 0 < p) (hi : i ∈ Icc 1 (p - 1)) :
    ((pbeta p i + alphaN t * (p : ℤ) ^ 2 : ℤ) : ℚ) ≠ 0 := by
  have hilt : i < p := mem_Icc_pred_lt hp0 hi
  have hi0 : 0 < i := (mem_Icc.mp hi).1
  have hL : ((i + t * p : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.add_pos_left hi0 _).ne'
  have hR : (((p - i) + t * p : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.add_pos_left (Nat.sub_pos_of_lt hilt) _).ne'
  have hdenZ := pair_prod_eq p i t hilt.le
  have hcast : ((pbeta p i + alphaN t * (p : ℤ) ^ 2 : ℤ) : ℚ) =
      ((i + t * p : ℕ) : ℚ) * (((p - i) + t * p : ℕ) : ℚ) := by
    have := congrArg (fun z : ℤ => (z : ℚ)) hdenZ
    simpa [Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_natCast] using this.symm
  rw [hcast]
  exact mul_ne_zero hL hR

lemma yterm_eq_ratio (N i t : ℕ) (hp0 : 0 < p) (hi : i ∈ Icc 1 (p - 1)) :
    ((pbeta p i + alphaN (N + t) * (p : ℤ) ^ 2 : ℤ) : ℚ) /
        ((pbeta p i + alphaN t * (p : ℤ) ^ 2 : ℤ) : ℚ) =
      1 + yterm (p := p) N i t := by
  have hden := pair_den_ne_zero (p := p) i t hp0 hi
  have hsub := pair_ratio_num_sub p N t i
  have hcast :
      ((pbeta p i + alphaN (N + t) * (p : ℤ) ^ 2 : ℤ) : ℚ) -
        ((pbeta p i + alphaN t * (p : ℤ) ^ 2 : ℤ) : ℚ) =
      (N : ℚ) * (2 * (t : ℚ) + N + 1) * (p : ℚ) ^ 2 := by
    have := congrArg (fun z : ℤ => (z : ℚ)) hsub
    simpa [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_pow, Int.cast_natCast] using this
  set denZ := ((pbeta p i + alphaN t * (p : ℤ) ^ 2 : ℤ) : ℚ)
  set numZ := ((pbeta p i + alphaN (N + t) * (p : ℤ) ^ 2 : ℤ) : ℚ)
  set numY := (N : ℚ) * (2 * (t : ℚ) + N + 1) * (p : ℚ) ^ 2
  have hden_eq : denZ = (pbeta p i : ℚ) + (alphaN t : ℚ) * (p : ℚ) ^ 2 := by
    simp [denZ, Int.cast_add, Int.cast_mul, Int.cast_pow]
  have hsum' : numZ = denZ + numY := by
    have := sub_eq_iff_eq_add'.mp hcast
    simpa [numZ, denZ, numY] using this
  unfold yterm
  have : numZ / denZ = 1 + numY / denZ := by
    rw [hsum', add_div, div_self hden]
  simpa [denZ, numZ, numY, hden_eq] using this

lemma alphaN_nonneg (t : ℕ) : 0 ≤ (alphaN t : ℚ) := by
  simp [alphaN]; exact mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast Nat.succ_pos t |>.le)

lemma yterm_den_ne_zero (N i t : ℕ) (hp0 : 0 < p) (hi : i ∈ Icc 1 (p - 1)) :
    (pbeta p i : ℚ) + (alphaN t : ℚ) * (p : ℚ) ^ 2 ≠ 0 := by
  have hden := pair_den_ne_zero (p := p) i t hp0 hi
  convert hden using 1
  simp [Int.cast_add, Int.cast_mul, Int.cast_pow]

lemma padicValRat_yterm_ge [hp : Fact p.Prime] (hp5 : 5 ≤ p) {N i t : ℕ}
    (hN : N ≠ 0) (hi : i ∈ Icc 1 (p - 1)) :
    yterm (p := p) N i t = 0 ∨
      (padicValNat p N : ℤ) + 2 ≤ padicValRat p (yterm (p := p) N i t) := by
  unfold yterm
  set den := (pbeta p i : ℚ) + (alphaN t : ℚ) * (p : ℚ) ^ 2
  have hden0 : den ≠ 0 := yterm_den_ne_zero (p := p) N i t hp.out.pos hi
  have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hlin : (2 * (t : ℚ) + N + 1 : ℚ) = 0 ∨
      (0 : ℤ) ≤ padicValRat p (2 * (t : ℚ) + N + 1) := by
    have : ∃ z : ℤ, (2 * (t : ℚ) + N + 1) = (z : ℚ) :=
      ⟨2 * (t : ℤ) + N + 1, by push_cast; ring⟩
    obtain ⟨z, hz⟩ := this
    by_cases h0 : (2 * (t : ℚ) + N + 1) = 0
    · exact Or.inl h0
    · right; rw [hz]; exact padicValRat_of_int_nonneg z
  by_cases hnum0 : (N : ℚ) * (2 * (t : ℚ) + N + 1) * (p : ℚ) ^ 2 = 0
  · exact Or.inl (by simp [hnum0])
  · right
    have hlin0 : (2 * (t : ℚ) + N + 1) ≠ 0 := by
      intro h; exact hnum0 (by simp [h])
    have hlinv : (0 : ℤ) ≤ padicValRat p (2 * (t : ℚ) + N + 1) :=
      hlin.resolve_left hlin0
    rw [padicValRat.div hnum0 hden0, padicValRat.mul (mul_ne_zero hN0 hlin0) (pow_ne_zero 2 hp0),
      padicValRat.mul hN0 hlin0, padicValRat.pow hp0, padicValRat_natCast, padicValRat_natCast]
    have hdenv : padicValRat p den = 0 := by
      -- den = β + α p², v(β)=0, v(α p²)≥2, so v(den)=0
      have hβ0 : (pbeta p i : ℚ) ≠ 0 := pbeta_ne_zero (p := p) hp.out.pos hi
      have hβv : padicValRat p (pbeta p i : ℚ) = 0 := padicValRat_pbeta (p := p) hp.out hi
      by_cases hα0 : (alphaN t : ℚ) * (p : ℚ) ^ 2 = 0
      · simp [den, hα0, hβv]
      · have hαne : (alphaN t : ℚ) ≠ 0 := by
          intro h; exact hα0 (by simp [h])
        have hpv : padicValRat p (p : ℚ) = 1 := by
          rw [padicValRat_natCast, padicValNat.self hp.out.one_lt]; norm_cast
        have heqα : padicValRat p ((alphaN t : ℚ) * (p : ℚ) ^ 2) =
            padicValRat p (alphaN t : ℚ) + 2 := by
          rw [padicValRat.mul hαne (pow_ne_zero 2 hp0), padicValRat.pow hp0, hpv]
          ring
        have hv2 : (2 : ℤ) ≤ padicValRat p ((alphaN t : ℚ) * (p : ℚ) ^ 2) := by
          rw [heqα]
          linarith [padicValRat_of_int_nonneg (p := p) (alphaN t)]
        have hlt : padicValRat p (pbeta p i : ℚ) <
            padicValRat p ((alphaN t : ℚ) * (p : ℚ) ^ 2) := by
          rw [hβv]; linarith
        have := padicValRat.add_eq_of_lt (p := p) hden0 hβ0 hα0 hlt
        simpa [den, hβv] using this
    simp [hdenv]
    linarith

lemma central_ratio_y (N : ℕ) (hp0 : 0 < p) (hN : 1 ≤ N) :
    (((2 * N * p).choose (N * p) : ℚ) / ((2 * N).choose N : ℚ)) ^ 2 =
      ∏ i ∈ Icc 1 (p - 1), ∏ t ∈ range N, (1 + yterm (p := p) N i t) := by
  rw [central_ratio (p := p) N hp0 hN]
  refine prod_congr rfl fun i hi => prod_congr rfl fun t ht => ?_
  exact yterm_eq_ratio (p := p) N i t hp0 hi

lemma sum_yterm_eq (N : ℕ) (hp0 : 0 < p) :
    ∑ i ∈ Icc 1 (p - 1), ∑ t ∈ range N, yterm (p := p) N i t =
      (N : ℚ) * (p : ℚ) ^ 2 *
        ∑ i ∈ Icc 1 (p - 1), ∑ t ∈ range N,
          (2 * (t : ℚ) + N + 1) /
            ((pbeta p i : ℚ) + (alphaN t : ℚ) * (p : ℚ) ^ 2) := by
  simp only [yterm, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  refine sum_congr rfl fun t ht => ?_
  have hden := yterm_den_ne_zero (p := p) N i t hp0 hi
  field_simp [hden]

lemma choose_sub_eq_mul_ratio_sub (N : ℕ) (hN : 1 ≤ N) :
    ((2 * N * p).choose (N * p) : ℚ) - ((2 * N).choose N : ℚ) =
      ((2 * N).choose N : ℚ) *
        ((((2 * N * p).choose (N * p) : ℚ) / ((2 * N).choose N : ℚ)) - 1) := by
  have hC : ((2 * N).choose N : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_two_mul_pos N hN).ne'
  field_simp [hC]

lemma kazandzidis_of_ratio_val [hp : Fact p.Prime] (N : ℕ) (hN : 1 ≤ N) {s : ℕ}
    (hval : ((2 * N * p).choose (N * p) : ℚ) / ((2 * N).choose N : ℚ) = 1 ∨
      (s : ℤ) ≤ padicValRat p
        (((2 * N * p).choose (N * p) : ℚ) / ((2 * N).choose N : ℚ) - 1)) :
    ((2 * N * p).choose (N * p) : ℤ) ≡ ((2 * N).choose N : ℤ)
      [ZMOD (p : ℤ) ^ s] := by
  have hC : ((2 * N).choose N : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_two_mul_pos N hN).ne'
  have hdiff := choose_sub_eq_mul_ratio_sub (p := p) N hN
  have hcast : ((((2 * N * p).choose (N * p) : ℤ) - ((2 * N).choose N : ℤ) : ℤ) : ℚ) =
      ((2 * N * p).choose (N * p) : ℚ) - ((2 * N).choose N : ℚ) := by
    push_cast; rfl
  rcases hval with h1 | h1
  · have heq : ((2 * N * p).choose (N * p) : ℚ) = ((2 * N).choose N : ℚ) := by
      have h' := hdiff
      rw [h1, sub_self, mul_zero] at h'
      linarith
    have : ((2 * N * p).choose (N * p) : ℤ) = ((2 * N).choose N : ℤ) := by
      exact_mod_cast heq
    simp [this]
  · by_cases hz : ((2 * N * p).choose (N * p) : ℤ) = ((2 * N).choose N : ℤ)
    · simp [hz]
    · have hsub0 : ((2 * N * p).choose (N * p) : ℤ) - ((2 * N).choose N : ℤ) ≠ 0 :=
        sub_ne_zero.mpr hz
      have hsubQ : ((2 * N * p).choose (N * p) : ℚ) - ((2 * N).choose N : ℚ) ≠ 0 := by
        exact_mod_cast hsub0
      have hrat0 : ((2 * N * p).choose (N * p) : ℚ) / ((2 * N).choose N : ℚ) - 1 ≠ 0 := by
        intro h0
        exact hsubQ (by rw [hdiff, h0, mul_zero])
      have hval' : (s : ℤ) ≤
          padicValRat p ((((2 * N * p).choose (N * p) : ℤ) -
            ((2 * N).choose N : ℤ) : ℤ) : ℚ) := by
        rw [hcast, hdiff, padicValRat.mul hC hrat0]
        have : (0 : ℤ) ≤ padicValRat p ((2 * N).choose N : ℚ) :=
          padicValRat_of_nat_nonneg _
        linarith
      exact zmod_of_val_sub (p := p) (Or.inr hval')

/-- `1/(β+αp²) = β⁻¹ ∑_{k<K} (-αp²/β)^k + remainder`. -/
lemma inv_paired_geom (i t K : ℕ) (hp0 : 0 < p) (hi : i ∈ Icc 1 (p - 1)) :
    let β := (pbeta p i : ℚ)
    let α := (alphaN t : ℚ)
    let z := α * (p : ℚ) ^ 2 / β
    (β + α * (p : ℚ) ^ 2)⁻¹ =
      β⁻¹ * ∑ k ∈ range K, (-z) ^ k +
        β⁻¹ * (-z) ^ K * (1 + z)⁻¹ := by
  intro β α z
  have hβ : β ≠ 0 := pbeta_ne_zero (p := p) hp0 hi
  have hden : β + α * (p : ℚ) ^ 2 ≠ 0 :=
    yterm_den_ne_zero (p := p) 0 i t hp0 hi
  have hz : z ≠ -1 := by
    intro h
    have : β + α * (p : ℚ) ^ 2 = 0 := by
      have : β * (1 + z) = β + α * (p : ℚ) ^ 2 := by
        simp [z]; field_simp [hβ]
      rw [h] at this; linarith
    exact hden this
  have hfac : β + α * (p : ℚ) ^ 2 = β * (1 + z) := by
    simp [z]; field_simp [hβ]
  rw [hfac, mul_inv]
  conv_lhs => rw [geometric_inv_partial z K hz]
  rw [mul_add, mul_assoc]

/-! Completing the central Kazandzidis congruence. -/

lemma padicValRat_p_pow [hp : Fact p.Prime] (t : ℕ) :
    padicValRat p ((p : ℚ) ^ t) = t := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  rw [padicValRat.pow hp0, padicValRat_natCast, padicValNat.self hp.out.one_lt]
  simp

lemma padicValRat_inv_pbeta [hp : Fact p.Prime] {i : ℕ} (hi : i ∈ Icc 1 (p - 1)) :
    padicValRat p ((pbeta p i : ℚ)⁻¹) = 0 := by
  have hβ := pbeta_ne_zero (p := p) hp.out.pos hi
  rw [padicValRat.inv (pbeta p i : ℚ), padicValRat_pbeta (p := p) hp.out hi]
  simp

lemma U0_eq (N : ℕ) :
    ∑ t ∈ range N, (2 * (t : ℚ) + N + 1) = (2 : ℚ) * (N : ℚ) ^ 2 := by
  have h := Usum_zero_diag N
  have := congrArg (fun z : ℤ => (z : ℚ)) h
  simp only [Usum, pow_zero, mul_one, Int.cast_sum, Int.cast_add, Int.cast_mul,
    Int.cast_pow, Int.cast_ofNat, Int.cast_natCast] at this
  simpa using this

lemma padicValRat_four_eq_zero [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    padicValRat p (4 : ℚ) = 0 := by
  rw [show (4 : ℚ) = ((4 : ℕ) : ℚ) from rfl, padicValRat_natCast]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd (fun hdiv => by
    have : p ≤ 4 := Nat.le_of_dvd (by decide) hdiv
    omega)

lemma leading_y_val [hp : Fact p.Prime] (hp5 : 5 ≤ p) {N : ℕ} (hN : N ≠ 0) :
    (∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / k) = 0 ∨
      (3 + 3 * padicValNat p N : ℤ) ≤
        padicValRat p
          ((4 : ℚ) * (N : ℚ) ^ 3 * (p : ℚ) *
            (∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / k)) := by
  set H := ∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / k
  have hH := padicValRat_harmonic_ge_two hp.out hp5
  rcases hH with hHg | hH0
  · right
    have hHne : H ≠ 0 := by
      intro h
      have hHg' : (2 : ℤ) ≤ padicValRat p H := hHg
      rw [h] at hHg'
      simp at hHg'
    have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
    have h4 : (4 : ℚ) ≠ 0 := by norm_num
    have hN3 : (N : ℚ) ^ 3 ≠ 0 := pow_ne_zero 3 hN0
    have hmul1 : (4 : ℚ) * (N : ℚ) ^ 3 ≠ 0 := mul_ne_zero h4 hN3
    have hmul2 : (4 : ℚ) * (N : ℚ) ^ 3 * (p : ℚ) ≠ 0 := mul_ne_zero hmul1 hp0
    rw [padicValRat.mul hmul2 hHne, padicValRat.mul hmul1 hp0,
      padicValRat.mul h4 hN3, padicValRat.pow hN0, padicValRat_natCast,
      padicValRat_four_eq_zero hp5]
    have hpv : padicValRat p (p : ℚ) = 1 := by
      rw [padicValRat_natCast, padicValNat.self hp.out.one_lt]; norm_cast
    rw [hpv]
    have hHg' : (2 : ℤ) ≤ padicValRat p H := hHg
    have hvN : (0 : ℤ) ≤ padicValNat p N := Nat.cast_nonneg _
    have : (3 + 3 * padicValNat p N : ℤ) ≤
        (0 : ℤ) + 3 * padicValNat p N + 1 + padicValRat p H := by
      linarith [hHg']
    exact this
  · exact Or.inl hH0

lemma choose_central_mul_p_val [hp : Fact p.Prime] (N : ℕ) (hN : 1 ≤ N) :
    padicValNat p ((2 * N * p).choose (N * p)) =
      padicValNat p ((2 * N).choose N) := by
  have hBA : N ≤ 2 * N := by omega
  have h1 := sub_one_mul_padicValNat_choose_eq_sub_sum_digits
    (p := p) (k := N * p) (n := 2 * N * p) (Nat.mul_le_mul_right p hBA)
  have h2 := sub_one_mul_padicValNat_choose_eq_sub_sum_digits
    (p := p) (k := N) (n := 2 * N) hBA
  have hsub : 2 * N * p - N * p = N * p := by
    have hNN : 2 * N - N = N := by omega
    calc 2 * N * p - N * p = (2 * N - N) * p := (Nat.mul_sub_right_distrib (2 * N) N p).symm
      _ = N * p := by rw [hNN]
  have h2N : 2 * N - N = N := by omega
  have hdigN : (p.digits (N * p)).sum = (p.digits N).sum := by
    cases N with
    | zero => simp
    | succ N =>
      rw [mul_comm (N + 1), Nat.digits_base_mul hp.out.one_lt (Nat.succ_pos _)]
      simp
  have hdig2 : (p.digits (2 * N * p)).sum = (p.digits (2 * N)).sum := by
    have hpos : 0 < 2 * N := by omega
    rw [show 2 * N * p = (2 * N) * p from rfl, mul_comm (2 * N) p,
      Nat.digits_base_mul hp.out.one_lt hpos]
    simp
  rw [hsub, hdig2, hdigN] at h1
  rw [h2N] at h2
  have hp1 : 0 < p - 1 := by
    have := hp.out.two_le
    omega
  exact Nat.mul_left_cancel hp1 (by linarith [h1, h2])

/-! ## Rational exponential coefficients and the Frobenius identity -/

/-- Coefficients of `exp(∑ d_k x^k / k)` over `ℚ`. -/
noncomputable def expQ (d : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 =>
      (∑ j ∈ range (k + 1), d (j + 1) * expQ d (k - j)) / (k + 1 : ℚ)

lemma expQ_zero (d : ℕ → ℚ) : expQ d 0 = 1 := by simp [expQ]

lemma expQ_succ (d : ℕ → ℚ) (k : ℕ) :
    expQ d (k + 1) =
      (∑ j ∈ range (k + 1), d (j + 1) * expQ d (k - j)) / (k + 1 : ℚ) := by
  simp [expQ]

lemma expQ_mul_succ (d : ℕ → ℚ) (k : ℕ) :
    (k + 1 : ℚ) * expQ d (k + 1) =
      ∑ j ∈ range (k + 1), d (j + 1) * expQ d (k - j) := by
  have hk : (k + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [expQ_succ, mul_div_cancel₀ _ hk]

lemma expQ_mul (d : ℕ → ℚ) (n : ℕ) :
    (n : ℚ) * expQ d n =
      if n = 0 then 0
      else ∑ j ∈ range n, d (j + 1) * expQ d (n - 1 - j) := by
  rcases n with _ | n
  · simp
  · simpa using expQ_mul_succ d n

/-- `α_j(N) = [x^j] A_m(x)^N`. -/
noncomputable def alphaQ (m N j : ℕ) : ℚ :=
  expQ (fun k => (N : ℚ) * (coeff_of_log_gf_gen m k : ℚ)) j

lemma alphaQ_zero (m N : ℕ) : alphaQ m N 0 = 1 := expQ_zero _

lemma alphaQ_rec (m N k : ℕ) :
    (k + 1 : ℚ) * alphaQ m N (k + 1) =
      (N : ℚ) * ∑ j ∈ range (k + 1),
        (coeff_of_log_gf_gen m (j + 1) : ℚ) * alphaQ m N (k - j) := by
  unfold alphaQ
  rw [expQ_mul_succ]
  simp [mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Driving coefficients of the Frobenius remainder `G`. -/
def eDrive (m q j : ℕ) : ℤ :=
  if q = 0 then 0
  else if q ∣ j then
    (q : ℤ) * ((coeff_of_log_gf_gen m j : ℤ) - (coeff_of_log_gf_gen m (j / q) : ℤ))
  else
    (q : ℤ) * (coeff_of_log_gf_gen m j : ℤ)

lemma eDrive_of_not_dvd {m q j : ℕ} (hq : q ≠ 0) (h : ¬ q ∣ j) :
    eDrive m q j = (q : ℤ) * (coeff_of_log_gf_gen m j : ℤ) := by
  simp [eDrive, hq, h]

lemma eDrive_of_dvd {m q j : ℕ} (hq : q ≠ 0) (h : q ∣ j) :
    eDrive m q j =
      (q : ℤ) * ((coeff_of_log_gf_gen m j : ℤ) -
        (coeff_of_log_gf_gen m (j / q) : ℤ)) := by
  simp [eDrive, hq, h]

lemma eDrive_decompose (m q j : ℕ) (hq : q ≠ 0) :
    (eDrive m q j : ℚ) =
      (q : ℚ) * (coeff_of_log_gf_gen m j : ℚ) -
        (if q ∣ j then (q : ℚ) * (coeff_of_log_gf_gen m (j / q) : ℚ) else 0) := by
  by_cases h : q ∣ j
  · rw [eDrive_of_dvd hq h]; simp [h]; ring
  · rw [eDrive_of_not_dvd hq h]; simp [h]

/-- `γ_j(N) = [x^j] G(x)^N`. -/
noncomputable def gammaQ (m q N j : ℕ) : ℚ :=
  expQ (fun k => (N : ℚ) * (eDrive m q k : ℚ)) j

lemma gammaQ_zero (m q N : ℕ) : gammaQ m q N 0 = 1 := expQ_zero _

lemma gammaQ_rec (m q N k : ℕ) :
    (k + 1 : ℚ) * gammaQ m q N (k + 1) =
      (N : ℚ) * ∑ j ∈ range (k + 1),
        (eDrive m q (j + 1) : ℚ) * gammaQ m q N (k - j) := by
  unfold gammaQ
  rw [expQ_mul_succ]
  simp [mul_sum, mul_assoc, mul_left_comm, mul_comm]

lemma gammaQ_mul (m q N n : ℕ) :
    (n : ℚ) * gammaQ m q N n =
      if n = 0 then 0
      else (N : ℚ) * ∑ j ∈ range n,
        (eDrive m q (j + 1) : ℚ) * gammaQ m q N (n - 1 - j) := by
  rcases n with _ | n
  · simp
  · simpa using gammaQ_rec m q N n

lemma alphaQ_mul (m N n : ℕ) :
    (n : ℚ) * alphaQ m N n =
      if n = 0 then 0
      else (N : ℚ) * ∑ j ∈ range n,
        (coeff_of_log_gf_gen m (j + 1) : ℚ) * alphaQ m N (n - 1 - j) := by
  rcases n with _ | n
  · simp
  · simpa using alphaQ_rec m N n

/-- Stretched Cauchy product `∑_i α_i(N) γ_{k - q i}(N)`. -/
noncomputable def cauchyPG (m q N k : ℕ) : ℚ :=
  ∑ i ∈ range (k / q + 1), alphaQ m N i * gammaQ m q N (k - q * i)

lemma cauchyPG_zero (m q N : ℕ) : cauchyPG m q N 0 = 1 := by
  simp [cauchyPG, alphaQ_zero, gammaQ_zero]

lemma mem_range_of_mul_le {q i k : ℕ} (hq : 0 < q) (hle : q * i ≤ k) :
    i ∈ range (k / q + 1) := by
  rw [mem_range, Nat.lt_succ_iff]
  have : q * i / q ≤ k / q := Nat.div_le_div_right hle
  rwa [Nat.mul_div_right i hq] at this

lemma mul_le_of_mem_div_range {q i k : ℕ} (hq : 0 < q)
    (hi : i ∈ range (k / q + 1)) : q * i ≤ k := by
  have : i ≤ k / q := Nat.lt_succ_iff.mp (mem_range.mp hi)
  calc q * i ≤ q * (k / q) := Nat.mul_le_mul_left q this
    _ ≤ k := Nat.mul_div_le k q

lemma cauchyPG_eq_sum (m q N k : ℕ) (hq : 0 < q) :
    cauchyPG m q N k =
      ∑ i ∈ range (k + 1),
        (if q * i ≤ k then alphaQ m N i * gammaQ m q N (k - q * i) else 0) := by
  unfold cauchyPG
  apply Eq.symm
  rw [sum_ite]
  have hfilter :
      (range (k + 1)).filter (fun i => q * i ≤ k) = range (k / q + 1) := by
    ext i
    simp only [mem_filter, mem_range]
    constructor
    · intro ⟨_, hle⟩
      exact mem_range.mp (mem_range_of_mul_le hq hle)
    · intro hi
      have hle := mul_le_of_mem_div_range (q := q) (i := i) (k := k) hq (mem_range.mpr hi)
      have : i ≤ k / q := Nat.lt_succ_iff.mp hi
      exact ⟨Nat.lt_succ_of_le (this.trans (Nat.div_le_self k q)), hle⟩
  simp [hfilter]

lemma gammaQ_split (m q N n i : ℕ) (hq : 0 < q) (hle : q * i ≤ n) :
    (n : ℚ) * gammaQ m q N (n - q * i) =
      ((n - q * i : ℕ) : ℚ) * gammaQ m q N (n - q * i) +
        (q * i : ℚ) * gammaQ m q N (n - q * i) := by
  have : (n : ℚ) = ((n - q * i : ℕ) : ℚ) + (q * i : ℚ) := by
    have := Nat.sub_add_cancel hle
    exact_mod_cast this.symm
  rw [this, add_mul]

/-- Multinomial Wolstenholme: `c_m(q k) ≡ c_m(k) (mod q^3)` for primes `q ≥ 5`. -/
lemma coeff_mul_prime_modEq (m k : ℕ) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) :
    (coeff_of_log_gf_gen m (q * k) : ℤ) ≡ (coeff_of_log_gf_gen m k : ℤ)
      [ZMOD (q ^ 3 : ℤ)] := by
  have hprod := coeff_of_log_gf_gen_eq_prod_choose (m := m) (k := q * k)
  have hprod' := coeff_of_log_gf_gen_eq_prod_choose (m := m) (k := k)
  rw [hprod, hprod', Nat.cast_prod, Nat.cast_prod]
  refine Int.ModEq.prod (fun s hs => ?_)
  have := wolstenholme_choose_r1 (p := q) (a := s * k) (b := k) hq hq5
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

lemma eDrive_dvd_pow (m q j : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q) :
    (q : ℤ) ∣ eDrive m q j := by
  have hqne : q ≠ 0 := hq.ne_zero
  by_cases h : q ∣ j
  · rw [eDrive_of_dvd hqne h]
    exact dvd_mul_right (q : ℤ) _
  · rw [eDrive_of_not_dvd hqne h]
    exact dvd_mul_right (q : ℤ) _

lemma eDrive_of_dvd_pow3 (m q j : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q)
    (hdvd : q ∣ j) :
    (q : ℤ) ^ 4 ∣ eDrive m q j := by
  have hqne : q ≠ 0 := hq.ne_zero
  rw [eDrive_of_dvd hqne hdvd]
  have : (q : ℤ) ^ 3 ∣
      (coeff_of_log_gf_gen m j : ℤ) - (coeff_of_log_gf_gen m (j / q) : ℤ) := by
    obtain ⟨t, ht⟩ := hdvd
    have hcongr := coeff_mul_prime_modEq m t hq hq5
    have : j = q * t := by rw [ht, mul_comm]
    rw [this, Nat.mul_div_right t hq.pos]
    exact (Int.modEq_iff_dvd.mp hcongr.symm)
  have hpow : (q : ℤ) ^ 4 = (q : ℤ) * (q : ℤ) ^ 3 := by ring
  rw [hpow]
  exact mul_dvd_mul_left _ this

lemma Nat.cast_div_eq_div_cast {a b : ℕ} (h : b ∣ a) (hb : b ≠ 0) :
    ((a / b : ℕ) : ℚ) = (a : ℚ) / (b : ℚ) := by
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  rw [eq_div_iff hb0]
  exact_mod_cast Nat.div_mul_cancel h

lemma sum_inv_pbeta_sq_val [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    (∑ i ∈ Icc 1 (p - 1), (pbeta p i : ℚ)⁻¹ ^ 2) = 0 ∨
      (0 : ℤ) ≤ padicValRat p
        (∑ i ∈ Icc 1 (p - 1), (pbeta p i : ℚ)⁻¹ ^ 2) := by
  sorry

/--
oeis_333042_conjecture_1:
More generally, for a positive integer $m$, set $A_m(x) = \exp( \sum_{n \ge 1} (m*n)!/(n!^m) * x^n/n )$
and define a sequence $\{b_m(n): n \ge 1\}$ by $b_m(n) := [x^n] A_m(x)^n$.
Then we conjecture that $b_m(n)$ is an integer sequence satisfying the supercongruences
$b_m(n p^r) \equiv b_m(n p^{r-1}) \pmod{p^{3r}}$ for prime $p \ge 5$ and all positive integers $m, n, r$.
-/
theorem general_supercongruence_conjecture (m n r p : ℕ) (hp : Nat.Prime p)
    (hp5 : p ≥ 5) (hm : m ≥ 1) (hn : n ≥ 1) (hr : r ≥ 1) :
    b_m_int m (n * p ^ r) ≡ b_m_int m (n * p ^ (r - 1)) [ZMOD (p ^ (3 * r) : ℤ)] := by
  have hidx : n * p ^ r = (n * p ^ (r - 1)) * p := by
    calc n * p ^ r = n * p ^ (r - 1 + 1) := by rw [Nat.sub_add_cancel hr]
      _ = n * (p ^ (r - 1) * p) := by rw [pow_succ]
      _ = n * p ^ (r - 1) * p := by rw [mul_assoc]
  rw [hidx]
  obtain rfl | _hm1 := eq_or_ne m 1
  · obtain rfl | _hr1 := eq_or_ne r 1
    · simpa [pow_one, pow_zero, mul_one] using
        general_supercongruence_m_one_r_one n p hp hp5 hn
    · sorry
  · sorry
