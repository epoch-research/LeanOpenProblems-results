import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 5000000

open Matrix Nat Int

/--
A226163: Determinant of the $(p_n-1)/2$-by-$(p_n-1)/2$ matrix with $(i,j)$-entry being the Legendre symbol
$$\left(\frac{i^2 - \left(\frac{p_n-1}{2}\right)! \cdot j}{p_n}\right)$$
where $p_n$ is the $n$-th prime.
The sequence is naturally indexed starting from $n=2$.
-/
noncomputable def A226163 (n : ℕ) : ℤ :=
  if h : n < 2 then 0 else

  -- p is the n-th prime, p_n. Mathlib's nth Nat.Prime is 0-indexed, so we use (n-1).
  -- Since n >= 2, p >= 3 is an an odd prime.
  let p : ℕ := Nat.nth Nat.Prime (n - 1)

  -- Matrix dimension m = (p-1)/2.
  let m : ℕ := (p - 1) / 2

  -- The constant C = ((p-1)/2)! as an integer.
  let C : ℤ := m.factorial.cast

  -- The matrix M has entries in ℤ.
  let M : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    -- 1-based indices i' and j' for the formula: 1 <= i', j' <= m.
    let i' : ℤ := (i.val + 1).cast
    let j' : ℤ := (j.val + 1).cast

    -- Argument for the Legendre symbol: i'^2 - C * j'
    let arg : ℤ := i' * i' - C * j'

    -- jacobiSym is the Legendre symbol since p is prime.
    jacobiSym arg p

  M.det


open Matrix Finset
open scoped BigOperators

lemma det_power_row_update_succ {R : Type*} [CommRing R] (n : ℕ) (z : Fin (n+1) → R) :
    let W : Matrix (Fin (n+1)) (Fin (n+1)) R := fun r c => z c ^ (r : ℕ)
    let H : Matrix (Fin (n+1)) (Fin (n+1)) R := fun r c => if r = 0 then z c ^ (n+1) else z c ^ (r : ℕ)
    H.det = ((-1 : R) ^ n) * (∏ c : Fin (n+1), z c) * W.det := by
  classical
  intro W H
  have hsub : H.submatrix (finRotate (n+1)) id = Matrix.of (fun r c : Fin (n+1) => z c * W r c) := by
    ext r c
    simp only [Matrix.submatrix_apply, id_eq, Matrix.of_apply]
    by_cases hr : r = Fin.last n
    · subst r
      simp [H, W, finRotate_last, pow_succ, mul_comm]
    · have hrotval : ((finRotate (n+1) r : Fin (n+1)) : ℕ) = r.val + 1 := by
        exact coe_finRotate_of_ne_last hr
      have hrotne : finRotate (n+1) r ≠ 0 := by
        intro h0
        have : ((finRotate (n+1) r : Fin (n+1)) : ℕ) = 0 := by simpa [h0]
        omega
      have haddne : (r + 1 : Fin (n+1)) ≠ 0 := by
        simpa [finRotate_succ_apply] using hrotne
      have hvaladd : ((r + 1 : Fin (n+1)) : ℕ) = r.val + 1 := by
        simpa [finRotate_succ_apply] using hrotval
      simp [H, W, haddne, hvaladd, pow_succ, mul_comm]
  have hdet_sub : (H.submatrix (finRotate (n+1)) id).det = Equiv.Perm.sign (finRotate (n+1)) * H.det := Matrix.det_permute (finRotate (n+1)) H
  have hdet_scaled : (Matrix.of (fun r c : Fin (n+1) => z c * W r c)).det = (∏ c : Fin (n+1), z c) * W.det := by
    simpa using Matrix.det_mul_row z W
  have hsign : ((Equiv.Perm.sign (finRotate (n+1)) : ℤˣ) : R) = (-1 : R) ^ n := by
    simpa using congrArg (fun u : ℤˣ => (u : R)) (sign_finRotate n)
  have hsrel : ((Equiv.Perm.sign (finRotate (n+1)) : ℤˣ) : R) * H.det = (∏ c : Fin (n+1), z c) * W.det := by
    rw [← hdet_sub, hsub, hdet_scaled]
  have hsgsq : (((Equiv.Perm.sign (finRotate (n+1)) : ℤˣ) : R) * ((Equiv.Perm.sign (finRotate (n+1)) : ℤˣ) : R)) = 1 := by
    rw [hsign]
    rw [← pow_add]
    have : n + n = 2 * n := by omega
    rw [this, pow_mul]
    simp
  calc
    H.det = (((Equiv.Perm.sign (finRotate (n+1)) : ℤˣ) : R) * ((Equiv.Perm.sign (finRotate (n+1)) : ℤˣ) : R)) * H.det := by
      rw [hsgsq, one_mul]
    _ = ((Equiv.Perm.sign (finRotate (n+1)) : ℤˣ) : R) * (((Equiv.Perm.sign (finRotate (n+1)) : ℤˣ) : R) * H.det) := by ring
    _ = ((Equiv.Perm.sign (finRotate (n+1)) : ℤˣ) : R) * ((∏ c : Fin (n+1), z c) * W.det) := by rw [hsrel]
    _ = ((-1 : R) ^ n) * (∏ c : Fin (n+1), z c) * W.det := by rw [hsign]; ring

lemma det_power_row_one_add {R : Type*} [CommRing R] (n : ℕ) (z : Fin (n+1) → R) :
    let W : Matrix (Fin (n+1)) (Fin (n+1)) R := fun r c => z c ^ (r : ℕ)
    let N : Matrix (Fin (n+1)) (Fin (n+1)) R := fun r c => if r = 0 then 1 + z c ^ (n+1) else z c ^ (r : ℕ)
    N.det = (1 + (-1 : R) ^ n * (∏ c : Fin (n+1), z c)) * W.det := by
  classical
  intro W N
  let H : Matrix (Fin (n+1)) (Fin (n+1)) R := fun r c => if r = 0 then z c ^ (n+1) else z c ^ (r : ℕ)
  have hN : N = W.updateRow 0 (W 0 + H 0) := by
    ext r c
    by_cases hr : r = 0
    · subst r; simp [N, W, H]
    · simp [N, W, H, hr]
  have hWupd : W.updateRow 0 (W 0) = W := by ext r c <;> by_cases hr : r=0 <;> simp [hr]
  have hHupd : W.updateRow 0 (H 0) = H := by
    ext r c
    by_cases hr : r=0
    · subst r; simp [H]
    · simp [H, W, hr]
  calc
    N.det = (W.updateRow 0 (W 0 + H 0)).det := by rw [hN]
    _ = (W.updateRow 0 (W 0)).det + (W.updateRow 0 (H 0)).det := by rw [Matrix.det_updateRow_add]
    _ = W.det + H.det := by rw [hWupd, hHupd]
    _ = W.det + ((-1 : R) ^ n) * (∏ c : Fin (n+1), z c) * W.det := by rw [det_power_row_update_succ]
    _ = (1 + (-1 : R) ^ n * (∏ c : Fin (n+1), z c)) * W.det := by ring

lemma det_coeff_matrix_formula {F : Type*} [Field F] (n : ℕ) (a : Fin (n+1) → F)
    (ha : ∀ j, a j ≠ 0) :
    let m := n+1
    let B : Matrix (Fin m) (Fin m) F := fun r c =>
      if r = 0 then 1 + a c ^ m else (Nat.choose m r.val : F) * a c ^ (m - r.val)
    let z : Fin m → F := fun c => (a c)⁻¹
    let W : Matrix (Fin m) (Fin m) F := fun r c => z c ^ (r : ℕ)
    B.det = (∏ c : Fin m, a c ^ m) * (∏ r : Fin m, if r = 0 then (1:F) else (Nat.choose m r.val : F)) *
      ((1 + (-1 : F)^n * (∏ c : Fin m, z c)) * W.det) := by
  classical
  intro m B z W
  let N : Matrix (Fin m) (Fin m) F := fun r c => if r = 0 then 1 + z c ^ m else z c ^ (r : ℕ)
  let rowfac : Fin m → F := fun r => if r = 0 then (1:F) else (Nat.choose m r.val : F)
  let C : Matrix (Fin m) (Fin m) F := Matrix.of fun r c => rowfac r * N r c
  have hB : B = Matrix.of (fun r c : Fin m => a c ^ m * C r c) := by
    ext r c
    by_cases hr : r = 0
    · subst r
      simp [B, C, N, rowfac, z, ha c, inv_pow, mul_add, pow_succ]
      field_simp [ha c]
      ring
    · have hrle : r.val ≤ m := le_of_lt r.isLt
      have hpow : a c ^ m * (a c)⁻¹ ^ r.val = a c ^ (m - r.val) := by
        rw [inv_pow]
        field_simp [pow_ne_zero r.val (ha c)]
        rw [← pow_add]
        have : r.val + (m - r.val) = m := Nat.add_sub_of_le hrle
        rw [this]
      simp [B, C, N, rowfac, z, hr]
      rw [← inv_pow]
      calc
        (m.choose r.val : F) * a c ^ (m - r.val) = (m.choose r.val : F) * (a c ^ m * (a c)⁻¹ ^ r.val) := by rw [hpow]
        _ = a c ^ m * (m.choose r.val : F) * (a c)⁻¹ ^ r.val := by ring
        _ = a c ^ m * ((m.choose r.val : F) * (a c)⁻¹ ^ r.val) := by rw [mul_assoc]
  have hC : C.det = (∏ r : Fin m, rowfac r) * N.det := by
    simpa [C] using Matrix.det_mul_column rowfac N
  have hBdet : B.det = (∏ c : Fin m, a c ^ m) * C.det := by
    rw [hB]
    simpa using Matrix.det_mul_row (fun c : Fin m => a c ^ m) C
  rw [hBdet, hC]
  have hNdet : N.det = (1 + (-1 : F)^n * (∏ c : Fin m, z c)) * W.det := by
    subst m
    exact det_power_row_one_add n z
  rw [hNdet]
  ring
open Finset
open scoped BigOperators

lemma fin_adjust_sum_eq_range {F : Type*} [Field F] (n : ℕ) (x b : F) :
    (∑ r : Fin (n+1), x^(r:ℕ) * (if r = 0 then 1 + b^(n+1) else (Nat.choose (n+1) r.val : F) * b^((n+1)-r.val))) =
    ∑ k ∈ range (n+1), x^k * (if k = 0 then 1 + b^(n+1) else (Nat.choose (n+1) k : F) * b^((n+1)-k)) := by
  classical
  simpa using (Fin.sum_univ_eq_sum_range (fun k => x^k * (if k = 0 then 1 + b^(n+1) else (Nat.choose (n+1) k : F) * b^((n+1)-k))) (n+1))

lemma binomial_adjust {F : Type*} [Field F] (n : ℕ) (x b : F) (hx : x^(n+1)=1) :
    (x + b)^(n+1) =
      ∑ r : Fin (n+1), x^(r:ℕ) * (if r = 0 then 1 + b^(n+1) else (Nat.choose (n+1) r.val : F) * b^((n+1)-r.val)) := by
  classical
  rw [fin_adjust_sum_eq_range]
  rw [add_pow]
  rw [Finset.sum_range_succ]
  simp only [Nat.choose_self, tsub_self, pow_zero, mul_one, Nat.cast_one]
  rw [hx]
  rw [add_comm]
  -- goal: adjusted range = binomial range without last plus 1
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, pow_zero, one_mul, tsub_zero, Nat.cast_one, if_true]
  conv_rhs => rw [Finset.sum_range_succ']
  simp only [if_true, pow_zero, one_mul]
  ring_nf
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : k + 1 ≠ 0 := by omega
  simp [hk0, mul_assoc, mul_comm, mul_left_comm]

lemma eval_adjusted_factorization {F : Type*} [Field F] (n : ℕ) (x b : Fin (n+1) → F)
    (hx : ∀ i, x i ^ (n+1) = 1) :
    let m := n+1
    let E : Matrix (Fin m) (Fin m) F := fun i j => (x i + b j) ^ m
    let B : Matrix (Fin m) (Fin m) F := fun r j =>
      if r = 0 then 1 + b j ^ m else (Nat.choose m r.val : F) * b j ^ (m-r.val)
    E = (Matrix.vandermonde x) * B := by
  classical
  intro m E B
  subst m
  ext i j
  simp [E, Matrix.mul_apply, Matrix.vandermonde, B]
  rw [binomial_adjust n (x i) (b j) (hx i)]
  congr 1
  ext r
  by_cases hr : r = 0 <;> simp [hr, mul_assoc]

lemma eval_adjusted_det_formula {F : Type*} [Field F] (n : ℕ) (x b : Fin (n+1) → F)
    (hx : ∀ i, x i ^ (n+1) = 1) (hb : ∀ j, b j ≠ 0) :
    let m := n+1
    let E : Matrix (Fin m) (Fin m) F := fun i j => (x i + b j) ^ m
    let z : Fin m → F := fun j => (b j)⁻¹
    let W : Matrix (Fin m) (Fin m) F := fun r c => z c ^ (r:ℕ)
    E.det = (Matrix.vandermonde x).det *
      ((∏ c : Fin m, b c ^ m) * (∏ r : Fin m, if r = 0 then (1:F) else (Nat.choose m r.val : F)) *
      ((1 + (-1 : F)^n * (∏ c : Fin m, z c)) * W.det)) := by
  classical
  intro m E z W
  let B : Matrix (Fin m) (Fin m) F := fun r j =>
      if r = 0 then 1 + b j ^ m else (Nat.choose m r.val : F) * b j ^ (m-r.val)
  have hfac : E = (Matrix.vandermonde x) * B := by
    subst m
    exact eval_adjusted_factorization n x b hx
  have hB := det_coeff_matrix_formula (n:=n) (a:=b) hb
  rw [hfac, Matrix.det_mul]
  rw [hB]

lemma eval_adjusted_det_zero_iff_factor {F : Type*} [Field F] (n : ℕ) (x b : Fin (n+1) → F)
    (hxpow : ∀ i, x i ^ (n+1) = 1) (hb : ∀ j, b j ≠ 0)
    (hinjx : Function.Injective x)
    (hinjz : Function.Injective (fun j : Fin (n+1) => (b j)⁻¹))
    (hrow : ∀ r : Fin (n+1), (if r = 0 then (1:F) else (Nat.choose (n+1) r.val : F)) ≠ 0) :
    let m := n+1
    let E : Matrix (Fin m) (Fin m) F := fun i j => (x i + b j) ^ m
    let z : Fin m → F := fun j => (b j)⁻¹
    E.det = 0 ↔ (1 + (-1 : F)^n * (∏ c : Fin m, z c)) = 0 := by
  classical
  intro m E z
  have hformula := eval_adjusted_det_formula n x b hxpow hb
  dsimp at hformula
  rw [hformula]
  have hVx : (Matrix.vandermonde x).det ≠ 0 := (Matrix.det_vandermonde_ne_zero_iff).mpr hinjx
  have hbprod : (∏ c : Fin (n+1), b c ^ (n+1)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (by intro c hc; exact pow_ne_zero _ (hb c))
  have hrowprod : (∏ r : Fin (n+1), if r = 0 then (1:F) else (Nat.choose (n+1) r.val : F)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (by intro r hr; exact hrow r)
  have hVz : (Matrix.of fun r c : Fin (n+1) => z c ^ (r:ℕ)).det ≠ 0 := by
    have hv : (Matrix.vandermonde z).det ≠ 0 := (Matrix.det_vandermonde_ne_zero_iff).mpr hinjz
    have hvt : (Matrix.vandermonde z).transpose.det ≠ 0 := by
      simpa [Matrix.det_transpose] using hv
    convert hvt using 2
  constructor
  · intro h
    by_contra hf
    exact (mul_ne_zero hVx (mul_ne_zero (mul_ne_zero hbprod hrowprod) (mul_ne_zero hf hVz))) h
  · intro hf
    rw [hf]
    ring

lemma zmod_nat_cast_eq_of_lt {p a b : ℕ} (ha : a < p) (hb : b < p)
    (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  have hv := congrArg ZMod.val h
  rw [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at hv
  exact hv

lemma zmod_nat_cast_ne_zero_of_pos_lt {p a : ℕ} (ha0 : 0 < a) (hap : a < p) :
    (a : ZMod p) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_cast_of_lt hap, ZMod.val_zero] at hv
  omega

lemma half_squares_injective (p m : ℕ) [Fact p.Prime] (hp : p = 2*m+1) :
    Function.Injective (fun i : Fin m => (((i.val+1 : ℕ) : ZMod p)^2)) := by
  intro i j h
  have hi_lt_p : i.val + 1 < p := by subst p; omega
  have hj_lt_p : j.val + 1 < p := by subst p; omega
  have hi_pos : 0 < i.val + 1 := by omega
  have hj_pos : 0 < j.val + 1 := by omega
  have hprod : (((i.val+1:ℕ):ZMod p) - ((j.val+1:ℕ):ZMod p)) *
      (((i.val+1:ℕ):ZMod p) + ((j.val+1:ℕ):ZMod p)) = 0 := by
    have hdiff : (((i.val+1:ℕ):ZMod p)^2 - ((j.val+1:ℕ):ZMod p)^2) = 0 := sub_eq_zero.mpr h
    calc
      (((i.val+1:ℕ):ZMod p) - ((j.val+1:ℕ):ZMod p)) * (((i.val+1:ℕ):ZMod p) + ((j.val+1:ℕ):ZMod p)) = (((i.val+1:ℕ):ZMod p)^2 - ((j.val+1:ℕ):ZMod p)^2) := by ring
      _ = 0 := hdiff
  have hzero := mul_eq_zero.mp hprod
  rcases hzero with hsub | hsum
  · apply Fin.ext
    have hc : ((i.val+1:ℕ):ZMod p) = ((j.val+1:ℕ):ZMod p) := sub_eq_zero.mp hsub
    have : i.val + 1 = j.val + 1 := zmod_nat_cast_eq_of_lt hi_lt_p hj_lt_p hc
    omega
  · exfalso
    have hsum_nat : (i.val+1) + (j.val+1) < p := by subst p; omega
    have hsum_pos : 0 < (i.val+1) + (j.val+1) := by omega
    have hcast_sum : (((i.val+1)+(j.val+1):ℕ) : ZMod p) = 0 := by
      simpa [Nat.cast_add] using hsum
    exact zmod_nat_cast_ne_zero_of_pos_lt hsum_pos hsum_nat hcast_sum

lemma zmod_nat_cast_ne_zero_of_not_dvd {p a : ℕ} (h : ¬ p ∣ a) : (a : ZMod p) ≠ 0 := by
  intro hz
  exact h ((ZMod.natCast_eq_zero_iff a p).mp hz)

lemma choose_cast_ne_zero_zmod {p m k : ℕ} (hp : p.Prime) (hm : m < p) (hk : k ≤ m) :
    ((Nat.choose m k : ℕ) : ZMod p) ≠ 0 := by
  apply zmod_nat_cast_ne_zero_of_not_dvd
  exact (hp.coprime_iff_not_dvd).mp (hp.coprime_choose_of_lt hm hk)

lemma scalar_factor_iff {F : Type*} [Field F] (n : ℕ) {D : F} (hD : D ≠ 0) :
    1 + (-1 : F)^n * (((-1 : F)^(n+1) * D)⁻¹) = 0 ↔ D = 1 := by
  have hsign_ne : (-1 : F)^(n+1) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr (one_ne_zero : (1:F)≠0))
  have hprod : (-1 : F)^(n+1) * D ≠ 0 := mul_ne_zero hsign_ne hD
  have hsimp : (-1 : F)^n * (((-1 : F)^(n+1) * D)⁻¹) = - D⁻¹ := by
    field_simp [hprod, hD]
    rw [pow_succ]
    ring
  rw [hsimp]
  constructor
  · intro h
    have hmul : D * (1 + -D⁻¹) = D * 0 := by rw [h]
    field_simp [hD] at hmul
    exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hmul)
  · intro h
    subst D
    simp

lemma half_linear_injective (p M : ℕ) [Fact p.Prime] (hp : p = 2*M+1) (d : ZMod p) (hd : d ≠ 0) :
    Function.Injective (fun j : Fin M => (-(d * ((j.val+1:ℕ) : ZMod p)))⁻¹) := by
  intro i j h
  have hinv := congrArg Inv.inv h
  rw [inv_inv, inv_inv] at hinv
  have hmul : ((i.val+1:ℕ) : ZMod p) = ((j.val+1:ℕ) : ZMod p) := by
    have := neg_inj.mp hinv
    exact mul_left_cancel₀ hd this
  apply Fin.ext
  have hi_lt : i.val+1 < p := by subst p; omega
  have hj_lt : j.val+1 < p := by subst p; omega
  have hnat := zmod_nat_cast_eq_of_lt hi_lt hj_lt hmul
  omega

lemma rowfactor_ne_zero_zmod_succ (n : ℕ) [Fact (Nat.Prime (2*(n+1)+1))] (r : Fin (n+1)) :
    (if r = 0 then (1 : ZMod (2*(n+1)+1)) else (Nat.choose (n+1) r.val : ZMod (2*(n+1)+1))) ≠ 0 := by
  by_cases hr : r = 0
  · simp [hr]
  · simp [hr]
    apply choose_cast_ne_zero_zmod (p:=2*(n+1)+1) (m:=n+1) (k:=r.val)
    · exact Fact.out
    · omega
    · exact Nat.le_of_lt r.isLt

lemma prod_half_nat_cast (p M : ℕ) :
    (∏ j : Fin M, (((j.val+1:ℕ) : ZMod p))) = (M.factorial : ZMod p) := by
  rw [Fin.prod_univ_eq_prod_range (fun k => (((k+1:ℕ) : ZMod p))) M]
  rw [← Finset.prod_Ico_id_eq_factorial, Finset.prod_natCast]
  rw [Finset.prod_Ico_eq_prod_range]
  apply Finset.prod_congr rfl
  intro x hx
  norm_num [Nat.cast_add, add_comm]

lemma power_det_zero_iff_scalar (N : ℕ) [Fact (Nat.Prime (2*N+1))] (d : ZMod (2*N+1)) (hd : d ≠ 0) :
    let E : Matrix (Fin N) (Fin N) (ZMod (2*N+1)) := fun i j =>
      ((((i.val+1:ℕ) : ZMod (2*N+1))^2) - d * (((j.val+1:ℕ) : ZMod (2*N+1)))) ^ N
    E.det = 0 ↔ d^N * (N.factorial : ZMod (2*N+1)) = 1 := by
  classical
  cases N with
  | zero =>
      have hp1 : Nat.Prime 1 := by simpa using (Fact.out : Nat.Prime (2*0+1))
      exact (Nat.not_prime_one hp1).elim
  | succ n =>
      let p := 2*(n+1)+1
      let x : Fin (n+1) → ZMod p := fun i => (((i.val+1:ℕ):ZMod p)^2)
      let b : Fin (n+1) → ZMod p := fun j => -(d * (((j.val+1:ℕ):ZMod p)))
      intro E
      have hxpow : ∀ i, x i ^ (n+1) = 1 := by
        intro i
        dsimp [x, p]
        rw [← pow_mul]
        have hnon : (((i.val+1:ℕ):ZMod (2*(n+1)+1))) ≠ 0 := by
          apply zmod_nat_cast_ne_zero_of_pos_lt <;> omega
        have hfermat : (((i.val+1:ℕ):ZMod (2*(n+1)+1))) ^ ((2*(n+1)+1)-1) = 1 := ZMod.pow_card_sub_one_eq_one hnon
        convert hfermat using 2
      have hb : ∀ j, b j ≠ 0 := by
        intro j
        dsimp [b, p]
        apply neg_ne_zero.mpr
        apply mul_ne_zero hd
        apply zmod_nat_cast_ne_zero_of_pos_lt <;> omega
      have hinjx : Function.Injective x := by
        dsimp [x, p]
        exact half_squares_injective (2*(n+1)+1) (n+1) rfl
      have hinjz : Function.Injective (fun j : Fin (n+1) => (b j)⁻¹) := by
        dsimp [b, p]
        exact half_linear_injective (2*(n+1)+1) (n+1) rfl d hd
      have hrow : ∀ r : Fin (n+1), (if r = 0 then (1 : ZMod p) else (Nat.choose (n+1) r.val : ZMod p)) ≠ 0 := by
        intro r
        dsimp [p]
        exact rowfactor_ne_zero_zmod_succ n r
      have hcrit := eval_adjusted_det_zero_iff_factor (n:=n) x b hxpow hb hinjx hinjz hrow
      dsimp [E, x, b, p] at hcrit ⊢
      simp only [sub_eq_add_neg]
      rw [hcrit]
      let D : ZMod (2*(n+1)+1) := d^(n+1) * ((n+1).factorial : ZMod (2*(n+1)+1))
      have hprod : (∏ c : Fin (n+1), (-(d * ((c.val+1:ℕ) : ZMod (2*(n+1)+1))))⁻¹) = ((-1 : ZMod (2*(n+1)+1))^(n+1) * D)⁻¹ := by
        rw [Finset.prod_inv_distrib]
        congr 1
        dsimp [D]
        calc
          (∏ c : Fin (n+1), -(d * ((c.val+1:ℕ) : ZMod (2*(n+1)+1))))
              = (∏ c : Fin (n+1), ((-1 : ZMod (2*(n+1)+1)) * d * ((c.val+1:ℕ) : ZMod (2*(n+1)+1)))) := by
                apply Finset.prod_congr rfl
                intro c hc
                ring
          _ = ((-1 : ZMod (2*(n+1)+1)) * d)^(n+1) * (∏ c : Fin (n+1), ((c.val+1:ℕ) : ZMod (2*(n+1)+1))) := by
                rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]
          _ = ((-1 : ZMod (2*(n+1)+1))^(n+1) * d^(n+1)) * ((n+1).factorial : ZMod (2*(n+1)+1)) := by
                rw [mul_pow, prod_half_nat_cast]
          _ = (-1 : ZMod (2*(n+1)+1))^(n+1) * (d^(n+1) * ((n+1).factorial : ZMod (2*(n+1)+1))) := by ring
      rw [hprod]
      have hD : D ≠ 0 := by
        dsimp [D]
        apply mul_ne_zero
        · exact pow_ne_zero _ hd
        · apply zmod_nat_cast_ne_zero_of_not_dvd
          have hpprime : Nat.Prime (2*(n+1)+1) := Fact.out
          rw [hpprime.dvd_factorial]
          omega
      exact scalar_factor_iff n hD

open Matrix Nat Int

lemma map_jacobi_matrix_entry (p m : ℕ) [Fact p.Prime] (hp : p = 2*m+1) (d : ℤ) (i j : Fin m) :
    ((jacobiSym (((i.val+1:ℤ)^2) - d * ((j.val+1:ℤ))) p : ℤ) : ZMod p) =
      ((((i.val+1:ℕ) : ZMod p)^2) - (d : ZMod p) * (((j.val+1:ℕ) : ZMod p))) ^ m := by
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  have hpow := legendreSym.eq_pow (p:=p) ((((i.val+1:ℤ)^2) - d * ((j.val+1:ℤ))))
  rw [hpow]
  have hpm : p / 2 = m := by
    subst p
    omega
  rw [hpm]
  congr 1
  push_cast
  ring

lemma map_jacobi_det (p m : ℕ) [Fact p.Prime] (hp : p = 2*m+1) (d : ℤ) :
    (((Matrix.of fun i j : Fin m => jacobiSym (((i.val+1:ℤ)^2) - d * ((j.val+1:ℤ))) p).det : ℤ) : ZMod p) =
      (Matrix.of fun i j : Fin m =>
        ((((i.val+1:ℕ) : ZMod p)^2) - (d : ZMod p) * (((j.val+1:ℕ) : ZMod p))) ^ m).det := by
  change (Int.castRingHom (ZMod p)) ((Matrix.of fun i j : Fin m => jacobiSym (((i.val+1:ℤ)^2) - d * ((j.val+1:ℤ))) p).det) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact map_jacobi_matrix_entry p m hp d i j

lemma jacobi_det_mod_zero_iff_scalar (N : ℕ) [Fact (Nat.Prime (2*N+1))] (d : ℤ)
    (hd : (d : ZMod (2*N+1)) ≠ 0) :
    ((((Matrix.of fun i j : Fin N => jacobiSym (((i.val+1:ℤ)^2) - d * ((j.val+1:ℤ))) (2*N+1)).det : ℤ) : ZMod (2*N+1)) = 0)
      ↔ (d : ZMod (2*N+1))^N * (N.factorial : ZMod (2*N+1)) = 1 := by
  have hmap := map_jacobi_det (2*N+1) N (by ring) d
  rw [hmap]
  exact power_det_zero_iff_scalar N (d : ZMod (2*N+1)) hd
open Finset Nat
open scoped BigOperators

lemma prod_Ico_split_two_mul {R} [CommMonoid R] (m : ℕ) (f : ℕ → R) :
    (∏ x ∈ Finset.Ico 1 (2*m+1), f x) =
      (∏ x ∈ Finset.Ico 1 (m+1), f x) * (∏ x ∈ Finset.Ico (m+1) (2*m+1), f x) := by
  rw [← Finset.prod_union]
  · congr 1
    ext x
    simp only [mem_union, mem_Ico]
    omega
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [mem_Ico] at hx1 hx2
    omega

lemma prod_second_half_zmod (m : ℕ) :
    (∏ x ∈ Finset.Ico (m+1) (2*m+1), (x : ZMod (2*m+1))) =
      (∏ j ∈ Finset.Ico 1 (m+1), (-(j : ZMod (2*m+1)))) := by
  symm
  refine Finset.prod_bij (fun j hj => 2*m+1 - j) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [mem_Ico] at hj ⊢
    omega
  · intro a ha b hb h
    simp only [mem_Ico] at ha hb
    dsimp at h
    omega
  · intro b hb
    simp only [mem_Ico] at hb ⊢
    refine ⟨2*m+1-b, ?_, ?_⟩
    · omega
    · omega
  · intro j hj
    simp only [mem_Ico] at hj
    have hjle : j ≤ 2*m+1 := by omega
    rw [Nat.cast_sub hjle]
    simp

lemma half_factorial_sq_zmod_expr (m : ℕ) [Fact (Nat.Prime (2*m+1))] :
    ((m.factorial : ZMod (2*m+1))^2) = (-1 : ZMod (2*m+1))^(m+1) := by
  have hw : (∏ x ∈ Finset.Ico 1 (2*m+1), (x : ZMod (2*m+1))) = -1 := ZMod.prod_Ico_one_prime (2*m+1)
  rw [prod_Ico_split_two_mul] at hw
  have hfirst : (∏ x ∈ Finset.Ico 1 (m+1), (x : ZMod (2*m+1))) = (m.factorial : ZMod (2*m+1)) := by
    rw [← Finset.prod_Ico_id_eq_factorial, Finset.prod_natCast]
  have hsecond : (∏ x ∈ Finset.Ico (m+1) (2*m+1), (x : ZMod (2*m+1))) = (-1 : ZMod (2*m+1))^m * (m.factorial : ZMod (2*m+1)) := by
    rw [prod_second_half_zmod]
    rw [Finset.prod_neg]
    have hcard : #(Finset.Ico 1 (m+1)) = m := by simp
    rw [hcard]
    rw [← Finset.prod_Ico_id_eq_factorial, Finset.prod_natCast]
  rw [hfirst, hsecond] at hw
  have hrel : (-1 : ZMod (2*m+1))^m * (m.factorial : ZMod (2*m+1))^2 = -1 := by
    calc
      (-1 : ZMod (2*m+1))^m * (m.factorial : ZMod (2*m+1))^2 = (m.factorial : ZMod (2*m+1)) * ((-1 : ZMod (2*m+1))^m * (m.factorial : ZMod (2*m+1))) := by ring
      _ = -1 := hw
  calc
    (m.factorial : ZMod (2*m+1))^2 = ((-1 : ZMod (2*m+1))^m * (-1 : ZMod (2*m+1))^m) * (m.factorial : ZMod (2*m+1))^2 := by
      rw [← pow_add]
      have : m + m = 2*m := by omega
      rw [this, pow_mul]
      simp
    _ = (-1 : ZMod (2*m+1))^m * ((-1 : ZMod (2*m+1))^m * (m.factorial : ZMod (2*m+1))^2) := by ring
    _ = (-1 : ZMod (2*m+1))^m * (-1 : ZMod (2*m+1)) := by rw [hrel]
    _ = (-1 : ZMod (2*m+1))^(m+1) := by rw [pow_succ]

lemma half_factorial_pow_succ_eq_one_iff_odd (N : ℕ) [Fact (Nat.Prime (2*N+1))] :
    ((N.factorial : ZMod (2*N+1))^(N+1) = 1) ↔ Odd N := by
  classical
  let f : ZMod (2*N+1) := N.factorial
  have hf2 : f^2 = (-1 : ZMod (2*N+1))^(N+1) := by
    simpa [f, pow_two] using half_factorial_sq_zmod_expr N
  constructor
  · intro h
    change f^(N+1) = 1 at h
    rcases Nat.even_or_odd N with hN | hN
    · exfalso
      have hNp1odd : Odd (N+1) := hN.add_odd odd_one
      have hleft : f^(2*(N+1)) = 1 := by
        rw [mul_comm 2 (N+1), pow_mul, h]
        simp
      have hright : f^(2*(N+1)) = -1 := by
        calc
          f^(2*(N+1)) = (f^2)^(N+1) := by rw [pow_mul]
          _ = ((-1 : ZMod (2*N+1))^(N+1))^(N+1) := by rw [hf2]
          _ = (-1 : ZMod (2*N+1))^((N+1)*(N+1)) := by rw [pow_mul]
          _ = -1 := Odd.neg_one_pow (hNp1odd.mul hNp1odd)
      have hone : (-1 : ZMod (2*N+1)) = 1 := by rw [← hright, hleft]
      have hpne2 : (2*N+1) ≠ 2 := by omega
      have hchar : ringChar (ZMod (2*N+1)) ≠ 2 := by
        simpa [ZMod.ringChar_zmod_n] using hpne2
      exact (Ring.neg_one_ne_one_of_char_ne_two hchar) hone
    · exact hN
  · intro hN
    rcases hN with ⟨k, hk⟩
    subst N
    change f^(2*k+1+1) = 1
    have hf2one : f^2 = 1 := by
      rw [hf2]
      have hev : Even (2*k+1+1) := by
        refine ⟨k+1, ?_⟩
        omega
      exact Even.neg_one_pow hev
    have hpow : 2*k+1+1 = 2*(k+1) := by omega
    rw [hpow]
    calc
      f^(2*(k+1)) = (f^2)^(k+1) := by rw [pow_mul]
      _ = 1 := by rw [hf2one, one_pow]

lemma two_mul_add_one_mod_four_eq_three_iff_odd (N : ℕ) :
    (2*N + 1) % 4 = 3 ↔ Odd N := by
  constructor
  · intro h
    rw [← Nat.not_even_iff_odd]
    intro he
    rcases he with ⟨k, hk⟩
    subst N
    omega
  · intro ho
    rcases ho with ⟨k, hk⟩
    subst N
    omega

lemma jacobi_det_mod_zero_iff_mod_four (N : ℕ) [Fact (Nat.Prime (2*N+1))]
    (hNpos : 0 < N) :
    ((((Matrix.of fun i j : Fin N => jacobiSym (((i.val+1:ℤ)^2) - (N.factorial : ℤ) * ((j.val+1:ℤ))) (2*N+1)).det : ℤ) : ZMod (2*N+1)) = 0)
      ↔ (2*N+1) % 4 = 3 := by
  have hd : ((N.factorial : ℤ) : ZMod (2*N+1)) ≠ 0 := by
    norm_cast
    apply zmod_nat_cast_ne_zero_of_not_dvd
    have hpprime : Nat.Prime (2*N+1) := Fact.out
    rw [hpprime.dvd_factorial]
    omega
  rw [jacobi_det_mod_zero_iff_scalar N (N.factorial : ℤ) hd]
  change ((N.factorial : ZMod (2*N+1))^N * (N.factorial : ZMod (2*N+1)) = 1) ↔ (2*N+1)%4=3
  rw [← pow_succ]
  rw [half_factorial_pow_succ_eq_one_iff_odd]
  exact (two_mul_add_one_mod_four_eq_three_iff_odd N).symm
set_option maxHeartbeats 5000000

open Finset
open scoped BigOperators

lemma quadraticChar_inv_eq_self {F : Type*} [Field F] [Fintype F] [DecidableEq F] :
    (quadraticChar F)⁻¹ = quadraticChar F := by
  apply MulChar.ext
  intro a
  rw [MulChar.inv_apply]
  have ha : (a : F) ≠ 0 := Units.ne_zero a
  rcases quadraticChar_dichotomy (F := F) ha with h | h
  · have hm : quadraticChar F ((a : F)⁻¹) * quadraticChar F (a : F) = 1 := by
      simpa using (map_mul (quadraticChar F) ((a : F)⁻¹) (a : F)).symm
    simpa [h] using hm
  · have hm : quadraticChar F ((a : F)⁻¹) * quadraticChar F (a : F) = 1 := by
      simpa using (map_mul (quadraticChar F) ((a : F)⁻¹) (a : F)).symm
    have : quadraticChar F ((a : F)⁻¹) = -1 := by
      nlinarith
    simpa [h, this]

lemma quadratic_char_monic_quad_sum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    (∑ t : F, quadraticChar F ((t - a) * (t - b))) = -1 := by
  classical
  let χ := quadraticChar F
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hsquare_factor : χ ((b - a)^2) = 1 := quadraticChar_sq_one' hne
  let e : Equiv.Perm F := (Equiv.mulLeft₀ (b-a) hne).trans (Equiv.addRight a)
  have he : ∀ x, e x = a + (b-a)*x := by intro x; simp [e, add_comm, mul_comm]
  calc
    (∑ t : F, χ ((t - a) * (t - b)))
        = ∑ x : F, χ (((a + (b-a)*x) - a) * ((a + (b-a)*x) - b)) := by
          rw [← Equiv.sum_comp e]
          apply sum_congr rfl
          intro x hx
          rw [he]
    _ = ∑ x : F, χ (((b-a)^2) * (x * (x - 1))) := by
          apply sum_congr rfl; intro x hx; congr 1; ring
    _ = ∑ x : F, χ (x * (x - 1)) := by
          apply sum_congr rfl; intro x hx
          rw [map_mul, hsquare_factor, one_mul]
    _ = ∑ x : F, χ x * χ (x - 1) := by simp [map_mul]
    _ = ∑ x : F, (χ x * χ (1 - x)) * χ (-1) := by
          apply sum_congr rfl; intro x hx
          have : x - 1 = (-1 : F) * (1 - x) := by ring
          rw [this, map_mul]
          ring
    _ = (jacobiSum χ χ) * χ (-1) := by
          rw [← Finset.sum_mul]
          simp [jacobiSum, mul_assoc]
    _ = (jacobiSum χ χ⁻¹) * χ (-1) := by rw [quadraticChar_inv_eq_self]
    _ = (-χ (-1)) * χ (-1) := by rw [jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)]
    _ = -1 := by
          have hsq := quadraticChar_sq_one (F:=F) (neg_ne_zero.mpr (one_ne_zero : (1:F)≠0))
          have hsq' : χ (-1) * χ (-1) = 1 := by simpa [χ, pow_two] using hsq
          rw [neg_mul, hsq']

lemma quadratic_char_skew_full_sum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (hneg : quadraticChar F (-1) = -1)
    {x y d : F} (hd : d ≠ 0) (hxy : x + y ≠ 0) :
    (∑ t : F, quadraticChar F ((x - d*t) * (y + d*t))) = 1 := by
  classical
  let χ := quadraticChar F
  -- (x-dt)(y+dt) = -d^2 * (t - x/d) * (t + y/d)
  let a : F := x / d
  let b : F := - y / d
  have hab : a ≠ b := by
    intro h
    have : x + y = 0 := by
      dsimp [a, b] at h
      field_simp [hd] at h
      rw [h]
      ring
    exact hxy this
  have hs := quadratic_char_monic_quad_sum (F:=F) hF (a:=a) (b:=b) hab
  have hfactor : χ (-(d^2)) = -1 := by
    have hd2 : d^2 ≠ 0 := pow_ne_zero 2 hd
    rw [show (-(d^2) : F) = (-1) * d^2 by ring, map_mul, hneg, quadraticChar_sq_one' hd]
    simp
  calc
    (∑ t : F, χ ((x - d*t) * (y + d*t)))
        = ∑ t : F, χ ((-(d^2)) * ((t - a) * (t - b))) := by
          apply sum_congr rfl
          intro t ht
          congr 1
          dsimp [a,b]
          field_simp [hd]
          ring
    _ = ∑ t : F, χ (-(d^2)) * χ ((t - a) * (t - b)) := by
          apply sum_congr rfl
          intro t ht
          rw [map_mul]
    _ = χ (-(d^2)) * (∑ t : F, χ ((t - a) * (t - b))) := by rw [Finset.mul_sum]
    _ = (-1) * (-1) := by rw [hfactor, hs]
    _ = 1 := by norm_num

noncomputable def finAddEquivUnits (m : ℕ) [Fact (Nat.Prime (2*m+1))]
    (d : ZMod (2*m+1)) (hd : d ≠ 0) : Fin (m+m) ≃ (ZMod (2*m+1))ˣ := by
  let f : Fin (m+m) → (ZMod (2*m+1))ˣ := fun k =>
    Units.mk0 (d * (((k.val+1:ℕ) : ZMod (2*m+1)))) (by
      apply mul_ne_zero hd
      apply zmod_nat_cast_ne_zero_of_pos_lt <;> omega)
  refine Equiv.ofBijective f ?_
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro a b h
    apply Fin.ext
    have hv : d * (((a.val+1:ℕ) : ZMod (2*m+1))) = d * (((b.val+1:ℕ) : ZMod (2*m+1))) := by
      exact congrArg (fun u : (ZMod (2*m+1))ˣ => (u : ZMod (2*m+1))) h
    have hc := mul_left_cancel₀ hd hv
    have ha_lt : a.val+1 < 2*m+1 := by omega
    have hb_lt : b.val+1 < 2*m+1 := by omega
    have hnat := zmod_nat_cast_eq_of_lt ha_lt hb_lt hc
    omega
  · rw [Fintype.card_fin, ZMod.card_units]
    omega

lemma sum_units_split_half (m : ℕ) [Fact (Nat.Prime (2*m+1))]
    (d : ZMod (2*m+1)) (hd : d ≠ 0) (f : ZMod (2*m+1) → ℤ) :
    (∑ u : (ZMod (2*m+1))ˣ, f (u : ZMod (2*m+1))) =
      (∑ j : Fin m, f (d * (((j.val+1:ℕ) : ZMod (2*m+1))))) +
      (∑ j : Fin m, f (-(d * (((j.val+1:ℕ) : ZMod (2*m+1)))))) := by
  classical
  let e := finAddEquivUnits m d hd
  rw [← Equiv.sum_comp e (fun u : (ZMod (2*m+1))ˣ => f (u : ZMod (2*m+1)))]
  dsimp [e, finAddEquivUnits]
  rw [Fin.sum_univ_add]
  congr 1
  simp only [Fin.val_natAdd]
  rw [← Equiv.sum_comp (Fin.revPerm (n:=m)) (fun j : Fin m => f (d * (((m + j.val + 1:ℕ) : ZMod (2*m+1)))))]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have hval : (m + (Fin.revPerm (n:=m) j).val + 1 : ℕ) = (2*m+1) - (j.val+1) := by
    simp [Fin.revPerm, Fin.val_rev]
    omega
  rw [hval]
  have hle : j.val + 1 ≤ 2*m+1 := by omega
  rw [Nat.cast_sub hle]
  have hmod : ((2*m+1 : ℕ) : ZMod (2*m+1)) = 0 := by simp
  change d * (((2*m+1 : ℕ) : ZMod (2*m+1)) - (((j.val+1:ℕ) : ZMod (2*m+1)))) = -(d * (((j.val+1:ℕ) : ZMod (2*m+1))))
  rw [hmod, zero_sub, mul_neg]

lemma sum_field_eq_zero_add_units {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (f : F → ℤ) :
    (∑ t : F, f t) = f 0 + ∑ u : Fˣ, f (u : F) := by
  classical
  let phi : Fˣ ↪ F := ⟨fun x => x, Units.val_injective⟩
  have hmap : (Finset.univ.map phi) = (Finset.univ \ ({0} : Finset F)) := by
    ext x
    simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Finset.mem_sdiff, Finset.mem_singleton, phi] using isUnit_iff_ne_zero
  calc
    (∑ t : F, f t) = f 0 + ∑ t ∈ Finset.univ \ ({0} : Finset F), f t := by
      rw [← Finset.sum_sdiff ({0} : Finset F).subset_univ, Finset.sum_singleton, add_comm]
    _ = f 0 + ∑ u : Fˣ, f (u : F) := by
      rw [← hmap]
      simp [phi]

lemma quadratic_char_half_skew_sum (m : ℕ) [Fact (Nat.Prime (2*m+1))]
    (hp3 : (2*m+1) % 4 = 3) (d x y : ZMod (2*m+1))
    (hd : d ≠ 0) (hx : quadraticChar (ZMod (2*m+1)) x = 1)
    (hy : quadraticChar (ZMod (2*m+1)) y = 1) :
    (∑ j : Fin m, quadraticChar (ZMod (2*m+1)) ((x - d*((j.val+1:ℕ):ZMod (2*m+1))) * (y + d*((j.val+1:ℕ):ZMod (2*m+1))))) +
    (∑ j : Fin m, quadraticChar (ZMod (2*m+1)) ((y - d*((j.val+1:ℕ):ZMod (2*m+1))) * (x + d*((j.val+1:ℕ):ZMod (2*m+1))))) = 0 := by
  classical
  have hchar : ringChar (ZMod (2*m+1)) ≠ 2 := by
    have hpne : 2*m+1 ≠ 2 := by omega
    simpa [ZMod.ringChar_zmod_n] using hpne
  have hneg : quadraticChar (ZMod (2*m+1)) (-1) = -1 := by
    rw [quadraticChar_neg_one hchar, ZMod.card]
    exact ZMod.χ₄_nat_three_mod_four hp3
  have hxy : x + y ≠ 0 := by
    intro hsum
    have hyx : y = -x := by
      rw [← sub_eq_zero, sub_neg_eq_add]
      simpa [add_comm] using hsum
    rw [hyx, neg_eq_neg_one_mul, map_mul, hneg, hx] at hy
    norm_num at hy
  let f : ZMod (2*m+1) → ℤ := fun t => quadraticChar (ZMod (2*m+1)) ((x - t) * (y + t))
  have hfull : (∑ t : ZMod (2*m+1), f t) = 1 := by
    simpa [f, one_mul] using (quadratic_char_skew_full_sum (F:=ZMod (2*m+1)) hchar hneg (show (1 : ZMod (2*m+1)) ≠ 0 by exact one_ne_zero) hxy)
  have hf0 : f 0 = 1 := by
    dsimp [f]
    show quadraticChar (ZMod (2*m+1)) ((x - 0) * (y + 0)) = 1
    rw [sub_zero, add_zero, map_mul, hx, hy, one_mul]
  have hsplit := sum_units_split_half m d hd f
  have hall := sum_field_eq_zero_add_units f
  have hunits : (∑ u : (ZMod (2*m+1))ˣ, f (u : ZMod (2*m+1))) = 0 := by
    rw [hfull, hf0] at hall
    omega
  -- rewrite target second sum as f at negative half
  have htarget_eq :
    (∑ j : Fin m, quadraticChar (ZMod (2*m+1)) ((x - d*((j.val+1:ℕ):ZMod (2*m+1))) * (y + d*((j.val+1:ℕ):ZMod (2*m+1))))) +
    (∑ j : Fin m, quadraticChar (ZMod (2*m+1)) ((y - d*((j.val+1:ℕ):ZMod (2*m+1))) * (x + d*((j.val+1:ℕ):ZMod (2*m+1)))))
    = (∑ j : Fin m, f (d * (((j.val+1:ℕ):ZMod (2*m+1))))) +
      (∑ j : Fin m, f (-(d * (((j.val+1:ℕ):ZMod (2*m+1)))))) := by
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [f]
    congr 1
    ring
  rw [htarget_eq, ← hsplit, hunits]

lemma jacobi_product_term_eq (p m : ℕ) [Fact p.Prime] (hp : p = 2*m+1)
    (d : ℤ) (i k j : Fin m) :
    jacobiSym (((i.val+1:ℤ)^2) - d * ((j.val+1:ℤ))) p *
      jacobiSym (((k.val+1:ℤ)^2) + d * ((j.val+1:ℤ))) p =
    quadraticChar (ZMod p)
      (((((i.val+1:ℕ):ZMod p)^2) - (d:ZMod p)*((j.val+1:ℕ):ZMod p)) *
       ((((k.val+1:ℕ):ZMod p)^2) + (d:ZMod p)*((j.val+1:ℕ):ZMod p))) := by
  rw [← jacobiSym.legendreSym.to_jacobiSym p, ← jacobiSym.legendreSym.to_jacobiSym p]
  simp only [legendreSym]
  rw [← map_mul]
  congr 1
  push_cast
  ring

lemma jacobi_mul_transpose_skew (m : ℕ) [Fact (Nat.Prime (2*m+1))]
    (hp3 : (2*m+1) % 4 = 3) (d : ℤ) (hd : (d : ZMod (2*m+1)) ≠ 0) :
    let A : Matrix (Fin m) (Fin m) ℤ := fun i j =>
      jacobiSym (((i.val+1:ℤ)^2) - d * ((j.val+1:ℤ))) (2*m+1)
    let B : Matrix (Fin m) (Fin m) ℤ := fun i j =>
      jacobiSym (((i.val+1:ℤ)^2) - (-d) * ((j.val+1:ℤ))) (2*m+1)
    (A * B.transpose).transpose = -(A * B.transpose) := by
  classical
  intro A B
  ext i k
  simp [Matrix.mul_apply, Matrix.transpose_apply, A, B]
  -- goal sums; convert lhs + rhs = 0 using half_skew
  apply add_eq_zero_iff_eq_neg.mp
  have hs := quadratic_char_half_skew_sum m hp3 (d : ZMod (2*m+1))
    ((((i.val+1:ℕ):ZMod (2*m+1))^2)) ((((k.val+1:ℕ):ZMod (2*m+1))^2)) hd
    (quadraticChar_sq_one' (F:=ZMod (2*m+1)) (by apply zmod_nat_cast_ne_zero_of_pos_lt <;> omega))
    (quadraticChar_sq_one' (F:=ZMod (2*m+1)) (by apply zmod_nat_cast_ne_zero_of_pos_lt <;> omega))
  let xi : ZMod (2*m+1) := (((i.val+1:ℕ):ZMod (2*m+1))^2)
  let xk : ZMod (2*m+1) := (((k.val+1:ℕ):ZMod (2*m+1))^2)
  let q1 : Fin m → ℤ := fun j => quadraticChar (ZMod (2*m+1)) ((xi - (d:ZMod (2*m+1))*((j.val+1:ℕ):ZMod (2*m+1))) * (xk + (d:ZMod (2*m+1))*((j.val+1:ℕ):ZMod (2*m+1))))
  let q2 : Fin m → ℤ := fun j => quadraticChar (ZMod (2*m+1)) ((xk - (d:ZMod (2*m+1))*((j.val+1:ℕ):ZMod (2*m+1))) * (xi + (d:ZMod (2*m+1))*((j.val+1:ℕ):ZMod (2*m+1))))
  have hs' : (∑ j : Fin m, q2 j) + (∑ j : Fin m, q1 j) = 0 := by
    simpa [q1, q2, xi, xk, add_comm, add_left_comm, add_assoc] using hs
  calc
    (∑ x : Fin m, jacobiSym ((↑↑k + 1) ^ 2 - d * (↑↑x + 1)) (2 * m + 1) *
          jacobiSym ((↑↑i + 1) ^ 2 + d * (↑↑x + 1)) (2 * m + 1)) +
        (∑ x : Fin m, jacobiSym ((↑↑i + 1) ^ 2 - d * (↑↑x + 1)) (2 * m + 1) *
          jacobiSym ((↑↑k + 1) ^ 2 + d * (↑↑x + 1)) (2 * m + 1))
        = (∑ j : Fin m, q2 j) + (∑ j : Fin m, q1 j) := by
            congr 1
            · apply Finset.sum_congr rfl
              intro j hj
              dsimp [q2]
              convert jacobi_product_term_eq (2*m+1) m rfl d k i j using 1 <;> ring
            · apply Finset.sum_congr rfl
              intro j hj
              dsimp [q1]
              convert jacobi_product_term_eq (2*m+1) m rfl d i k j using 1 <;> ring
    _ = 0 := hs' 

open Matrix

lemma det_eq_zero_of_skew_odd {m : ℕ} (hm : Odd m) (K : Matrix (Fin m) (Fin m) ℤ)
    (hskew : Kᵀ = -K) : K.det = 0 := by
  have hneg : (-K).det = (-1 : ℤ) ^ m * K.det := by
    simpa using Matrix.det_neg K
  have hoddpow : (-1 : ℤ) ^ m = -1 := Odd.neg_one_pow hm
  have heq : K.det = - K.det := by
    calc
      K.det = Kᵀ.det := by rw [Matrix.det_transpose]
      _ = (-K).det := by rw [hskew]
      _ = (-1 : ℤ)^m * K.det := hneg
      _ = - K.det := by rw [hoddpow, neg_one_mul]
  omega

lemma det_left_zero_of_mul_transpose_skew_odd {m : ℕ} (hm : Odd m)
    (A B : Matrix (Fin m) (Fin m) ℤ) (hB : B.det ≠ 0)
    (hskew : (A * Bᵀ)ᵀ = -(A * Bᵀ)) : A.det = 0 := by
  have hK := det_eq_zero_of_skew_odd hm (A * Bᵀ) hskew
  rw [Matrix.det_mul, Matrix.det_transpose] at hK
  exact Or.resolve_right (mul_eq_zero.mp hK) hB

lemma jacobi_det_int_zero_iff_mod_four (m : ℕ) [Fact (Nat.Prime (2*m+1))] (hmpos : 0 < m) :
    (Matrix.of fun i j : Fin m => jacobiSym (((i.val+1:ℤ)^2) - (m.factorial : ℤ) * ((j.val+1:ℤ))) (2*m+1)).det = 0
      ↔ (2*m+1) % 4 = 3 := by
  classical
  constructor
  · intro hzero
    have hmod : ((((Matrix.of fun i j : Fin m => jacobiSym (((i.val+1:ℤ)^2) - (m.factorial : ℤ) * ((j.val+1:ℤ))) (2*m+1)).det : ℤ) : ZMod (2*m+1)) = 0) := by
      rw [hzero]
      norm_num
    exact (jacobi_det_mod_zero_iff_mod_four m hmpos).mp hmod
  · intro hp3
    let A : Matrix (Fin m) (Fin m) ℤ := fun i j => jacobiSym (((i.val+1:ℤ)^2) - (m.factorial : ℤ) * ((j.val+1:ℤ))) (2*m+1)
    let B : Matrix (Fin m) (Fin m) ℤ := fun i j => jacobiSym (((i.val+1:ℤ)^2) - (-(m.factorial : ℤ)) * ((j.val+1:ℤ))) (2*m+1)
    have hCne : ((m.factorial : ℤ) : ZMod (2*m+1)) ≠ 0 := by
      norm_cast
      apply zmod_nat_cast_ne_zero_of_not_dvd
      have hpprime : Nat.Prime (2*m+1) := Fact.out
      rw [hpprime.dvd_factorial]
      omega
    have hBne : B.det ≠ 0 := by
      intro hBzero
      have hBmod : (((B.det : ℤ) : ZMod (2*m+1)) = 0) := by rw [hBzero]; norm_num
      have hcrit := (jacobi_det_mod_zero_iff_scalar m (-(m.factorial : ℤ)) ?_).mp ?_
      · -- scalar contradiction
        have hodd : Odd m := (two_mul_add_one_mod_four_eq_three_iff_odd m).mp hp3
        have hpow : ((m.factorial : ZMod (2*m+1))^(m+1) = 1) := (half_factorial_pow_succ_eq_one_iff_odd m).mpr hodd
        have hcrit' : (-(m.factorial : ZMod (2*m+1)))^m * (m.factorial : ZMod (2*m+1)) = 1 := by
          simpa only [Int.cast_neg, Int.cast_natCast] using hcrit
        have hcalc : (-(m.factorial : ZMod (2*m+1)))^m * (m.factorial : ZMod (2*m+1)) = -1 := by
          rw [neg_eq_neg_one_mul, mul_pow]
          rw [Odd.neg_one_pow hodd]
          rw [show (-1 : ZMod (2*m+1)) * (m.factorial : ZMod (2*m+1))^m * (m.factorial : ZMod (2*m+1)) = -((m.factorial : ZMod (2*m+1))^(m+1)) by rw [pow_succ]; ring]
          rw [hpow]
        rw [hcalc] at hcrit'
        have hpne2 : 2*m+1 ≠ 2 := by omega
        have hchar : ringChar (ZMod (2*m+1)) ≠ 2 := by simpa [ZMod.ringChar_zmod_n] using hpne2
        exact (Ring.neg_one_ne_one_of_char_ne_two hchar) hcrit'
      · simpa using (neg_ne_zero.mpr hCne)
      · simpa [B] using hBmod
    have hskew : (A * B.transpose).transpose = -(A * B.transpose) := by
      simpa [A, B] using jacobi_mul_transpose_skew m hp3 (m.factorial : ℤ) hCne
    have hmodd : Odd m := (two_mul_add_one_mod_four_eq_three_iff_odd m).mp hp3
    have hAzero : A.det = 0 := det_left_zero_of_mul_transpose_skew_odd hmodd A B hBne hskew
    simpa [A] using hAzero

/--
Conjecture: a(n) = 0 if and only if p_n ≡ 3 (mod 4).
-/
theorem oeis_226163_conjecture_0 (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  classical
  let p : ℕ := Nat.nth Nat.Prime (n - 1)
  let m : ℕ := (p - 1) / 2
  have hpprime : Nat.Prime p := by simpa [p] using Nat.prime_nth_prime (n - 1)
  have hge3 : 3 ≤ p := by
    have h1 : 1 ≤ n - 1 := by omega
    have hle := Nat.add_two_le_nth_prime (n - 1)
    dsimp [p]
    omega
  have hpne2 : p ≠ 2 := by omega
  have hpodd : Odd p := hpprime.odd_of_ne_two hpne2
  have hp_eq : p = 2*m + 1 := by
    rcases hpodd with ⟨k, hk⟩
    have hm_eq : m = k := by
      dsimp [m]
      rw [hk]
      simp
    rw [hk, hm_eq]
  have hmpos : 0 < m := by omega
  letI : Fact (Nat.Prime (2*m+1)) := ⟨by simpa [← hp_eq] using hpprime⟩
  have hgen := jacobi_det_int_zero_iff_mod_four m hmpos
  have hnot : ¬ n < 2 := by omega
  rw [A226163, dif_neg hnot]
  dsimp only
  change (Matrix.of (fun i j : Fin m => jacobiSym (((i.val + 1 : ℤ) * (i.val + 1 : ℤ)) - (m.factorial : ℤ) * (j.val + 1 : ℤ)) p)).det = 0 ↔ p % 4 = 3
  rw [hp_eq]
  simpa [pow_two] using hgen
