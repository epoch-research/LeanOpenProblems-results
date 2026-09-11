import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A357565: $a(n) = 3 \sum_{k = 0}^n \binom{n+k-1}{k}^2 + 2 \sum_{k = 0}^n \binom{n+k-1}{k}^3$.
-/
def A357565 (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    let b := choose (n + k - 1) k
    3 * b ^ 2 + 2 * b ^ 3

/--
The generalized sequence $u(n, m)$ from the conjecture section:
$u(n, m) = (m + 2) \sum_{k = 0}^{m \cdot n} \binom{n+k-1}{k}^2 + 2m \sum_{k = 0}^{m \cdot n} \binom{n+k-1}{k}^3$.
Note that $A357565(n) = A357565\_u(n, 1)$.
-/
def A357565_u (n m : ℕ) : ℕ :=
  (range (m * n + 1)).sum fun k =>
    (m + 2) * (choose (n + k - 1) k) ^ 2 + (2 * m) * (choose (n + k - 1) k) ^ 3

/-! Auxiliary p-adic estimates and finite-sum identities. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace A357565Proof

/-- Divisibility in the localization of the rationals at `p`, allowing integral exponents. -/
def D (p : ℕ) (e : ℤ) (x : ℚ) : Prop := padicNorm p x ≤ (p : ℚ) ^ (-e)

abbrev C (p : ℕ) (e : ℤ) (x y : ℚ) : Prop := D p e (x - y)

variable {p : ℕ} [hp : Fact p.Prime]

lemma p_pos : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
lemma p_ne : (p : ℚ) ≠ 0 := ne_of_gt p_pos
lemma p_one : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_le

namespace D
variable {a b e : ℤ} {x y : ℚ}

lemma zero (e : ℤ) : D p e 0 := by
  exact (padicNorm.zero.trans_le (zpow_nonneg (le_of_lt p_pos) _))

lemma mono (h : D p b x) (he : a ≤ b) : D p a x :=
  h.trans (zpow_le_zpow_right₀ p_one (neg_le_neg he))

lemma add (hx : D p e x) (hy : D p e y) : D p e (x + y) :=
  padicNorm.nonarchimedean.trans (max_le hx hy)

lemma neg (hx : D p e x) : D p e (-x) := by simpa [D] using hx

lemma sub (hx : D p e x) (hy : D p e y) : D p e (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

lemma mul (hx : D p a x) (hy : D p b y) : D p (a + b) (x * y) := by
  unfold D at *
  rw [padicNorm.mul, neg_add, zpow_add₀ p_ne]
  exact mul_le_mul hx hy (padicNorm.nonneg _) (zpow_nonneg (le_of_lt p_pos) _)

lemma mul_of_le (hx : D p a x) (hy : D p b y) (h : e ≤ a + b) : D p e (x * y) :=
  (hx.mul hy).mono h

lemma nat (n : ℕ) : D p 0 n := by simpa [D] using padicNorm.of_nat (p := p) n
lemma int (n : ℤ) : D p 0 n := by simpa [D] using padicNorm.of_int (p := p) n
lemma one : D p 0 1 := by simpa using nat (p := p) 1

lemma pow (hx : D p a x) (n : ℕ) : D p (a * n) (x ^ n) := by
  induction n with
  | zero => simpa using (one (p := p))
  | succ n ih =>
    convert ih.mul hx using 1 <;> push_cast <;> ring

lemma prime : D p 1 p := by simp [D, zpow_neg_one]

lemma prime_pow (n : ℕ) : D p n ((p : ℚ) ^ n) := by simpa using (prime (p := p)).pow n

lemma norm_pow (x : ℚ) (n : ℕ) : padicNorm p (x ^ n) = (padicNorm p x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, padicNorm.mul, ih]

lemma norm_inv (x : ℚ) : padicNorm p x⁻¹ = (padicNorm p x)⁻¹ := by
  simpa only [one_div, padicNorm.one] using padicNorm.div (p := p) 1 x

lemma prime_zpow (n : ℤ) : D p n ((p : ℚ) ^ n) := by
  cases n with
  | ofNat n => simpa using prime_pow (p := p) n
  | negSucc n =>
    simp only [D, zpow_negSucc, norm_inv,
      norm_pow, padicNorm.padicNorm_p_of_prime, Int.neg_negSucc, zpow_natCast,
      inv_pow, inv_inv]
    rfl

lemma mul_prime_zpow (hx : D p a x) (b : ℤ) : D p (a + b) (x * (p : ℚ) ^ b) :=
  hx.mul (prime_zpow b)

lemma inv_nat (n : ℕ) (hn : ¬p ∣ n) : D p 0 (n : ℚ)⁻¹ := by
  simp only [D, neg_zero, zpow_zero, inv_eq_one_div, padicNorm.div, padicNorm.one]
  rw [(padicNorm.nat_eq_one_iff n).mpr hn]
  norm_num

lemma div_nat (hx : D p e x) (n : ℕ) (hn : ¬p ∣ n) : D p e (x / n) := by
  simpa [div_eq_mul_inv] using hx.mul (inv_nat n hn)

lemma sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, D p e (f i)) :
    D p e (∑ i ∈ s, f i) := by
  exact padicNorm.sum_le' h (zpow_nonneg (le_of_lt p_pos) _)

lemma of_dvd {n : ℕ} {z : ℤ} (h : ((p ^ n : ℕ) : ℤ) ∣ z) : D p n z :=
  padicNorm.dvd_iff_norm_le.mp h

lemma to_dvd {n : ℕ} {z : ℤ} (h : D p n z) : ((p ^ n : ℕ) : ℤ) ∣ z :=
  padicNorm.dvd_iff_norm_le.mpr h

lemma nat_valuation (n : ℕ) : D p (padicValNat p n) n := by
  apply of_dvd
  exact_mod_cast pow_padicValNat_dvd

lemma inv_nat_valuation (n : ℕ) (hn : n ≠ 0) :
    D p (-(padicValNat p n : ℤ)) (n : ℚ)⁻¹ := by
  unfold D
  rw [norm_inv, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn)]
  simp only [padicValRat.of_nat, zpow_neg, inv_inv, neg_neg]
  rfl

lemma div_valuation (hx : D p a x) (n : ℕ) (hn : n ≠ 0) :
    D p (a - padicValNat p n) (x / n) := by
  simpa [div_eq_mul_inv, sub_eq_add_neg] using hx.mul (inv_nat_valuation n hn)

lemma inv_small (n : ℕ) (hn : 0 < n) (hnp : n < p) : D p 0 (n : ℚ)⁻¹ :=
  inv_nat n (Nat.not_dvd_of_pos_of_lt hn hnp)

lemma prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, D p 0 (f i)) :
    D p 0 (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one (p := p))
  | @insert i s hi ih =>
    rw [prod_insert hi]
    simpa using (h i (mem_insert_self i s)).mul
      (ih (fun j hj => h j (mem_insert_of_mem hj)))

lemma prod_one_add {ι : Type*} (s : Finset ι) (f : ι → ℚ) (he : 0 ≤ e)
    (h : ∀ i ∈ s, D p e (f i)) : D p e ((∏ i ∈ s, (1 + f i)) - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (p := p) e)
  | @insert i s hi ih =>
    rw [prod_insert hi]
    have hf := h i (mem_insert_self i s)
    have hrest := ih (fun j hj => h j (mem_insert_of_mem hj))
    have hint : D p 0 (∏ j ∈ s, (1 + f j)) := prod s _ (fun j hj =>
      (one (p := p)).add ((h j (mem_insert_of_mem hj)).mono he))
    have hm : D p e (f i * ∏ j ∈ s, (1 + f j)) := by simpa using hf.mul hint
    convert hm.add hrest using 1 <;> ring

lemma den (h : D p 0 x) : ¬p ∣ x.den := by
  intro hd
  have hn : ¬(p : ℤ) ∣ x.num := by
    intro hn
    have hn' : p ∣ x.num.natAbs := Int.natCast_dvd.mp hn
    have he := Nat.eq_one_of_dvd_coprimes x.reduced hn' hd
    exact hp.out.ne_one he
  have hvn : padicNorm p x.num = 1 := (padicNorm.int_eq_one_iff x.num).mpr hn
  have hvd : padicNorm p x.den < 1 := (padicNorm.nat_lt_one_iff x.den).mpr hd
  have hvdpos : 0 < padicNorm p x.den := lt_of_le_of_ne
    (padicNorm.nonneg _) (Ne.symm (padicNorm.nonzero (by exact_mod_cast x.den_ne_zero)))
  have hx : padicNorm p x = 1 / padicNorm p x.den := by
    nth_rw 1 [← x.num_div_den]
    rw [padicNorm.div, hvn]
  have hh : 1 / padicNorm p x.den ≤ 1 := by simpa [D, hx] using h
  have hh' : 1 ≤ padicNorm p x.den := by simpa using (div_le_iff₀ hvdpos).mp hh
  exact (not_le_of_gt hvd) hh'

lemma of_den (h : ¬p ∣ x.den) : D p 0 x := by
  rw [← x.num_div_den]
  exact div_nat (int _) _ h

lemma den_cast (h : D p 0 x) : (x.den : ZMod p) ≠ 0 := by
  simpa only [ne_eq, ZMod.natCast_eq_zero_iff] using h.den

lemma cast_zero_iff (h : D p 0 x) : (x : ZMod p) = 0 ↔ D p 1 x := by
  have hnorm : padicNorm p x = padicNorm p x.num := by
    nth_rw 1 [← x.num_div_den]
    rw [padicNorm.div, (padicNorm.nat_eq_one_iff x.den).mpr h.den, div_one]
  rw [Rat.cast_def, div_eq_zero_iff]
  simp only [h.den_cast, or_false]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  change (p : ℤ) ∣ x.num ↔ padicNorm p x ≤ (p : ℚ) ^ (-1 : ℤ)
  rw [hnorm]
  simpa using (padicNorm.dvd_iff_norm_le (p := p) (n := 1) (z := x.num))


lemma norm_one_add (hx : D p 1 x) : padicNorm p (1 + x) = 1 := by
  have hlt : padicNorm p x < 1 := hx.trans_lt (by
    simpa using padicNorm.padicNorm_p_lt_one_of_prime (p := p))
  rw [padicNorm.add_eq_max_of_ne, padicNorm.one, max_eq_left hlt.le]
  simpa using ne_of_gt hlt

lemma one_add_ne (hx : D p 1 x) : 1 + x ≠ 0 := by
  intro h
  have := norm_one_add hx
  simp [h] at this

lemma inv_one_add (hx : D p 1 x) : D p 0 (1 + x)⁻¹ := by
  simp [D, norm_inv, norm_one_add hx]


lemma of_nat_dvd {n v : ℕ} (h : p ^ v ∣ n) : D p v (n : ℚ) := by
  have h' : ((p ^ v : ℕ) : ℤ) ∣ (n : ℤ) := by exact_mod_cast h
  simpa using of_dvd h'


lemma cancel_nat {n : ℕ} (hn : ¬p ∣ n) (h : D p e ((n : ℚ) * x)) : D p e x := by
  simpa only [D, padicNorm.mul, (padicNorm.nat_eq_one_iff n).mpr hn, one_mul] using h


lemma cancel_prime (a : ℤ) (h : D p (a + 1) ((p : ℚ) * x)) : D p a x := by
  have ht := h.div_valuation p hp.out.ne_zero
  have hn : (p : ℚ) ≠ 0 := p_ne
  simpa only [padicValNat.self hp.out.one_lt, Nat.cast_one, add_sub_cancel_right,
    mul_div_cancel_left₀ _ hn] using ht


lemma prod_same {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, D p e (f i)) :
    D p (e * s.card) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one (p := p)
  | @insert i s hi ih =>
    rw [prod_insert hi, card_insert_of_notMem hi]
    convert (h i (mem_insert_self _ _)).mul
      (ih (fun j hj => h j (mem_insert_of_mem hj))) using 1 <;> push_cast <;> ring


end D

namespace C
variable {a b e : ℤ} {x y z u v : ℚ}
lemma refl (x : ℚ) (e : ℤ) : C p e x x := by simpa [C] using D.zero (p := p) e
lemma symm (h : C p e x y) : C p e y x := by
  simpa only [neg_sub] using h.neg
lemma trans (h : C p e x y) (h' : C p e y z) : C p e x z := by
  dsimp only [C] at *
  convert D.add h h' using 1 <;> ring
lemma mono (h : C p b x y) (he : a ≤ b) : C p a x y := D.mono h he
lemma add (h : C p e x y) (h' : C p e u v) : C p e (x + u) (y + v) := by
  dsimp only [C] at *
  convert D.add h h' using 1 <;> ring
lemma sub (h : C p e x y) (h' : C p e u v) : C p e (x - u) (y - v) := by
  dsimp only [C] at *
  convert D.sub h h' using 1 <;> ring
lemma neg (h : C p e x y) : C p e (-x) (-y) := by
  dsimp only [C] at *
  convert D.neg h using 1 <;> ring
lemma mul_left (h : C p a x y) (hz : D p b z) : C p (a + b) (z * x) (z * y) := by
  dsimp only [C] at *
  convert D.mul h hz using 1 <;> ring
lemma mul_right (h : C p a x y) (hz : D p b z) : C p (a + b) (x * z) (y * z) := by
  dsimp only [C] at *
  convert D.mul h hz using 1 <;> ring
lemma sum {ι : Type*} (s : Finset ι) (f g : ι → ℚ) (h : ∀ i ∈ s, C p e (f i) (g i)) :
    C p e (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  simpa [C, ← sum_sub_distrib] using D.sum s (fun i => f i - g i) h
lemma dvd_left (h : C p e x y) (hy : D p e y) : D p e x := by
  have := D.add h hy
  simpa only [sub_add_cancel] using this

lemma dvd_right (h : C p e x y) (hx : D p e x) : D p e y := h.symm.dvd_left hx


lemma sum_range_trunc (f : ℕ → ℚ) (K d : ℕ) (hd : d ≤ K)
    (h : ∀ k, d ≤ k → k < K → D p e (f k)) :
    C p e (∑ k ∈ range K, f k) (∑ k ∈ range d, f k) := by
  have hsum : D p e (∑ j ∈ range (K - d), f (d + j)) := by
    apply D.sum
    intro j hj
    exact h _ (by omega) (by have := mem_range.mp hj; omega)
  rw [show K = d + (K - d) by omega, sum_range_add]
  dsimp only [C]
  convert hsum using 1 <;> ring


lemma mul (hxy : C p e x y) (huv : C p e u v) (hx : D p 0 x) (hv : D p 0 v) :
    C p e (x * u) (y * v) := by
  have h1 : D p e ((x - y) * v) := by simpa using D.mul hxy hv
  have h2 : D p e ((u - v) * x) := by simpa using D.mul huv hx
  dsimp only [C]
  convert D.add h1 h2 using 1 <;> ring

lemma pow (hxy : C p e x y) (hx : D p 0 x) (hy : D p 0 y) (n : ℕ) :
    C p e (x ^ n) (y ^ n) := by
  induction n with
  | zero => simpa using refl (p := p) 1 e
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact C.mul ih hxy (by simpa using hx.pow n) hy


end C

lemma cast_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, D p 0 (f i)) :
    ((∑ i ∈ s, f i : ℚ) : ZMod p) = ∑ i ∈ s, (f i : ZMod p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi,
      Rat.cast_add_of_ne_zero (h i (mem_insert_self _ _)).den_cast
        (D.sum s _ (fun j hj => h j (mem_insert_of_mem hj))).den_cast,
      ih (fun j hj => h j (mem_insert_of_mem hj))]

lemma sum_blocks {R : Type*} [AddCommMonoid R] (f : ℕ → R) (m n : ℕ) :
    ∑ k ∈ range (m * n), f k = ∑ i ∈ range m, ∑ j ∈ range n, f (i * n + j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]


lemma sum_zmod_range {R : Type*} [AddCommMonoid R] (f : ZMod p → R) :
    (∑ i ∈ range p, f i) = ∑ z : ZMod p, f z := by
  let E : Fin p ≃ ZMod p :=
    { toFun := fun i => i.val
      invFun := fun z => ⟨z.val, ZMod.val_lt z⟩
      left_inv := by intro i; apply Fin.ext; simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]
      right_inv := by intro z; exact ZMod.natCast_zmod_val z }
  rw [← Fin.sum_univ_eq_sum_range]
  exact E.sum_comp f

def PS (n k : ℕ) : ℚ := ∑ i ∈ range n, (i : ℚ) ^ k

lemma PS_integral (n k : ℕ) : D p 0 (PS n k) := by
  apply D.sum
  intro i hi
  simpa using (D.nat (p := p) i).pow k

lemma PS_zero (n : ℕ) : PS n 0 = n := by simp [PS]

lemma PS_prime (k : ℕ) (hk : k < p - 1) : D p 1 (PS p k) := by
  apply (D.cast_zero_iff (PS_integral p k)).mp
  rw [PS, cast_sum _ _ (fun i _ => by simpa using (D.nat (p := p) i).pow k)]
  simp only [Rat.cast_pow, Rat.cast_natCast]
  rw [sum_zmod_range (fun z : ZMod p => z ^ k)]
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) k (by simpa using hk)

lemma PS_blocks (n m k : ℕ) : PS (m * n) k =
    ∑ a ∈ range (k + 1), (k.choose a : ℚ) * (n : ℚ) ^ a * PS m a * PS n (k - a) := by
  rw [PS, sum_blocks]
  simp only [Nat.cast_add, Nat.cast_mul, add_pow]
  calc
    _ = ∑ i ∈ range m, ∑ a ∈ range (k + 1), ∑ j ∈ range n,
        (k.choose a : ℚ) * (n : ℚ) ^ a * (i : ℚ) ^ a * (j : ℚ) ^ (k - a) := by
      apply sum_congr rfl
      intro i hi
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      simp only [← mul_sum]
      rw [← sum_mul, ← mul_sum]
      rfl


lemma PS_pow_mul_weak (v m k : ℕ) : D p ((v : ℤ) - 1) (PS (p ^ v * m) k) := by
  induction v generalizing m k with
  | zero =>
    simpa using (PS_integral (p := p) m k).mono (by omega : (-1 : ℤ) ≤ 0)
  | succ v ih =>
    rw [show p ^ (v + 1) * m = (p ^ v * m) * p by ring, PS_blocks]
    apply D.sum
    intro a ha
    by_cases ha0 : a = 0
    · subst a
      simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, PS_zero,
        Nat.sub_zero, Nat.cast_mul, Nat.cast_pow]
      exact (((D.prime_pow (p := p) v).mul (D.nat m)).mul
        (PS_integral p k)).mono (by omega)
    · exact ((((D.nat (p := p) (k.choose a)).mul (D.prime_pow a)).mul
        (ih m a)).mul (PS_integral p (k - a))).mono (by omega)

lemma PS_pow_mul (v m k : ℕ) (hk : k < p - 1) : D p v (PS (p ^ v * m) k) := by
  cases v with
  | zero => simpa using PS_integral (p := p) m k
  | succ v =>
    rw [show p ^ (v + 1) * m = (p ^ v * m) * p by ring, PS_blocks]
    apply D.sum
    intro a ha
    by_cases ha0 : a = 0
    · subst a
      simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, PS_zero,
        Nat.sub_zero, Nat.cast_mul, Nat.cast_pow]
      exact (((D.prime_pow (p := p) v).mul (D.nat m)).mul (PS_prime k hk)).mono (by omega)
    · exact ((((D.nat (p := p) (k.choose a)).mul (D.prime_pow a)).mul
        (PS_pow_mul_weak v m a)).mul (PS_prime (k - a) (by omega))).mono (by omega)

lemma PS_dvd_weak (v n k : ℕ) (h : p ^ v ∣ n) : D p ((v : ℤ) - 1) (PS n k) := by
  obtain ⟨m, rfl⟩ := h
  exact PS_pow_mul_weak v m k

lemma PS_dvd (v n k : ℕ) (h : p ^ v ∣ n) (hk : k < p - 1) : D p v (PS n k) := by
  obtain ⟨m, rfl⟩ := h
  exact PS_pow_mul v m k hk


def J (p L : ℕ) : Finset ℕ := (range L).filter (fun i => ¬p ∣ i)
def H (p L m : ℕ) : ℚ := ∑ i ∈ J p L, (i : ℚ)⁻¹ ^ m

lemma mem_J {i L : ℕ} (h : i ∈ J p L) : i < L ∧ ¬p ∣ i := by
  simpa [J] using h

lemma H_integral (L m : ℕ) : D p 0 (H p L m) := by
  apply D.sum
  intro i hi
  simpa using (D.inv_nat i (mem_J hi).2).pow m

lemma H_zero (m : ℕ) : H p 0 m = 0 := by simp [H, J]

lemma H_prime_sum (m : ℕ) (hm : m ≠ 0) :
    H p p m = ∑ i ∈ range p, (i : ℚ)⁻¹ ^ m := by
  rw [H, J, sum_filter]
  apply sum_congr rfl
  intro i hi
  by_cases hd : p ∣ i
  · have hi0 : i = 0 := Nat.eq_zero_of_dvd_of_lt hd (mem_range.mp hi)
    simp [hd, hi0, hm]
  · simp [hd]

lemma H_prime_cast (m : ℕ) (hm : m ≠ 0) :
    ((H p p m : ℚ) : ZMod p) = ∑ z : ZMod p, z ^ m := by
  rw [H_prime_sum m hm]
  have hi : ∀ i ∈ range p, D p 0 ((i : ℚ)⁻¹ ^ m) := by
    intro i hi
    by_cases h0 : i = 0
    · simp [h0, hm, D]
    · exact ((D.inv_small i (by omega) (mem_range.mp hi)).pow m).mono (by simp)
  rw [cast_sum _ _ hi]
  simp only [Rat.cast_pow, Rat.cast_inv_nat]
  rw [sum_zmod_range (fun z : ZMod p => z⁻¹ ^ m)]
  exact Equiv.sum_comp (Equiv.inv (ZMod p)) (fun z => z ^ m)

lemma H_prime_small (m : ℕ) (hm : m ≠ 0) (hmp : m < p - 1) : D p 1 (H p p m) := by
  apply (D.cast_zero_iff (H_integral p m)).mp
  rw [H_prime_cast m hm]
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) m (by simpa using hmp)

lemma H_prime_odd (m : ℕ) (hm : Odd m) (hp3 : 3 ≤ p) : D p 1 (H p p m) := by
  apply (D.cast_zero_iff (H_integral p m)).mp
  have hm0 : m ≠ 0 := by obtain ⟨a, ha⟩ := hm; omega
  rw [H_prime_cast m hm0]
  have he := Equiv.sum_comp (Equiv.neg (ZMod p)) (fun z => z ^ m)
  simp only [Equiv.neg_apply, hm.neg_pow, sum_neg_distrib] at he
  have h2 : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hz : (2 : ZMod p) * (∑ z : ZMod p, z ^ m) = 0 := by linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left h2

lemma H_blocks (l m : ℕ) : H p (p * l) m =
    ∑ i ∈ range l, ∑ j ∈ J p p, ((p * i + j : ℕ) : ℚ)⁻¹ ^ m := by
  rw [H, J, sum_filter, Nat.mul_comm p l, sum_blocks]
  apply sum_congr rfl
  intro i hi
  rw [J, sum_filter]
  apply sum_congr rfl
  intro j hj
  have hd : p ∣ i * p + j ↔ p ∣ j :=
    (Nat.dvd_add_iff_right (dvd_mul_left p i)).symm
  simp only [hd]
  simp only [Nat.mul_comm i p]


def T (m K : ℕ) (x : ℚ) : ℚ :=
  ∑ k ∈ range K, (-1 : ℚ) ^ k * (Nat.choose (m + k - 1) k : ℚ) * x ^ k

lemma T_zero (m : ℕ) (x : ℚ) : T m 0 x = 0 := by simp [T]
lemma T_zero_left (K : ℕ) (x : ℚ) : T 0 (K + 1) x = 1 := by
  rw [T, sum_range_succ']
  simp

lemma T_recurrence (m K : ℕ) (x : ℚ) :
    T (m + 1) (K + 1) x = T m (K + 1) x - x * T (m + 1) K x := by
  rw [T, T, T, sum_range_succ', sum_range_succ']
  simp only [Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul]
  rw [mul_sum, add_sub_right_comm, ← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro k hk
  rw [show m + 1 + (k + 1) - 1 = m + k + 1 by omega,
    show m + (k + 1) - 1 = m + k by omega,
    show m + 1 + k - 1 = m + k by omega,
    Nat.choose_succ_succ', Nat.cast_add]
  simp only [pow_succ]
  ring

lemma inverse_taylor (e : ℤ) (x : ℚ) (he : 0 ≤ e) (hx : D p e x)
    (hi : D p 0 (1 + x)⁻¹) (hn : 1 + x ≠ 0) (m K : ℕ) :
    C p (e * K) ((1 + x)⁻¹ ^ m) (T m K x) := by
  induction K generalizing m with
  | zero =>
    simpa [C, T_zero] using hi.pow m
  | succ K ih =>
    induction m with
    | zero => simpa [T_zero_left] using C.refl (p := p) 1 (e * (K + 1))
    | succ m ihm =>
      have hid : (1 + x)⁻¹ ^ (m + 1) = (1 + x)⁻¹ ^ m - x * (1 + x)⁻¹ ^ (m + 1) := by
        rw [pow_succ]
        field_simp
        <;> ring
      rw [hid, T_recurrence]
      apply C.sub ihm
      convert C.mul_left (ih (m + 1)) hx using 1 <;> push_cast <;> ring


lemma inverse_shift (e : ℤ) (x a : ℚ) (he : 1 ≤ e) (hx : D p e x)
    (ha : D p 0 a⁻¹) (ha0 : a ≠ 0) (m K : ℕ) :
    C p (e * K) ((a + x)⁻¹ ^ m)
      (∑ k ∈ range K, (-1 : ℚ) ^ k * (Nat.choose (m + k - 1) k : ℚ) *
        x ^ k * a⁻¹ ^ (m + k)) := by
  have hy : D p e (x * a⁻¹) := by simpa using hx.mul ha
  have hy1 := hy.mono he
  have ht := inverse_taylor e (x * a⁻¹) (by omega) hy
    (D.inv_one_add hy1) (D.one_add_ne hy1) m K
  have ht' : C p (e * K) (a⁻¹ ^ m * (1 + x * a⁻¹)⁻¹ ^ m)
      (a⁻¹ ^ m * T m K (x * a⁻¹)) := by
    simpa using C.mul_left ht (ha.pow m)
  have hid : a + x = a * (1 + x * a⁻¹) := by field_simp
  convert ht' using 1
  · rw [hid, mul_inv, mul_pow]
  · rw [T, mul_sum]
    apply sum_congr rfl
    intro k hk
    simp only [mul_pow, pow_add]
    ring

lemma H_blocks_taylor (l m K : ℕ) :
    C p K (H p (p * l) m)
      (∑ k ∈ range K, (-1 : ℚ) ^ k * (Nat.choose (m + k - 1) k : ℚ) *
        (p : ℚ) ^ k * PS l k * H p p (m + k)) := by
  rw [H_blocks]
  have h : C p K (∑ i ∈ range l, ∑ j ∈ J p p, ((p * i + j : ℕ) : ℚ)⁻¹ ^ m)
      (∑ i ∈ range l, ∑ j ∈ J p p, ∑ k ∈ range K,
        (-1 : ℚ) ^ k * (Nat.choose (m + k - 1) k : ℚ) *
          ((p : ℚ) * i) ^ k * (j : ℚ)⁻¹ ^ (m + k)) := by
    apply C.sum
    intro i hi
    apply C.sum
    intro j hj
    have hx : D p 1 ((p : ℚ) * i) := by simpa using (D.prime (p := p)).mul (D.nat i)
    have hn : j ≠ 0 := by intro he; exact (mem_J hj).2 (he ▸ dvd_zero p)
    simpa [Nat.cast_add, Nat.cast_mul, add_comm] using
      inverse_shift (p := p) 1 ((p : ℚ) * i) (j : ℚ) (by omega) hx
        (D.inv_nat j (mem_J hj).2) (by exact_mod_cast hn) m K
  convert h using 1
  simp_rw [sum_comm (s := J p p) (t := range K)]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  simp only [mul_pow, ← mul_sum]
  rw [← sum_mul, ← mul_sum, ← mul_sum]
  dsimp only [PS, H]
  ring


lemma H_weak (l m v : ℕ) (hl : p ^ v ∣ l) : D p v (H p (p * l) m) := by
  apply C.dvd_left (H_blocks_taylor l m v)
  apply D.sum
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, PS_zero, Nat.add_zero]
    exact ((D.of_nat_dvd hl).mul (H_integral p m)).mono (by omega)
  · exact ((((((D.int (p := p) (-1)).pow k).mul (D.nat (Nat.choose (m + k - 1) k))).mul
      (D.prime_pow k)).mul (PS_dvd_weak v l k hl)).mul (H_integral p (m + k))).mono (by omega)

lemma H_strong (l m v : ℕ) (hl : p ^ v ∣ l)
    (hm : D p 1 (H p p m)) (hm1 : D p 1 (H p p (m + 1))) :
    D p (v + 1) (H p (p * l) m) := by
  have ht : C p (v + 1) (H p (p * l) m)
      (∑ k ∈ range (v + 1), (-1 : ℚ) ^ k * ↑((m + k - 1).choose k) *
        (p : ℚ) ^ k * PS l k * H p p (m + k)) := by
    simpa using H_blocks_taylor (p := p) l m (v + 1)
  apply ht.dvd_left
  apply D.sum
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, PS_zero, Nat.add_zero]
    exact ((D.of_nat_dvd hl).mul hm).mono (by omega)
  · by_cases hk1 : k = 1
    · subst k
      exact ((((((D.int (p := p) (-1)).pow 1).mul (D.nat (Nat.choose (m + 1 - 1) 1))).mul
        (D.prime_pow 1)).mul (PS_dvd_weak v l 1 hl)).mul hm1).mono (by omega)
    · exact ((((((D.int (p := p) (-1)).pow k).mul (D.nat (Nat.choose (m + k - 1) k))).mul
        (D.prime_pow k)).mul (PS_dvd_weak v l k hl)).mul (H_integral p (m + k))).mono (by omega)


lemma J_pos {i L : ℕ} (hi : i ∈ J p L) : 0 < i := by
  have hni : i ≠ 0 := by intro h; exact (mem_J hi).2 (h ▸ dvd_zero p)
  omega

lemma J_reflect {i L : ℕ} (hL : p ∣ L) (hi : i ∈ J p L) : L - i ∈ J p L := by
  have hii := mem_J hi
  have hip := J_pos hi
  have hn : ¬p ∣ L - i := by
    intro h
    have := Nat.dvd_sub hL h
    rw [Nat.sub_sub_self hii.1.le] at this
    exact hii.2 this
  simp only [J, mem_filter, mem_range]
  exact ⟨by omega, hn⟩

lemma sum_J_reflect {R : Type*} [AddCommMonoid R] (L : ℕ) (hL : p ∣ L) (f : ℕ → R) :
    ∑ i ∈ J p L, f (L - i) = ∑ i ∈ J p L, f i := by
  apply sum_bij' (fun i _ => L - i) (fun i _ => L - i)
  · exact fun i hi => J_reflect hL hi
  · exact fun i hi => J_reflect hL hi
  · exact fun i hi => Nat.sub_sub_self (mem_J hi).1.le
  · exact fun i hi => Nat.sub_sub_self (mem_J hi).1.le
  · intros; rfl

lemma H_reflect_taylor (L m K : ℕ) (q : ℤ) (hq : 1 ≤ q) (hL : p ∣ L)
    (hD : D p q (L : ℚ)) :
    C p (q * K) (H p L m)
      ((-1 : ℚ) ^ m * ∑ k ∈ range K, (Nat.choose (m + k - 1) k : ℚ) *
        (L : ℚ) ^ k * H p L (m + k)) := by
  have h : C p (q * K) (∑ i ∈ J p L, ((L - i : ℕ) : ℚ)⁻¹ ^ m)
      (∑ i ∈ J p L, (-1 : ℚ) ^ m * ∑ k ∈ range K,
        (Nat.choose (m + k - 1) k : ℚ) * (L : ℚ) ^ k * (i : ℚ)⁻¹ ^ (m + k)) := by
    apply C.sum
    intro i hi
    have ht := inverse_shift q (-(L : ℚ)) (i : ℚ) hq hD.neg
      (D.inv_nat i (mem_J hi).2) (by exact_mod_cast (J_pos hi).ne') m K
    have ht' : C p (q * K)
        ((-1 : ℚ) ^ m * ((i : ℚ) + -(L : ℚ))⁻¹ ^ m)
        ((-1 : ℚ) ^ m * ∑ k ∈ range K,
          (-1 : ℚ) ^ k * ↑((m + k - 1).choose k) * (-(L : ℚ)) ^ k *
            (i : ℚ)⁻¹ ^ (m + k)) := by
      simpa using C.mul_left ht ((D.int (p := p) (-1)).pow m)
    convert ht' using 1
    · rw [Nat.cast_sub (mem_J hi).1.le]
      have heq : (L : ℚ) - i = -((i : ℚ) + -(L : ℚ)) := by ring
      rw [heq, inv_neg, neg_eq_neg_one_mul, mul_pow]
    · congr 1
      apply sum_congr rfl
      intro k hk
      have hs : (-1 : ℚ) ^ k * (-(L : ℚ)) ^ k = (L : ℚ) ^ k := by
        rw [← mul_pow]
        simp
      calc
        _ = ↑((m + k - 1).choose k) * ((-1 : ℚ) ^ k * (-(L : ℚ)) ^ k) *
            (i : ℚ)⁻¹ ^ (m + k) := by rw [hs]
        _ = _ := by ring
  rw [sum_J_reflect L hL (fun i => (i : ℚ)⁻¹ ^ m)] at h
  convert h using 1
  rw [← mul_sum, sum_comm]
  congr 1
  apply sum_congr rfl
  intro k hk
  rw [← mul_sum]
  rfl


lemma H_weak_of_dvd (L v m : ℕ) (hL : p ^ (v + 1) ∣ L) : D p v (H p L m) := by
  obtain ⟨a, rfl⟩ := hL
  rw [show p ^ (v + 1) * a = p * (p ^ v * a) by ring]
  exact H_weak _ _ _ (dvd_mul_right _ _)

lemma H_strong_of_dvd (L v m : ℕ) (hL : p ^ (v + 1) ∣ L)
    (hm : D p 1 (H p p m)) (hm1 : D p 1 (H p p (m + 1))) :
    D p (v + 1) (H p L m) := by
  obtain ⟨a, rfl⟩ := hL
  rw [show p ^ (v + 1) * a = p * (p ^ v * a) by ring]
  exact H_strong _ _ _ (dvd_mul_right _ _) hm hm1

lemma H_odd_from_next (L m : ℕ) (q e : ℤ) (hq : 1 ≤ q) (he : e ≤ q)
    (hm : Odd m) (hp3 : 3 ≤ p) (hL : p ∣ L) (hD : D p q (L : ℚ))
    (hn : D p e (H p L (m + 1))) : D p (q + e) (H p L m) := by
  have ht := H_reflect_taylor L m 2 q hq hL hD
  have hmneg : (-1 : ℚ) ^ m = -1 := by simpa using hm.neg_pow (1 : ℚ)
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.add_zero, Nat.choose_zero_right,
    Nat.cast_one, pow_zero, one_mul, pow_one, Nat.add_sub_cancel, Nat.choose_one_right,
    hmneg, neg_one_mul] at ht
  have hnext : D p (q + e) ((m : ℚ) * L * H p L (m + 1)) :=
    (((D.nat m).mul hD).mul hn).mono (by omega)
  have hh : D p (q + e) (2 * H p L m) := by
    have hd := D.sub (D.mono ht (by omega : q + e ≤ q * (2 : ℕ))) hnext
    convert hd using 1 <;> ring
  exact D.cancel_nat (Nat.not_dvd_of_pos_of_lt (by omega) (by omega) : ¬p ∣ 2) hh

lemma H_odd_weak (L v m : ℕ) (hL : p ^ (v + 1) ∣ L) (hm : Odd m) (hp3 : 3 ≤ p) :
    D p (2 * (v : ℤ) + 1) (H p L m) := by
  have hdp : p ∣ L := dvd_trans (dvd_pow_self p (by omega : v + 1 ≠ 0)) hL
  have hD : D p (v + 1) (L : ℚ) := by simpa using D.of_nat_dvd hL
  convert H_odd_from_next L m (v + 1) v (by omega) (by omega) hm hp3 hdp hD
    (H_weak_of_dvd L v (m + 1) hL) using 1 <;> ring

lemma H_two_bound (L v : ℕ) (hL : p ^ (v + 1) ∣ L) (hp5 : 5 ≤ p) :
    D p (v + 1) (H p L 2) :=
  H_strong_of_dvd L v 2 hL (H_prime_small 2 (by omega) (by omega))
    (H_prime_odd 3 (by decide) (by omega))

lemma H_four_bound (L v : ℕ) (hL : p ^ (v + 1) ∣ L) (hp7 : 7 ≤ p) :
    D p (v + 1) (H p L 4) :=
  H_strong_of_dvd L v 4 hL (H_prime_small 4 (by omega) (by omega))
    (H_prime_odd 5 (by decide) (by omega))

lemma H_one_bound (L v : ℕ) (hL : p ^ (v + 1) ∣ L) (hp5 : 5 ≤ p) :
    D p (2 * (v : ℤ) + 2) (H p L 1) := by
  have hdp : p ∣ L := dvd_trans (dvd_pow_self p (by omega : v + 1 ≠ 0)) hL
  have hD : D p (v + 1) (L : ℚ) := by simpa using D.of_nat_dvd hL
  convert H_odd_from_next L 1 (v + 1) (v + 1) (by omega) (by omega)
    (by decide) (by omega) hdp hD (H_two_bound L v hL hp5) using 1 <;> ring


lemma not_dvd_two (hp3 : 3 ≤ p) : ¬p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
lemma not_dvd_four (hp3 : 3 ≤ p) : ¬p ∣ 4 := by
  simpa using hp.out.not_dvd_mul (not_dvd_two hp3) (not_dvd_two hp3)

lemma PS_succ (n k : ℕ) : PS (n + 1) k = PS n k + (n : ℚ) ^ k := by
  exact sum_range_succ _ _

lemma PS_one_eq (n : ℕ) : 2 * PS n 1 = (n : ℚ) * (n - 1) := by
  induction n with
  | zero => simp [PS]
  | succ n ih => rw [PS_succ]; push_cast; rw [pow_one]; linear_combination ih

lemma PS_one_two_eq (n : ℕ) : 3 * (PS n 1 + PS n 2) = (n : ℚ) ^ 3 - n := by
  induction n with
  | zero => simp [PS]
  | succ n ih => rw [PS_succ, PS_succ]; push_cast; linear_combination ih

lemma PS_three_eq (n : ℕ) : 4 * PS n 3 = (n : ℚ) ^ 2 * (n - 1) ^ 2 := by
  induction n with
  | zero => simp [PS]
  | succ n ih => rw [PS_succ]; push_cast; linear_combination ih

lemma PS_one_bound (n v : ℕ) (hn : p ^ v ∣ n) (hp3 : 3 ≤ p) : D p v (PS n 1) := by
  apply D.cancel_nat (not_dvd_two hp3)
  norm_num only [Nat.cast_ofNat]
  rw [PS_one_eq]
  exact ((D.of_nat_dvd hn).mul ((D.nat n).sub D.one)).mono (by omega)

lemma PS_three_bound (n v : ℕ) (hn : p ^ v ∣ n) (hp3 : 3 ≤ p) : D p (2 * v) (PS n 3) := by
  apply D.cancel_nat (not_dvd_four hp3)
  norm_num only [Nat.cast_ofNat]
  rw [PS_three_eq]
  exact (((D.of_nat_dvd hn).pow 2).mul (((D.nat n).sub D.one).pow 2)).mono (by omega)

lemma H_three_reflect (L v : ℕ) (hL : p ^ (v + 1) ∣ L) (hp3 : 3 ≤ p) :
    C p (4 * (v : ℤ) + 3) (H p L 3) (-3 * L / 2 * H p L 4) := by
  have hdp : p ∣ L := dvd_trans (dvd_pow_self p (by omega : v + 1 ≠ 0)) hL
  have hD : D p (v + 1) (L : ℚ) := by simpa using D.of_nat_dvd hL
  have ht := H_reflect_taylor L 3 4 (v + 1) (by omega) hdp hD
  norm_num [sum_range_succ, Nat.choose] at ht
  have h5 : D p (4 * (v : ℤ) + 3) (6 * (L : ℚ) ^ 2 * H p L 5) := by
    exact (((D.nat (p := p) 6).mul (hD.pow 2)).mul
      (H_odd_weak L v 5 hL (by decide) hp3)).mono (by omega)
  have h6 : D p (4 * (v : ℤ) + 3) (10 * (L : ℚ) ^ 3 * H p L 6) := by
    exact (((D.nat (p := p) 10).mul (hD.pow 3)).mul
      (H_weak_of_dvd L v 6 hL)).mono (by omega)
  have hh : D p (4 * (v : ℤ) + 3) (2 * (H p L 3 - -3 * L / 2 * H p L 4)) := by
    have hd := (D.mono ht (by omega : 4 * (v : ℤ) + 3 ≤ (↑v + 1) * (4 : ℕ))).sub (h5.add h6)
    convert hd using 1 <;> ring
  exact D.cancel_nat (not_dvd_two hp3) hh

lemma H_one_reflect (L v : ℕ) (hL : p ^ (v + 1) ∣ L) (hp3 : 3 ≤ p) :
    C p (6 * (v : ℤ) + 5) (H p L 1)
      (-(L : ℚ) / 2 * H p L 2 + (L : ℚ) ^ 3 / 4 * H p L 4) := by
  have hdp : p ∣ L := dvd_trans (dvd_pow_self p (by omega : v + 1 ≠ 0)) hL
  have hD : D p (v + 1) (L : ℚ) := by simpa using D.of_nat_dvd hL
  have ht := H_reflect_taylor L 1 6 (v + 1) (by omega) hdp hD
  norm_num [sum_range_succ, Nat.choose] at ht
  have h5 : D p (6 * (v : ℤ) + 5) ((L : ℚ) ^ 4 * H p L 5) :=
    ((hD.pow 4).mul (H_odd_weak L v 5 hL (by decide) hp3)).mono (by omega)
  have h6 : D p (6 * (v : ℤ) + 5) ((L : ℚ) ^ 5 * H p L 6) :=
    ((hD.pow 5).mul (H_weak_of_dvd L v 6 hL)).mono (by omega)
  have ha : D p (6 * (v : ℤ) + 5)
      (2 * H p L 1 + L * H p L 2 + (L : ℚ) ^ 2 * H p L 3 + (L : ℚ) ^ 3 * H p L 4) := by
    have hd := (D.mono ht (by omega : 6 * (v : ℤ) + 5 ≤ (↑v + 1) * (6 : ℕ))).sub (h5.add h6)
    convert hd using 1 <;> ring
  have hb : D p (6 * (v : ℤ) + 5)
      ((L : ℚ) ^ 2 * (2 * H p L 3 + 3 * L * H p L 4)) := by
    have h3 := H_three_reflect L v hL hp3
    have hd := ((D.mul h3 (D.nat 2)).mul (hD.pow 2)).mono
      (by omega : 6 * (v : ℤ) + 5 ≤ (4 * ↑v + 3 + 0) + (↑v + 1) * (2 : ℕ))
    convert hd using 1 <;> ring
  have hh : D p (6 * (v : ℤ) + 5)
      (4 * (H p L 1 - (-(L : ℚ) / 2 * H p L 2 + (L : ℚ) ^ 3 / 4 * H p L 4))) := by
    have hd := (ha.mul (D.nat 2)).mono (by omega : 6 * (v : ℤ) + 5 ≤ 6 * ↑v + 5 + 0)
    have hd' := hd.sub hb
    convert hd' using 1 <;> ring
  exact D.cancel_nat (not_dvd_four hp3) hh


def eps (p : ℕ) : ℤ := if p = 3 then 1 else 0
lemma eps_nonneg : 0 ≤ eps p := by unfold eps; split_ifs <;> omega
lemma eps_le_one : eps p ≤ 1 := by unfold eps; split_ifs <;> omega
lemma prime_ge_five (hp3 : 3 ≤ p) (hn : p ≠ 3) : 5 ≤ p := by
  have ho := hp.out.eq_two_or_odd.resolve_left (by omega : p ≠ 2)
  omega
lemma prime_ge_seven (hp3 : 3 ≤ p) (hn3 : p ≠ 3) (hn5 : p ≠ 5) : 7 ≤ p := by
  have ho := hp.out.eq_two_or_odd.resolve_left (by omega : p ≠ 2)
  omega

def alpha (p : ℕ) : ℚ := H p p 2 / p - p * H p p 4
def beta (p : ℕ) : ℚ := H p p 4 / p

lemma beta_mul (l : ℕ) : beta p * ((p : ℚ) * l) = (l : ℚ) * H p p 4 := by
  unfold beta
  have hn : (p : ℚ) ≠ 0 := p_ne
  field_simp [hn]

lemma alpha_beta_mul (l : ℕ) :
    alpha p * ((p : ℚ) * l) + beta p * ((p : ℚ) * l) ^ 3 =
      (l : ℚ) * H p p 2 + (p : ℚ) ^ 2 * ((l : ℚ) ^ 3 - l) * H p p 4 := by
  unfold alpha beta
  have hn : (p : ℚ) ≠ 0 := p_ne
  field_simp [hn]
  <;> ring

lemma H_four_expansion (l v : ℕ) (hl : p ^ v ∣ l) (hp3 : 3 ≤ p) :
    C p (v + 2 - eps p) (H p (p * l) 4) (beta p * ((p : ℚ) * l)) := by
  have hc : 0 ≤ eps p := eps_nonneg
  have ht := (H_blocks_taylor (p := p) l 4 (v + 2)).mono
    (by push_cast; omega : (v : ℤ) + 2 - eps p ≤ (v + 2 : ℕ))
  have htail : C p (v + 2 - eps p)
      (∑ k ∈ range (v + 2), (-1 : ℚ) ^ k * ↑((4 + k - 1).choose k) *
        (p : ℚ) ^ k * PS l k * H p p (4 + k))
      (∑ k ∈ range 1, (-1 : ℚ) ^ k * ↑((4 + k - 1).choose k) *
        (p : ℚ) ^ k * PS l k * H p p (4 + k)) := by
    apply C.sum_range_trunc _ _ _ (by omega)
    intro k hk hkK
    have hcoeff : D p 0 ((-1 : ℚ) ^ k * ↑((4 + k - 1).choose k)) := by
      simpa using ((D.int (p := p) (-1)).pow k).mul (D.nat ((4 + k - 1).choose k))
    by_cases hk1 : k = 1
    · subst k
      exact (((hcoeff.mul (D.prime_pow 1)).mul (PS_one_bound l v hl hp3)).mul
        (H_prime_odd 5 (by decide) hp3)).mono (by omega)
    · by_cases hk2 : k = 2
      · subst k
        by_cases hpz : p = 3
        · have he : eps p = 1 := by simp [eps, hpz]
          exact (((hcoeff.mul (D.prime_pow 2)).mul (PS_dvd_weak v l 2 hl)).mul
            (H_integral p 6)).mono (by omega)
        · have hp5 := prime_ge_five hp3 hpz
          exact (((hcoeff.mul (D.prime_pow 2)).mul (PS_dvd v l 2 hl (by omega))).mul
            (H_integral p 6)).mono (by omega)
      · exact (((hcoeff.mul (D.prime_pow k)).mul (PS_dvd_weak v l k hl)).mul
          (H_integral p (4 + k))).mono (by omega)
  rw [beta_mul]
  simpa [sum_range_succ, PS_zero] using ht.trans htail


lemma H_two_expansion (l v : ℕ) (hl : p ^ v ∣ l) (hp3 : 3 ≤ p) :
    C p (v + 4 - eps p) (H p (p * l) 2)
      (alpha p * ((p : ℚ) * l) + beta p * ((p : ℚ) * l) ^ 3) := by
  have hc : 0 ≤ eps p := eps_nonneg
  have ht := (H_blocks_taylor (p := p) l 2 (v + 4)).mono
    (by push_cast; omega : (v : ℤ) + 4 - eps p ≤ (v + 4 : ℕ))
  have htail : C p (v + 4 - eps p)
      (∑ k ∈ range (v + 4), (-1 : ℚ) ^ k * ↑((2 + k - 1).choose k) *
        (p : ℚ) ^ k * PS l k * H p p (2 + k))
      (∑ k ∈ range 4, (-1 : ℚ) ^ k * ↑((2 + k - 1).choose k) *
        (p : ℚ) ^ k * PS l k * H p p (2 + k)) := by
    apply C.sum_range_trunc _ _ _ (by omega)
    intro k hk hkK
    have hcoeff : D p 0 ((-1 : ℚ) ^ k * ↑((2 + k - 1).choose k)) := by
      simpa using ((D.int (p := p) (-1)).pow k).mul (D.nat ((2 + k - 1).choose k))
    by_cases hk4 : k = 4
    · subst k
      by_cases hpz : p = 3
      · have he : eps p = 1 := by simp [eps, hpz]
        exact (((hcoeff.mul (D.prime_pow 4)).mul (PS_dvd_weak v l 4 hl)).mul
          (H_integral p 6)).mono (by omega)
      · by_cases hpz5 : p = 5
        · have hco : D p 1 ((-1 : ℚ) ^ 4 * ↑((2 + 4 - 1).choose 4)) := by
            have hprime := D.prime (p := p)
            norm_num [Nat.choose, hpz5] at hprime ⊢
            exact hprime
          exact (((hco.mul (D.prime_pow 4)).mul (PS_dvd_weak v l 4 hl)).mul
            (H_integral p 6)).mono (by omega)
        · have hp7 := prime_ge_seven hp3 hpz hpz5
          exact (((hcoeff.mul (D.prime_pow 4)).mul (PS_dvd v l 4 hl (by omega))).mul
            (H_integral p 6)).mono (by omega)
    · exact (((hcoeff.mul (D.prime_pow k)).mul (PS_dvd_weak v l k hl)).mul
        (H_integral p (2 + k))).mono (by omega)
  have ht4 : C p (v + 4 - eps p) (H p (p * l) 2)
      ((l : ℚ) * H p p 2 - 2 * p * PS l 1 * H p p 3 +
        3 * (p : ℚ) ^ 2 * PS l 2 * H p p 4 - 4 * (p : ℚ) ^ 3 * PS l 3 * H p p 5) := by
    have hz := ht.trans htail
    norm_num [sum_range_succ, PS_zero, Nat.choose] at hz
    convert hz using 1 <;> ring
  have hcoef : D p (v + 1) (-2 * (p : ℚ) * PS l 1) :=
    (((D.int (p := p) (-2)).mul D.prime).mul (PS_one_bound l v hl hp3)).mono (by omega)
  have h3base : C p 3 (H p p 3) (-3 * p / 2 * H p p 4) := by
    simpa using H_three_reflect (p := p) p 0 (by simp) hp3
  have h3 : C p (v + 4 - eps p) ((-2 * p * PS l 1) * H p p 3)
      ((-2 * p * PS l 1) * (-3 * p / 2 * H p p 4)) :=
    (C.mul_left h3base hcoef).mono (by omega)
  have h5 : D p (v + 4 - eps p) (4 * (p : ℚ) ^ 3 * PS l 3 * H p p 5) :=
    ((((D.nat (p := p) 4).mul (D.prime_pow 3)).mul (PS_three_bound l v hl hp3)).mul
      (H_prime_odd 5 (by decide) hp3)).mono (by omega)
  have heq : (l : ℚ) * H p p 2 + (-2 * p * PS l 1) * (-3 * p / 2 * H p p 4) +
      3 * (p : ℚ) ^ 2 * PS l 2 * H p p 4 =
        alpha p * ((p : ℚ) * l) + beta p * ((p : ℚ) * l) ^ 3 := by
    rw [alpha_beta_mul]
    linear_combination (p : ℚ) ^ 2 * H p p 4 * PS_one_two_eq l
  apply ht4.trans
  rw [← heq]
  dsimp only [C]
  convert (D.sub h3 h5) using 1 <;> ring

lemma H_one_expansion (l v : ℕ) (hl : p ^ v ∣ l) (hp3 : 3 ≤ p) :
    C p (2 * (v : ℤ) + 5 - eps p) (H p (p * l) 1)
      (-alpha p / 2 * ((p : ℚ) * l) ^ 2 - beta p / 4 * ((p : ℚ) * l) ^ 4) := by
  have hc : 0 ≤ eps p := eps_nonneg
  have hd : p ^ (v + 1) ∣ p * l := by
    rw [pow_succ]
    simpa [mul_comm] using Nat.mul_dvd_mul (dvd_refl p) hl
  have hD : D p (v + 1) ((p : ℚ) * l) :=
    ((D.prime (p := p)).mul (D.of_nat_dvd hl)).mono (by omega)
  have hhalf : D p (v + 1) (-((p : ℚ) * l) / 2) := by
    simpa using (hD.neg.div_nat 2 (not_dvd_two hp3))
  have hquarter : D p (3 * ((v : ℤ) + 1)) (((p : ℚ) * l) ^ 3 / 4) :=
    ((hD.pow 3).div_nat 4 (not_dvd_four hp3)).mono (by omega)
  have h2 := (C.mul_left (H_two_expansion l v hl hp3) hhalf).mono
    (by omega : 2 * (v : ℤ) + 5 - eps p ≤ (↑v + 4 - eps p) + (↑v + 1))
  have h4 := (C.mul_left (H_four_expansion l v hl hp3) hquarter).mono
    (by omega : 2 * (v : ℤ) + 5 - eps p ≤ (↑v + 2 - eps p) + 3 * (↑v + 1))
  have hr := (H_one_reflect (p := p) (p * l) v hd hp3).mono
    (by omega : 2 * (v : ℤ) + 5 - eps p ≤ 6 * ↑v + 5)
  have hr' : C p (2 * (v : ℤ) + 5 - eps p) (H p (p * l) 1)
      (-((p : ℚ) * l) / 2 * H p (p * l) 2 + ((p : ℚ) * l) ^ 3 / 4 * H p (p * l) 4) := by
    simpa only [Nat.cast_mul] using hr
  apply hr'.trans
  convert C.add h2 h4 using 1 <;> ring


def F (x : ℚ) (n : ℕ) : ℚ := ∏ i ∈ range n, (1 + x / (i + 1 : ℕ))
lemma F_zero (x : ℚ) : F x 0 = 1 := by simp [F]
lemma F_succ (x : ℚ) (n : ℕ) : F x (n + 1) = F x n * (1 + x / (n + 1 : ℕ)) :=
  prod_range_succ _ _

lemma F_nat (n k : ℕ) : F n k = Nat.choose (n + k) k := by
  induction k with
  | zero => simp [F_zero]
  | succ k ih =>
    rw [F_succ, ih]
    have hne : (k + 1 : ℚ) ≠ 0 := by positivity
    have he : (n + k + 1 : ℚ) * Nat.choose (n + k) k =
        (Nat.choose (n + k + 1) (k + 1) : ℚ) * (k + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq (n + k) k
    simp only [Nat.cast_add, Nat.cast_one, ← Nat.add_assoc]
    field_simp [hne]
    linear_combination he

lemma F_neg_nat (n k : ℕ) (hn : 0 < n) :
    F (-(n : ℚ)) k = (-1 : ℚ) ^ k * Nat.choose (n - 1) k := by
  induction k with
  | zero => simp [F_zero]
  | succ k ih =>
    rw [F_succ, ih]
    by_cases hk : k < n
    · have hne : (k + 1 : ℚ) ≠ 0 := by positivity
      have he : (Nat.choose (n - 1) (k + 1) : ℚ) * (k + 1) =
          (Nat.choose (n - 1) k : ℚ) * ((n : ℚ) - (k + 1)) := by
        have h := congrArg (fun a : ℕ => (a : ℚ)) (Nat.choose_succ_right_eq (n - 1) k)
        dsimp only at h
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one] at h
        convert h using 1 <;> ring
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp [hne]
      linear_combination he
    · simp [Nat.choose_eq_zero_of_lt (show n - 1 < k by omega),
        Nat.choose_eq_zero_of_lt (show n - 1 < k + 1 by omega)]

lemma F_integral (n k : ℕ) : D p 0 (F n k) := by rw [F_nat]; exact D.nat _


/-- An alternating binomial transform; the value at zero is omitted. -/
def BT (n : ℕ) (f : ℕ → ℚ) : ℚ :=
  ∑ k ∈ range n, (-1 : ℚ) ^ k * (Nat.choose n (k + 1) : ℚ) * f (k + 1)

def pref (f : ℕ → ℚ) (n : ℕ) : ℚ := ∑ k ∈ range n, f (k + 1)
def h (n m : ℕ) : ℚ := pref (fun k => (k : ℚ)⁻¹ ^ m) n
def h2 (n a b : ℕ) : ℚ := ∑ k ∈ range n, ((k + 1 : ℕ) : ℚ)⁻¹ ^ b * h k a

def h3 (n a b c : ℕ) : ℚ := ∑ k ∈ range n, ((k + 1 : ℕ) : ℚ)⁻¹ ^ c * h2 k a b

lemma pref_succ (f : ℕ → ℚ) (n : ℕ) : pref f (n + 1) = pref f n + f (n + 1) :=
  sum_range_succ _ _
lemma h_succ (n m : ℕ) : h (n + 1) m = h n m + ((n + 1 : ℕ) : ℚ)⁻¹ ^ m := pref_succ _ _
lemma h2_succ (n a b : ℕ) : h2 (n + 1) a b = h2 n a b + ((n + 1 : ℕ) : ℚ)⁻¹ ^ b * h n a :=
  sum_range_succ _ _
lemma h3_succ (n a b c : ℕ) : h3 (n + 1) a b c = h3 n a b c + ((n + 1 : ℕ) : ℚ)⁻¹ ^ c * h2 n a b :=
  sum_range_succ _ _

lemma BT_congr (n : ℕ) (f g : ℕ → ℚ) (hfg : ∀ k, 0 < k → k ≤ n → f k = g k) :
    BT n f = BT n g := by
  apply sum_congr rfl
  intro k hk
  rw [hfg (k + 1) (by omega) (by have := mem_range.mp hk; omega)]

lemma BT_step (n : ℕ) (f : ℕ → ℚ) : BT (n + 1) f - BT n f =
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * f (k + 1) := by
  have he : BT n f = ∑ k ∈ range (n + 1),
      (-1 : ℚ) ^ k * (Nat.choose n (k + 1) : ℚ) * f (k + 1) := by
    rw [sum_range_succ]
    simp [BT]
  rw [BT, he, ← sum_sub_distrib]
  apply sum_congr rfl
  intro k hk
  rw [Nat.choose_succ_succ', Nat.cast_add]
  ring

lemma BT_step_mul (n : ℕ) (f : ℕ → ℚ) :
    (n + 1 : ℚ) * (BT (n + 1) f - BT n f) = BT (n + 1) (fun k => (k : ℚ) * f k) := by
  rw [BT_step, mul_sum, BT]
  apply sum_congr rfl
  intro k hk
  have he : (n + 1 : ℚ) * (Nat.choose n k : ℚ) =
      (Nat.choose (n + 1) (k + 1) : ℚ) * (k + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n k
  push_cast
  linear_combination (-1 : ℚ) ^ k * f (k + 1) * he

lemma sum_by_parts (n : ℕ) (f g : ℕ → ℚ) :
    (∑ k ∈ range n, f k * (g (k + 1) - g k)) = f n * g n - f 0 * g 0 -
      ∑ k ∈ range n, (f (k + 1) - f k) * g (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, sum_range_succ, ih]; ring

lemma BT_pref (n : ℕ) (f : ℕ → ℚ) :
    BT (n + 1) (pref f) = BT (n + 1) f - BT n f := by
  rw [BT_step]
  have he := sum_by_parts (n + 1) (fun k => (-1 : ℚ) ^ k * (Nat.choose n k : ℚ)) (pref f)
  simp only [pref_succ, add_sub_cancel_left, Nat.choose_succ_self, Nat.cast_zero,
    mul_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul] at he
  simp only [pref, sum_range_zero, mul_zero, sub_zero, zero_sub] at he
  rw [he, zero_mul, zero_sub, ← sum_neg_distrib, BT]
  apply sum_congr rfl
  intro k hk
  rw [Nat.choose_succ_succ', Nat.cast_add, pow_succ]
  simp only [pref, sum_range_succ]
  ring

lemma BT_one (n : ℕ) : BT (n + 1) (fun _ => 1) = 1 := by
  have he : (∑ k ∈ range (n + 1 + 1), (-1 : ℚ) ^ k * (Nat.choose (n + 1) k : ℚ)) = 0 := by
    exact_mod_cast Int.alternating_sum_range_choose_of_ne (by omega : n + 1 ≠ 0)
  rw [sum_range_succ'] at he
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, pow_succ] at he
  have he' : -(BT (n + 1) (fun _ => 1)) + 1 = 0 := by
    convert he using 1
    rw [BT, ← sum_neg_distrib]
    congr 1
    apply sum_congr rfl
    intros
    ring
  linarith

lemma BT_inv_step (n m : ℕ) :
    (n + 1 : ℚ) * (BT (n + 1) (fun k => (k : ℚ)⁻¹ ^ (m + 1)) -
      BT n (fun k => (k : ℚ)⁻¹ ^ (m + 1))) = BT (n + 1) (fun k => (k : ℚ)⁻¹ ^ m) := by
  rw [BT_step_mul]
  apply BT_congr
  intro k hk hkN
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [pow_succ]
  field_simp

lemma BT_inv (n : ℕ) : BT n (fun k => (k : ℚ)⁻¹) = h n 1 := by
  induction n with
  | zero => simp [BT, h, pref]
  | succ n ih =>
    have ht := BT_inv_step n 0
    simp only [zero_add, pow_one, pow_zero, BT_one] at ht
    rw [ih] at ht
    rw [h_succ]
    have hn : (n + 1 : ℚ) ≠ 0 := by positivity
    apply (mul_left_cancel₀ hn)
    push_cast
    have hc : (n + 1 : ℚ) * (n + 1 : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hn
    linear_combination ht - hc

def star11 (n : ℕ) : ℚ := ∑ k ∈ range n, ((k + 1 : ℕ) : ℚ)⁻¹ * h (k + 1) 1
def star112 (n : ℕ) : ℚ := ∑ k ∈ range n, ((k + 1 : ℕ) : ℚ)⁻¹ ^ 2 * star11 (k + 1)

lemma BT_inv_sq (n : ℕ) : BT n (fun k => (k : ℚ)⁻¹ ^ 2) = star11 n := by
  induction n with
  | zero => simp [BT, star11]
  | succ n ih =>
    have ht := BT_inv_step n 1
    simp only [one_add_one_eq_two, pow_one, BT_inv] at ht
    rw [ih] at ht
    rw [star11, sum_range_succ]
    change BT (n + 1) _ = star11 n + ((n + 1 : ℕ) : ℚ)⁻¹ * h (n + 1) 1
    have hn : (n + 1 : ℚ) ≠ 0 := by positivity
    apply (mul_left_cancel₀ hn)
    push_cast
    have hc : (n + 1 : ℚ) * (n + 1 : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hn
    linear_combination ht - h (n + 1) 1 * hc

lemma BT_h_three (n : ℕ) : (n + 1 : ℚ) * BT (n + 1) (fun k => h k 3) = star11 (n + 1) := by
  change (n + 1 : ℚ) * BT (n + 1) (pref (fun k => (k : ℚ)⁻¹ ^ 3)) = _
  rw [BT_pref]
  simpa only [BT_inv_sq] using BT_inv_step n 2

lemma binomial_duality_112 (n : ℕ) :
    BT n (fun k => (k : ℚ)⁻¹ * h k 3) = star112 n := by
  induction n with
  | zero => simp [BT, star112]
  | succ n ih =>
    have ht := BT_step_mul n (fun k => (k : ℚ)⁻¹ * h k 3)
    have he : BT (n + 1) (fun k => (k : ℚ) * ((k : ℚ)⁻¹ * h k 3)) =
        BT (n + 1) (fun k => h k 3) := by
      apply BT_congr
      intro k hk hkN
      have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
      simp [← mul_assoc, hk0]
    rw [he, ih] at ht
    have ht' := BT_h_three (n := n)
    rw [star112, sum_range_succ]
    change BT (n + 1) _ = star112 n + ((n + 1 : ℕ) : ℚ)⁻¹ ^ 2 * star11 (n + 1)
    have hn : (n + 1 : ℚ) ≠ 0 := by positivity
    apply (mul_left_cancel₀ (pow_ne_zero 2 hn))
    push_cast
    have hc : (n + 1 : ℚ) ^ 2 * ((n + 1 : ℚ)⁻¹) ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hn, one_pow]
    linear_combination (n + 1 : ℚ) * ht + ht' - star11 (n + 1) * hc


lemma J_prime : J p p = Ico 1 p := by
  ext i
  simp only [J, mem_filter, mem_range, mem_Ico]
  constructor
  · intro hi
    have hi0 : i ≠ 0 := by intro he; exact hi.2 (he ▸ dvd_zero p)
    omega
  · rintro ⟨hi0, hi⟩
    exact ⟨hi, Nat.not_dvd_of_pos_of_lt (by omega) hi⟩

lemma H_prime_eq_h (m : ℕ) : H p p m = h (p - 1) m := by
  rw [H, J_prime, sum_Ico_eq_sum_range]
  simp only [h, pref, Nat.add_comm 1]

lemma h_integral (n m : ℕ) (hn : n < p) : D p 0 (h n m) := by
  dsimp only [h, pref]
  apply D.sum
  intro k hk
  have hk' := mem_range.mp hk
  exact ((D.inv_small (k + 1) (by omega) (by omega)).pow m).mono (by simp)

lemma h2_integral (n a b : ℕ) (hn : n < p) : D p 0 (h2 n a b) := by
  apply D.sum
  intro k hk
  have hk' := mem_range.mp hk
  exact (((D.inv_small (k + 1) (by omega) (by omega)).pow b).mul
    (h_integral k a (by omega))).mono (by simp)

lemma h3_integral (n a b c : ℕ) (hn : n < p) : D p 0 (h3 n a b c) := by
  apply D.sum
  intro k hk
  have hk' := mem_range.mp hk
  exact (((D.inv_small (k + 1) (by omega) (by omega)).pow c).mul
    (h2_integral k a b (by omega))).mono (by simp)

lemma h2_shuffle (n a b : ℕ) : h2 n a b + h2 n b a + h n (a + b) = h n a * h n b := by
  induction n with
  | zero => simp [h2, h, pref]
  | succ n ih =>
    rw [h2_succ, h2_succ, h_succ, h_succ, h_succ, pow_add]
    linear_combination ih

lemma star11_eq (n : ℕ) : star11 n = h2 n 1 1 + h n 2 := by
  induction n with
  | zero => simp [star11, h2, h, pref]
  | succ n ih =>
    rw [star11, sum_range_succ]
    change star11 n + _ = _
    rw [ih, h_succ, h2_succ, h_succ]
    ring

lemma star11_sq (n : ℕ) : 2 * star11 n = h n 1 ^ 2 + h n 2 := by
  rw [star11_eq]
  have hh := h2_shuffle n 1 1
  norm_num only [Nat.reduceAdd] at hh
  linear_combination hh

lemma star112_eq (n : ℕ) :
    star112 n = h3 n 1 1 2 + h2 n 2 2 + h2 n 1 3 + h n 4 := by
  induction n with
  | zero => simp [star112, h3, h2, h, pref]
  | succ n ih =>
    rw [star112, sum_range_succ]
    change star112 n + _ = _
    rw [ih, star11_eq, h2_succ, h_succ, h3_succ, h2_succ, h2_succ, h_succ]
    ring

lemma star31_eq (n : ℕ) :
    (∑ k ∈ range n, ((k + 1 : ℕ) : ℚ)⁻¹ * h (k + 1) 3) = h2 n 3 1 + h n 4 := by
  simp_rw [h_succ, mul_add]
  rw [sum_add_distrib]
  congr 1
  · simp [h2]
  · apply sum_congr rfl
    intros
    ring

lemma triangle_reverse (n : ℕ) (f g : ℕ → ℚ) :
    (∑ j ∈ range n, ∑ i ∈ range j, f i * g j) =
      ∑ j ∈ range n, ∑ i ∈ range j, f (n - 1 - j) * g (n - 1 - i) := by
  calc
    _ = ∑ i ∈ range n, ∑ j ∈ Ico (i + 1) n, f i * g j := by
      simpa only [range_eq_Ico] using
        (sum_Ico_Ico_comm' 0 n (fun i j => f i * g j)).symm
    _ = ∑ j ∈ range n, ∑ i ∈ range (n - 1 - j),
        f (n - 1 - (n - 1 - j)) * g (n - 1 - i) := by
      apply sum_congr rfl
      intro j hj
      have hj' := mem_range.mp hj
      rw [show n - 1 - (n - 1 - j) = j by omega]
      have he := sum_Ico_reflect (fun i => f j * g i) 0 (m := n - 1 - j) (n := n - 1) (by omega)
      simpa only [Nat.sub_zero, show n - 1 + 1 = n by omega,
        show n - (n - 1 - j) = j + 1 by omega, ← range_eq_Ico] using he.symm
    _ = _ := sum_range_reflect (fun j => ∑ i ∈ range j, f (n - 1 - j) * g (n - 1 - i)) n


lemma inv_reflect_mod (i m : ℕ) (hi : 0 < i) (hip : i < p) :
    C p 1 (((p - i : ℕ) : ℚ)⁻¹ ^ m) ((-1 : ℚ) ^ m * (i : ℚ)⁻¹ ^ m) := by
  have ht := inverse_shift (p := p) 1 (-(p : ℚ)) (i : ℚ) (by omega) D.prime.neg
    (D.inv_small i hi hip) (by exact_mod_cast hi.ne') m 1
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.add_zero, Nat.choose_zero_right,
    Nat.cast_one, pow_zero, one_mul, mul_one] at ht
  have ht' : C p 1 ((-1 : ℚ) ^ m * ((i : ℚ) + -(p : ℚ))⁻¹ ^ m)
      ((-1 : ℚ) ^ m * (i : ℚ)⁻¹ ^ m) := by
    simpa using C.mul_left ht ((D.int (p := p) (-1)).pow m)
  convert ht' using 1
  rw [Nat.cast_sub hip.le]
  have he : (p : ℚ) - i = -((i : ℚ) + -(p : ℚ)) := by ring
  rw [he, inv_neg, neg_eq_neg_one_mul, mul_pow]

lemma h2_reverse_eq (n a b : ℕ) : h2 n a b =
    ∑ j ∈ range n, ∑ i ∈ range j,
      (((n - 1 - j + 1 : ℕ) : ℚ)⁻¹ ^ a) * (((n - 1 - i + 1 : ℕ) : ℚ)⁻¹ ^ b) := by
  calc
    _ = ∑ j ∈ range n, ∑ i ∈ range j,
        (((i + 1 : ℕ) : ℚ)⁻¹ ^ a) * (((j + 1 : ℕ) : ℚ)⁻¹ ^ b) := by
      simp only [h2, h, pref, mul_sum]
      apply sum_congr rfl
      intro j hj
      apply sum_congr rfl
      intros
      ring
    _ = _ := triangle_reverse n (fun i => ((i + 1 : ℕ) : ℚ)⁻¹ ^ a)
      (fun i => ((i + 1 : ℕ) : ℚ)⁻¹ ^ b)

lemma h2_reverse_mod (a b : ℕ) :
    C p 1 (h2 (p - 1) a b) ((-1 : ℚ) ^ (a + b) * h2 (p - 1) b a) := by
  have hpp : 1 < p := hp.out.one_lt
  rw [h2_reverse_eq]
  have ht : C p 1
      (∑ j ∈ range (p - 1), ∑ i ∈ range j,
        (((p - 1 - 1 - j + 1 : ℕ) : ℚ)⁻¹ ^ a) * (((p - 1 - 1 - i + 1 : ℕ) : ℚ)⁻¹ ^ b))
      (∑ j ∈ range (p - 1), ∑ i ∈ range j,
        ((-1 : ℚ) ^ a * (((j + 1 : ℕ) : ℚ)⁻¹ ^ a)) *
        ((-1 : ℚ) ^ b * (((i + 1 : ℕ) : ℚ)⁻¹ ^ b))) := by
    apply C.sum
    intro j hj
    have hj' := mem_range.mp hj
    apply C.sum
    intro i hi
    have hi' := mem_range.mp hi
    rw [show p - 1 - 1 - j + 1 = p - (j + 1) by omega,
      show p - 1 - 1 - i + 1 = p - (i + 1) by omega]
    apply C.mul (inv_reflect_mod (j + 1) a (by omega) (by omega))
      (inv_reflect_mod (i + 1) b (by omega) (by omega))
    · exact ((D.inv_small (p - (j + 1)) (by omega) (by omega)).pow a).mono (by simp)
    · exact (((D.int (p := p) (-1)).pow b).mul
        ((D.inv_small (i + 1) (by omega) (by omega)).pow b)).mono (by simp)
  convert ht using 1
  simp only [h2, h, pref, mul_sum]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intros
  rw [pow_add]
  ring

lemma F_neg_mod (k : ℕ) (hk : k < p) : C p 1 (F (-(p : ℚ)) k) 1 := by
  apply D.prod_one_add (range k) (fun i => -(p : ℚ) / (i + 1 : ℕ)) (by omega)
  intro i hi
  have hi' := mem_range.mp hi
  exact D.div_nat D.prime.neg (i + 1) (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))

lemma BT_coeff (n k : ℕ) (hn : 0 < n) :
    (-1 : ℚ) ^ k * Nat.choose (n - 1) (k + 1) = -F (-(n : ℚ)) (k + 1) := by
  rw [F_neg_nat n (k + 1) hn, pow_succ]
  ring

lemma BT_mod (f : ℕ → ℚ) (hf : ∀ k, 0 < k → k < p → D p 0 (f k)) :
    C p 1 (BT (p - 1) f) (-pref f (p - 1)) := by
  have hpp := hp.out.one_lt
  have ht : C p 1 (BT (p - 1) f) (∑ k ∈ range (p - 1), -1 * f (k + 1)) := by
    apply C.sum
    intro k hk
    have hk' := mem_range.mp hk
    rw [BT_coeff p k hp.out.pos]
    have hc := C.neg (F_neg_mod (p := p) (k + 1) (by omega))
    simpa using C.mul_right hc (hf (k + 1) (by omega) (by omega))
  simpa only [pref, neg_mul, one_mul, sum_neg_distrib] using ht

lemma h2_22_mod (hp7 : 7 ≤ p) : D p 1 (h2 (p - 1) 2 2) := by
  have h2b : D p 1 (h (p - 1) 2) := by
    rw [← H_prime_eq_h]
    exact H_prime_small 2 (by omega) (by omega)
  have h4b : D p 1 (h (p - 1) 4) := by
    rw [← H_prime_eq_h]
    exact H_prime_small 4 (by omega) (by omega)
  have he := h2_shuffle (p - 1) 2 2
  norm_num only [Nat.reduceAdd] at he
  have ht : D p 1 (2 * h2 (p - 1) 2 2) := by
    have hd := ((h2b.mul h2b).mono (by omega : (1 : ℤ) ≤ 1 + 1)).sub h4b
    convert hd using 1 <;> linear_combination he
  exact D.cancel_nat (not_dvd_two (by omega)) ht

lemma h2_13_31_mod (hp7 : 7 ≤ p) :
    D p 1 (h2 (p - 1) 1 3) ∧ D p 1 (h2 (p - 1) 3 1) := by
  have h1b : D p 1 (h (p - 1) 1) := by
    rw [← H_prime_eq_h]; exact H_prime_small 1 (by omega) (by omega)
  have h3b : D p 1 (h (p - 1) 3) := by
    rw [← H_prime_eq_h]; exact H_prime_odd 3 (by decide) (by omega)
  have h4b : D p 1 (h (p - 1) 4) := by
    rw [← H_prime_eq_h]; exact H_prime_small 4 (by omega) (by omega)
  have he := h2_shuffle (p - 1) 1 3
  norm_num only [Nat.reduceAdd] at he
  have hs : D p 1 (h2 (p - 1) 1 3 + h2 (p - 1) 3 1) := by
    have hd := ((h1b.mul h3b).mono (by omega : (1 : ℤ) ≤ 1 + 1)).sub h4b
    convert hd using 1 <;> linear_combination he
  have hr : D p 1 (h2 (p - 1) 1 3 - h2 (p - 1) 3 1) := by
    have hrev := h2_reverse_mod (p := p) 1 3
    norm_num [C] at hrev
    exact hrev
  have ha : D p 1 (h2 (p - 1) 1 3) := by
    apply D.cancel_nat (not_dvd_two (by omega))
    norm_num only [Nat.cast_ofNat]
    convert hs.add hr using 1 <;> ring
  refine ⟨ha, ?_⟩
  convert hs.sub ha using 1 <;> ring

lemma h3_112_mod (hp7 : 7 ≤ p) : D p 1 (h3 (p - 1) 1 1 2) := by
  have hpp : p - 1 < p := by omega
  have ht := BT_mod (p := p) (fun k => (k : ℚ)⁻¹ * h k 3) (by
    intro k hk hkp
    exact ((D.inv_small k hk hkp).mul (h_integral k 3 hkp)).mono (by simp))
  rw [binomial_duality_112, star112_eq] at ht
  have he : pref (fun k => (k : ℚ)⁻¹ * h k 3) (p - 1) =
      h2 (p - 1) 3 1 + h (p - 1) 4 := star31_eq _
  rw [he] at ht
  have h4b : D p 1 (h (p - 1) 4) := by
    rw [← H_prime_eq_h]; exact H_prime_small 4 (by omega) (by omega)
  have hh := h2_13_31_mod (p := p) hp7
  have hd := D.sub ht ((h2_22_mod hp7).add (hh.1.add (hh.2.add (h4b.add h4b))))
  convert hd using 1 <;> ring


lemma F_taylor_two (x : ℚ) (e : ℤ) (he : 0 ≤ e) (hx : D p e x)
    (n : ℕ) (hn : n < p) :
    C p (3 * e) (F x n) (1 + x * h n 1 + x ^ 2 * h2 n 1 1) := by
  induction n with
  | zero => simp [F_zero, h2, h, pref, C, D, zpow_nonneg (le_of_lt p_pos)]
  | succ n ih =>
    have hn' : n < p := by omega
    have hv : D p 0 ((n + 1 : ℕ) : ℚ)⁻¹ := D.inv_small (n + 1) (by omega) hn
    have hm : D p 0 (1 + x / (n + 1 : ℕ)) := by
      have ht : D p 0 (x / (n + 1 : ℕ)) := by simpa [div_eq_mul_inv] using (hx.mono he).mul hv
      exact D.one.add ht
    have ht : C p (3 * e) (F x (n + 1))
        ((1 + x * h n 1 + x ^ 2 * h2 n 1 1) * (1 + x / (n + 1 : ℕ))) := by
      rw [F_succ]
      simpa using C.mul_right (ih hn') hm
    apply ht.trans
    rw [h_succ, h2_succ]
    dsimp only [C]
    have hd : D p (3 * e) (x ^ 3 * h2 n 1 1 * ((n + 1 : ℕ) : ℚ)⁻¹) :=
      (((hx.pow 3).mul (h2_integral n 1 1 hn')).mul hv).mono (by omega)
    convert hd using 1 <;> simp only [div_eq_mul_inv, pow_one] <;> ring

lemma h2_star_last (n a b : ℕ) :
    (∑ k ∈ range n, ((k + 1 : ℕ) : ℚ)⁻¹ ^ b * h (k + 1) a) = h2 n a b + h n (a + b) := by
  simp_rw [h_succ, mul_add]
  rw [sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro k hk
  dsimp only
  rw [pow_add]
  ring

lemma h3_star_last (n a b c : ℕ) :
    (∑ k ∈ range n, ((k + 1 : ℕ) : ℚ)⁻¹ ^ c * h2 (k + 1) a b) = h3 n a b c + h2 n a (b + c) := by
  simp_rw [h2_succ, mul_add]
  rw [sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro k hk
  dsimp only
  rw [pow_add]
  ring

lemma BT_harmonic_expansion :
    C p 3 (BT (p - 1) (fun k => (k : ℚ)⁻¹ ^ 2))
      (-h (p - 1) 2 + p * (h2 (p - 1) 1 2 + h (p - 1) 3) -
        (p : ℚ) ^ 2 * (h3 (p - 1) 1 1 2 + h2 (p - 1) 1 3)) := by
  have hpp := hp.out.one_lt
  have ht : C p 3 (BT (p - 1) (fun k => (k : ℚ)⁻¹ ^ 2))
      (∑ k ∈ range (p - 1), -(((k + 1 : ℕ) : ℚ)⁻¹ ^ 2) *
        (1 - (p : ℚ) * h (k + 1) 1 + (p : ℚ) ^ 2 * h2 (k + 1) 1 1)) := by
    apply C.sum
    intro k hk
    have hk' := mem_range.mp hk
    rw [BT_coeff p k hp.out.pos]
    have hf := F_taylor_two (p := p) (-(p : ℚ)) 1 (by omega) D.prime.neg (k + 1) (by omega)
    have hd := C.mul_right (C.neg hf) ((D.inv_small (k + 1) (by omega) (by omega)).pow 2)
    norm_num only [mul_one, mul_zero, add_zero] at hd
    convert hd using 1 <;> ring
  convert ht using 1
  calc
    _ = -(∑ k ∈ range (p - 1), ((k + 1 : ℕ) : ℚ)⁻¹ ^ 2) +
        (p : ℚ) * (∑ k ∈ range (p - 1), ((k + 1 : ℕ) : ℚ)⁻¹ ^ 2 * h (k + 1) 1) -
        (p : ℚ) ^ 2 * (∑ k ∈ range (p - 1), ((k + 1 : ℕ) : ℚ)⁻¹ ^ 2 * h2 (k + 1) 1 1) := by
      rw [h2_star_last, h3_star_last]
      rfl
    _ = _ := by
      rw [← sum_neg_distrib, mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      apply sum_congr rfl
      intros
      ring

lemma harmonic_delta_remainder :
    D p 3 (2 * p * h2 (p - 1) 1 2 - 3 * h (p - 1) 2 + 2 * p * h (p - 1) 3 -
      2 * (p : ℚ) ^ 2 * (h3 (p - 1) 1 1 2 + h2 (p - 1) 1 3) - h (p - 1) 1 ^ 2) := by
  have ht := BT_harmonic_expansion (p := p)
  rw [BT_inv_sq] at ht
  have hd : D p 3 ((star11 (p - 1) -
      (-h (p - 1) 2 + p * (h2 (p - 1) 1 2 + h (p - 1) 3) -
        (p : ℚ) ^ 2 * (h3 (p - 1) 1 1 2 + h2 (p - 1) 1 3))) * -2) := by
    simpa using D.mul ht (D.int (-2))
  convert hd using 1
  linear_combination star11_sq (p - 1)


lemma h_one_base_strong (hp5 : 5 ≤ p) : D p 2 (h (p - 1) 1) := by
  rw [← H_prime_eq_h]
  simpa using H_one_bound (p := p) p 0 (by simp) hp5

lemma h_three_base_strong (hp7 : 7 ≤ p) : D p 2 (h (p - 1) 3) := by
  rw [← H_prime_eq_h]
  have ht := H_odd_from_next (p := p) p 3 1 1 (by omega) (by omega) (by decide) (by omega)
    (dvd_refl p) D.prime (H_prime_small 4 (by omega) (by omega))
  simpa using ht

lemma harmonic_delta_bound (d : ℤ) (hd1 : 1 ≤ d) (hd2 : d ≤ 2) (hp5 : 5 ≤ p)
    (hthree : D p d (h (p - 1) 3)) (h112 : D p (d - 1) (h3 (p - 1) 1 1 2))
    (h13 : D p (d - 1) (h2 (p - 1) 1 3)) (hfour : D p (d - 1) (h (p - 1) 4)) :
    D p d (2 * h2 (p - 1) 1 2 - 3 * alpha p) := by
  apply D.cancel_prime
  have hrem := (harmonic_delta_remainder (p := p)).mono (by omega : d + 1 ≤ 3)
  have h3term : D p (d + 1) (2 * p * h (p - 1) 3) :=
    (((D.nat (p := p) 2).mul D.prime).mul hthree).mono (by omega)
  have h112term : D p (d + 1) (2 * (p : ℚ) ^ 2 * (h3 (p - 1) 1 1 2 + h2 (p - 1) 1 3)) :=
    (((D.nat (p := p) 2).mul (D.prime_pow 2)).mul (h112.add h13)).mono (by omega)
  have h1term : D p (d + 1) (h (p - 1) 1 ^ 2) := ((h_one_base_strong hp5).pow 2).mono (by omega)
  have h4term : D p (d + 1) (3 * (p : ℚ) ^ 2 * h (p - 1) 4) :=
    (((D.nat (p := p) 3).mul (D.prime_pow 2)).mul hfour).mono (by omega)
  have ht := (((hrem.sub h3term).add h112term).add h1term).add h4term
  convert ht using 1
  rw [alpha, H_prime_eq_h 2, H_prime_eq_h 4]
  have hn : (p : ℚ) ≠ 0 := p_ne
  field_simp [hn]
  <;> ring

lemma harmonic_delta_one (hp5 : 5 ≤ p) : D p 1 (2 * h2 (p - 1) 1 2 - 3 * alpha p) := by
  have hpp : p - 1 < p := by omega
  apply harmonic_delta_bound 1 (by omega) (by omega) hp5
  · rw [← H_prime_eq_h]; exact H_prime_odd 3 (by decide) (by omega)
  · simpa using h3_integral (p - 1) 1 1 2 hpp
  · simpa using h2_integral (p - 1) 1 3 hpp
  · simpa using h_integral (p - 1) 4 hpp

lemma harmonic_delta_two (hp7 : 7 ≤ p) : D p 2 (2 * h2 (p - 1) 1 2 - 3 * alpha p) := by
  apply harmonic_delta_bound 2 (by omega) (by omega) (by omega)
  · exact h_three_base_strong hp7
  · simpa using h3_112_mod hp7
  · simpa using (h2_13_31_mod hp7).1
  · rw [← H_prime_eq_h]; simpa using H_prime_small (p := p) 4 (by omega) (by omega)

lemma H_two_base (hp3 : 3 ≤ p) : D p (1 - eps p) (H p p 2) := by
  by_cases hpz : p = 3
  · simpa [eps, hpz] using H_integral (p := p) p 2
  · have hp5 := prime_ge_five hp3 hpz
    simpa [eps, hpz] using H_prime_small (p := p) 2 (by omega) (by omega)

lemma alpha_bound (hp3 : 3 ≤ p) : D p (-eps p) (alpha p) := by
  have hc : 0 ≤ eps p := eps_nonneg
  unfold alpha
  apply D.sub
  · have ht := (H_two_base hp3).div_valuation p hp.out.ne_zero
    simpa only [padicValNat.self hp.out.one_lt, Nat.cast_one, sub_sub_cancel_left] using ht
  · exact ((D.prime (p := p)).mul (H_integral p 4)).mono (by omega)

lemma beta_bound : D p (-1) (beta p) := by
  unfold beta
  have ht := (H_integral (p := p) p 4).div_valuation p hp.out.ne_zero
  simpa only [padicValNat.self hp.out.one_lt, Nat.cast_one, zero_sub] using ht

lemma beta_bound_large (hp7 : 7 ≤ p) : D p 0 (beta p) := by
  unfold beta
  have ht := (H_prime_small (p := p) 4 (by omega) (by omega)).div_valuation p hp.out.ne_zero
  simpa only [padicValNat.self hp.out.one_lt, Nat.cast_one, sub_self] using ht

lemma H_two_bound_general (L v : ℕ) (hL : p ^ (v + 1) ∣ L) (hp3 : 3 ≤ p) :
    D p (v + 1 - eps p) (H p L 2) := by
  by_cases hpz : p = 3
  · simpa [eps, hpz] using H_weak_of_dvd (p := p) L v 2 hL
  · have hp5 := prime_ge_five hp3 hpz
    simpa [eps, hpz] using H_two_bound L v hL hp5

lemma H_one_bound_general (L v : ℕ) (hL : p ^ (v + 1) ∣ L) (hp3 : 3 ≤ p) :
    D p (2 * (v : ℤ) + 2 - eps p) (H p L 1) := by
  by_cases hpz : p = 3
  · have he : 2 * (v : ℤ) + 2 - eps p = 2 * ↑v + 1 := by simp [eps, hpz]; ring
    rw [he]
    exact H_odd_weak L v 1 hL (by decide) hp3
  · have hp5 := prime_ge_five hp3 hpz
    simpa [eps, hpz] using H_one_bound L v hL hp5


/-- Elementary symmetric sums of a finite family. -/
def E {ι : Type*} (s : Finset ι) (f : ι → ℚ) (k : ℕ) : ℚ :=
  ∑ t ∈ s.powersetCard k, ∏ i ∈ t, f i

lemma E_zero {ι : Type*} (s : Finset ι) (f : ι → ℚ) : E s f 0 = 1 := by simp [E]
lemma E_one {ι : Type*} (s : Finset ι) (f : ι → ℚ) : E s f 1 = ∑ i ∈ s, f i := by simp [E, powersetCard_one]

lemma E_empty {ι : Type*} (f : ι → ℚ) (k : ℕ) : E ∅ f k = if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp [E_zero]
  | succ k =>
    rw [E, powersetCard_eq_empty.mpr (by simp), sum_empty]
    simp

lemma E_insert {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℚ) (a : ι) (ha : a ∉ s) (k : ℕ) :
    E (insert a s) f (k + 1) = E s f (k + 1) + f a * E s f k := by
  have hdis : Disjoint (s.powersetCard (k + 1)) ((s.powersetCard k).image (insert a)) := by
    apply disjoint_left.mpr
    intro t ht hu
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hu
    exact ha ((mem_powersetCard.mp ht).1 (mem_insert_self _ _))
  rw [E, powersetCard_succ_insert ha, sum_union hdis]
  rw [sum_image]
  · congr 1
    rw [E, mul_sum]
    apply sum_congr rfl
    intro t ht
    rw [prod_insert]
    exact not_mem_subset (mem_powersetCard.mp ht).1 ha
  · intro t ht u hu he
    have hat : a ∉ t := not_mem_subset (mem_powersetCard.mp ht).1 ha
    have hau : a ∉ u := not_mem_subset (mem_powersetCard.mp hu).1 ha
    have he' := congrArg (fun v : Finset ι => v.erase a) he
    simpa [hat, hau] using he'

lemma E_two {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    2 * E s f 2 = (∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, f i ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [E_empty]
  | @insert i s hi ih =>
    rw [E_insert s f i hi 1, E_one, sum_insert hi, sum_insert hi]
    linear_combination ih

lemma E_three {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    6 * E s f 3 = (∑ i ∈ s, f i) ^ 3 -
      3 * (∑ i ∈ s, f i) * (∑ i ∈ s, f i ^ 2) + 2 * ∑ i ∈ s, f i ^ 3 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [E_empty]
  | @insert i s hi ih =>
    rw [E_insert s f i hi 2]
    simp only [sum_insert hi]
    linear_combination ih + 3 * f i * E_two s f

lemma E_four {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    24 * E s f 4 = (∑ i ∈ s, f i) ^ 4 -
      6 * (∑ i ∈ s, f i) ^ 2 * (∑ i ∈ s, f i ^ 2) +
      3 * (∑ i ∈ s, f i ^ 2) ^ 2 + 8 * (∑ i ∈ s, f i) * (∑ i ∈ s, f i ^ 3) -
      6 * ∑ i ∈ s, f i ^ 4 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [E_empty]
  | @insert i s hi ih =>
    rw [E_insert s f i hi 3]
    simp only [sum_insert hi]
    linear_combination ih + 4 * f i * E_three s f

lemma E_bound {ι : Type*} (s : Finset ι) (f : ι → ℚ) (e : ℤ)
    (hf : ∀ i ∈ s, D p e (f i)) (k : ℕ) : D p (e * k) (E s f k) := by
  apply D.sum
  intro t ht
  have hts := mem_powersetCard.mp ht
  have hd := D.prod_same t f (fun i hi => hf i (hts.1 hi))
  simpa only [hts.2] using hd

lemma E_large {ι : Type*} (s : Finset ι) (f : ι → ℚ) (k : ℕ) (hk : s.card < k) : E s f k = 0 := by
  apply sum_eq_zero
  intro t ht
  have hts := mem_powersetCard.mp ht
  have hc := card_le_card hts.1
  omega

lemma prod_eq_sum_E {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    (∏ i ∈ s, (1 + f i)) = ∑ k ∈ range (s.card + 1), E s f k := by
  rw [Finset.prod_one_add, sum_powerset]
  rfl

lemma prod_eq_sum_E_of_large {ι : Type*} (s : Finset ι) (f : ι → ℚ) (K : ℕ) (hK : s.card < K) :
    (∏ i ∈ s, (1 + f i)) = ∑ k ∈ range K, E s f k := by
  rw [prod_eq_sum_E]
  apply sum_subset (range_mono (by omega))
  intro k hkK hks
  exact E_large s f k (by simp only [mem_range, not_lt] at hks; omega)

lemma prod_approx {ι : Type*} (s : Finset ι) (f : ι → ℚ) (e : ℤ) (he : 0 ≤ e)
    (hf : ∀ i ∈ s, D p e (f i)) (d : ℕ) :
    C p (e * d) (∏ i ∈ s, (1 + f i)) (∑ k ∈ range d, E s f k) := by
  rw [prod_eq_sum_E_of_large s f (s.card + d + 1) (by omega)]
  apply C.sum_range_trunc _ _ _ (by omega)
  intro k hkd hkK
  exact (E_bound s f e hf k).mono (mul_le_mul_of_nonneg_left (by exact_mod_cast hkd) he)

lemma prod_approx_one {ι : Type*} (s : Finset ι) (f : ι → ℚ) (e : ℤ) (he : 0 ≤ e)
    (hf : ∀ i ∈ s, D p e (f i)) :
    C p (2 * e) (∏ i ∈ s, (1 + f i)) (1 + ∑ i ∈ s, f i) := by
  have ht := prod_approx s f e he hf 2
  simpa [sum_range_succ, E_zero, E_one, mul_comm] using ht


@[to_additive sum_split_multiples]
lemma prod_split_multiples {R : Type*} [CommMonoid R] (f : ℕ → R) (t : ℕ) :
    (∏ k ∈ range (p * t), f k) = (∏ i ∈ range t, f (p * i)) * ∏ k ∈ J p (p * t), f k := by
  rw [J, ← prod_filter_mul_prod_filter_not (range (p * t)) (fun k => p ∣ k) f]
  congr 1
  apply prod_bij' (fun k _ => k / p) (fun i _ => p * i)
  · intro k hk
    have hks := mem_filter.mp hk
    apply mem_range.mpr
    rw [Nat.div_lt_iff_lt_mul hp.out.pos]
    simpa [Nat.mul_comm] using mem_range.mp hks.1
  · intro i hi
    apply mem_filter.mpr
    exact ⟨mem_range.mpr ((Nat.mul_lt_mul_left hp.out.pos).mpr (mem_range.mp hi)), dvd_mul_right _ _⟩
  · intro k hk
    exact Nat.mul_div_cancel' (mem_filter.mp hk).2
  · intro i hi
    exact Nat.mul_div_cancel_left i hp.out.pos
  · intro k hk
    rw [Nat.mul_div_cancel' (mem_filter.mp hk).2]

lemma valuation_lt_power (s k : ℕ) (hk : 0 < k) (hks : k < p ^ s) : padicValNat p k < s := by
  by_contra h
  have hd : p ^ s ∣ k := (padicValNat_dvd_iff_le hk.ne').mpr (by omega)
  exact Nat.not_dvd_of_pos_of_lt hk hks hd

lemma ratio_bound (s k : ℕ) (hk : k ≠ 0) :
    D p ((s : ℤ) - padicValNat p k) ((p : ℚ) ^ s / k) :=
  (D.prime_pow s).div_valuation k hk

lemma ratio_one (s k : ℕ) (hk : k < p ^ s) : D p 1 ((p : ℚ) ^ s / k) := by
  by_cases hk0 : k = 0
  · simp only [hk0, Nat.cast_zero, div_zero]; exact D.zero _
  · have hv := valuation_lt_power s k (by omega) hk
    exact (ratio_bound s k hk0).mono (by omega)

lemma F_prime_power_mod (s k : ℕ) (hk : k < p ^ s) : C p 1 (F (p ^ s : ℕ) k) 1 := by
  apply D.prod_one_add (range k) (fun i => ((p ^ s : ℕ) : ℚ) / (i + 1 : ℕ)) (by omega)
  intro i hi
  have hi' := mem_range.mp hi
  simpa only [Nat.cast_pow] using ratio_one (p := p) s (i + 1) (by omega)

def b (n k : ℕ) : ℚ := Nat.choose (n + k - 1) k
lemma b_zero (n : ℕ) : b n 0 = 1 := by simp [b]
lemma b_integral (n k : ℕ) : D p 0 (b n k) := D.nat _

lemma b_succ (n k : ℕ) : b n (k + 1) = (n : ℚ) / (k + 1 : ℕ) * F n k := by
  rw [b, show n + (k + 1) - 1 = n + k by omega, F_nat]
  have hn : (k + 1 : ℚ) ≠ 0 := by positivity
  have he : (Nat.choose (n + k) (k + 1) : ℚ) * (k + 1) =
      (Nat.choose (n + k) k : ℚ) * n := by
    have ht := Nat.choose_succ_right_eq (n + k) k
    simp only [Nat.add_sub_cancel_right] at ht
    exact_mod_cast ht
  push_cast
  field_simp [hn]
  linear_combination he

lemma b_pos (n k : ℕ) (hk : 0 < k) : b n k = (n : ℚ) / k * F n (k - 1) := by
  have he : k - 1 + 1 = k := by omega
  simpa only [he] using b_succ n (k - 1)

lemma F_step (n k : ℕ) : F n (k + 1) - F n k = b n (k + 1) := by
  rw [F_succ, b_succ]
  ring

lemma b_top (n : ℕ) (hn : 0 < n) : b n n = F n (n - 1) := by
  rw [b_pos n n hn]
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [hn0]

lemma F_top (n : ℕ) (hn : 0 < n) : F n n = 2 * b n n := by
  have hs := F_step n (n - 1)
  rw [show n - 1 + 1 = n by omega, ← b_top n hn] at hs
  linear_combination hs

lemma b_prime_power_bound (s k : ℕ) (hk : 0 < k) :
    D p ((s : ℤ) - padicValNat p k) (b (p ^ s) k) := by
  rw [b_pos _ _ hk]
  simpa only [Nat.cast_pow, add_zero] using
    (ratio_bound (p := p) s k hk.ne').mul (F_integral (p := p) (p ^ s) (k - 1))

lemma b_prime_power_one (s k : ℕ) (hk : 0 < k) (hks : k < p ^ s) : D p 1 (b (p ^ s) k) := by
  have hv := valuation_lt_power s k hk hks
  exact (b_prime_power_bound s k hk).mono (by omega)

def X (n m : ℕ) : ℚ := ∑ k ∈ range n, ((n : ℚ) / k) ^ m

lemma X_split (t m : ℕ) :
    X (p * t) m = X t m + ((p : ℚ) * t) ^ m * H p (p * t) m := by
  rw [X, sum_split_multiples]
  congr 1
  · apply sum_congr rfl
    intro k hk
    congr 1
    simp only [Nat.cast_mul]
    exact mul_div_mul_left _ _ p_ne
  · rw [H, mul_sum]
    apply sum_congr rfl
    intros
    simp only [Nat.cast_mul, div_eq_mul_inv, mul_pow]

lemma X_one (m : ℕ) (hm : m ≠ 0) : X 1 m = 0 := by simp [X, hm]

lemma X_bound (s m : ℕ) : D p m (X (p ^ s) m) := by
  apply D.sum
  intro k hk
  have hd := (ratio_one (p := p) s k (mem_range.mp hk)).pow m
  simpa only [one_mul, Nat.cast_pow] using hd

lemma X_two_bound (s : ℕ) (hp5 : 5 ≤ p) : D p 3 (X (p ^ s) 2) := by
  induction s with
  | zero => simp only [pow_zero, X_one 2 (by omega)]; exact D.zero _
  | succ s ih =>
    rw [show p ^ (s + 1) = p * p ^ s by ring, X_split]
    apply ih.add
    have hd : D p (s + 1) ((p : ℚ) * (p ^ s : ℕ)) := by
      simpa only [Nat.cast_pow, pow_succ, mul_comm] using D.prime_pow (p := p) (s + 1)
    have hH : D p (s + 1) (H p (p * p ^ s) 2) :=
      H_two_bound _ s (by rw [pow_succ]; simp [mul_comm]) hp5
    exact ((hd.pow 2).mul hH).mono (by omega)

lemma X_three_bound (s : ℕ) (hp3 : 3 ≤ p) : D p 4 (X (p ^ s) 3) := by
  induction s with
  | zero => simp only [pow_zero, X_one 3 (by omega)]; exact D.zero _
  | succ s ih =>
    rw [show p ^ (s + 1) = p * p ^ s by ring, X_split]
    apply ih.add
    have hd : D p (s + 1) ((p : ℚ) * (p ^ s : ℕ)) := by
      simpa only [Nat.cast_pow, pow_succ, mul_comm] using D.prime_pow (p := p) (s + 1)
    have hH : D p (2 * (s : ℤ) + 1) (H p (p * p ^ s) 3) :=
      H_odd_weak _ s 3 (by rw [pow_succ]; simp [mul_comm]) (by decide) hp3
    exact ((hd.pow 3).mul hH).mono (by omega)


lemma X_shift (n m : ℕ) (hn : 0 < n) (hm : m ≠ 0) :
    X n m = ∑ k ∈ range (n - 1), ((n : ℚ) / (k + 1 : ℕ)) ^ m := by
  have he := sum_range_succ' (fun k => ((n : ℚ) / k) ^ m) (n - 1)
  rw [show n - 1 + 1 = n by omega] at he
  simpa only [X, Nat.cast_zero, div_zero, zero_pow hm, add_zero] using he

lemma odd_prime_power (s : ℕ) (hp3 : 3 ≤ p) : Odd (p ^ s) := by
  have ho : Odd p := Nat.odd_iff.mpr (hp.out.eq_two_or_odd.resolve_left (by omega))
  exact ho.pow

lemma F_neg_top (n : ℕ) (hn : Odd n) : F (-(n : ℚ)) (n - 1) = 1 := by
  have hnpos : 0 < n := by obtain ⟨a, ha⟩ := hn; omega
  rw [F_neg_nat n (n - 1) hnpos, Nat.choose_self, Nat.cast_one, mul_one]
  obtain ⟨a, rfl⟩ := hn
  simp [pow_mul]

lemma b_top_product (n : ℕ) (hn : Odd n) :
    b n n = ∏ i ∈ range (n - 1), (1 - ((n : ℚ) / (i + 1 : ℕ)) ^ 2) := by
  have hnpos : 0 < n := by obtain ⟨a, ha⟩ := hn; omega
  rw [b_top n hnpos]
  calc
    _ = F n (n - 1) * F (-(n : ℚ)) (n - 1) := by rw [F_neg_top n hn, mul_one]
    _ = _ := by
      rw [F, F, ← prod_mul_distrib]
      apply prod_congr rfl
      intros
      rw [neg_div]
      ring

lemma b_top_expansion (s : ℕ) (hp3 : 3 ≤ p) :
    C p 4 (b (p ^ s) (p ^ s)) (1 - X (p ^ s) 2) := by
  have hn : 0 < p ^ s := pow_pos hp.out.pos _
  rw [b_top_product _ (odd_prime_power s hp3), X_shift _ _ hn (by omega)]
  have ht := prod_approx_one (p := p) (range (p ^ s - 1))
    (fun i => -(((p ^ s : ℕ) : ℚ) / (i + 1 : ℕ)) ^ 2) 2 (by omega) (by
      intro i hi
      have hi' := mem_range.mp hi
      have hd := (ratio_one (p := p) s (i + 1) (by omega)).pow 2
      simpa only [one_mul, Nat.cast_pow] using hd.neg)
  simpa only [sub_eq_add_neg, sum_neg_distrib, show (2 : ℤ) * 2 = 4 by decide] using ht

lemma b_top_close (s : ℕ) (hp3 : 3 ≤ p) : C p 2 (b (p ^ s) (p ^ s)) 1 := by
  have ht := (b_top_expansion s hp3).mono (by omega : (2 : ℤ) ≤ 4)
  apply ht.trans
  simpa only [C, sub_sub_cancel_left] using (X_bound (p := p) s 2).neg

lemma b_top_close_large (s : ℕ) (hp5 : 5 ≤ p) : C p 3 (b (p ^ s) (p ^ s)) 1 := by
  have ht := (b_top_expansion (p := p) s (by omega)).mono (by omega : (3 : ℤ) ≤ 4)
  apply ht.trans
  simpa only [C, sub_sub_cancel_left] using (X_two_bound (p := p) s hp5).neg

def S (n m : ℕ) : ℚ := ∑ k ∈ range (n + 1), b n k ^ m

lemma S_split (n m : ℕ) (hn : 0 < n) :
    S n m = 1 + b n n ^ m + ∑ k ∈ range (n - 1), b n (k + 1) ^ m := by
  rw [S, sum_range_succ]
  have he := sum_range_succ' (fun k => b n k ^ m) (n - 1)
  rw [show n - 1 + 1 = n by omega, b_zero, one_pow] at he
  rw [he]
  ring

lemma S_approx (s m : ℕ) (hm : m ≠ 0) :
    C p (m + 1) (S (p ^ s) m) (1 + b (p ^ s) (p ^ s) ^ m + X (p ^ s) m) := by
  have hn : 0 < p ^ s := pow_pos hp.out.pos _
  rw [S_split _ _ hn, X_shift _ _ hn hm]
  apply C.add (C.refl _ _)
  apply C.sum
  intro k hk
  have hk' := mem_range.mp hk
  have hF := F_prime_power_mod (p := p) s k (by omega)
  have hFp := C.pow hF (F_integral (p := p) (p ^ s) k) D.one m
  have hx : D p m ((((p ^ s : ℕ) : ℚ) / (k + 1 : ℕ)) ^ m) := by
    simpa only [Nat.cast_pow, one_mul] using (ratio_one (p := p) s (k + 1) (by omega)).pow m
  rw [b_succ, mul_pow]
  have hc := C.mul_left hFp hx
  simpa only [one_pow, mul_one, show (1 : ℤ) + m = m + 1 by omega] using hc

lemma nine_X_two (s : ℕ) (hp3 : 3 ≤ p) : D p 3 (9 * X (p ^ s) 2) := by
  by_cases hpz : p = 3
  · have hnine : D p 2 (9 : ℚ) := by
      have ht := D.prime_pow (p := p) 2
      norm_num [hpz] at ht ⊢
      exact ht
    exact (hnine.mul (X_bound (p := p) s 2)).mono (by omega)
  · exact ((D.nat (p := p) 9).mul (X_two_bound s (prime_ge_five hp3 hpz))).mono (by omega)

lemma S_two_low (s : ℕ) (hp3 : 3 ≤ p) :
    C p 3 (S (p ^ s) 2 + F (p ^ s : ℕ) (p ^ s) ^ 2) 6 := by
  have hn : 0 < p ^ s := pow_pos hp.out.pos _
  have hx := X_bound (p := p) s 2
  have hp0 := b_integral (p := p) (p ^ s) (p ^ s)
  have hy0 : D p 0 (1 - X (p ^ s) 2) := D.one.sub (hx.mono (by omega))
  have hP := C.pow (b_top_expansion s hp3) hp0 hy0 2
  have hP5 : D p 3 (5 * (b (p ^ s) (p ^ s) ^ 2 - (1 - X (p ^ s) 2) ^ 2)) := by
    have hd := D.mul (D.nat (p := p) 5) hP
    exact hd.mono (by omega)
  have hx5 : D p 3 (5 * X (p ^ s) 2 ^ 2) :=
    ((D.nat (p := p) 5).mul (hx.pow 2)).mono (by omega)
  have hs := S_approx (p := p) s 2 (by omega)
  have hd := ((D.add hs hP5).sub (nine_X_two s hp3)).add hx5
  rw [F_top _ hn]
  dsimp only [C]
  convert hd using 1 <;> ring


def ff (x : ℚ) : ℚ := 3 * x ^ 2 + 2 * x ^ 3
def aQ (n : ℕ) : ℚ := 3 * S n 2 + 2 * S n 3

lemma ff_congr {e : ℤ} {x y : ℚ} (hxy : C p e x y) (hx : D p 0 x) (hy : D p 0 y) :
    C p e (ff x) (ff y) := by
  have h2 := C.mul_left (C.pow hxy hx hy 2) (D.nat (p := p) 3)
  have h3 := C.mul_left (C.pow hxy hx hy 3) (D.nat (p := p) 2)
  simpa only [ff, add_zero, Nat.cast_ofNat] using C.add h2 h3

lemma aQ_close_large (s : ℕ) (hp5 : 5 ≤ p) : C p 3 (aQ (p ^ s)) 10 := by
  have hP := b_top_close_large s hp5
  have hp0 := b_integral (p := p) (p ^ s) (p ^ s)
  have hP2 : C p 3 (b (p ^ s) (p ^ s) ^ 2) 1 := by
    simpa only [one_pow] using C.pow hP hp0 D.one 2
  have hP3 : C p 3 (b (p ^ s) (p ^ s) ^ 3) 1 := by
    simpa only [one_pow] using C.pow hP hp0 D.one 3
  have hs2 : C p 3 (S (p ^ s) 2) 2 := by
    apply C.trans (S_approx s 2 (by omega))
    dsimp only [C]
    convert D.add hP2 (X_two_bound s hp5) using 1 <;> ring
  have hs3 : C p 3 (S (p ^ s) 3) 2 := by
    apply C.trans ((S_approx (p := p) s 3 (by omega)).mono (by omega : (3 : ℤ) ≤ 3 + 1))
    dsimp only [C]
    have hx := (X_three_bound (p := p) s (by omega)).mono (by omega : (3 : ℤ) ≤ 4)
    convert D.add hP3 hx using 1 <;> ring
  have ht := C.add (C.mul_left hs2 (D.nat (p := p) 3)) (C.mul_left hs3 (D.nat (p := p) 2))
  norm_num only [add_zero, Nat.cast_ofNat, reduceMul, reduceAdd] at ht
  exact ht

lemma aQ_close_three (s : ℕ) (hpz : p = 3) : C p 4 (aQ (p ^ s)) 10 := by
  have hp3 : 3 ≤ p := by omega
  have hc3 : D p 1 (3 : ℚ) := by simpa only [hpz, Nat.cast_ofNat] using D.prime (p := p)
  have hc9 : D p 2 (9 : ℚ) := by simpa using hc3.pow 2
  have hx := X_bound (p := p) s 2
  have hP := b_top_expansion s hp3
  have hff := ff_congr hP (b_integral (p ^ s) (p ^ s)) (D.one.sub (hx.mono (by omega)))
  have hw : C p 4 (aQ (p ^ s))
      (3 * (1 + b (p ^ s) (p ^ s) ^ 2 + X (p ^ s) 2) +
        2 * (1 + b (p ^ s) (p ^ s) ^ 3 + X (p ^ s) 3)) := by
    have h2 := C.mul_left (S_approx (p := p) s 2 (by omega)) hc3
    have h3 := C.mul_left (S_approx (p := p) s 3 (by omega)) (D.nat (p := p) 2)
    norm_num only [Nat.cast_ofNat, add_zero, reduceAdd] at h2 h3
    exact C.add h2 h3
  have h9x : D p 4 (9 * X (p ^ s) 2) := (hc9.mul hx).mono (by omega)
  have h9xx : D p 4 (9 * X (p ^ s) 2 ^ 2) := (hc9.mul (hx.pow 2)).mono (by omega)
  have h2xxx : D p 4 (2 * X (p ^ s) 2 ^ 3) := ((D.nat (p := p) 2).mul (hx.pow 3)).mono (by omega)
  have h2X3 : D p 4 (2 * X (p ^ s) 3) :=
    ((D.nat (p := p) 2).mul (X_three_bound s hp3)).mono (by omega)
  have hd := ((((D.add hw hff).sub h9x).add h9xx).sub h2xxx).add h2X3
  dsimp only [C]
  convert hd using 1
  unfold ff
  ring

lemma aQ_close (s : ℕ) (hp3 : 3 ≤ p) : C p (3 + eps p) (aQ (p ^ s)) 10 := by
  by_cases hpz : p = 3
  · simpa only [eps, if_pos hpz, show (3 : ℤ) + 1 = 4 by decide] using aQ_close_three s hpz
  · simpa only [eps, if_neg hpz, add_zero] using aQ_close_large s (prime_ge_five hp3 hpz)

lemma ff_top_close (s : ℕ) (hp3 : 3 ≤ p) :
    C p (3 + eps p) (ff (F (p ^ s : ℕ) (p ^ s))) 28 := by
  have hn : 0 < p ^ s := pow_pos hp.out.pos _
  by_cases hpz : p = 3
  · have he : 3 + eps p = (4 : ℤ) := by simp [eps, hpz]
    rw [he, F_top _ hn]
    have hP := b_top_close s hp3
    have hc3 : D p 1 (3 : ℚ) := by simpa only [hpz, Nat.cast_ofNat] using D.prime (p := p)
    have hc9 : D p 2 (9 : ℚ) := by simpa using hc3.pow 2
    have hc72 : D p 2 (72 : ℚ) := by
      have ht := (D.nat (p := p) 8).mul hc9
      norm_num only [Nat.cast_ofNat, reduceMul, zero_add] at ht
      exact ht
    have hlin : D p 4 (72 * (b (p ^ s) (p ^ s) - 1)) := (D.mul hc72 hP).mono (by omega)
    have hquad : D p 4 (60 * (b (p ^ s) (p ^ s) - 1) ^ 2) :=
      ((D.nat (p := p) 60).mul (D.pow hP 2)).mono (by omega)
    have hcub : D p 4 (16 * (b (p ^ s) (p ^ s) - 1) ^ 3) :=
      ((D.nat (p := p) 16).mul (D.pow hP 3)).mono (by omega)
    dsimp only [C]
    convert (hlin.add hquad).add hcub using 1 <;> unfold ff <;> ring
  · have hp5 := prime_ge_five hp3 hpz
    have he : 3 + eps p = (3 : ℤ) := by simp [eps, hpz]
    rw [he]
    have hP := C.mul_left (b_top_close_large s hp5) (D.nat (p := p) 2)
    have hP' : C p 3 (F (p ^ s : ℕ) (p ^ s)) 2 := by
      rw [F_top _ hn]
      simpa using hP
    have ht := ff_congr hP' (F_integral (p := p) (p ^ s) (p ^ s)) (D.nat 2)
    norm_num [ff] at ht
    simpa only [ff, Nat.cast_pow] using ht

lemma aQ_ff_top_close (s : ℕ) (hp3 : 3 ≤ p) :
    C p (3 + eps p) (aQ (p ^ s) - ff (F (p ^ s : ℕ) (p ^ s))) (-18) := by
  have ht := C.sub (aQ_close s hp3) (ff_top_close s hp3)
  norm_num only [reduceSub] at ht
  exact ht


def M (n d : ℕ) : ℚ := ∑ k ∈ range n, (k : ℚ) ^ d * F n k ^ 2
def U (n : ℕ) : ℚ := M n 0 / n
def V (n : ℕ) : ℚ := (3 * M n 2 + 3 * M n 1 + M n 0) / n

lemma F_mul_succ (n k : ℕ) : (k + 1 : ℚ) * F n (k + 1) = (n + k + 1 : ℚ) * F n k := by
  rw [F_succ]
  have hn : (k + 1 : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp [hn]
  <;> ring

lemma b_mul_succ (n k : ℕ) : (k + 1 : ℚ) * b n (k + 1) = (n : ℚ) * F n k := by
  rw [b_succ]
  have hn : (k + 1 : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp [hn]

lemma S_shift (n m : ℕ) : ∑ k ∈ range n, b n (k + 1) ^ m = S n m - 1 := by
  have he := sum_range_succ' (fun k => b n k ^ m) n
  rw [b_zero, one_pow] at he
  dsimp only [S]
  linear_combination -he

lemma M_zero_identity (n : ℕ) :
    2 * (2 * n + 1 : ℚ) * M n 0 = (n : ℚ) * (F n n ^ 2 + S n 2) := by
  have hpw : ∀ k : ℕ,
      (2 * (k + 1 : ℚ) - n) * F n (k + 1) ^ 2 - (2 * (k : ℚ) - n) * F n k ^ 2 =
        2 * (2 * n + 1 : ℚ) * F n k ^ 2 - n * b n (k + 1) ^ 2 := by
    intro k
    have hs := F_step n k
    have hb := b_mul_succ n k
    have he : F n (k + 1) = F n k + b n (k + 1) := by linear_combination hs
    rw [he]
    linear_combination (4 * F n k + 2 * b n (k + 1)) * hb
  have he := sum_range_sub (fun k => (2 * (k : ℚ) - n) * F n k ^ 2) n
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, F_zero, one_pow, mul_zero, zero_sub, mul_one] at he
  have hh : (∑ k ∈ range n, ((2 * (k + 1 : ℚ) - n) * F n (k + 1) ^ 2 -
      (2 * (k : ℚ) - n) * F n k ^ 2)) =
      2 * (2 * n + 1 : ℚ) * M n 0 - n * (S n 2 - 1) := by
    simp_rw [hpw]
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum, S_shift]
    simp [M]
  rw [hh] at he
  linear_combination he

lemma M_one_identity (n : ℕ) :
    2 * (n + 1 : ℚ) * M n 1 + (n + 1 : ℚ) ^ 2 * M n 0 = (n : ℚ) ^ 2 * F n n ^ 2 := by
  have hpw : ∀ k : ℕ, (k + 1 : ℚ) ^ 2 * F n (k + 1) ^ 2 - (k : ℚ) ^ 2 * F n k ^ 2 =
      (2 * (n + 1 : ℚ) * k + (n + 1 : ℚ) ^ 2) * F n k ^ 2 := by
    intro k
    have he := congrArg (fun x : ℚ => x ^ 2) (F_mul_succ n k)
    dsimp only at he
    linear_combination he
  have he := sum_range_sub (fun k => (k : ℚ) ^ 2 * F n k ^ 2) n
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero] at he
  have hh : (∑ k ∈ range n, ((k + 1 : ℚ) ^ 2 * F n (k + 1) ^ 2 - (k : ℚ) ^ 2 * F n k ^ 2)) =
      2 * (n + 1 : ℚ) * M n 1 + (n + 1 : ℚ) ^ 2 * M n 0 := by
    simp_rw [hpw, add_mul]
    rw [sum_add_distrib]
    simp only [M, pow_one, pow_zero, one_mul, mul_assoc, sum_add_distrib, ← mul_sum]
  rw [hh] at he
  exact he

lemma M_two_identity (n : ℕ) :
    (2 * n + 3 : ℚ) * M n 2 + (n + 1 : ℚ) * (n + 3 : ℚ) * M n 1 +
      (n + 1 : ℚ) ^ 2 * M n 0 = (n : ℚ) ^ 3 * F n n ^ 2 := by
  have hpw : ∀ k : ℕ, (k + 1 : ℚ) ^ 3 * F n (k + 1) ^ 2 - (k : ℚ) ^ 3 * F n k ^ 2 =
      ((2 * n + 3 : ℚ) * (k : ℚ) ^ 2 + (n + 1 : ℚ) * (n + 3 : ℚ) * k +
        (n + 1 : ℚ) ^ 2) * F n k ^ 2 := by
    intro k
    have he := congrArg (fun x : ℚ => x ^ 2) (F_mul_succ n k)
    dsimp only at he
    linear_combination (k + 1 : ℚ) * he
  have he := sum_range_sub (fun k => (k : ℚ) ^ 3 * F n k ^ 2) n
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_pow (by decide : 3 ≠ 0), zero_mul, sub_zero] at he
  have hh : (∑ k ∈ range n, ((k + 1 : ℚ) ^ 3 * F n (k + 1) ^ 2 - (k : ℚ) ^ 3 * F n k ^ 2)) =
      (2 * n + 3 : ℚ) * M n 2 + (n + 1 : ℚ) * (n + 3 : ℚ) * M n 1 +
        (n + 1 : ℚ) ^ 2 * M n 0 := by
    simp_rw [hpw, add_mul]
    rw [sum_add_distrib, sum_add_distrib]
    simp only [M, pow_one, pow_zero, one_mul, mul_assoc, sum_add_distrib, ← mul_sum]
  rw [hh] at he
  exact he

lemma U_identity (n : ℕ) (hn : 0 < n) :
    2 * (2 * n + 1 : ℚ) * U n = F n n ^ 2 + S n 2 := by
  unfold U
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hn0]
  linear_combination M_zero_identity n

lemma M_zero_eq (n : ℕ) (hn : 0 < n) : M n 0 = (n : ℚ) * U n := by
  unfold U
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hn0]

lemma V_identity (n : ℕ) (hn : 0 < n) :
    2 * (n + 1 : ℚ) * (2 * n + 3 : ℚ) * V n =
      (n : ℚ) * (3 * F n n ^ 2 * (n : ℚ) ^ 2 + U n * (3 * (n : ℚ) ^ 3 + 6 * (n : ℚ) ^ 2 + n - 2)) := by
  unfold V U
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hn0]
  linear_combination 6 * (n + 1 : ℚ) * M_two_identity n - 3 * (n : ℚ) * (n + 2 : ℚ) * M_one_identity n



lemma D.cancel {a b : ℤ} {x y : ℚ} (hy : y ≠ 0) (hi : D p b y⁻¹)
    (h : D p a (y * x)) : D p (a + b) x := by
  simpa only [mul_assoc, mul_comm y x, mul_inv_cancel₀ hy, mul_one] using h.mul hi

lemma three_bound : D p (eps p) (3 : ℚ) := by
  by_cases he : p = 3
  · simpa [eps, he] using D.prime (p := p)
  · simpa [eps, he] using D.nat (p := p) 3

lemma pow_nat_bound (s : ℕ) : D p s (p ^ s : ℕ) := by
  simpa only [Nat.cast_pow] using D.prime_pow (p := p) s

lemma inv_linear_pow (s c : ℕ) (hs : 1 ≤ s) :
    D p 0 (c * (p ^ s : ℕ) + 1 : ℚ)⁻¹ := by
  have hx : D p 1 ((c : ℚ) * (p ^ s : ℕ)) :=
    ((D.nat c).mul (pow_nat_bound (p := p) s)).mono (by omega)
  simpa only [add_comm] using D.inv_one_add hx

lemma U_close (s : ℕ) (hp3 : 3 ≤ p) :
    C p 3 ((2 * (p ^ s : ℕ) + 1 : ℚ) * U (p ^ s)) 3 := by
  have h := S_two_low (p := p) s hp3
  have hn := U_identity (p ^ s) (pow_pos hp.out.pos _)
  have ht : D p 3 (2 * ((2 * (p ^ s : ℕ) + 1 : ℚ) * U (p ^ s) - 3)) := by
    dsimp only [C] at h
    convert h using 1
    linear_combination hn
  exact D.cancel_nat (n := 2) (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) ht

lemma U_bound (s : ℕ) (hs : 1 ≤ s) (hp3 : 3 ≤ p) : D p (eps p) (U (p ^ s)) := by
  have h := (U_close s hp3).mono (by have := eps_le_one (p := p); omega : eps p ≤ 3)
  have hd : D p (eps p) ((2 * (p ^ s : ℕ) + 1 : ℚ) * U (p ^ s)) := by
    convert D.add h (three_bound (p := p)) using 1 <;> ring
  have hn : (2 * (p ^ s : ℕ) + 1 : ℚ) ≠ 0 := by positivity
  simpa using D.cancel hn (inv_linear_pow s 2 hs) hd

lemma M_zero_bound (s : ℕ) (hs : 1 ≤ s) (hp3 : 3 ≤ p) :
    D p (s + eps p) (M (p ^ s) 0) := by
  rw [M_zero_eq _ (pow_pos hp.out.pos _)]
  exact (pow_nat_bound s).mul (U_bound s hs hp3)

set_option maxHeartbeats 800000 in
lemma M_one_bound (s : ℕ) (hs : 1 ≤ s) (hp3 : 3 ≤ p) :
    D p (s + eps p) (M (p ^ s) 1) := by
  have h0 := M_zero_bound s hs hp3
  have hf : D p 0 (F (p ^ s : ℕ) (p ^ s) ^ 2) := by
    simpa using (F_integral (p := p) (p ^ s) (p ^ s)).pow 2
  have hn : D p 0 ((p ^ s : ℕ) + 1 : ℚ) := (D.nat _).add D.one
  have hd := ((pow_nat_bound (p := p) s).pow 2).mul hf
  have hd' := hd.mono (by have := eps_le_one (p := p); omega : (s : ℤ) + eps p ≤ (s : ℤ) * 2 + 0)
  have hx : D p (s + eps p) (2 * ((p ^ s : ℕ) + 1 : ℚ) * M (p ^ s) 1) := by
    have hh : D p (s + eps p) (((p ^ s : ℕ) + 1 : ℚ) ^ 2 * M (p ^ s) 0) := by
      simpa only [zero_mul, zero_add] using (hn.pow 2).mul h0
    have ht := D.sub hd' hh
    convert ht using 1
    linear_combination M_one_identity (p ^ s)
  have hx' : D p (s + eps p) (((p ^ s : ℕ) + 1 : ℚ) * M (p ^ s) 1) := by
    apply D.cancel_nat (n := 2) (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    simpa only [Nat.cast_ofNat, ← mul_assoc] using hx
  have hinv : D p 0 (((p ^ s : ℕ) + 1 : ℚ)⁻¹) := by simpa using inv_linear_pow (p := p) s 1 hs
  simpa using D.cancel (by positivity) hinv hx'

lemma inv_two_pow_three (s : ℕ) (hs : 1 ≤ s) (hp3 : 3 ≤ p)
    (hgood : p ≠ 3 ∨ 2 ≤ s) : D p (-eps p) (2 * (p ^ s : ℕ) + 3 : ℚ)⁻¹ := by
  by_cases hpz : p = 3
  · have hs2 : 2 ≤ s := hgood.resolve_left (not_not.mpr hpz)
    have hpow : (p ^ s : ℕ) = p * p ^ (s - 1) := by
      rw [← pow_succ']; congr 1; omega
    have he : (2 * (p ^ s : ℕ) + 3 : ℚ) = (p : ℚ) * (2 * (p ^ (s - 1) : ℕ) + 1) := by
      rw [hpow]; push_cast; rw [hpz]; norm_num; ring
    rw [he, mul_inv_rev]
    have hi := inv_linear_pow (p := p) (s - 1) 2 (by omega)
    have ht := hi.mul (D.prime_zpow (p := p) (-1))
    simpa [eps, hpz] using ht
  · have hp5 := prime_ge_five hp3 hpz
    have hi := D.inv_small (p := p) 3 (by omega) (by omega)
    have hx : D p 1 (2 * (p ^ s : ℕ) / 3 : ℚ) := by
      have ht := ((D.nat (p := p) 2).mul (pow_nat_bound (p := p) s)).mul hi
      simpa only [Nat.cast_ofNat, div_eq_mul_inv] using ht.mono (by omega : (1 : ℤ) ≤ 0 + s + 0)
    have he : (2 * (p ^ s : ℕ) + 3 : ℚ) = 3 * (1 + 2 * (p ^ s : ℕ) / 3) := by ring
    rw [he, mul_inv_rev]
    simpa [eps, hpz] using (D.inv_one_add hx).mul hi

lemma M_two_bound (s : ℕ) (hs : 1 ≤ s) (hp3 : 3 ≤ p) (hgood : p ≠ 3 ∨ 2 ≤ s) :
    D p s (M (p ^ s) 2) := by
  have hn : D p 0 ((p ^ s : ℕ) + 1 : ℚ) := (D.nat _).add D.one
  have hn3 : D p 0 ((p ^ s : ℕ) + 3 : ℚ) := (D.nat _).add (D.nat 3)
  have hf : D p 0 (F (p ^ s : ℕ) (p ^ s) ^ 2) := by
    simpa using (F_integral (p := p) (p ^ s) (p ^ s)).pow 2
  have hd := ((pow_nat_bound (p := p) s).pow 3).mul hf
  have hd' := hd.mono (by have := eps_le_one (p := p); omega : (s : ℤ) + eps p ≤ (s : ℤ) * 3 + 0)
  have h1 := (hn.mul hn3).mul (M_one_bound s hs hp3)
  have h0 := (hn.pow 2).mul (M_zero_bound s hs hp3)
  simp only [zero_add, zero_mul] at h0 h1
  have hx : D p (s + eps p) ((2 * (p ^ s : ℕ) + 3 : ℚ) * M (p ^ s) 2) := by
    convert (hd'.sub h1).sub h0 using 1
    linear_combination M_two_identity (p ^ s)
  have ht := D.cancel (by positivity) (inv_two_pow_three s hs hp3 hgood) hx
  simpa using ht

lemma V_bound (s : ℕ) (hs : 1 ≤ s) (hp3 : 3 ≤ p) (hgood : p ≠ 3 ∨ 2 ≤ s) :
    D p s (V (p ^ s)) := by
  have hn0 : D p 0 (p ^ s : ℕ) := D.nat _
  have hf : D p 0 (F (p ^ s : ℕ) (p ^ s) ^ 2) := by
    simpa using (F_integral (p := p) (p ^ s) (p ^ s)).pow 2
  have hpoly : D p 0 (3 * (p ^ s : ℕ) ^ 3 + 6 * (p ^ s : ℕ) ^ 2 + (p ^ s : ℕ) - 2 : ℚ) := by
    exact (((D.nat 3).mul (hn0.pow 3)).add ((D.nat 6).mul (hn0.pow 2))).add hn0 |>.sub (D.nat 2)
  have hh : D p (eps p) (3 * F (p ^ s : ℕ) (p ^ s) ^ 2 * (p ^ s : ℕ) ^ 2) := by
    simpa only [add_zero, zero_mul] using ((three_bound (p := p)).mul hf).mul (hn0.pow 2)
  have hu : D p (eps p) (U (p ^ s) * (3 * (p ^ s : ℕ) ^ 3 + 6 * (p ^ s : ℕ) ^ 2 + (p ^ s : ℕ) - 2)) := by
    simpa using (U_bound s hs hp3).mul hpoly
  have hd := (pow_nat_bound s).mul (hh.add hu)
  rw [← V_identity _ (pow_pos hp.out.pos _)] at hd
  have hinv : D p (-eps p) (2 * ((p ^ s : ℕ) + 1 : ℚ) * (2 * (p ^ s : ℕ) + 3))⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev]
    have h1 : D p 0 (((p ^ s : ℕ) + 1 : ℚ)⁻¹) := by simpa using inv_linear_pow (p := p) s 1 hs
    have h2 := D.inv_small (p := p) 2 (by omega) (by omega)
    simpa only [add_zero, Nat.cast_ofNat] using (inv_two_pow_three s hs hp3 hgood).mul (h1.mul h2)
  simpa using D.cancel (by positivity) hinv hd


lemma final_delta_bound (s : ℕ) (hs : 1 ≤ s) (hp3 : 3 ≤ p) (hgood : 7 ≤ p ∨ 2 ≤ s) :
    D p 3 ((6 * h2 (p - 1) 1 2 - 9 * alpha p) * M (p ^ s) 0) := by
  have hM := M_zero_bound s hs hp3
  by_cases hpz : p = 3
  · have hs2 : 2 ≤ s := by rcases hgood with hg | hg <;> omega
    have hc3 : D p 1 (3 : ℚ) := by simpa [eps, hpz] using three_bound (p := p)
    have hh := h2_integral (p := p) (p - 1) 1 2 (by have := hp.out.pos; omega)
    have h6 : D p 1 (6 * h2 (p - 1) 1 2) := by
      have ht := ((D.nat (p := p) 2).mul hc3).mul hh
      norm_num only [Nat.cast_ofNat, reduceMul, zero_add, add_zero] at ht
      exact ht
    have h9 : D p 1 (9 * alpha p) := by
      have ht := (hc3.pow 2).mul (alpha_bound hp3)
      simpa [eps, hpz] using ht
    have ht := (h6.sub h9).mul hM
    apply ht.mono
    simp only [eps, if_pos hpz]; omega
  · have hp5 := prime_ge_five hp3 hpz
    have he : eps p = 0 := by simp [eps, hpz]
    have hd : D p (3 - (s : ℤ)) (2 * h2 (p - 1) 1 2 - 3 * alpha p) := by
      rcases hgood with hg | hg
      · exact (harmonic_delta_two hg).mono (by omega)
      · exact (harmonic_delta_one hp5).mono (by omega)
    have ht := ((D.nat (p := p) 3).mul hd).mul hM
    have ht' := ht.mono (by rw [he]; omega : (3 : ℤ) ≤ 0 + (3 - s) + (s + eps p))
    convert ht' using 1 <;> ring

lemma final_cancellation (s : ℕ) (hs : 1 ≤ s) (hp3 : 3 ≤ p) (hgood : 7 ≤ p ∨ 2 ≤ s) :
    D p 3 (alpha p / 2 * (aQ (p ^ s) - ff (F (p ^ s : ℕ) (p ^ s))) +
      3 * alpha p * (1 / (p ^ s : ℕ) - 1) * M (p ^ s) 0 +
      6 * h2 (p - 1) 1 2 * M (p ^ s) 0) := by
  have ha := alpha_bound (p := p) hp3
  have hi2 := D.inv_small (p := p) 2 (by omega) (by omega)
  have h1 := D.mul (ha.mul hi2) (aQ_ff_top_close s hp3)
  have h1' : D p 3 (alpha p / 2 * (aQ (p ^ s) - ff (F (p ^ s : ℕ) (p ^ s)) + 18)) := by
    convert h1 using 1 <;> (try simp only [Nat.cast_ofNat, sub_neg_eq_add, div_eq_mul_inv]) <;> ring
  have h2 := D.mul ((three_bound (p := p)).mul ha) (U_close s hp3)
  have h2' : D p 3 (3 * alpha p * ((2 * (p ^ s : ℕ) + 1 : ℚ) * U (p ^ s) - 3)) := by
    convert h2 using 1 <;> ring
  have h3 := final_delta_bound s hs hp3 hgood
  have ht := (h1'.add h2').add h3
  rw [M_zero_eq _ (pow_pos hp.out.pos _)] at ht ⊢
  have hn : (p ^ s : ℕ) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hnq : ((p ^ s : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hn
  convert ht using 1
  field_simp [hnq]
  <;> ring


lemma inv_three_bound (hp3 : 3 ≤ p) : D p (-eps p) (3 : ℚ)⁻¹ := by
  by_cases he : p = 3
  · simpa [eps, he] using D.prime_zpow (p := p) (-1)
  · simpa [eps, he] using D.inv_small (p := p) 3 (by omega) (by have := prime_ge_five hp3 he; omega)

lemma inv_six_bound (hp3 : 3 ≤ p) : D p (-eps p) (6 : ℚ)⁻¹ := by
  have ht := (D.inv_small (p := p) 2 (by omega) (by omega)).mul (inv_three_bound hp3)
  norm_num only [Nat.cast_ofNat, zero_add] at ht
  convert ht using 1 <;> norm_num

lemma inv_twentyfour_bound (hp3 : 3 ≤ p) : D p (-eps p) (24 : ℚ)⁻¹ := by
  have ht := (D.inv_nat (p := p) 4 (not_dvd_four hp3)).mul (inv_six_bound hp3)
  norm_num only [Nat.cast_ofNat, zero_add] at ht
  convert ht using 1 <;> norm_num

lemma product_second_approx {ι : Type*} (I : Finset ι) (f : ι → ℚ)
    (r q : ℤ) (hr : 2 ≤ r) (hq : 1 ≤ q) (hqr : q ≤ r) (hp3 : 3 ≤ p)
    (hf : ∀ i ∈ I, D p r (f i))
    (h1 : D p (r + 2*q - eps p) (∑ i ∈ I, f i))
    (h2 : D p (2*r + q - eps p) (∑ i ∈ I, f i ^ 2))
    (h3 : D p (3*r + 2*q - 1) (∑ i ∈ I, f i ^ 3))
    (h4 : D p (4*r + q - 1) (∑ i ∈ I, f i ^ 4)) :
    C p (r + 2*q + 3 - eps p) (∏ i ∈ I, (1 + f i))
      (1 + (∑ i ∈ I, f i) - (∑ i ∈ I, f i ^ 2) / 2) := by
  have hc := eps_nonneg (p := p)
  have hc1 := eps_le_one (p := p)
  have hi2 := D.inv_small (p := p) 2 (by omega) (by omega)
  have he2 : D p (r + 2*q + 3 - eps p) (E I f 2 + (∑ i ∈ I, f i ^ 2) / 2) := by
    have ht := (h1.pow 2).mul hi2
    have ht' := ht.mono (by omega : r + 2*q + 3 - eps p ≤ (r + 2*q - eps p) * 2 + 0)
    convert ht' using 1
    norm_num only [Nat.cast_ofNat]
    linear_combination (1/2 : ℚ) * E_two I f
  have he3 : D p (3*r + 2*q - 1 - eps p) (E I f 3) := by
    have ht1 := (h1.pow 3).mono (by omega : 3*r + 2*q - 1 ≤ (r + 2*q - eps p) * 3)
    have ht2 := (((D.nat (p := p) 3).mul h1).mul h2).mono
      (by omega : 3*r + 2*q - 1 ≤ (0 + (r + 2*q - eps p)) + (2*r + q - eps p))
    have ht3 : D p (3*r + 2*q - 1) (2 * ∑ i ∈ I, f i ^ 3) := by
      simpa only [Nat.cast_ofNat, zero_add] using (D.nat (p := p) 2).mul h3
    have ht := (ht1.sub ht2).add ht3
    norm_num only [Nat.cast_ofNat] at ht
    rw [← E_three] at ht
    have ht' := D.cancel (by norm_num : (6 : ℚ) ≠ 0) (inv_six_bound hp3) ht
    simpa only [sub_eq_add_neg] using ht'
  have he4 : D p (4*r + q - 1 - eps p) (E I f 4) := by
    have hw1 := h1.mono (by omega : r + q - 1 ≤ r + 2*q - eps p)
    have hw2 := h2.mono (by omega : 2*r + q - 1 ≤ 2*r + q - eps p)
    have hw3 := h3.mono (by omega : 3*r + q - 1 ≤ 3*r + 2*q - 1)
    have ht1 := (hw1.pow 4).mono (by omega : 4*r + q - 1 ≤ (r + q - 1)*4)
    have ht2 := (((D.nat (p := p) 6).mul (hw1.pow 2)).mul hw2).mono
      (by omega : 4*r + q - 1 ≤ 0 + (r + q - 1)*2 + (2*r + q - 1))
    have ht3 := ((D.nat (p := p) 3).mul (hw2.pow 2)).mono
      (by omega : 4*r + q - 1 ≤ 0 + (2*r + q - 1)*2)
    have ht4 := (((D.nat (p := p) 8).mul hw1).mul hw3).mono
      (by omega : 4*r + q - 1 ≤ 0 + (r + q - 1) + (3*r + q - 1))
    have ht5 : D p (4*r + q - 1) (6 * ∑ i ∈ I, f i ^ 4) := by
      simpa only [Nat.cast_ofNat, zero_add] using (D.nat (p := p) 6).mul h4
    have ht := (((ht1.sub ht2).add ht3).add ht4).sub ht5
    norm_num only [Nat.cast_ofNat] at ht
    rw [← E_four] at ht
    have ht' := D.cancel (by norm_num : (24 : ℚ) ≠ 0) (inv_twentyfour_bound hp3) ht
    simpa only [sub_eq_add_neg] using ht'
  have htail := (prod_approx I f r (by omega) hf 5).mono
    (by omega : r + 2*q + 3 - eps p ≤ r * 5)
  have he3' := he3.mono (by omega : r + 2*q + 3 - eps p ≤ 3*r + 2*q - 1 - eps p)
  have he4' := he4.mono (by omega : r + 2*q + 3 - eps p ≤ 4*r + q - 1 - eps p)
  have ht := ((D.add htail he2).add he3').add he4'
  simp only [sum_range_succ, sum_range_zero, E_zero, E_one, zero_add] at ht
  dsimp only [C]
  convert ht using 1 <;> ring


def Q (p n L : ℕ) : ℚ := ∏ i ∈ J p L, (1 + (n : ℚ) / i)

lemma Q_integral (n L : ℕ) : D p 0 (Q p n L) := by
  apply D.prod
  intro i hi
  exact D.one.add ((D.nat n).div_nat i (mem_filter.mp hi).2)

lemma unit_power_sum (n L m : ℕ) :
    (∑ i ∈ J p L, ((n : ℚ) / i) ^ m) = (n : ℚ)^m * H p L m := by
  simp only [H, div_eq_mul_inv, mul_pow, mul_sum]

lemma Q_second_approx (r v L : ℕ) (hr : 2 ≤ r) (hv : v < r)
    (hL : p ^ (v + 1) ∣ L) (hp3 : 3 ≤ p) :
    C p (r + 2 * (v : ℤ) + 5 - eps p) (Q p (p ^ r) L)
      (1 + (p : ℚ)^r * H p L 1 - (p : ℚ)^(2*r) * H p L 2 / 2) := by
  have h1 := (pow_nat_bound (p := p) r).mul (H_one_bound_general L v hL hp3)
  have h2 := ((pow_nat_bound (p := p) r).pow 2).mul (H_two_bound_general L v hL hp3)
  have h3 := ((pow_nat_bound (p := p) r).pow 3).mul (H_odd_weak L v 3 hL (by decide) hp3)
  have h4 := ((pow_nat_bound (p := p) r).pow 4).mul (H_weak_of_dvd L v 4 hL)
  have hs1 : D p (r + 2*((v:ℤ)+1) - eps p) (∑ i ∈ J p L, ((p ^ r : ℕ) : ℚ) / i) := by
    rw [← pow_one ((p ^ r : ℕ) : ℚ), ← unit_power_sum (p ^ r) L 1] at h1
    simpa only [pow_one, mul_add, mul_one, add_sub_assoc, add_assoc] using h1
  have hs2 : D p (2*(r:ℤ) + (v+1) - eps p) (∑ i ∈ J p L, (((p ^ r : ℕ) : ℚ) / i)^2) := by
    rw [← unit_power_sum] at h2
    convert h2 using 1 <;> ring
  have hs3 : D p (3*(r:ℤ) + 2*(v+1) - 1) (∑ i ∈ J p L, (((p ^ r : ℕ) : ℚ) / i)^3) := by
    rw [← unit_power_sum] at h3
    convert h3 using 1 <;> ring
  have hs4 : D p (4*(r:ℤ) + (v+1) - 1) (∑ i ∈ J p L, (((p ^ r : ℕ) : ℚ) / i)^4) := by
    rw [← unit_power_sum] at h4
    convert h4 using 1 <;> ring
  have ht := product_second_approx (p := p) (J p L) (fun i => ((p ^ r : ℕ) : ℚ) / i)
    r (v+1) (by omega) (by omega) (by omega) hp3
    (fun i hi => (pow_nat_bound r).div_nat i (mem_filter.mp hi).2) hs1 hs2 hs3 hs4
  rw [show 2*r = r*2 by omega, pow_mul]
  simp only [Q, H, div_eq_mul_inv, mul_pow, ← mul_sum, Nat.cast_pow, pow_one] at ht ⊢
  convert ht using 1 <;> ring



lemma Q_close (r v L : ℕ) (hr : 2 ≤ r) (hv : v < r)
    (hL : p ^ (v + 1) ∣ L) (hp3 : 3 ≤ p) :
    C p (r + 2 * (v : ℤ) + 2 - eps p) (Q p (p ^ r) L) 1 := by
  have h1 := (D.prime_pow (p := p) r).mul (H_one_bound_general L v hL hp3)
  have h2 := ((D.prime_pow (p := p) (2*r)).mul (H_two_bound_general L v hL hp3)).div_nat 2 (not_dvd_two hp3)
  have ht := Q_second_approx r v L hr hv hL hp3
  have ht' := ht.mono (by omega : (r : ℤ) + 2*v + 2 - eps p ≤ r + 2*v + 5 - eps p)
  have h1' := h1.mono (by omega : (r : ℤ) + 2*v + 2 - eps p ≤ r + (2*v + 2 - eps p))
  have h2' := h2.mono (by push_cast; omega : (r : ℤ) + 2*v + 2 - eps p ≤ (2*r : ℕ) + (v+1-eps p))
  dsimp only [C]
  convert (D.add ht' h1').sub h2' using 1 <;> norm_num only [Nat.cast_ofNat] <;> ring

lemma Q_refined (r v l : ℕ) (hr : 2 ≤ r) (hv : v < r)
    (hl : p ^ v ∣ l) (hp3 : 3 ≤ p) :
    C p (r + 2 * (v : ℤ) + 5 - eps p) (Q p (p ^ r) (p*l))
      (1 - alpha p * (p:ℚ)^r * ((p:ℚ)*l) * ((p:ℚ)^r + (p:ℚ)*l) / 2 -
        beta p * (p:ℚ)^r * ((p:ℚ)*l)^3 * ((p:ℚ)*l + 2*(p:ℚ)^r) / 4) := by
  have hL : p ^ (v+1) ∣ p*l := by simpa only [pow_succ'] using Nat.mul_dvd_mul_left p hl
  have hQ := Q_second_approx r v (p*l) hr hv hL hp3
  have h1 := C.mul_left (H_one_expansion l v hl hp3) (D.prime_pow (p := p) r)
  have h2 := C.mul_left (H_two_expansion l v hl hp3) (D.prime_pow (p := p) (2*r))
  have h2' := C.mul_right h2 (D.inv_nat (p := p) 2 (not_dvd_two hp3))
  have hd1 := h1.mono (by omega : (r : ℤ)+2*v+5-eps p ≤ (2*v+5-eps p)+r)
  have hd2 := h2'.mono (by push_cast; omega : (r : ℤ)+2*v+5-eps p ≤ (v+4-eps p)+(2*r : ℕ)+0)
  dsimp only [C]
  convert (D.add hQ hd1).sub hd2 using 1
  simp only [Nat.cast_ofNat, show 2*r = r*2 by omega, pow_mul]
  ring

lemma ff_product_linear (r q : ℤ) (hr : 2 ≤ r) (hq : 1 ≤ q) (hqr : q ≤ r)
    (x y a : ℚ) (hx : D p (r-q) x)
    (hy : C p (r+2*q-eps p) y 1)
    (ha : C p (r+2*q+3-eps p) y (1+a)) :
    C p (3*r+3) (ff (x*y) - ff x) (6*(x^2+x^3)*a) := by
  have hc := eps_nonneg (p := p)
  have hc1 := eps_le_one (p := p)
  have h6 : D p (eps p) (6:ℚ) := by
    have ht := (D.nat (p := p) 2).mul (three_bound (p := p))
    norm_num only [Nat.cast_ofNat, zero_add, reduceMul] at ht
    exact ht
  have hx3 := (hx.pow 3).mono (by omega : 2*(r-q) ≤ (r-q)*3)
  have hx2 := (hx.pow 2).mono (by omega : 2*(r-q) ≤ (r-q)*2)
  have hlin := D.mul (h6.mul (hx2.add hx3)) ha
  have hlin' := hlin.mono (by omega : 3*r+3 ≤ (eps p + 2*(r-q)) + (r+2*q+3-eps p))
  have hsq := (((three_bound (p := p)).mul (hx.pow 2)).mul (D.pow hy 2)).mono
    (by omega : 3*r+3 ≤ eps p + (r-q)*2 + (r+2*q-eps p)*2)
  have hsq3 := ((h6.mul (hx.pow 3)).mul (D.pow hy 2)).mono
    (by omega : 3*r+3 ≤ eps p + (r-q)*3 + (r+2*q-eps p)*2)
  have hcub := (((D.nat (p := p) 2).mul (hx.pow 3)).mul (D.pow hy 3)).mono
    (by omega : 3*r+3 ≤ 0 + (r-q)*3 + (r+2*q-eps p)*3)
  dsimp only [C, ff]
  convert ((hlin'.add hsq).add hsq3).add hcub using 1 <;> norm_num only [Nat.cast_ofNat] <;> ring

lemma multiple_term_refined (r v l : ℕ) (hr : 2 ≤ r) (hv : v < r)
    (hl : p ^ v ∣ l) (hp3 : 3 ≤ p) (x : ℚ) (hx : D p ((r:ℤ)-v-1) x) :
    C p (3*(r:ℤ)+3) (ff (x * Q p (p^r) (p*l)) - ff x)
      (-3 * alpha p * (p:ℚ)^r * (x^2+x^3) * ((p:ℚ)*l) * ((p:ℚ)^r+(p:ℚ)*l) -
        3/2 * beta p * (p:ℚ)^r * (x^2+x^3) * ((p:ℚ)*l)^3 * ((p:ℚ)*l+2*(p:ℚ)^r)) := by
  have hL : p ^ (v+1) ∣ p*l := by simpa only [pow_succ'] using Nat.mul_dvd_mul_left p hl
  have hy := Q_close r v (p*l) hr hv hL hp3
  have ha := Q_refined r v l hr hv hl hp3
  have hx' : D p ((r:ℤ)-(v+1)) x := by convert hx using 1 <;> ring
  have hy' : C p ((r:ℤ)+2*(v+1)-eps p) (Q p (p^r) (p*l)) 1 := by convert hy using 1 <;> ring
  have ha' : C p ((r:ℤ)+2*(v+1)+3-eps p) (Q p (p^r) (p*l))
      (1 + (- alpha p * (p:ℚ)^r * ((p:ℚ)*l) * ((p:ℚ)^r + (p:ℚ)*l) / 2 -
        beta p * (p:ℚ)^r * ((p:ℚ)*l)^3 * ((p:ℚ)*l + 2*(p:ℚ)^r) / 4)) := by
    dsimp only [C] at *
    convert ha using 1 <;> ring
  have ht := ff_product_linear (p := p) r (v+1) (by omega) (by omega) (by omega)
    x (Q p (p^r) (p*l)) _ hx' hy' ha'
  dsimp only [C] at *
  convert ht using 1 <;> ring


/-- The binomial product, with its harmless zero-index factor included. -/
def G (x : ℚ) (k : ℕ) : ℚ := ∏ i ∈ range k, (1+x/i)
lemma G_zero (x : ℚ) : G x 0 = 1 := by simp [G]
lemma G_succ (x : ℚ) (k : ℕ) : G x (k+1) = G x k * (1+x/k) := prod_range_succ _ _
lemma G_eq_F (x : ℚ) (k : ℕ) : G x (k+1) = F x k := by
  rw [G, prod_range_succ']
  simp only [Nat.cast_zero, div_zero, add_zero, mul_one]
  rfl
lemma G_pos (x : ℚ) (k : ℕ) (hk : 0 < k) : G x k = F x (k-1) := by
  simpa only [Nat.sub_add_cancel hk] using G_eq_F x (k-1)

lemma G_split (n l : ℕ) : G (p*n : ℕ) (p*l) = G n l * Q p (p*n) (p*l) := by
  rw [G, prod_split_multiples]
  congr 1
  apply prod_congr rfl
  intro i hi
  push_cast
  have hn : (p:ℚ) ≠ 0 := p_ne
  rw [mul_div_mul_left _ _ hn]

lemma b_split (n l : ℕ) : b (p*n) (p*l) = b n l * Q p (p*n) (p*l) := by
  by_cases hl : l = 0
  · subst l; simp [b_zero, Q, J]
  · have hlp : 0 < p*l := Nat.mul_pos hp.out.pos (Nat.pos_of_ne_zero hl)
    rw [b_pos _ _ hlp, ← G_pos _ _ hlp, G_split,
      b_pos _ _ (Nat.pos_of_ne_zero hl), ← G_pos _ _ (Nat.pos_of_ne_zero hl)]
    push_cast
    have hn : (p:ℚ) ≠ 0 := p_ne
    rw [mul_div_mul_left _ _ hn, mul_assoc]


def W (n : ℕ) : ℚ := ∑ k ∈ range n, F n k * F n (k+1) * (1+b n (k+1))
def WB (n : ℕ) : ℚ := ∑ k ∈ range n, F n k * F n (k+1) * (1+b n (k+1)) *
  ((k+1:ℚ)^2 + n*(k+1:ℚ) + (n:ℚ)^2)

lemma W_identity (n : ℕ) : W n = M n 0 - (aQ n - ff (F n n)) / 6 := by
  have he : ∀ k, ff (b n (k+1)) - (ff (F n (k+1)) - ff (F n k)) =
      6 * (F n k ^ 2 - F n k * F n (k+1) * (1+b n (k+1))) := by
    intro k
    have ht : F n (k+1) = F n k + b n (k+1) := by linear_combination F_step n k
    rw [ht]
    unfold ff
    ring
  have ht := sum_congr (s₁ := range n) rfl (fun k hk => he k)
  simp only [sum_sub_distrib, ← mul_sum] at ht
  have htel := sum_range_sub (fun k => ff (F n k)) n
  rw [sum_sub_distrib] at htel
  rw [htel] at ht
  have ha : ∑ k ∈ range n, ff (b n (k+1)) = aQ n - 5 := by
    simp only [ff, sum_add_distrib, ← mul_sum, S_shift, aQ]
    ring
  rw [ha, F_zero] at ht
  norm_num only [ff, reducePow, reduceMul, reduceAdd] at ht
  simp only [M, pow_zero, one_mul, W]
  unfold ff
  linear_combination (1/6:ℚ) * ht

lemma WB_term_identity (n k : ℕ) :
    F n k * F n (k+1) * (1+b n (k+1)) * ((k+1:ℚ)^2+n*(k+1:ℚ)+(n:ℚ)^2) -
      (k+1:ℚ)^2 * F n (k+1)^2 =
    (n:ℚ) * (F n k * F n (k+1) * ((k+1:ℚ)*(F n (k+1)-1) -
      n*F n k + (1+b n (k+1))*((k+1:ℚ)+n))) := by
  have hb := b_mul_succ n k
  have hf : F n (k+1) = F n k + b n (k+1) := by linear_combination F_step n k
  rw [hf] at *
  linear_combination (F n k + b n (k+1)) *
    ((k+1:ℚ)*(F n k-1) - n*F n k) * hb


lemma WB_bound (s : ℕ) (hs : 1 ≤ s) (hp3 : 3 ≤ p) (hgood : p ≠ 3 ∨ 2 ≤ s) :
    D p s (WB (p ^ s)) := by
  have hterm : ∀ k, C p s
      (F (p^s:ℕ) k * F (p^s:ℕ) (k+1) * (1+b (p^s) (k+1)) *
        ((k+1:ℚ)^2+(p^s:ℕ)*(k+1:ℚ)+(p^s:ℕ)^2))
      ((k+1:ℚ)^2 * F (p^s:ℕ) (k+1)^2) := by
    intro k
    dsimp only [C]
    rw [WB_term_identity]
    have hf := F_integral (p := p) (p^s) k
    have hf' := F_integral (p := p) (p^s) (k+1)
    have hb := b_integral (p := p) (p^s) (k+1)
    have hk : D p 0 (k+1:ℚ) := (D.nat k).add D.one
    have hn := D.nat (p := p) (p^s)
    have hh := ((hf.mul hf').mul (((hk.mul (hf'.sub D.one)).sub (hn.mul hf)).add
      ((D.one.add hb).mul (hk.add hn))))
    simpa only [zero_add, add_zero] using (pow_nat_bound s).mul hh
  have ht := C.sum (range (p^s)) _ _ (fun k hk => hterm k)
  have he : ∑ k ∈ range (p^s), (k+1:ℚ)^2 * F (p^s:ℕ) (k+1)^2 =
      M (p^s) 2 + (p^s:ℕ)^2 * F (p^s:ℕ) (p^s)^2 := by
    have h := sum_range_succ' (fun k => (k:ℚ)^2 * F (p^s:ℕ) k^2) (p^s)
    rw [sum_range_succ] at h
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero, M] using h.symm
  rw [he] at ht
  apply ht.dvd_left
  apply (M_two_bound s hs hp3 hgood).add
  exact (((pow_nat_bound (p := p) s).pow 2).mul
    ((F_integral (p := p) (p^s) (p^s)).pow 2)).mono (by omega)


lemma multiple_term_completed (r v l : ℕ) (hr : 2 ≤ r) (hv : v < r)
    (hl : p ^ v ∣ l) (hp3 : 3 ≤ p) (x : ℚ) (hx : D p ((r:ℤ)-v-1) x) :
    C p (3*(r:ℤ)+3) (ff (x * Q p (p^r) (p*l)) - ff x)
      (-3 * alpha p * (p:ℚ)^r * (x^2+x^3) * ((p:ℚ)*l) * ((p:ℚ)^r+(p:ℚ)*l) -
        3/2 * beta p * (p:ℚ)^r * (x^2+x^3) * ((p:ℚ)*l) * ((p:ℚ)^r+(p:ℚ)*l) *
          (((p:ℚ)*l)^2+(p:ℚ)^r*((p:ℚ)*l)+((p:ℚ)^r)^2)) := by
  have hq := (D.prime (p := p)).mul (D.of_nat_dvd hl)
  have hx2 := (hx.pow 2).mono (by omega : 2*((r:ℤ)-v-1) ≤ ((r:ℤ)-v-1)*2)
  have hx3 := (hx.pow 3).mono (by omega : 2*((r:ℤ)-v-1) ≤ ((r:ℤ)-v-1)*3)
  have hb := (D.nat (p := p) 3).mul (beta_bound (p := p))
  have h1 := (((hb.mul ((D.prime_pow r).pow 3)).mul (hx2.add hx3)).mul (hq.pow 2)).mono
    (by omega : 3*(r:ℤ)+3 ≤ ((0+(-1)+(r:ℤ)*3)+2*((r:ℤ)-v-1))+(1+(v:ℤ))*2)
  have h2 := (((hb.mul ((D.prime_pow r).pow 4)).mul (hx2.add hx3)).mul hq).div_nat 2 (not_dvd_two hp3)
  have h2' := h2.mono (by omega : 3*(r:ℤ)+3 ≤ ((0+(-1)+(r:ℤ)*4)+2*((r:ℤ)-v-1))+(1+(v:ℤ)))
  have ht := multiple_term_refined r v l hr hv hl hp3 x hx
  dsimp only [C] at *
  convert (D.add ht h1).add h2' using 1 <;> norm_num only [Nat.cast_ofNat] <;> ring

lemma b_weight_identity (n k : ℕ) :
    b n (k+1)^2 * (k+1:ℚ) * (n+k+1:ℚ) = (n:ℚ)^2 * F n k * F n (k+1) := by
  have hb := b_mul_succ n k
  have hf : F n (k+1) = F n k + b n (k+1) := by linear_combination F_step n k
  rw [hf]
  linear_combination ((n+k+1:ℚ)*b n (k+1)+(n:ℚ)*F n k) * hb

lemma multiple_prime_power_term (s k : ℕ) (hs : 1 ≤ s) (hk : k < p^s) (hp3 : 3 ≤ p) :
    C p (3*((s:ℤ)+1)+3) (ff (b (p^(s+1)) (p*(k+1))) - ff (b (p^s) (k+1)))
      (-3 * alpha p * ((p:ℚ)^(s+1))^3 *
        (F (p^s:ℕ) k * F (p^s:ℕ) (k+1) * (1+b (p^s) (k+1))) -
       3/2 * beta p * ((p:ℚ)^(s+1))^3 * (p:ℚ)^2 *
        (F (p^s:ℕ) k * F (p^s:ℕ) (k+1) * (1+b (p^s) (k+1)) *
          ((k+1:ℚ)^2+(p^s:ℕ)*(k+1:ℚ)+(p^s:ℕ)^2))) := by
  have hpow : p^s < p^(s+1) := by exact (pow_lt_pow_right₀ hp.out.one_lt (by omega))
  have hv := valuation_lt_power (p := p) (s+1) (k+1) (by omega) (by omega)
  have hb := b_prime_power_bound (p := p) s (k+1) (by omega)
  have hb' : D p (((s+1:ℕ):ℤ)-padicValNat p (k+1)-1) (b (p^s) (k+1)) := by
    convert hb using 1 <;> push_cast <;> ring
  have ht := multiple_term_completed (p := p) (s+1) (padicValNat p (k+1)) (k+1)
    (by omega) hv pow_padicValNat_dvd hp3 (b (p^s) (k+1)) hb'
  have hsplit : b (p^(s+1)) (p*(k+1)) = b (p^s) (k+1) * Q p (p^(s+1)) (p*(k+1)) := by
    simpa only [pow_succ'] using b_split (p := p) (p^s) (k+1)
  rw [← hsplit] at ht
  have hw := b_weight_identity (p^s) k
  have he : (b (p^s) (k+1)^2+b (p^s) (k+1)^3) * ((p:ℚ)*(k+1)) *
      ((p:ℚ)^(s+1)+(p:ℚ)*(k+1)) =
      ((p:ℚ)^(s+1))^2 * F (p^s:ℕ) k * F (p^s:ℕ) (k+1) * (1+b (p^s) (k+1)) := by
    simp only [pow_succ', Nat.cast_pow] at hw ⊢
    linear_combination (p:ℚ)^2*(1+b (p^s) (k+1)) * hw
  have hepoly : ((p:ℚ)*(k+1))^2+(p:ℚ)^(s+1)*((p:ℚ)*(k+1))+((p:ℚ)^(s+1))^2 =
      (p:ℚ)^2*((k+1:ℚ)^2+(p^s:ℕ)*(k+1:ℚ)+(p^s:ℕ)^2) := by
    simp only [pow_succ', Nat.cast_pow]; ring
  dsimp only [C] at *
  simp only [Nat.cast_add, Nat.cast_one] at ht
  convert ht using 1
  rw [hepoly]
  linear_combination -(3 * alpha p * (p:ℚ)^(s+1) +
    3/2 * beta p * (p:ℚ)^(s+1) * (p:ℚ)^2 * ((k+1:ℚ)^2+(p^s:ℕ)*(k+1:ℚ)+(p^s:ℕ)^2)) * he

lemma beta_WB_vanish (s : ℕ) (hs : 1 ≤ s) (hp3 : 3 ≤ p) (hgood : 7 ≤ p ∨ 2 ≤ s) :
    D p (3*((s:ℤ)+1)+3) (3/2 * beta p * ((p:ℚ)^(s+1))^3 * (p:ℚ)^2 * WB (p^s)) := by
  have hg : p ≠ 3 ∨ 2 ≤ s := by rcases hgood with h | h; exact Or.inl (by omega); exact Or.inr h
  have hw := WB_bound s hs hp3 hg
  have hi := D.inv_nat (p := p) 2 (not_dvd_two hp3)
  have hb : D p (1-(s:ℤ)) (beta p) := by
    rcases hgood with hg | hg
    · exact (beta_bound_large hg).mono (by omega)
    · exact (beta_bound (p := p)).mono (by omega)
  have ht := (((((D.nat (p := p) 3).mul hi).mul hb).mul ((D.prime_pow (s+1)).pow 3)).mul (D.prime_pow 2)).mul hw
  have ht' := ht.mono (by push_cast; omega : 3*((s:ℤ)+1)+3 ≤ 0+0+(1-s)+((s+1:ℕ):ℤ)*3+2+s)
  convert ht' using 1 <;> norm_num only [Nat.cast_ofNat] <;> ring

lemma multiples_contribution (s : ℕ) (hs : 1 ≤ s) (hp3 : 3 ≤ p) (hgood : 7 ≤ p ∨ 2 ≤ s) :
    C p (3*((s:ℤ)+1)+3)
      (∑ l ∈ range (p^s+1), (ff (b (p^(s+1)) (p*l)) - ff (b (p^s) l)))
      (((p:ℚ)^(s+1))^3 * (alpha p / 2 * (aQ (p^s) - ff (F (p^s:ℕ) (p^s))) -
        3 * alpha p * M (p^s) 0)) := by
  have ht := C.sum (range (p^s)) _ _ (fun k hk => multiple_prime_power_term s k hs (mem_range.mp hk) hp3)
  have he : (∑ l ∈ range (p^s+1), (ff (b (p^(s+1)) (p*l)) - ff (b (p^s) l))) =
      ∑ k ∈ range (p^s), (ff (b (p^(s+1)) (p*(k+1))) - ff (b (p^s) (k+1))) := by
    rw [sum_range_succ']; simp only [mul_zero, b_zero, sub_self, add_zero]
  rw [he]
  simp only [sum_sub_distrib, ← mul_sum] at ht
  change C p _ _ (-3 * alpha p * ((p:ℚ)^(s+1))^3 * W (p^s) -
    3/2 * beta p * ((p:ℚ)^(s+1))^3 * (p:ℚ)^2 * WB (p^s)) at ht
  have hd := D.sub ht (beta_WB_vanish s hs hp3 hgood)
  rw [W_identity] at hd
  dsimp only [C]
  simp only [sum_sub_distrib]
  convert hd using 1 <;> ring


lemma F_weighted_sum (n : ℕ) :
    (∑ k ∈ range n, (2*k+1:ℚ)*F n k) = (n:ℚ)^2*F n n -
      (n:ℚ) * ∑ k ∈ range n, (k+1:ℚ)*F n k := by
  have he : ∀ k : ℕ, (k+1:ℚ)^2*F n (k+1) - (k:ℚ)^2*F n k =
      (2*k+1:ℚ)*F n k + (n:ℚ)*(k+1:ℚ)*F n k := by
    intro k
    linear_combination (k+1:ℚ)*F_mul_succ n k
  have ht := sum_congr (s₁ := range n) rfl (fun k hk => he k)
  have htel := sum_range_sub (fun k => (k:ℚ)^2*F n k) n
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero] at htel
  rw [htel, sum_add_distrib] at ht
  simp only [mul_assoc, ← mul_sum] at ht
  linear_combination -ht

lemma F_cube_weighted_bound (s : ℕ) (hs : 1 ≤ s) :
    D p (min (s:ℤ) 2) (∑ k ∈ range (p^s), (2*k+1:ℚ)*F (p^s:ℕ) k^3) := by
  have hn := pow_nat_bound (p := p) s
  have hf := F_integral (p := p) (p^s) (p^s)
  have hsum : D p 0 (∑ k ∈ range (p^s), (k+1:ℚ)*F (p^s:ℕ) k) := by
    apply D.sum; intro k hk
    simpa using ((D.nat (p := p) k).add D.one).mul (F_integral (p := p) (p^s) k)
  have hw : D p s (∑ k ∈ range (p^s), (2*k+1:ℚ)*F (p^s:ℕ) k) := by
    rw [F_weighted_sum]
    exact ((hn.pow 2).mul hf).mono (by omega) |>.sub (by simpa using hn.mul hsum)
  have he : ∑ k ∈ range (p^s), (2*k+1:ℚ) = ((p^s:ℕ):ℚ)^2 := by
    have ht := sum_range_sub (fun k => (k:ℚ)^2) (p^s)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] at ht
    convert ht using 1
    apply sum_congr rfl
    intro k hk; ring
  have hrem : D p 2 (∑ k ∈ range (p^s), (2*k+1:ℚ)*(F (p^s:ℕ) k^3-3*F (p^s:ℕ) k+2)) := by
    apply D.sum
    intro k hk
    have hF := F_prime_power_mod (p := p) s k (mem_range.mp hk)
    have ha := ((D.nat (p := p) 2).mul (D.nat k)).add D.one
    have hx : D p 2 (F (p^s:ℕ) k^3-3*F (p^s:ℕ) k+2) := by
      have h3 := (D.pow hF 3).mono (by norm_num : (2:ℤ) ≤ 1*3)
      have h2 := (D.mul (D.nat (p := p) 3) (D.pow hF 2)).mono (by norm_num : (2:ℤ) ≤ 0+1*2)
      convert h3.add h2 using 1 <;> norm_num only [Nat.cast_ofNat] <;> ring
    simpa only [Nat.cast_ofNat, zero_add] using ha.mul hx
  have hbase : D p (min (s:ℤ) 2) (3 * ∑ k ∈ range (p^s), (2*k+1:ℚ)*F (p^s:ℕ) k -
      2 * ∑ k ∈ range (p^s), (2*k+1:ℚ)) := by
    rw [he]
    exact (((D.nat (p := p) 3).mul hw).mono (by omega)).sub
      (((D.nat (p := p) 2).mul (hn.pow 2)).mono (by omega))
  have ht := (hrem.mono (min_le_right _ _)).add hbase
  simp_rw [mul_add, mul_sub, mul_left_comm _ (3:ℚ)] at ht
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul] at ht
  convert ht using 1 <;> norm_num only [Nat.cast_ofNat] <;> ring

/-- The unit harmonic sum in one block. -/
def B (p l m : ℕ) : ℚ := H p (p*(l+1)) m - H p (p*l) m
lemma B_sum (l m : ℕ) : B p l m = ∑ j ∈ range (p-1), ((p*l+j+1:ℕ):ℚ)⁻¹^m := by
  rw [B, H_blocks, H_blocks, sum_range_succ, add_sub_cancel_left]
  rw [J, sum_filter]
  have he : ∀ j ∈ range p, (if ¬p∣j then ((p*l+j:ℕ):ℚ)⁻¹^m else 0) =
      if j=0 then 0 else ((p*l+j:ℕ):ℚ)⁻¹^m := by
    intro j hj
    by_cases hz : j=0
    · simp [hz]
    · simp only [if_neg hz, if_pos (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hz) (mem_range.mp hj))]
  rw [sum_congr rfl he]
  have hp' : p = (p-1)+1 := by have := hp.out.pos; omega
  rw [hp', sum_range_succ']
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_zero, if_true, add_zero,
    Nat.add_assoc, Nat.add_sub_cancel]

lemma block_unit (l j : ℕ) (hj : j < p-1) : ¬p∣p*l+j+1 := by
  rw [Nat.add_assoc, ← Nat.dvd_add_iff_right (dvd_mul_right p l)]
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)

lemma B_integral (l m : ℕ) : D p 0 (B p l m) := by
  rw [B_sum]
  apply D.sum
  intro j hj
  simpa using (D.inv_nat _ (block_unit l j (mem_range.mp hj))).pow m

lemma block_inverse_taylor (l j m d : ℕ) (hj : j < p-1) :
    C p d (((p*l+j+1:ℕ):ℚ)⁻¹^m)
      (∑ k ∈ range d, (-1:ℚ)^k * (Nat.choose (m+k-1) k:ℚ) * ((p:ℚ)*l)^k *
        ((j+1:ℕ):ℚ)⁻¹^(m+k)) := by
  have hx : D p 1 ((p:ℚ)*l) := by simpa using (D.prime (p := p)).mul (D.nat l)
  have ha : D p 0 ((j+1:ℕ):ℚ)⁻¹ := D.inv_small _ (by omega) (by omega)
  have ha0 : ((j+1:ℕ):ℚ) ≠ 0 := by positivity
  have ht := inverse_shift (p := p) 1 ((p:ℚ)*l) (j+1:ℕ) (by omega) hx ha ha0 m d
  convert ht using 1 <;> push_cast <;> ring

lemma B_taylor (l m d : ℕ) : C p d (B p l m)
    (∑ k ∈ range d, (-1:ℚ)^k * (Nat.choose (m+k-1) k:ℚ) * ((p:ℚ)*l)^k * H p p (m+k)) := by
  rw [B_sum]
  have ht := C.sum (range (p-1)) _ _ (fun j hj => block_inverse_taylor l j m d (mem_range.mp hj))
  convert ht using 1
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [H_prime_eq_h, h, pref, mul_sum]

lemma B_mod (l m : ℕ) : C p 1 (B p l m) (H p p m) := by
  have ht := B_taylor (p := p) l m 1
  simpa only [sum_range_succ, sum_range_zero, Nat.add_zero, Nat.choose_zero_right, Nat.cast_one,
    pow_zero, one_mul, mul_one, zero_add] using ht

lemma B_two_bound (l : ℕ) (hp3 : 3 ≤ p) : D p (1-eps p) (B p l 2) := by
  apply C.dvd_left ((B_mod l 2).mono (by have := eps_nonneg (p := p); omega))
  exact H_two_base hp3


lemma summation_parts (w E : ℕ → ℚ) (n : ℕ) :
    (∑ k ∈ range n, w k * (E (k+1)-E k)) = w n * E n - w 0 * E 0 -
      ∑ k ∈ range n, E (k+1) * (w (k+1)-w k) := by
  have he := sum_range_sub (fun k => w k * E k) n
  have ht : ∀ k, w (k+1)*E (k+1) - w k*E k =
      w k*(E (k+1)-E k) + E (k+1)*(w (k+1)-w k) := by intro k; ring
  simp_rw [ht] at he
  rw [sum_add_distrib] at he
  linear_combination he

def EH2 (p l : ℕ) : ℚ := H p (p*l) 2 - alpha p * ((p:ℚ)*l) - beta p * ((p:ℚ)*l)^3
lemma EH2_zero : EH2 p 0 = 0 := by simp [EH2, H, J]
lemma EH2_bound (l v : ℕ) (hl : p^v∣l) (hp3 : 3 ≤ p) : D p (v+4-eps p) (EH2 p l) := by
  have ht := H_two_expansion (p := p) l v hl hp3
  dsimp only [EH2, C] at *
  convert ht using 1 <;> ring

lemma F_square_step_bound (s k : ℕ) :
    D p ((s:ℤ)-padicValNat p (k+1)) (F (p^s:ℕ) (k+1)^2-F (p^s:ℕ) k^2) := by
  have hb := b_prime_power_bound (p := p) s (k+1) (by omega)
  have hf := (F_integral (p := p) (p^s) (k+1)).add (F_integral (p := p) (p^s) k)
  have ht := hb.mul hf
  rw [← F_step] at ht
  convert ht using 1 <;> ring

lemma weighted_EH2 (s : ℕ) (hp3 : 3 ≤ p) :
    D p (s+4-eps p) (∑ l ∈ range (p^s), F (p^s:ℕ) l^2*(EH2 p (l+1)-EH2 p l)) := by
  rw [summation_parts, EH2_zero, mul_zero, sub_zero]
  have hf0 : D p 0 (F (p^s:ℕ) (p^s)^2) := by simpa using (F_integral (p := p) (p^s) (p^s)).pow 2
  apply D.sub
  · simpa only [zero_add] using hf0.mul (EH2_bound (p^s) s dvd_rfl hp3)
  · apply D.sum
    intro k hk
    have ht := (EH2_bound (k+1) (padicValNat p (k+1)) pow_padicValNat_dvd hp3).mul (F_square_step_bound s k)
    convert ht using 1 <;> ring

lemma B_two_weighted (s : ℕ) (hp3 : 3 ≤ p) :
    C p (s+4-eps p) (∑ l ∈ range (p^s), F (p^s:ℕ) l^2 * B p l 2)
      (alpha p * p * M (p^s) 0 + beta p * (p:ℚ)^3 * (3*M (p^s) 2+3*M (p^s) 1+M (p^s) 0)) := by
  have ht := weighted_EH2 s hp3
  have he : ∀ l : ℕ, F (p^s:ℕ) l^2 * (EH2 p (l+1)-EH2 p l) =
      F (p^s:ℕ) l^2 * B p l 2 - alpha p * p * F (p^s:ℕ) l^2 -
      beta p * (p:ℚ)^3 * (3*(l:ℚ)^2*F (p^s:ℕ) l^2+3*(l:ℚ)*F (p^s:ℕ) l^2+F (p^s:ℕ) l^2) := by
    intro l
    simp only [EH2, B, Nat.cast_add, Nat.cast_one]
    ring
  simp_rw [he] at ht
  simp only [sum_sub_distrib, sum_add_distrib, mul_assoc, ← mul_sum] at ht
  dsimp only [C, M]
  simp only [pow_zero, one_mul, pow_one]
  convert ht using 1 <;> ring

lemma beta_moment_vanish (s : ℕ) (hs : 1 ≤ s) (hp3 : 3 ≤ p) (hgood : 7 ≤ p ∨ 2 ≤ s)
    (z : ℚ) (hz : D p s z) :
    D p (3*((s:ℤ)+1)+3) (3 * beta p * ((p:ℚ)^(s+1))^3 * (p:ℚ)^2 * z) := by
  have hb : D p (1-(s:ℤ)) (beta p) := by
    rcases hgood with hg | hg
    · exact (beta_bound_large hg).mono (by omega)
    · exact (beta_bound (p := p)).mono (by omega)
  have ht := ((((D.nat (p := p) 3).mul hb).mul ((D.prime_pow (s+1)).pow 3)).mul (D.prime_pow 2)).mul hz
  have ht' := ht.mono (by push_cast; omega : 3*((s:ℤ)+1)+3 ≤ 0+(1-s)+((s+1:ℕ):ℤ)*3+2+s)
  simpa only [Nat.cast_ofNat] using ht'

lemma unit_quadratic_contribution (s : ℕ) (hs : 1 ≤ s) (hp3 : 3 ≤ p) (hgood : 7 ≤ p ∨ 2 ≤ s) :
    C p (3*((s:ℤ)+1)+3) (3*((p:ℚ)^(s+1))^2 * ∑ l ∈ range (p^s), F (p^s:ℕ) l^2 * B p l 2)
      (3*alpha p*((p:ℚ)^(s+1))^2*p*M (p^s) 0) := by
  have hc := (three_bound (p := p)).mul ((D.prime_pow (s+1)).pow 2)
  have ht := C.mul_left (B_two_weighted s hp3) hc
  have ht' := ht.mono (by push_cast; omega : 3*((s:ℤ)+1)+3 ≤ s+4-eps p+(eps p+((s+1:ℕ):ℤ)*2))
  have hg : p ≠ 3 ∨ 2 ≤ s := by rcases hgood with h | h; exact Or.inl (by omega); exact Or.inr h
  have hv := beta_moment_vanish s hs hp3 hgood (V (p^s)) (V_bound s hs hp3 hg)
  have hv' : D p (3*((s:ℤ)+1)+3)
      (3*((p:ℚ)^(s+1))^2*beta p*(p:ℚ)^3*(3*M (p^s) 2+3*M (p^s) 1+M (p^s) 0)) := by
    have hn : ((p^s:ℕ):ℚ) ≠ 0 := by exact_mod_cast pow_ne_zero s hp.out.ne_zero
    unfold V at hv
    convert hv using 1
    simp only [pow_succ', Nat.cast_pow] at *
    field_simp [hn]
    <;> ring
  dsimp only [C]
  convert D.add ht' hv' using 1 <;> ring


lemma B_three_approx (l : ℕ) (hp3 : 3 ≤ p) :
    C p 3 (B p l 3) (-3*(p:ℚ)/2 * H p p 4 * (2*l+1:ℚ)) := by
  have ht := B_taylor (p := p) l 3 3
  norm_num only [sum_range_succ, sum_range_zero, Nat.choose, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, reduceAdd, reduceSub, reducePow, reduceMul,
    pow_zero, pow_one, zero_add, one_mul, mul_one, neg_one_sq] at ht
  have h3 := H_three_reflect (p := p) p 0 (by simp) hp3
  norm_num only [Nat.cast_zero, mul_zero, zero_add] at h3
  have h5 := H_prime_odd (p := p) 5 (by decide) hp3
  have hc := ((((D.nat (p := p) 6).mul (D.prime_pow 2)).mul ((D.nat l).pow 2)).mul h5)
  have hc' : D p 3 (6*(p:ℚ)^2*(l:ℚ)^2*H p p 5) := by simpa using hc
  dsimp only [C]
  convert (D.add ht h3).add hc' using 1 <;> ring

lemma B_three_weighted_vanish (s : ℕ) (hs : 1 ≤ s) (hp3 : 3 ≤ p) (hgood : 7 ≤ p ∨ 2 ≤ s) :
    D p 3 (∑ l ∈ range (p^s), F (p^s:ℕ) l^3 * B p l 3) := by
  have hsum := C.sum (range (p^s)) _ _ (fun l hl =>
    C.mul_left (B_three_approx l hp3) ((F_integral (p := p) (p^s) l).pow 3))
  simp only [zero_mul, add_zero] at hsum
  have hc : D p (3-min (s:ℤ) 2) (-3*(p:ℚ)/2 * H p p 4) := by
    have hi := D.inv_nat (p := p) 2 (not_dvd_two hp3)
    rcases hgood with hg | hg
    · have ht := ((((D.nat (p := p) 3).neg.mul D.prime).mul hi).mul
        (H_prime_small (p := p) 4 (by omega) (by omega)))
      simpa only [Nat.cast_ofNat, div_eq_mul_inv] using ht.mono (by omega : 3-min (s:ℤ) 2 ≤ 0+1+0+1)
    · have ht := ((((D.nat (p := p) 3).neg.mul D.prime).mul hi).mul (H_integral (p := p) p 4))
      simpa only [Nat.cast_ofNat, div_eq_mul_inv] using ht.mono (by omega : 3-min (s:ℤ) 2 ≤ 0+1+0+0)
  have ht := hc.mul (F_cube_weighted_bound (p := p) s hs)
  have ht' : D p 3 (∑ l ∈ range (p^s), F (p^s:ℕ) l^3 * (-3*(p:ℚ)/2*H p p 4*(2*l+1:ℚ))) := by
    simp only [mul_left_comm (F (p^s:ℕ) _^3), ← mul_sum]
    convert ht using 1
    · ring
    · congr 1
      apply sum_congr rfl
      intro l hl; ring
  exact hsum.dvd_left ht'


def B12 (p l : ℕ) : ℚ := ∑ j ∈ range (p-1), ((p*l+j+1:ℕ):ℚ)⁻¹^2 *
  ∑ i ∈ range j, ((p*l+i+1:ℕ):ℚ)⁻¹

def D4 (p : ℕ) : ℚ := h2 (p-1) 2 2 + 2*h2 (p-1) 1 3
def D5 (p : ℕ) : ℚ := h2 (p-1) 3 2 + 2*h2 (p-1) 2 3 + 3*h2 (p-1) 1 4

lemma B12_integral (l : ℕ) : D p 0 (B12 p l) := by
  apply D.sum
  intro j hj
  have hjp := mem_range.mp hj
  have h1 : D p 0 (((p*l+j+1:ℕ):ℚ)⁻¹^2) := by simpa using (D.inv_nat _ (block_unit l j hjp)).pow 2
  have h2 : D p 0 (∑ i ∈ range j, ((p*l+i+1:ℕ):ℚ)⁻¹) := by
    apply D.sum; intro i hi
    exact D.inv_nat _ (block_unit l i (by have := mem_range.mp hi; omega))
  simpa using h1.mul h2

lemma block_mixed_taylor (l i j : ℕ) (hi : i < p-1) (hj : j < p-1) :
    C p 3 (((p*l+i+1:ℕ):ℚ)⁻¹ * ((p*l+j+1:ℕ):ℚ)⁻¹^2)
      (((i+1:ℚ)⁻¹ * (j+1:ℚ)⁻¹^2) - (p:ℚ)*l *
        ((i+1:ℚ)⁻¹^2*(j+1:ℚ)⁻¹^2 + 2*(i+1:ℚ)⁻¹*(j+1:ℚ)⁻¹^3) +
        ((p:ℚ)*l)^2 * ((i+1:ℚ)⁻¹^3*(j+1:ℚ)⁻¹^2 +
          2*(i+1:ℚ)⁻¹^2*(j+1:ℚ)⁻¹^3 + 3*(i+1:ℚ)⁻¹*(j+1:ℚ)⁻¹^4)) := by
  have h1 := block_inverse_taylor (p := p) l i 1 3 hi
  have h2 := block_inverse_taylor (p := p) l j 2 3 hj
  norm_num [sum_range_succ, Nat.choose] at h1 h2
  simp only [← inv_pow] at h1 h2
  have hx : D p 1 ((p:ℚ)*l) := by simpa using D.prime.mul (D.nat (p := p) l)
  have hu : D p 0 (i+1:ℚ)⁻¹ := by simpa using D.inv_small (p := p) (i+1) (by omega) (by omega)
  have hv : D p 0 (j+1:ℚ)⁻¹ := by simpa using D.inv_small (p := p) (j+1) (by omega) (by omega)
  have hv0 : D p 0 (((p*l+j+1:ℕ):ℚ)⁻¹^2) := by simpa using (D.inv_nat _ (block_unit l j hj)).pow 2
  have hu0 := D.inv_nat (p := p) _ (block_unit l i hi)
  push_cast at hv0 hu0
  have h2int' := h2.symm.mono (by omega : (0:ℤ) ≤ 3) |>.dvd_left hv0
  have ht := C.mul h1 h2 hu0 h2int'
  have hcoef3 : D p 0 (-3*(i+1:ℚ)⁻¹^2*(j+1:ℚ)⁻¹^4 - 2*(i+1:ℚ)⁻¹^3*(j+1:ℚ)⁻¹^3) := by
    have ha := (((D.nat (p := p) 3).neg.mul (hu.pow 2)).mul (hv.pow 4))
    have hb := (((D.nat (p := p) 2).mul (hu.pow 3)).mul (hv.pow 3))
    simpa using ha.sub hb
  have hcoef4 : D p 0 (3*(i+1:ℚ)⁻¹^3*(j+1:ℚ)⁻¹^4) := by
    simpa using ((D.nat (p := p) 3).mul (hu.pow 3)).mul (hv.pow 4)
  have h3 : D p 3 (((p:ℚ)*l)^3 * (-3*(i+1:ℚ)⁻¹^2*(j+1:ℚ)⁻¹^4 - 2*(i+1:ℚ)⁻¹^3*(j+1:ℚ)⁻¹^3)) := by
    simpa using (hx.pow 3).mul hcoef3
  have h4 := ((hx.pow 4).mul hcoef4).mono (by norm_num : (3:ℤ) ≤ 1*4+0)
  dsimp only [C]
  convert (D.add ht h3).add h4 using 1
  push_cast
  ring

lemma B12_approx (l : ℕ) : C p 3 (B12 p l)
    (h2 (p-1) 1 2 - (p:ℚ)*l*D4 p + ((p:ℚ)*l)^2 * D5 p) := by
  have ht := C.sum (range (p-1)) _ _ (fun j hj =>
    C.sum (range j) _ _ (fun i hi => block_mixed_taylor l i j
      (by have := mem_range.mp hi; have := mem_range.mp hj; omega) (mem_range.mp hj)))
  dsimp only [C, B12, D4, D5, h2, h, pref] at *
  simp only [pow_one, Nat.cast_add, Nat.cast_one] at ht ⊢
  simp only [sum_add_distrib, sum_sub_distrib, mul_add, mul_sub, mul_assoc, ← mul_sum] at ht
  convert ht using 1
  congr 1
  · apply sum_congr rfl
    intro j hj
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi; push_cast; ring
  · simp only [mul_add, mul_sub, mul_assoc, ← mul_sum, ← sum_mul]
    simp_rw [mul_comm (∑ _ ∈ _, _) _]


lemma D4_integral : D p 0 (D4 p) := by
  have hp' : p-1 < p := by have := hp.out.pos; omega
  have ht := (h2_integral (p := p) (p-1) 2 2 hp').add
    (by simpa only [zero_add, Nat.cast_ofNat] using (D.nat (p := p) 2).mul (h2_integral (p-1) 1 3 hp'))
  exact ht
lemma D5_integral : D p 0 (D5 p) := by
  have hp' : p-1 < p := by have := hp.out.pos; omega
  have hc2 : D p 0 (2*h2 (p-1) 2 3) := by simpa using (D.nat (p := p) 2).mul (h2_integral (p-1) 2 3 hp')
  have h3 : D p 0 (3*h2 (p-1) 1 4) := by simpa using (D.nat (p := p) 3).mul (h2_integral (p-1) 1 4 hp')
  exact ((h2_integral (p-1) 3 2 hp').add hc2).add h3
lemma D4_bound_large (hp7 : 7 ≤ p) : D p 1 (D4 p) := by
  have h13 := (h2_13_31_mod hp7).1
  exact (h2_22_mod hp7).add (by simpa using (D.nat (p := p) 2).mul h13)

lemma B12_weighted (s : ℕ) (hs : 1 ≤ s) (hp3 : 3 ≤ p) (hgood : 7 ≤ p ∨ 2 ≤ s) :
    C p 3 (∑ l ∈ range (p^s), F (p^s:ℕ) l^2 * B12 p l) (h2 (p-1) 1 2 * M (p^s) 0) := by
  have ht := C.sum (range (p^s)) _ _ (fun l hl =>
    C.mul_left (B12_approx l) ((F_integral (p := p) (p^s) l).pow 2))
  simp only [zero_mul, add_zero] at ht
  have he : (∑ l ∈ range (p^s), F (p^s:ℕ) l^2 *
      (h2 (p-1) 1 2 - (p:ℚ)*l*D4 p + ((p:ℚ)*l)^2*D5 p)) =
      h2 (p-1) 1 2 * M (p^s) 0 - (p:ℚ)*D4 p*M (p^s) 1 + (p:ℚ)^2*D5 p*M (p^s) 2 := by
    simp only [M, pow_one, pow_zero, one_mul, mul_add, mul_sub, mul_sum]
    simp only [← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro l hl; ring
  rw [he] at ht
  have hc := eps_nonneg (p := p)
  have hD4 : D p (2-(s:ℤ)-eps p) (D4 p) := by
    rcases hgood with hg | hg
    · exact (D4_bound_large hg).mono (by omega)
    · exact (D4_integral (p := p)).mono (by omega)
  have h1 := (D.prime.mul hD4).mul (M_one_bound s hs hp3)
  have h1' : D p 3 ((p:ℚ)*D4 p*M (p^s) 1) := by convert h1 using 1 <;> ring
  have hg : p ≠ 3 ∨ 2 ≤ s := by rcases hgood with h | h; exact Or.inl (by omega); exact Or.inr h
  have h2 := ((D.prime_pow 2).mul (D5_integral (p := p))).mul (M_two_bound s hs hp3 hg)
  have h2' := h2.mono (by omega : (3:ℤ) ≤ 2+0+s)
  dsimp only [C]
  convert (D.sub ht h1').add h2' using 1 <;> ring

lemma H_one_block_low (l : ℕ) (hp3 : 3 ≤ p) :
    C p 2 (H p (p*l) 1) (-alpha p*(p:ℚ)^2*(l:ℚ)^2/2) := by
  have ht := H_one_expansion (p := p) l 0 (by simp) hp3
  have ht' := ht.mono (by have := eps_le_one (p := p); norm_num; omega : (2:ℤ) ≤ 2*(0:ℕ)+5-eps p)
  have hb := (((beta_bound (p := p)).mul (D.prime_pow 4)).mul ((D.nat l).pow 4)).div_nat 4 (not_dvd_four hp3)
  have hb' := hb.mono (by norm_num : (2:ℤ) ≤ -1+4+0*4)
  dsimp only [C]
  convert D.sub ht' hb' using 1 <;> norm_num only [Nat.cast_ofNat] <;> ring

lemma H1_B2_weighted (s : ℕ) (hs : 1 ≤ s) (hp3 : 3 ≤ p) (hgood : 7 ≤ p ∨ 2 ≤ s) :
    D p (3-eps p) (∑ l ∈ range (p^s), F (p^s:ℕ) l^2 * H p (p*l) 1 * B p l 2) := by
  by_cases hpz : p=3
  · have hs2 : 2 ≤ s := by rcases hgood with h | h <;> omega
    have heps : eps p = 1 := by simp [eps, hpz]
    rw [heps]; norm_num only [reduceSub]
    have hc : D p 1 (-alpha p*(p:ℚ)^2/2 * H p p 2) := by
      have ht := ((((alpha_bound hp3).neg.mul (D.prime_pow 2)).div_nat 2 (not_dvd_two hp3)).mul (H_integral (p := p) p 2))
      simpa only [heps, Nat.cast_ofNat] using ht
    have hg : p ≠ 3 ∨ 2 ≤ s := Or.inr hs2
    have hm := hc.mul (M_two_bound s hs hp3 hg)
    have hm' := hm.mono (by omega : (2:ℤ) ≤ 1+s)
    have hterm : ∀ l, C p 2 (F (p^s:ℕ) l^2 * H p (p*l) 1 * B p l 2)
        (-alpha p*(p:ℚ)^2/2 * H p p 2 * ((l:ℚ)^2 * F (p^s:ℕ) l^2)) := by
      intro l
      have hlow := H_one_block_low l hp3
      have h1 : D p 1 (-alpha p*(p:ℚ)^2*(l:ℚ)^2/2) := by
        have ht := (((alpha_bound hp3).neg.mul (D.prime_pow 2)).mul ((D.nat l).pow 2)).div_nat 2 (not_dvd_two hp3)
        simpa only [heps, Nat.cast_ofNat] using ht
      have ht1 := C.mul_right hlow (B_integral l 2)
      have ht2 := C.mul_left (B_mod l 2) h1
      have ht0 := D.add ht1 ht2
      have hf : D p 0 (F (p^s:ℕ) l^2) := by simpa using (F_integral (p := p) (p^s) l).pow 2
      have ht := D.mul hf ht0
      dsimp only [C]
      convert ht using 1 <;> ring
    have ht := C.sum (range (p^s)) _ _ (fun l hl => hterm l)
    simp only [← mul_sum] at ht
    exact ht.dvd_left hm'
  · have heps : eps p = 0 := by simp [eps, hpz]
    rw [heps]; norm_num only [sub_zero]
    apply D.sum
    intro l hl
    have hf := (F_integral (p := p) (p^s) l).pow 2
    have h1 := H_one_bound_general (p*l) 0 (by simp) hp3
    have h2 := B_two_bound l hp3
    have ht := (hf.mul h1).mul h2
    simpa only [heps, Nat.cast_zero, zero_mul, zero_add, sub_zero] using ht


lemma product_square_approx {ι : Type*} (I : Finset ι) (f : ι → ℚ)
    (r : ℤ) (hr : 0 ≤ r) (hf : ∀ i ∈ I, D p r (f i)) :
    C p (3*r) ((∏ i ∈ I, (1+f i))^2)
      (1+2*(∑ i ∈ I, f i)+2*(∑ i ∈ I, f i)^2-(∑ i ∈ I, f i^2)) := by
  have hA := D.sum I f hf
  have hE := E_bound I f r hf 2
  have hp0 := D.prod I (fun i => 1+f i) (fun i hi => D.one.add ((hf i hi).mono hr))
  have ht := prod_approx I f r hr hf 3
  simp only [sum_range_succ, sum_range_zero, E_zero, E_one, zero_add] at ht
  have happrox0 : D p 0 (1+(∑ i ∈ I, f i)+E I f 2) :=
    (D.one.add (hA.mono hr)).add (hE.mono (by omega))
  have hsq := C.pow ht hp0 happrox0 2
  have h3 := (((D.nat (p := p) 2).mul hA).mul hE).mono (by omega : 3*r ≤ 0+r+r*2)
  have h4 := (hE.pow 2).mono (by omega : 3*r ≤ r*2*2)
  dsimp only [C]
  have hsq' := hsq.mono (by omega : 3*r ≤ r*3)
  have hd := (D.add hsq' h3).add h4
  convert hd using 1
  norm_num only [Nat.cast_ofNat]
  linear_combination E_two I f

lemma product_cube_approx {ι : Type*} (I : Finset ι) (f : ι → ℚ)
    (r : ℤ) (hr : 0 ≤ r) (hf : ∀ i ∈ I, D p r (f i)) :
    C p (2*r) ((∏ i ∈ I, (1+f i))^3) (1+3*(∑ i ∈ I, f i)) := by
  have hA := D.sum I f hf
  have hp0 := D.prod I (fun i => 1+f i) (fun i hi => D.one.add ((hf i hi).mono hr))
  have ht := prod_approx_one I f r hr hf
  have hcube := C.pow ht hp0 (D.one.add (hA.mono hr)) 3
  have h2 := ((D.nat (p := p) 3).mul (hA.pow 2)).mono (by omega : 2*r ≤ 0+r*2)
  have h3 := (hA.pow 3).mono (by omega : 2*r ≤ r*3)
  dsimp only [C]
  convert (D.add hcube h2).add h3 using 1 <;> norm_num only [Nat.cast_ofNat] <;> ring

lemma Q_square_approx (r L : ℕ) : C p (3*(r:ℤ)) (Q p (p^r) L^2)
    (1+2*(p:ℚ)^r*H p L 1+((p:ℚ)^r)^2*(2*H p L 1^2-H p L 2)) := by
  have ht := product_square_approx (p := p) (J p L) (fun i => (p:ℚ)^r/i) r (by omega)
    (fun i hi => (D.prime_pow r).div_nat i (mem_filter.mp hi).2)
  simp only [Q, Nat.cast_pow, div_eq_mul_inv, mul_pow, ← mul_sum, H] at ht ⊢
  convert ht using 1 <;> ring

lemma Q_cube_approx (r L : ℕ) : C p (2*(r:ℤ)) (Q p (p^r) L^3)
    (1+3*(p:ℚ)^r*H p L 1) := by
  have ht := product_cube_approx (p := p) (J p L) (fun i => (p:ℚ)^r/i) r (by omega)
    (fun i hi => (D.prime_pow r).div_nat i (mem_filter.mp hi).2)
  simp only [Q, Nat.cast_pow, div_eq_mul_inv, ← mul_sum, H, pow_one] at ht ⊢
  convert ht using 1 <;> ring

lemma H_succ (k m : ℕ) : H p (k+1) m = H p k m + if p∣k then 0 else (k:ℚ)⁻¹^m := by
  simp only [H, J, sum_filter, sum_range_succ]
  split_ifs <;> simp_all
lemma Q_succ (n k : ℕ) : Q p n (k+1) = Q p n k * if p∣k then 1 else (1+(n:ℚ)/k) := by
  simp only [Q, J, prod_filter, prod_range_succ]
  split_ifs <;> simp_all

lemma H_prefix_split (l j m : ℕ) (hj : j < p) :
    H p (p*l+j+1) m = H p (p*l) m + ∑ i ∈ range j, ((p*l+i+1:ℕ):ℚ)⁻¹^m := by
  induction j with
  | zero => simp [H_succ]
  | succ j ih =>
    have hj' : j < p-1 := by omega
    rw [show p*l+(j+1)+1 = (p*l+j+1)+1 by omega, H_succ,
      if_neg (block_unit l j hj'), ih (by omega), sum_range_succ, add_assoc]

lemma G_unit_split (n l j : ℕ) (hj : j < p) :
    G (p*n:ℕ) (p*l+j+1) = F n l * Q p (p*n) (p*l+j+1) := by
  induction j with
  | zero =>
    simp only [Nat.add_zero, Q_succ, dvd_mul_right, if_true, mul_one]
    rw [G_succ, G_split]
    have he : (1+((p*n:ℕ):ℚ)/(p*l:ℕ)) = 1+(n:ℚ)/l := by
      push_cast; rw [mul_div_mul_left _ _ (p_ne (p := p))]
    rw [he, mul_right_comm, ← G_succ, G_eq_F]
  | succ j ih =>
    rw [show p*l+(j+1)+1 = (p*l+j+1)+1 by omega, G_succ, Q_succ,
      if_neg (block_unit l j (by omega)), ih (by omega), mul_assoc]

lemma b_unit_split (n l j : ℕ) (hj : j < p-1) :
    b (p*n) (p*l+j+1) = ((p*n:ℕ):ℚ)/(p*l+j+1:ℕ) * F n l * Q p (p*n) (p*l+j+1) := by
  have hk : 0 < p*l+j+1 := by omega
  rw [b_pos _ _ hk, ← G_pos _ _ hk, G_unit_split n l j (by omega), mul_assoc]

lemma H_prefix_mod (l j m : ℕ) (hj : j < p) (hH : D p 1 (H p (p*l) m)) :
    C p 1 (H p (p*l+j+1) m) (h j m) := by
  rw [H_prefix_split l j m hj]
  have ht := C.sum (range j) _ _ (fun i hi => block_inverse_taylor (p := p) l i m 1
    (by have := mem_range.mp hi; omega))
  simp only [sum_range_succ, sum_range_zero, pow_zero, Nat.add_zero, Nat.choose_zero_right,
    Nat.cast_one, one_mul, mul_one, zero_add] at ht
  dsimp only [C, h, pref] at *
  convert D.add hH ht using 1 <;> ring


lemma block_inverse_mod (l j m : ℕ) (hj : j < p-1) :
    C p 1 (((p*l+j+1:ℕ):ℚ)⁻¹^m) (((j+1:ℕ):ℚ)⁻¹^m) := by
  have ht := block_inverse_taylor (p := p) l j m 1 hj
  simpa only [sum_range_succ, sum_range_zero, pow_zero, Nat.add_zero, Nat.choose_zero_right,
    Nat.cast_one, one_mul, mul_one, zero_add] using ht

def K4 (p l : ℕ) : ℚ := ∑ j ∈ range (p-1), ((p*l+j+1:ℕ):ℚ)⁻¹^2 *
  (2 * H p (p*l+j+1) 1^2 - H p (p*l+j+1) 2)
def K13 (p l : ℕ) : ℚ := ∑ j ∈ range (p-1), ((p*l+j+1:ℕ):ℚ)⁻¹^3 * H p (p*l+j+1) 1

lemma K4_integral (l : ℕ) : D p 0 (K4 p l) := by
  apply D.sum
  intro j hj
  have hz : D p 0 (((p*l+j+1:ℕ):ℚ)⁻¹^2) := by simpa using (D.inv_nat _ (block_unit l j (mem_range.mp hj))).pow 2
  have hh : D p 0 (2*H p (p*l+j+1) 1^2-H p (p*l+j+1) 2) := by
    have ht := (D.nat (p := p) 2).mul ((H_integral (p := p) (p*l+j+1) 1).pow 2)
    simpa using ht.sub (H_integral (p := p) (p*l+j+1) 2)
  simpa using hz.mul hh
lemma K13_integral (l : ℕ) : D p 0 (K13 p l) := by
  apply D.sum
  intro j hj
  simpa using ((D.inv_nat _ (block_unit l j (mem_range.mp hj))).pow 3).mul (H_integral (p := p) (p*l+j+1) 1)

lemma K4_base (n : ℕ) :
    (∑ j ∈ range n, ((j+1:ℕ):ℚ)⁻¹^2 * (2*h j 1^2-h j 2)) = 4*h3 n 1 1 2+h2 n 2 2 := by
  change (∑ j ∈ range n, ((j+1:ℕ):ℚ)⁻¹^2 * (2*h j 1^2-h j 2)) =
    4*(∑ j ∈ range n, ((j+1:ℕ):ℚ)⁻¹^2*h2 j 1 1) +
      (∑ j ∈ range n, ((j+1:ℕ):ℚ)⁻¹^2*h j 2)
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  have ht := h2_shuffle j 1 1
  norm_num only [reduceAdd] at ht
  change ((j+1:ℕ):ℚ)⁻¹^2 * (2*h j 1^2-h j 2) =
    4*(((j+1:ℕ):ℚ)⁻¹^2 * h2 j 1 1) + ((j+1:ℕ):ℚ)⁻¹^2 * h j 2
  linear_combination -2*((j+1:ℕ):ℚ)⁻¹^2 * ht

lemma H_prefix_small_mod (l j m : ℕ) (hj : j < p) (hm : m=1 ∨ m=2) (hp7 : 7 ≤ p) :
    C p 1 (H p (p*l+j+1) m) (h j m) := by
  apply H_prefix_mod l j m hj
  have heps : eps p = 0 := by simp [eps, show p≠3 by omega]
  rcases hm with rfl | rfl
  · have ht := H_one_bound_general (p := p) (p*l) 0 (by simp) (by omega)
    exact ht.mono (by rw [heps]; norm_num)
  · have ht := H_two_bound_general (p := p) (p*l) 0 (by simp) (by omega)
    simpa only [heps, Nat.cast_zero, zero_add, sub_zero] using ht

lemma K4_bound (l : ℕ) (hp7 : 7 ≤ p) : D p 1 (K4 p l) := by
  have hterm : ∀ j ∈ range (p-1), C p 1
      (((p*l+j+1:ℕ):ℚ)⁻¹^2 * (2*H p (p*l+j+1) 1^2-H p (p*l+j+1) 2))
      (((j+1:ℕ):ℚ)⁻¹^2 * (2*h j 1^2-h j 2)) := by
    intro j hj
    have hj' : j < p := by have := mem_range.mp hj; omega
    have h1 := H_prefix_small_mod l j 1 hj' (Or.inl rfl) hp7
    have h2 := H_prefix_small_mod l j 2 hj' (Or.inr rfl) hp7
    have h1sq := C.pow h1 (H_integral _ _) (h_integral _ _ hj') 2
    have h1sq2 := C.mul_left h1sq (D.nat (p := p) 2)
    simp only [add_zero, Nat.cast_ofNat] at h1sq2
    have hp := C.sub h1sq2 h2
    have hz : D p 0 (((p*l+j+1:ℕ):ℚ)⁻¹^2) := by simpa using (D.inv_nat _ (block_unit l j (mem_range.mp hj))).pow 2
    have hh : D p 0 (2*h j 1^2-h j 2) := by
      have ht := (D.nat (p := p) 2).mul ((h_integral (p := p) j 1 hj').pow 2)
      simpa using ht.sub (h_integral (p := p) j 2 hj')
    exact C.mul (block_inverse_mod l j 2 (mem_range.mp hj)) hp hz hh
  have ht := C.sum (range (p-1)) _ _ hterm
  rw [K4_base] at ht
  apply ht.dvd_left
  have hh : D p 1 (4*h3 (p-1) 1 1 2) := by simpa using (D.nat (p := p) 4).mul (h3_112_mod hp7)
  exact hh.add (h2_22_mod hp7)

lemma K13_bound (l : ℕ) (hp7 : 7 ≤ p) : D p 1 (K13 p l) := by
  have hterm : ∀ j ∈ range (p-1), C p 1
      (((p*l+j+1:ℕ):ℚ)⁻¹^3 * H p (p*l+j+1) 1) (((j+1:ℕ):ℚ)⁻¹^3 * h j 1) := by
    intro j hj
    have hj' : j < p := by have := mem_range.mp hj; omega
    have hh := H_prefix_small_mod l j 1 hj' (Or.inl rfl) hp7
    have hz : D p 0 (((p*l+j+1:ℕ):ℚ)⁻¹^3) := by simpa using (D.inv_nat _ (block_unit l j (mem_range.mp hj))).pow 3
    exact C.mul (block_inverse_mod l j 3 (mem_range.mp hj)) hh hz (h_integral _ _ hj')
  have ht := C.sum (range (p-1)) _ _ hterm
  exact ht.dvd_left (h2_13_31_mod hp7).1

lemma fourth_block_vanish (s l : ℕ) (hs : 1 ≤ s) (hgood : 7 ≤ p ∨ 2 ≤ s) :
    D p (3*((s:ℤ)+1)+3) (((p:ℚ)^(s+1))^4 *
      (3*F (p^s:ℕ) l^2*K4 p l + 6*F (p^s:ℕ) l^3*K13 p l)) := by
  have hf := F_integral (p := p) (p^s) l
  have hk4 : D p (max 0 (2-(s:ℤ))) (K4 p l) := by
    rcases hgood with hg | hg
    · exact (K4_bound l hg).mono (by omega)
    · exact (K4_integral l).mono (by omega)
  have hk13 : D p (max 0 (2-(s:ℤ))) (K13 p l) := by
    rcases hgood with hg | hg
    · exact (K13_bound l hg).mono (by omega)
    · exact (K13_integral l).mono (by omega)
  have h4 := ((D.nat (p := p) 3).mul (hf.pow 2)).mul hk4
  have h13 := ((D.nat (p := p) 6).mul (hf.pow 3)).mul hk13
  simp only [zero_mul, zero_add, Nat.cast_ofNat] at h4 h13
  have ht := ((D.prime_pow (s+1)).pow 4).mul (h4.add h13)
  exact ht.mono (by push_cast; omega)


lemma unit_term_approx (s l j : ℕ) (hj : j < p-1) :
    C p (5*((s:ℤ)+1)) (ff (b (p^(s+1)) (p*l+j+1)))
      (3*((p:ℚ)^(s+1))^2 * F (p^s:ℕ) l^2 * ((p*l+j+1:ℕ):ℚ)⁻¹^2 +
       6*((p:ℚ)^(s+1))^3 * F (p^s:ℕ) l^2 * ((p*l+j+1:ℕ):ℚ)⁻¹^2 * H p (p*l+j+1) 1 +
       2*((p:ℚ)^(s+1))^3 * F (p^s:ℕ) l^3 * ((p*l+j+1:ℕ):ℚ)⁻¹^3 +
       ((p:ℚ)^(s+1))^4 *
         (3*F (p^s:ℕ) l^2 * ((p*l+j+1:ℕ):ℚ)⁻¹^2 * (2*H p (p*l+j+1) 1^2-H p (p*l+j+1) 2) +
          6*F (p^s:ℕ) l^3 * ((p*l+j+1:ℕ):ℚ)⁻¹^3 * H p (p*l+j+1) 1)) := by
  have hn := D.prime_pow (p := p) (s+1)
  have hf := F_integral (p := p) (p^s) l
  have hz := D.inv_nat (p := p) _ (block_unit l j hj)
  have hc2 : D p (2*((s:ℤ)+1)) (3*((p:ℚ)^(s+1))^2 * F (p^s:ℕ) l^2 * ((p*l+j+1:ℕ):ℚ)⁻¹^2) := by
    have ht := (((D.nat (p := p) 3).mul (hn.pow 2)).mul (hf.pow 2)).mul (hz.pow 2)
    convert ht using 1 <;> push_cast <;> ring
  have hc3 : D p (3*((s:ℤ)+1)) (2*((p:ℚ)^(s+1))^3 * F (p^s:ℕ) l^3 * ((p*l+j+1:ℕ):ℚ)⁻¹^3) := by
    have ht := (((D.nat (p := p) 2).mul (hn.pow 3)).mul (hf.pow 3)).mul (hz.pow 3)
    convert ht using 1 <;> push_cast <;> ring
  have h2 := C.mul_left (Q_square_approx (p := p) (s+1) (p*l+j+1)) hc2
  have h3 := C.mul_left (Q_cube_approx (p := p) (s+1) (p*l+j+1)) hc3
  have h2' := h2.mono (by push_cast; omega : 5*((s:ℤ)+1) ≤ 3*((s+1:ℕ):ℤ)+2*((s:ℤ)+1))
  have h3' := h3.mono (by push_cast; omega : 5*((s:ℤ)+1) ≤ 2*((s+1:ℕ):ℤ)+3*((s:ℤ)+1))
  have ht := C.add h2' h3'
  have he : b (p^(s+1)) (p*l+j+1) = (p:ℚ)^(s+1) * ((p*l+j+1:ℕ):ℚ)⁻¹ *
      F (p^s:ℕ) l * Q p (p^(s+1)) (p*l+j+1) := by
    have hh := b_unit_split (p := p) (p^s) l j hj
    simpa only [← pow_succ', Nat.cast_pow, div_eq_mul_inv] using hh
  rw [he]
  dsimp only [C, ff] at ht ⊢
  convert ht using 1 <;> ring

lemma unit_block_approx (s l : ℕ) (hs : 1 ≤ s) (hgood : 7 ≤ p ∨ 2 ≤ s) :
    C p (3*((s:ℤ)+1)+3) (∑ j ∈ range (p-1), ff (b (p^(s+1)) (p*l+j+1)))
      (3*((p:ℚ)^(s+1))^2 * F (p^s:ℕ) l^2 * B p l 2 +
       6*((p:ℚ)^(s+1))^3 * F (p^s:ℕ) l^2 * H p (p*l) 1 * B p l 2 +
       6*((p:ℚ)^(s+1))^3 * F (p^s:ℕ) l^2 * B12 p l +
       2*((p:ℚ)^(s+1))^3 * F (p^s:ℕ) l^3 * B p l 3) := by
  have ht := C.sum (range (p-1)) _ _ (fun j hj => unit_term_approx s l j (mem_range.mp hj))
  have he : (∑ j ∈ range (p-1), ((p*l+j+1:ℕ):ℚ)⁻¹^2 * H p (p*l+j+1) 1) =
      H p (p*l) 1 * B p l 2 + B12 p l := by
    have hh : ∀ j ∈ range (p-1), ((p*l+j+1:ℕ):ℚ)⁻¹^2 * H p (p*l+j+1) 1 =
        H p (p*l) 1 * ((p*l+j+1:ℕ):ℚ)⁻¹^2 +
          ((p*l+j+1:ℕ):ℚ)⁻¹^2 * ∑ i ∈ range j, ((p*l+i+1:ℕ):ℚ)⁻¹ := by
      intro j hj
      rw [H_prefix_split l j 1 (by have := mem_range.mp hj; omega)]
      simp only [pow_one]; ring
    rw [sum_congr rfl hh, sum_add_distrib, ← mul_sum, ← B_sum]
    rfl
  have hsum : (∑ j ∈ range (p-1),
      (3*((p:ℚ)^(s+1))^2 * F (p^s:ℕ) l^2 * ((p*l+j+1:ℕ):ℚ)⁻¹^2 +
       6*((p:ℚ)^(s+1))^3 * F (p^s:ℕ) l^2 * ((p*l+j+1:ℕ):ℚ)⁻¹^2 * H p (p*l+j+1) 1 +
       2*((p:ℚ)^(s+1))^3 * F (p^s:ℕ) l^3 * ((p*l+j+1:ℕ):ℚ)⁻¹^3 +
       ((p:ℚ)^(s+1))^4 *
         (3*F (p^s:ℕ) l^2 * ((p*l+j+1:ℕ):ℚ)⁻¹^2 * (2*H p (p*l+j+1) 1^2-H p (p*l+j+1) 2) +
          6*F (p^s:ℕ) l^3 * ((p*l+j+1:ℕ):ℚ)⁻¹^3 * H p (p*l+j+1) 1))) =
       3*((p:ℚ)^(s+1))^2 * F (p^s:ℕ) l^2 * B p l 2 +
       6*((p:ℚ)^(s+1))^3 * F (p^s:ℕ) l^2 * (H p (p*l) 1 * B p l 2 + B12 p l) +
       2*((p:ℚ)^(s+1))^3 * F (p^s:ℕ) l^3 * B p l 3 +
       ((p:ℚ)^(s+1))^4 * (3*F (p^s:ℕ) l^2*K4 p l+6*F (p^s:ℕ) l^3*K13 p l) := by
    simp only [sum_add_distrib, mul_assoc, ← mul_sum]
    simp only [← B_sum, he, K4, K13, mul_assoc]
  rw [hsum] at ht
  have ht' := ht.mono (by omega : 3*((s:ℤ)+1)+3 ≤ 5*((s:ℤ)+1))
  dsimp only [C]
  convert D.add ht' (fourth_block_vanish s l hs hgood) using 1 <;> ring


lemma units_contribution (s : ℕ) (hs : 1 ≤ s) (hp3 : 3 ≤ p) (hgood : 7 ≤ p ∨ 2 ≤ s) :
    C p (3*((s:ℤ)+1)+3)
      (∑ l ∈ range (p^s), ∑ j ∈ range (p-1), ff (b (p^(s+1)) (p*l+j+1)))
      (3*alpha p*((p:ℚ)^(s+1))^2*p*M (p^s) 0 +
        6*((p:ℚ)^(s+1))^3*h2 (p-1) 1 2*M (p^s) 0) := by
  have ht := C.sum (range (p^s)) _ _ (fun l hl => unit_block_approx s l hs hgood)
  simp only [sum_add_distrib, mul_assoc, ← mul_sum] at ht
  have hq := unit_quadratic_contribution s hs hp3 hgood
  have h6 : D p (eps p) (6:ℚ) := by
    have ht := (D.nat (p := p) 2).mul (three_bound (p := p))
    norm_num only [Nat.cast_ofNat, reduceMul, zero_add] at ht
    exact ht
  have hn := (D.prime_pow (p := p) (s+1)).pow 3
  have hcross := (h6.mul hn).mul (H1_B2_weighted s hs hp3 hgood)
  have hcross' : D p (3*((s:ℤ)+1)+3)
      (6*((p:ℚ)^(s+1))^3*∑ l ∈ range (p^s), F (p^s:ℕ) l^2*H p (p*l) 1*B p l 2) := by
    convert hcross using 1 <;> push_cast <;> ring
  have hm := C.mul_left (B12_weighted s hs hp3 hgood) ((D.nat (p := p) 6).mul hn)
  have hm' := hm.mono (by push_cast; omega : 3*((s:ℤ)+1)+3 ≤ 3+(0+((s+1:ℕ):ℤ)*3))
  norm_num only [Nat.cast_ofNat] at hm'
  have hc := ((D.nat (p := p) 2).mul hn).mul (B_three_weighted_vanish s hs hp3 hgood)
  have hc' : D p (3*((s:ℤ)+1)+3)
      (2*((p:ℚ)^(s+1))^3*∑ l ∈ range (p^s), F (p^s:ℕ) l^3*B p l 3) := by
    convert hc using 1 <;> push_cast <;> ring
  have hd := ((((D.add ht hq).add hm').add hcross').add hc')
  simp only [mul_assoc] at hd
  dsimp only [C]
  convert hd using 1 <;> ring

lemma sum_prime_blocks (f : ℕ → ℚ) (t : ℕ) :
    (∑ k ∈ range (p*t+1), f k) = (∑ l ∈ range (t+1), f (p*l)) +
      ∑ l ∈ range t, ∑ j ∈ range (p-1), f (p*l+j+1) := by
  rw [sum_range_succ, Nat.mul_comm p t, sum_blocks]
  have he : ∀ l, (∑ j ∈ range p, f (l*p+j)) = f (p*l)+∑ j ∈ range (p-1), f (p*l+j+1) := by
    intro l
    have hp' : p = (p-1)+1 := by have := hp.out.pos; omega
    conv_lhs => arg 1; rw [hp']
    rw [sum_range_succ']
    simp only [Nat.add_zero, Nat.mul_comm l p, Nat.add_assoc]
    ring
  simp_rw [he]
  rw [sum_add_distrib, sum_range_succ]
  simp only [Nat.mul_comm t p]
  ring

lemma aQ_sum (n : ℕ) : aQ n = ∑ k ∈ range (n+1), ff (b n k) := by
  simp only [aQ, S, ff, sum_add_distrib, ← mul_sum]

lemma prime_power_congruence (s : ℕ) (hs : 1 ≤ s) (hp3 : 3 ≤ p) (hgood : 7 ≤ p ∨ 2 ≤ s) :
    C p (3*((s:ℤ)+1)+3) (aQ (p^(s+1))) (aQ (p^s)) := by
  have hm := multiples_contribution s hs hp3 hgood
  have hu := units_contribution s hs hp3 hgood
  have hc := final_cancellation s hs hp3 hgood
  have hn := (D.prime_pow (p := p) (s+1)).pow 3
  have hlast := hn.mul hc
  have hlast' := hlast.mono (by push_cast; omega : 3*((s:ℤ)+1)+3 ≤ ((s+1:ℕ):ℤ)*3+3)
  have he : aQ (p^(s+1))-aQ (p^s) =
      (∑ l ∈ range (p^s+1), (ff (b (p^(s+1)) (p*l))-ff (b (p^s) l))) +
        ∑ l ∈ range (p^s), ∑ j ∈ range (p-1), ff (b (p^(s+1)) (p*l+j+1)) := by
    rw [aQ_sum, aQ_sum]
    have ht := sum_prime_blocks (p := p) (fun k => ff (b (p^(s+1)) k)) (p^s)
    rw [← pow_succ'] at ht
    rw [ht, sum_sub_distrib]
    ring
  dsimp only [C]
  rw [he]
  have hd := (D.add hm hu).add hlast'
  have hn0 : (p:ℚ)^s ≠ 0 := pow_ne_zero _ p_ne
  convert hd using 1
  simp only [Nat.cast_pow, pow_succ']
  field_simp [hn0]
  <;> ring

end A357565Proof

namespace A357565Proof
variable {p : ℕ} [hp : Fact p.Prime]

lemma aQ_eq_cast (n : ℕ) : aQ n = (A357565 n : ℚ) := by
  simp only [aQ_sum, A357565, ff, b, Nat.cast_sum, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat]

lemma natural_congruence (r : ℕ) (hr : 2 ≤ r) (hp3 : 3 ≤ p)
    (hgood : 7 ≤ p ∨ 3 ≤ r) :
    A357565 (p^r) ≡ A357565 (p^(r-1)) [MOD (p^(3*r+3))] := by
  have hs : 1 ≤ r-1 := by omega
  have hg : 7 ≤ p ∨ 2 ≤ r-1 := by omega
  have hd := prime_power_congruence (p := p) (r-1) hs hp3 hg
  have hr' : r-1+1 = r := by omega
  have he : 3*(((r-1:ℕ):ℤ)+1)+3 = ((3*r+3:ℕ):ℤ) := by omega
  rw [he, hr', aQ_eq_cast, aQ_eq_cast] at hd
  apply Nat.ModEq.symm
  rw [Nat.modEq_iff_dvd]
  apply D.to_dvd (p := p) (n := 3*r+3)
  simpa only [Int.cast_sub, Int.cast_natCast] using hd

end A357565Proof

-- Formalizing Conjecture 2
/--
Conjecture 2 for A357565: $a(p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$ for $r \ge 2$ and all primes $p \ge 3$.
-/
theorem A357565_conjecture_2 (p r : ℕ) (hp : Nat.Prime p) (h_pge3 : p ≥ 3) (hr : r ≥ 2) :
    (A357565 (p ^ r)) ≡ (A357565 (p ^ (r - 1))) [MOD (p ^ (3 * r + 3))] := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hr2 : r = 2
  · subst r
    by_cases hp3 : p = 3
    · subst p
      norm_num [A357565, Nat.ModEq, Finset.sum_range_succ,
        Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
    by_cases hp5 : p = 5
    · subst p
      norm_num [A357565, Nat.ModEq, Finset.sum_range_succ,
        Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
    have hp7 : 7 ≤ p := by
      by_contra! hn
      interval_cases p <;> norm_num at *
      all_goals norm_num [Nat.prime_def_lt] at hp
    exact A357565Proof.natural_congruence 2 (by omega) h_pge3 (Or.inl hp7)
  · exact A357565Proof.natural_congruence r hr h_pge3 (Or.inr (by omega))

theorem A357565_conjecture_2.disproof : ¬ (type_of% @A357565_conjecture_2) := sorry
