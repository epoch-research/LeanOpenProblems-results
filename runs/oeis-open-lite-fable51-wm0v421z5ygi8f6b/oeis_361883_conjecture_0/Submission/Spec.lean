import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The sequence $a(n)$ defined by
$$a(n) = \frac{1}{n} \sum_{k = 0}^n (n+2k) \binom{n+k-1}{k}^3$$
for $n \ge 1$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- Calculate the numerator sum S in ℕ
    -- We use binomial(n+k-1, n-1) which is equal to binomial(n+k-1, k)
    -- This makes the dependency on 'n - 1' explicit for the lower index.
    let S : ℕ := Finset.sum (range (n + 1)) fun k =>
      (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3

    -- Division is exact since a(n) is an integer sequence.
    S / n

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Sc

/-- `D p e x` : the rational `x` is divisible by `p^e` in the `p`-adic sense. -/
def D (p e : ℕ) (x : ℚ) : Prop := padicNorm p x ≤ (p : ℚ) ^ (-(e : ℤ))

variable {p : ℕ} [hp : Fact p.Prime]

lemma p_pos : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
lemma p_ne_zero : (p : ℚ) ≠ 0 := (p_pos (p := p)).ne'
lemma one_le_p : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
lemma one_lt_p : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt

lemma zpow_neg_nonneg (e : ℕ) : (0 : ℚ) ≤ (p : ℚ) ^ (-(e : ℤ)) :=
  zpow_nonneg (p_pos (p := p)).le _

lemma D.mono {e e' : ℕ} {x : ℚ} (h : e' ≤ e) (hx : D p e x) : D p e' x := by
  unfold D at *
  refine hx.trans ?_
  apply zpow_le_zpow_right₀ (one_le_p (p := p))
  omega

lemma D.add {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p e y) : D p e (x + y) := by
  unfold D at *
  exact padicNorm.nonarchimedean.trans (max_le hx hy)

lemma D.neg {e : ℕ} {x : ℚ} (hx : D p e x) : D p e (-x) := by
  unfold D at *
  rwa [padicNorm.neg]

lemma D.sub {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p e y) : D p e (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

lemma D.sum {e : ℕ} {ι : Type*} {s : Finset ι} {f : ι → ℚ}
    (h : ∀ i ∈ s, D p e (f i)) : D p e (∑ i ∈ s, f i) := by
  unfold D at *
  exact padicNorm.sum_le' h (zpow_neg_nonneg e)

lemma D.mul {a b : ℕ} {x y : ℚ} (hx : D p a x) (hy : D p b y) : D p (a + b) (x * y) := by
  unfold D at *
  rw [padicNorm.mul]
  have : (p : ℚ) ^ (-((a + b : ℕ) : ℤ)) = (p : ℚ) ^ (-(a : ℤ)) * (p : ℚ) ^ (-(b : ℤ)) := by
    rw [← zpow_add₀ (p_ne_zero (p := p))]
    congr 1
    push_cast
    ring
  rw [this]
  exact mul_le_mul hx hy (padicNorm.nonneg _) (zpow_neg_nonneg a)

lemma D.mul_left {a : ℕ} {z x : ℚ} (hz : D p 0 z) (hx : D p a x) : D p a (z * x) := by
  have := hz.mul hx
  simpa using this

lemma D.mul_right {a : ℕ} {z x : ℚ} (hx : D p a x) (hz : D p 0 z) : D p a (x * z) := by
  have := hx.mul hz
  simpa using this

lemma D.pow {a : ℕ} {x : ℚ} (hx : D p a x) (n : ℕ) : D p (n * a) (x ^ n) := by
  induction n with
  | zero =>
    unfold D; simp
  | succ n ih =>
    rw [pow_succ, add_mul, one_mul]
    exact ih.mul hx

lemma D.pow0 {x : ℚ} (hx : D p 0 x) (n : ℕ) : D p 0 (x ^ n) := by
  simpa using hx.pow n

lemma D.zero (e : ℕ) : D p e 0 := by
  unfold D; simp [padicNorm.zero]

lemma D.one : D p 0 (1 : ℚ) := by
  unfold D; simp

lemma D_zero_iff {x : ℚ} : D p 0 x ↔ padicNorm p x ≤ 1 := by
  unfold D; simp

lemma D.intCast (z : ℤ) : D p 0 (z : ℚ) := by
  rw [D_zero_iff]; exact padicNorm.of_int z

lemma D.natCast (n : ℕ) : D p 0 (n : ℚ) := by
  rw [D_zero_iff]; exact padicNorm.of_nat n

lemma D.nat_of_dvd {e n : ℕ} (h : p ^ e ∣ n) : D p e (n : ℚ) := by
  unfold D
  have := (padicNorm.dvd_iff_norm_le (p := p) (n := e) (z := (n : ℤ))).1 (by exact_mod_cast h)
  simpa using this

lemma D.p_pow (e : ℕ) : D p e ((p : ℚ) ^ e) := by
  have := D.nat_of_dvd (p := p) (e := e) (n := p ^ e) dvd_rfl
  simpa using this

lemma padicNorm_unit {i : ℕ} (hi : ¬ p ∣ i) : padicNorm p (i : ℚ) = 1 :=
  (padicNorm.nat_eq_one_iff i).2 hi

lemma padicNorm_unit_inv {i : ℕ} (hi : ¬ p ∣ i) : padicNorm p ((i : ℚ)⁻¹) = 1 := by
  rw [inv_eq_one_div, padicNorm.div, padicNorm.one, padicNorm_unit hi, div_one]

lemma D.inv_unit {i : ℕ} (hi : ¬ p ∣ i) : D p 0 ((i : ℚ)⁻¹) := by
  rw [D_zero_iff, padicNorm_unit_inv hi]

lemma D.div_unit {e : ℕ} {x : ℚ} {i : ℕ} (hi : ¬ p ∣ i) (hx : D p e x) : D p e (x / i) := by
  rw [div_eq_mul_inv]; exact hx.mul_right (D.inv_unit hi)

lemma D.inv_sub_inv {e : ℕ} {a b : ℕ} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b)
    (h : D p e ((a : ℚ) - b)) : D p e ((a : ℚ)⁻¹ - (b : ℚ)⁻¹) := by
  have ha0 : (a : ℚ) ≠ 0 := by
    intro h0; apply ha; have : a = 0 := by exact_mod_cast h0
    simp [this]
  have hb0 : (b : ℚ) ≠ 0 := by
    intro h0; apply hb; have : b = 0 := by exact_mod_cast h0
    simp [this]
  have : (a : ℚ)⁻¹ - (b : ℚ)⁻¹ = ((b : ℚ) - a) * (a : ℚ)⁻¹ * (b : ℚ)⁻¹ := by
    field_simp
  rw [this]
  exact (h.neg.mul_right (D.inv_unit ha)).mul_right (D.inv_unit hb) |>.mono le_rfl
    |> fun h' => by simpa [neg_sub] using h'

lemma D.sq_sub_sq {e : ℕ} {x y : ℚ} (hx : D p 0 x) (hy : D p 0 y) (h : D p e (x - y)) :
    D p e (x ^ 2 - y ^ 2) := by
  have : x ^ 2 - y ^ 2 = (x - y) * (x + y) := by ring
  rw [this]; exact h.mul_right (hx.add hy)

lemma D.cube_sub_cube {e : ℕ} {x y : ℚ} (hx : D p 0 x) (hy : D p 0 y) (h : D p e (x - y)) :
    D p e (x ^ 3 - y ^ 3) := by
  have : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring
  rw [this]
  exact h.mul_right (((hx.pow0 2).add (hx.mul_left hy)).add (hy.pow0 2))

lemma D.of_eq {e : ℕ} {x y : ℚ} (h : x = y) (hy : D p e y) : D p e x := h ▸ hy


/-! ### Harmonic-type sums and the product `U` -/

/-- `x p i = 1/i` if `p ∤ i`, else `0`. -/
def x (p i : ℕ) : ℚ := if p ∣ i then 0 else (i : ℚ)⁻¹

def h1 (p L : ℕ) : ℚ := ∑ i ∈ range L, x p i
def h2 (p L : ℕ) : ℚ := ∑ i ∈ range L, (x p i) ^ 2
def U (p : ℕ) (N : ℚ) (L : ℕ) : ℚ := ∏ i ∈ range L, (1 + N * x p i)
def σ (p u K : ℕ) : ℚ := ∑ i ∈ range (p ^ u), (x p (p ^ u * K + i)) ^ 2

lemma x_zero : x p 0 = 0 := by simp [x]

lemma x_of_dvd {i : ℕ} (h : p ∣ i) : x p i = 0 := by simp [x, h]

lemma x_of_not_dvd {i : ℕ} (h : ¬ p ∣ i) : x p i = (i : ℚ)⁻¹ := by simp [x, h]

lemma D_x (i : ℕ) : D p 0 (x p i) := by
  unfold x; split_ifs with h
  · exact D.zero 0
  · exact D.inv_unit h

lemma D_h1 (L : ℕ) : D p 0 (h1 p L) := D.sum fun i _ => D_x i
lemma D_h2 (L : ℕ) : D p 0 (h2 p L) := D.sum fun i _ => (D_x i).pow0 2
lemma D_U {N : ℚ} (hN : D p 0 N) (L : ℕ) : D p 0 (U p N L) := by
  unfold U
  induction L with
  | zero => simp; exact D.one
  | succ L ih =>
    rw [prod_range_succ]
    exact ih.mul_left (D.one.add (hN.mul_left (D_x L)))

lemma U_succ (N : ℚ) (L : ℕ) : U p N (L + 1) = U p N L * (1 + N * x p L) := by
  unfold U; rw [prod_range_succ]

lemma h1_succ (L : ℕ) : h1 p (L + 1) = h1 p L + x p L := by
  unfold h1; rw [sum_range_succ]

lemma h2_succ (L : ℕ) : h2 p (L + 1) = h2 p L + (x p L) ^ 2 := by
  unfold h2; rw [sum_range_succ]

lemma D_two_inv (hp2 : ¬ p ∣ 2) : D p 0 ((2 : ℚ)⁻¹) := by
  have := D.inv_unit (p := p) hp2
  simpa using this

/-- Expansion of the product `U` to second order. -/
lemma U_expand (hp2 : ¬ p ∣ 2) {N : ℚ} (hN : D p 0 N) (L : ℕ) :
    ∃ R : ℚ, D p 0 R ∧
      U p N L = 1 + N * h1 p L + N ^ 2 * ((h1 p L) ^ 2 - h2 p L) / 2 + N ^ 3 * R := by
  induction L with
  | zero =>
    refine ⟨0, D.zero 0, ?_⟩
    simp [U, h1, h2]
  | succ L ih =>
    obtain ⟨R, hR, hU⟩ := ih
    refine ⟨R + ((h1 p L) ^ 2 - h2 p L) / 2 * x p L + N * R * x p L, ?_, ?_⟩
    · refine (hR.add ?_).add ((hN.mul_left hR).mul_right (D_x L))
      rw [div_eq_mul_inv]
      exact (((D_h1 L).pow0 2).sub (D_h2 L)).mul_right (D_two_inv hp2) |>.mul_right (D_x L)
    · rw [U_succ, hU, h1_succ, h2_succ]
      ring

/-- `U ≡ 1 mod N`. -/
lemma D_U_sub_one (hp2 : ¬ p ∣ 2) {e : ℕ} {N : ℚ} (hN : D p e N) (L : ℕ) :
    D p e (U p N L - 1) := by
  obtain ⟨R, hR, hU⟩ := U_expand hp2 (hN.mono (Nat.zero_le _)) L
  rw [hU]
  have h0 : D p 0 N := hN.mono (Nat.zero_le _)
  have e1 : D p e (N * h1 p L) := hN.mul_right (D_h1 L)
  have e2 : D p e (N ^ 2 * ((h1 p L) ^ 2 - h2 p L) / 2) := by
    rw [div_eq_mul_inv]
    refine ((?_ : D p e (N ^ 2)).mul_right ?_).mul_right (D_two_inv hp2)
    · have := hN.pow 2; exact this.mono (by omega)
    · exact ((D_h1 L).pow0 2).sub (D_h2 L)
  have e3 : D p e (N ^ 3 * R) := by
    have := hN.pow 3; exact (this.mono (by omega)).mul_right hR
  have := (e1.add e2).add e3
  convert this using 1; ring

/-! ### Binomial identities -/

lemma choose_succ_succ_rat (n k : ℕ) :
    (Nat.choose (n + 1) (k + 1) : ℚ) = Nat.choose n k * (n + 1) / (k + 1) := by
  have := Nat.add_one_mul_choose_eq n k
  have h : ((k : ℚ) + 1) ≠ 0 := by positivity
  rw [eq_div_iff h]
  have h2 : (((n + 1).choose (k + 1) * (k + 1) : ℕ) : ℚ) = ((n + 1) * n.choose k : ℕ) := by
    rw [this]
  push_cast at h2
  rw [h2]; ring

lemma choose_add_succ_rat (n L : ℕ) :
    (Nat.choose (n + L) (L + 1) : ℚ) = Nat.choose (n + L) L * n / (L + 1) := by
  have := Nat.choose_succ_right_eq (n + L) L
  rw [Nat.add_sub_cancel] at this
  have h : ((L : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  exact_mod_cast this

/-- The key identity: `C(pN' + L, L) = C(N' + L/p, L/p) * U(pN', L+1)`. -/
lemma choose_key (N' L : ℕ) :
    (Nat.choose (p * N' + L) L : ℚ) =
      Nat.choose (N' + L / p) (L / p) * U p (p * N' : ℚ) (L + 1) := by
  induction L with
  | zero => simp [U, x_zero]
  | succ L ih =>
    rw [← add_assoc, choose_succ_succ_rat, ih, U_succ (p := p) (p * N' : ℚ) (L + 1)]
    by_cases hL : p ∣ L + 1
    · rw [Nat.succ_div_of_dvd hL, x_of_dvd hL]
      obtain ⟨q, hq⟩ := hL
      have hq' : L / p = q - 1 := by
        rcases q with _ | q
        · omega
        · have hpp := hp.out.pos
          have : L = p * q + (p - 1) := by
            rw [Nat.mul_add, Nat.mul_one] at hq; omega
          rw [this, Nat.add_comm, Nat.add_mul_div_left _ _ hpp,
            Nat.div_eq_of_lt (by omega)]
          simp
      have hq1 : 1 ≤ q := by
        rcases q with _ | q
        · omega
        · omega
      rw [hq', ← add_assoc, Nat.sub_add_cancel hq1, ← Nat.sub_add_cancel hq1,
        choose_succ_succ_rat, Nat.sub_add_cancel hq1]
      have hp0 : (p : ℚ) ≠ 0 := p_ne_zero
      have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
      have hcast : ((L : ℚ) + 1) = p * q := by exact_mod_cast hq
      have hq2 : ((q - 1 : ℕ) : ℚ) + 1 = q := by
        rw [Nat.cast_sub hq1]; push_cast; ring
      have hL : (L : ℚ) = p * q - 1 := by linarith
      rw [hcast, hq2]
      push_cast [Nat.cast_sub hq1]
      rw [hL]
      field_simp
      ring
    · rw [Nat.succ_div_of_not_dvd hL, x_of_not_dvd hL]
      have h0 : ((L : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-! ### Harmonic sum congruences -/

lemma dvd_pow_mul_add_iff {t c i : ℕ} (ht : 1 ≤ t) : p ∣ c * p ^ t + i ↔ p ∣ i := by
  have : p ∣ c * p ^ t := Dvd.dvd.mul_left (dvd_pow_self p (by omega)) c
  constructor
  · intro h; exact (Nat.dvd_add_right this).1 h
  · intro h; exact dvd_add this h

/-- Shift lemma: `x(c p^t + i)^2 ≡ x(i)^2 mod p^t`. -/
lemma xsq_shift {t : ℕ} (ht : 1 ≤ t) (c i : ℕ) :
    D p t ((x p (c * p ^ t + i)) ^ 2 - (x p i) ^ 2) := by
  by_cases hi : p ∣ i
  · rw [x_of_dvd hi, x_of_dvd ((dvd_pow_mul_add_iff ht).2 hi)]
    simp; exact D.zero t
  · have hi' : ¬ p ∣ c * p ^ t + i := fun h => hi ((dvd_pow_mul_add_iff ht).1 h)
    rw [x_of_not_dvd hi, x_of_not_dvd hi']
    apply D.sq_sub_sq (D.inv_unit hi') (D.inv_unit hi)
    apply D.inv_sub_inv hi' hi
    push_cast
    have : (c : ℚ) * (p : ℚ) ^ t + i - i = c * (p : ℚ) ^ t := by ring
    rw [this]
    exact (D.natCast c).mul_left (D.p_pow t)

lemma sum_range_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a b : ℕ) :
    ∑ i ∈ range (a * b), f i = ∑ y ∈ range b, ∑ z ∈ range a, f (a * y + z) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

/-- `Σ_{i < K p^t} x(i)^2 ≡ 0 mod p^t` given the core case `K = 1`. -/
lemma h2_mul_of_core {t : ℕ} (ht : 1 ≤ t) (hcore : D p t (h2 p (p ^ t))) (K : ℕ) :
    D p t (h2 p (K * p ^ t)) := by
  induction K with
  | zero => simp [h2]; exact D.zero t
  | succ K ih =>
    unfold h2 at *
    rw [Nat.succ_mul, sum_range_add]
    refine ih.add ?_
    have : ∑ i ∈ range (p ^ t), (x p (K * p ^ t + i)) ^ 2 =
        ∑ i ∈ range (p ^ t), (x p i) ^ 2 +
          ∑ i ∈ range (p ^ t), ((x p (K * p ^ t + i)) ^ 2 - (x p i) ^ 2) := by
      rw [← sum_add_distrib]; congr 1; ext i; ring
    rw [this]
    exact hcore.add (D.sum fun i _ => xsq_shift ht K i)

/-- The core case: `Σ_{i < p^t} x(i)^2 ≡ 0 mod p^t`. -/
lemma h2_core (hp2 : ¬ p ∣ 2) (hp3 : ¬ p ∣ 3) {t : ℕ} (ht : 1 ≤ t) : D p t (h2 p (p ^ t)) := by
  set M := p ^ t with hM
  have hMpos : 0 < M := pow_pos hp.out.pos t
  have hDM : D p t (M : ℚ) := by rw [hM]; push_cast; exact D.p_pow t
  have hpM : p ∣ M := dvd_pow_self p (by omega)
  have hcop : Nat.Coprime 2 M := by
    rw [hM]; apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]; exact hp2
  -- the bijection i ↦ 2 i mod M on range M
  have hinj : Set.InjOn (fun i : ℕ => 2 * i % M) (range M : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have h1 : 2 * a ≡ 2 * b [MOD M] := hab
    have h2 : a ≡ b [MOD M] := Nat.ModEq.cancel_left_of_coprime (by simpa using hcop) h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 ha hb
  have himg : (range M).image (fun i : ℕ => 2 * i % M) = range M := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      simp only [mem_image, mem_range] at hj ⊢
      obtain ⟨i, _, rfl⟩ := hj
      exact Nat.mod_lt _ hMpos
    · rw [Finset.card_image_of_injOn hinj]
  -- reindex
  have hre : h2 p M = ∑ i ∈ range M, (x p (2 * i % M)) ^ 2 := by
    unfold h2
    conv_lhs => rw [← himg]
    rw [sum_image hinj]
  -- termwise: x(2i mod M)^2 ≡ x(i)^2 / 4
  have hterm : ∀ i ∈ range M, D p t ((x p (2 * i % M)) ^ 2 - (2 : ℚ)⁻¹ ^ 2 * (x p i) ^ 2) := by
    intro i _
    by_cases hi : p ∣ i
    · have h2i : p ∣ 2 * i % M := by
        have : p ∣ 2 * i := Dvd.dvd.mul_left hi 2
        have hd : p ∣ M * (2 * i / M) := Dvd.dvd.mul_right hpM _
        rw [← Nat.mod_add_div (2 * i) M] at this
        exact (Nat.dvd_add_left hd).1 this
      rw [x_of_dvd hi, x_of_dvd h2i]; simp; exact D.zero t
    · have h2i : ¬ p ∣ 2 * i := fun h => hi ((Nat.Prime.dvd_mul hp.out).1 h |>.resolve_left hp2)
      have h2i' : ¬ p ∣ 2 * i % M := by
        intro h
        have hh := Nat.mod_add_div (2 * i) M
        have hd : p ∣ M * (2 * i / M) := Dvd.dvd.mul_right hpM _
        exact h2i (hh ▸ dvd_add h hd)
      rw [x_of_not_dvd hi, x_of_not_dvd h2i']
      have : (2 : ℚ)⁻¹ ^ 2 * ((i : ℚ)⁻¹) ^ 2 = (((2 * i : ℕ) : ℚ)⁻¹) ^ 2 := by
        push_cast; rw [mul_inv, mul_pow]
      rw [this]
      apply D.sq_sub_sq (D.inv_unit h2i') (D.inv_unit h2i)
      apply D.inv_sub_inv h2i' h2i
      have hh := Nat.mod_add_div (2 * i) M
      have : ((2 * i % M : ℕ) : ℚ) - ((2 * i : ℕ) : ℚ) = -((M : ℚ) * ((2 * i / M : ℕ) : ℚ)) := by
        have : ((2 * i : ℕ) : ℚ) = ((2 * i % M : ℕ) : ℚ) + (M : ℚ) * ((2 * i / M : ℕ) : ℚ) := by
          exact_mod_cast hh.symm
        rw [this]; ring
      rw [this]
      exact (hDM.mul_right (D.natCast _)).neg
  -- conclude
  have hsum : D p t (h2 p M - (2 : ℚ)⁻¹ ^ 2 * h2 p M) := by
    have hre' := hre
    unfold h2 at hre'
    have e : h2 p M - (2 : ℚ)⁻¹ ^ 2 * h2 p M =
        ∑ i ∈ range M, ((x p (2 * i % M)) ^ 2 - (2 : ℚ)⁻¹ ^ 2 * (x p i) ^ 2) := by
      rw [sum_sub_distrib, ← mul_sum, ← hre']
      rfl
    rw [e]
    exact D.sum hterm
  have hunit : D p 0 ((3 : ℚ)⁻¹ * 4) := by
    have := (D.inv_unit (p := p) hp3).mul_right (D.natCast 4)
    simpa using this
  have : h2 p M = (3 : ℚ)⁻¹ * 4 * (h2 p M - (2 : ℚ)⁻¹ ^ 2 * h2 p M) := by ring
  rw [this]
  exact hunit.mul_left hsum

lemma h2_mul (hp2 : ¬ p ∣ 2) (hp3 : ¬ p ∣ 3) {t : ℕ} (ht : 1 ≤ t) (K : ℕ) :
    D p t (h2 p (K * p ^ t)) :=
  h2_mul_of_core ht (h2_core hp2 hp3 ht) K

/-- Reflection: `Σ_{i<L} x i = Σ_{i<L} x (L - i)` when `p ∣ L`. -/
lemma h1_reflect {L : ℕ} (hL : p ∣ L) : h1 p L = ∑ i ∈ range L, x p (L - i) := by
  unfold h1
  have h := sum_range_reflect (fun j => x p (j + 1)) L
  have e1 : ∑ i ∈ range L, x p (L - i) = ∑ j ∈ range L, x p (L - 1 - j + 1) := by
    apply sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    congr 1; omega
  rw [e1, h]
  have := sum_range_succ' (fun j => x p j) L
  rw [sum_range_succ, x_of_dvd hL, x_zero] at this
  simpa using this

lemma h1_mul (hp2 : ¬ p ∣ 2) (hp3 : ¬ p ∣ 3) {t : ℕ} (ht : 1 ≤ t) (K : ℕ) :
    D p (2 * t) (h1 p (K * p ^ t)) := by
  set L := K * p ^ t with hLdef
  have hpL : p ∣ L := Dvd.dvd.mul_left (dvd_pow_self p (by omega)) K
  have hDL : D p t (L : ℚ) := by
    rw [hLdef]; push_cast; exact (D.natCast K).mul_left (D.p_pow t)
  -- 2 h1 = Σ (x i + x (L - i)) = L * Σ_{p∤i} i⁻¹ (L-i)⁻¹
  have key : 2 * h1 p L = (L : ℚ) * ∑ i ∈ range L,
      (if p ∣ i then 0 else (i : ℚ)⁻¹ * ((L - i : ℕ) : ℚ)⁻¹) := by
    rw [two_mul]
    nth_rewrite 2 [h1_reflect hpL]
    unfold h1
    rw [← sum_add_distrib, mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [mem_range] at hi
    by_cases hpi : p ∣ i
    · have : p ∣ L - i := (Nat.dvd_sub hpL hpi)
      rw [x_of_dvd hpi, x_of_dvd this]; simp [hpi]
    · have hLi : ¬ p ∣ L - i := by
        intro h
        apply hpi
        have := Nat.dvd_sub hpL h
        rwa [Nat.sub_sub_self hi.le] at this
      rw [x_of_not_dvd hpi, x_of_not_dvd hLi]
      simp only [hpi, if_false]
      have hi0 : (i : ℚ) ≠ 0 := by
        norm_cast; rintro rfl; exact hpi (dvd_zero p)
      have hLi0 : ((L - i : ℕ) : ℚ) ≠ 0 := by
        norm_cast; intro h; rw [h] at hLi; exact hLi (dvd_zero p)
      have hcast : ((L - i : ℕ) : ℚ) = (L : ℚ) - i := by
        rw [Nat.cast_sub hi.le]
      field_simp
      rw [hcast]; ring
  -- each term ≡ -(x i)^2 mod p^t
  have hterm : ∀ i ∈ range L, D p t
      ((if p ∣ i then 0 else (i : ℚ)⁻¹ * ((L - i : ℕ) : ℚ)⁻¹) + (x p i) ^ 2) := by
    intro i hi
    rw [mem_range] at hi
    by_cases hpi : p ∣ i
    · simp [hpi, x_of_dvd hpi]; exact D.zero t
    · have hLi : ¬ p ∣ L - i := by
        intro h
        apply hpi
        have := Nat.dvd_sub hpL h
        rwa [Nat.sub_sub_self hi.le] at this
      simp only [hpi, if_false, x_of_not_dvd hpi]
      have : (i : ℚ)⁻¹ * ((L - i : ℕ) : ℚ)⁻¹ + ((i : ℚ)⁻¹) ^ 2 =
          (i : ℚ)⁻¹ * (((L - i : ℕ) : ℚ)⁻¹ - (-(i : ℚ))⁻¹) := by ring
      rw [this]
      apply (D.inv_unit hpi).mul_left
      -- (L-i)⁻¹ - (-i)⁻¹
      have hi0 : (i : ℚ) ≠ 0 := by
        norm_cast; rintro rfl; exact hpi (dvd_zero p)
      have hLi0 : ((L - i : ℕ) : ℚ) ≠ 0 := by
        norm_cast; intro h; rw [h] at hLi; exact hLi (dvd_zero p)
      have hcast : ((L - i : ℕ) : ℚ) = (L : ℚ) - i := by
        rw [Nat.cast_sub hi.le]
      have : ((L - i : ℕ) : ℚ)⁻¹ - (-(i : ℚ))⁻¹ = (L : ℚ) * (((L - i : ℕ) : ℚ)⁻¹ * (i : ℚ)⁻¹) := by
        field_simp
        rw [hcast]; ring
      rw [this]
      exact hDL.mul_right ((D.inv_unit hLi).mul_left (D.inv_unit hpi))
  have hsum : D p t (∑ i ∈ range L,
      (if p ∣ i then 0 else (i : ℚ)⁻¹ * ((L - i : ℕ) : ℚ)⁻¹)) := by
    have e : ∑ i ∈ range L, (if p ∣ i then 0 else (i : ℚ)⁻¹ * ((L - i : ℕ) : ℚ)⁻¹) =
        ∑ i ∈ range L, ((if p ∣ i then 0 else (i : ℚ)⁻¹ * ((L - i : ℕ) : ℚ)⁻¹) + (x p i) ^ 2)
          - h2 p L := by
      unfold h2; rw [sum_add_distrib]; ring
    rw [e]
    exact (D.sum hterm).sub (h2_mul hp2 hp3 ht K)
  have h2h : D p (t + t) (2 * h1 p L) := by
    rw [key]; exact hDL.mul hsum
  have : h1 p L = (2 : ℚ)⁻¹ * (2 * h1 p L) := by ring
  rw [this, two_mul]
  exact (D_two_inv hp2).mul_left h2h

/-! ### The sums σ and Ω -/

lemma σ_bound (hp2 : ¬ p ∣ 2) (hp3 : ¬ p ∣ 3) {u : ℕ} (hu : 1 ≤ u) (K : ℕ) :
    D p u (σ p u K) := by
  have e : σ p u K = h2 p (p ^ u) +
      ∑ i ∈ range (p ^ u), ((x p (K * p ^ u + i)) ^ 2 - (x p i) ^ 2) := by
    unfold σ h2
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [mul_comm K]; ring
  rw [e]
  exact (h2_core hp2 hp3 hu).add (D.sum fun i _ => xsq_shift hu K i)

lemma σ_merge (u K1 : ℕ) : ∑ K2 ∈ range p, σ p u (p * K1 + K2) = σ p (u + 1) K1 := by
  unfold σ
  rw [pow_succ, sum_range_mul _ (p ^ u) p]
  apply sum_congr rfl
  intro K2 _
  apply sum_congr rfl
  intro i _
  rw [show p ^ u * (p * K1 + K2) + i = p ^ u * p * K1 + (p ^ u * K2 + i) by ring]

/-- The sharp bound `U(m p^r, L) ≡ 1 mod p^(r + 2t)` when `p^t ∣ L`, `1 ≤ t ≤ r`. -/
lemma U_sub_one_bound (hp2 : ¬ p ∣ 2) (hp3 : ¬ p ∣ 3) (m r t L : ℕ) (ht : 1 ≤ t) (htr : t ≤ r)
    (hL : p ^ t ∣ L) : D p (r + 2 * t) (U p ((m : ℚ) * (p : ℚ) ^ r) L - 1) := by
  obtain ⟨K, hK⟩ := hL
  have hK' : L = K * p ^ t := by rw [hK, mul_comm]
  subst hK'
  have hN : D p r ((m : ℚ) * (p : ℚ) ^ r) := (D.natCast m).mul_left (D.p_pow r)
  obtain ⟨R, hR, hU⟩ := U_expand hp2 (hN.mono (Nat.zero_le _)) (K * p ^ t)
  rw [hU]
  have e1 : D p (r + 2 * t) (((m : ℚ) * (p : ℚ) ^ r) * h1 p (K * p ^ t)) :=
    hN.mul (h1_mul hp2 hp3 ht K)
  have e2 : D p (r + 2 * t) (((m : ℚ) * (p : ℚ) ^ r) ^ 2 *
      ((h1 p (K * p ^ t)) ^ 2 - h2 p (K * p ^ t)) / 2) := by
    rw [div_eq_mul_inv]
    have h2t : D p t (h2 p (K * p ^ t)) := h2_mul hp2 hp3 ht K
    have h1t : D p t ((h1 p (K * p ^ t)) ^ 2) := by
      have := (h1_mul hp2 hp3 ht K).pow 2
      exact this.mono (by omega)
    have := ((hN.pow 2).mul (h1t.sub h2t)).mul_right (D_two_inv hp2)
    exact this.mono (by omega)
  have e3 : D p (r + 2 * t) (((m : ℚ) * (p : ℚ) ^ r) ^ 3 * R) := by
    have := (hN.pow 3).mul_right hR
    exact this.mono (by omega)
  have := (e1.add e2).add e3
  convert this using 1; ring

/-- `Ω p s u m c = Σ_{K < c p^s} C(m p^s + K, K)^3 σ_u(K)`. -/
def Ω (p s u m c : ℕ) : ℚ :=
  ∑ K ∈ range (c * p ^ s), (Nat.choose (m * p ^ s + K) K : ℚ) ^ 3 * σ p u K

lemma Ω_bound (hp2 : ¬ p ∣ 2) (hp3 : ¬ p ∣ 3) (s : ℕ) :
    ∀ u m c : ℕ, 1 ≤ u → D p (s + u) (Ω p s u m c) := by
  induction s with
  | zero =>
    intro u m c hu
    unfold Ω
    simp only [pow_zero, mul_one, zero_add]
    exact D.sum fun K _ => ((D.natCast _).pow0 3).mul_left (σ_bound hp2 hp3 hu K)
  | succ s ih =>
    intro u m c hu
    unfold Ω
    have hsplit : c * p ^ (s + 1) = p * (c * p ^ s) := by ring
    rw [hsplit, sum_range_mul _ p (c * p ^ s)]
    -- rewrite each term via the key identity
    have hterm : ∀ K1 K2 : ℕ, K2 < p →
        (Nat.choose (m * p ^ (s + 1) + (p * K1 + K2)) (p * K1 + K2) : ℚ) =
          Nat.choose (m * p ^ s + K1) K1 * U p (p * (m * p ^ s) : ℚ) (p * K1 + K2 + 1) := by
      intro K1 K2 hK2
      have e : m * p ^ (s + 1) = p * (m * p ^ s) := by ring
      rw [e, choose_key]
      have : (p * K1 + K2) / p = K1 := by
        rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp.out.pos, Nat.div_eq_of_lt hK2]; simp
      rw [this]; push_cast; ring
    have hDN : D p (s + 1) (p * (m * p ^ s) : ℚ) := by
      have : (p * (m * p ^ s) : ℚ) = (m : ℚ) * (p : ℚ) ^ (s + 1) := by push_cast; ring
      rw [this]
      exact (D.natCast m).mul_left (D.p_pow (s + 1))
    -- main term + error term
    have hmain : ∑ K1 ∈ range (c * p ^ s), ∑ K2 ∈ range p,
        (Nat.choose (m * p ^ (s + 1) + (p * K1 + K2)) (p * K1 + K2) : ℚ) ^ 3 *
          σ p u (p * K1 + K2) =
        Ω p s (u + 1) m c +
        ∑ K1 ∈ range (c * p ^ s), ∑ K2 ∈ range p,
          (Nat.choose (m * p ^ s + K1) K1 : ℚ) ^ 3 *
            ((U p (p * (m * p ^ s) : ℚ) (p * K1 + K2 + 1)) ^ 3 - 1) * σ p u (p * K1 + K2) := by
      unfold Ω
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro K1 _
      rw [← σ_merge, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro K2 hK2
      rw [mem_range] at hK2
      rw [hterm K1 K2 hK2]
      ring
    rw [hmain]
    have hIH := ih (u + 1) m c (by omega)
    refine (hIH.mono (by omega)).add ?_
    apply D.sum; intro K1 _
    apply D.sum; intro K2 _
    have hU1 : D p (s + 1) ((U p (p * (m * p ^ s) : ℚ) (p * K1 + K2 + 1)) ^ 3 - 1) := by
      have h0 : D p 0 (U p (p * (m * p ^ s) : ℚ) (p * K1 + K2 + 1)) :=
        D_U (hDN.mono (Nat.zero_le _)) _
      have := D.cube_sub_cube h0 D.one (D_U_sub_one hp2 hDN _)
      simpa using this
    have := (((D.natCast (Nat.choose (m * p ^ s + K1) K1)).pow0 3).mul_left hU1).mul
      (σ_bound hp2 hp3 hu (p * K1 + K2))
    convert this using 2

/-! ### Consequences of the key identity -/

/-- For `p ∤ k`: `C(pN' + k - 1, k) = (pN'/k) * C(N' + k/p, k/p) * U(pN', k)`. -/
lemma choose_not_dvd (N' k : ℕ) (hk : ¬ p ∣ k) :
    (Nat.choose (p * N' + k - 1) k : ℚ) =
      ((p * N' : ℕ) : ℚ) / k * Nat.choose (N' + k / p) (k / p) * U p (p * N' : ℚ) k := by
  obtain ⟨L, rfl⟩ : ∃ L, k = L + 1 := ⟨k - 1, by
    have : k ≠ 0 := fun h => hk (h ▸ dvd_zero p); omega⟩
  rw [show p * N' + (L + 1) - 1 = p * N' + L by omega, choose_add_succ_rat, choose_key,
    Nat.succ_div_of_not_dvd hk]
  push_cast
  ring

/-- For `1 ≤ k'`: `C(pN' + pk' - 1, pk') = C(N' + k' - 1, k') * U(pN', pk')`. -/
lemma choose_dvd (N' k' : ℕ) (hk : 1 ≤ k') :
    (Nat.choose (p * N' + p * k' - 1) (p * k') : ℚ) =
      Nat.choose (N' + k' - 1) k' * U p (p * N' : ℚ) (p * k') := by
  obtain ⟨j, rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
  have hpp := hp.out.pos
  have e1 : p * N' + p * (j + 1) - 1 = p * N' + (p * j + (p - 1)) := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  have e2 : p * (j + 1) = (p * j + (p - 1)) + 1 := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  have e3 : (p * j + (p - 1)) / p = j := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hpp, Nat.div_eq_of_lt (by omega)]; simp
  rw [e1, e2, choose_add_succ_rat, choose_key, e3, ← e2,
    show N' + (j + 1) - 1 = N' + j by omega, choose_add_succ_rat]
  have hj : ((j : ℚ) + 1) ≠ 0 := by positivity
  have hp0 : (p : ℚ) ≠ 0 := p_ne_zero
  have : ((p * j + (p - 1) : ℕ) : ℚ) + 1 = p * (j + 1) := by
    push_cast [Nat.cast_pred hpp]; ring
  rw [this]
  push_cast
  field_simp

/-! ### The terms of the sum -/

/-- `τ N k = (N + 2k) * C(N + k - 1, k)^3`. -/
def τ (N k : ℕ) : ℚ := ((N + 2 * k : ℕ) : ℚ) * (Nat.choose (N + k - 1) k : ℚ) ^ 3

lemma padicNorm_p_pow (f : ℕ) : padicNorm p ((p : ℚ) ^ f) = (p : ℚ) ^ (-(f : ℤ)) := by
  induction f with
  | zero => simp
  | succ f ih =>
    rw [pow_succ, padicNorm.mul, ih, padicNorm.padicNorm_p hp.out.one_lt]
    rw [show (-((f + 1 : ℕ) : ℤ)) = -(f : ℤ) + (-1 : ℤ) by push_cast; ring,
      zpow_add₀ (p_ne_zero (p := p)), zpow_neg_one]

lemma D.div_p_pow {e f : ℕ} {x : ℚ} (hx : D p (e + f) x) : D p e (x / (p : ℚ) ^ f) := by
  unfold D at *
  rw [padicNorm.div, padicNorm_p_pow, div_eq_mul_inv, ← zpow_neg, neg_neg]
  calc padicNorm p x * (p : ℚ) ^ (f : ℤ) ≤ (p : ℚ) ^ (-((e + f : ℕ) : ℤ)) * (p : ℚ) ^ (f : ℤ) :=
        mul_le_mul_of_nonneg_right hx (zpow_nonneg (p_pos (p := p)).le _)
    _ = (p : ℚ) ^ (-(e : ℤ)) := by
        rw [← zpow_add₀ (p_ne_zero (p := p))]; congr 1; push_cast; ring

/-- Part (I): the terms with `p ∣ k` match the lower level. -/
lemma termI (hp2 : ¬ p ∣ 2) (hp3 : ¬ p ∣ 3) (m r k' : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k') :
    D p (4 * r) (τ (m * p ^ r) (p * k') - p * τ (m * p ^ (r - 1)) k') := by
  set N' := m * p ^ (r - 1) with hN'
  have hN : m * p ^ r = p * N' := by
    rw [hN', ← mul_assoc, mul_comm p m, mul_assoc, ← _root_.pow_succ']
    congr 2; omega
  have hNq : (p : ℚ) * (N' : ℚ) = (m : ℚ) * (p : ℚ) ^ r := by
    have : ((p * N' : ℕ) : ℚ) = ((m * p ^ r : ℕ) : ℚ) := by rw [hN]
    push_cast at this; exact this
  unfold τ
  rw [hN, choose_dvd N' k' hk, hNq]
  set C := (Nat.choose (N' + k' - 1) k' : ℚ) with hC
  set Uq := U p ((m : ℚ) * (p : ℚ) ^ r) (p * k') with hUq
  suffices H : D p (4 * r) (p * ((N' + 2 * k' : ℕ) : ℚ) * C ^ 3 * (Uq ^ 3 - 1)) by
    convert H using 1; push_cast; ring
  have hDp : D p 1 (p : ℚ) := by have := D.p_pow (p := p) 1; simpa using this
  have hU0 : D p 0 Uq := D_U ((D.natCast m).mul_left (D.p_pow r) |>.mono (Nat.zero_le _)) _
  -- decompose k'
  obtain ⟨v, k'', hk'', hkv⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : k' ≠ 0) p hp.out.ne_one
  by_cases hcase : v + 2 ≤ r
  · -- case (a)
    have hpt : p ^ (v + 1) ∣ p * k' := by
      rw [hkv, _root_.pow_succ', ← mul_assoc]
      exact Dvd.intro _ rfl
    have hU : D p (r + 2 * (v + 1)) (Uq ^ 3 - 1) := by
      have := D.cube_sub_cube hU0 D.one
        (U_sub_one_bound hp2 hp3 m r (v + 1) (p * k') (by omega) (by omega) hpt)
      simpa using this
    have hC3 : D p (3 * (r - 1 - v)) (C ^ 3) := by
      apply D.pow
      rw [hC]
      obtain ⟨L, hL⟩ : ∃ L, k' = L + 1 := ⟨k' - 1, by omega⟩
      have hLq : (L : ℚ) + 1 = k' := by rw [hL]; push_cast; ring
      rw [hL, show N' + (L + 1) - 1 = N' + L by omega, choose_add_succ_rat, hLq]
      have : (Nat.choose (N' + L) L : ℚ) * N' / k' =
          (Nat.choose (N' + L) L : ℚ) * (m : ℚ) * (p : ℚ) ^ (r - 1 - v) * ((k'' : ℚ)⁻¹) := by
        rw [hN', hkv]
        push_cast
        have hp0 : (p : ℚ) ≠ 0 := p_ne_zero
        have hk0 : (k'' : ℚ) ≠ 0 := by
          norm_cast; rintro rfl; exact hk'' (dvd_zero p)
        have : (p : ℚ) ^ (r - 1) = (p : ℚ) ^ (r - 1 - v) * (p : ℚ) ^ v := by
          rw [← pow_add]; congr 1; omega
        rw [this]
        field_simp
      rw [this]
      have := (((D.natCast (Nat.choose (N' + L) L)).mul_right (D.natCast m)).mul
        (D.p_pow (r - 1 - v))).mul_right (D.inv_unit hk'')
      simpa using this
    have hN2 : D p v ((N' + 2 * k' : ℕ) : ℚ) := by
      apply D.nat_of_dvd
      apply dvd_add
      · rw [hN']; exact Dvd.dvd.mul_left (pow_dvd_pow p (by omega)) m
      · rw [hkv]; exact Dvd.dvd.mul_left (Dvd.dvd.mul_right dvd_rfl _) 2
    have := ((hDp.mul hN2).mul hC3).mul hU
    exact this.mono (by omega)
  · -- case (b): r ≤ v + 1
    have hpt : p ^ r ∣ p * k' := by
      rw [hkv, ← mul_assoc, ← _root_.pow_succ']
      exact Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) _
    have hU : D p (r + 2 * r) (Uq ^ 3 - 1) := by
      have := D.cube_sub_cube hU0 D.one
        (U_sub_one_bound hp2 hp3 m r r (p * k') hr le_rfl hpt)
      simpa using this
    have hC3 : D p 0 (C ^ 3) := (D.natCast _).pow0 3
    have hN2 : D p (r - 1) ((N' + 2 * k' : ℕ) : ℚ) := by
      apply D.nat_of_dvd
      apply dvd_add
      · rw [hN']; exact Dvd.dvd.mul_left dvd_rfl m
      · rw [hkv]; exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) _) 2
    have := ((hDp.mul hN2).mul hC3).mul hU
    exact this.mono (by omega)

lemma σ_one (K : ℕ) : σ p 1 K = ∑ j ∈ range p,
    if p ∣ j then 0 else (((p * K + j : ℕ) : ℚ)⁻¹) ^ 2 := by
  unfold σ
  simp only [pow_one]
  apply sum_congr rfl
  intro j _
  have : p ∣ p * K + j ↔ p ∣ j := Nat.dvd_add_right (dvd_mul_right p K)
  by_cases hj : p ∣ j
  · rw [x_of_dvd (this.2 hj)]; simp [hj]
  · rw [x_of_not_dvd (fun h => hj (this.1 h))]; simp [hj]

/-- Part (II): the terms with `p ∤ k` sum to something divisible by `p^(4r)`. -/
lemma termII (hp2 : ¬ p ∣ 2) (hp3 : ¬ p ∣ 3) (m r : ℕ) (hr : 1 ≤ r) :
    D p (4 * r) (∑ K ∈ range (m * p ^ (r - 1)), ∑ j ∈ range p,
      if p ∣ j then 0 else τ (m * p ^ r) (p * K + j)) := by
  set N' := m * p ^ (r - 1) with hN'
  have hN : m * p ^ r = p * N' := by
    rw [hN', ← mul_assoc, mul_comm p m, mul_assoc, ← _root_.pow_succ']
    congr 2; omega
  set N : ℚ := (m : ℚ) * (p : ℚ) ^ r with hNdef
  have hNq : ((p * N' : ℕ) : ℚ) = N := by
    rw [← hN]; push_cast; ring
  have hNq' : (p : ℚ) * (N' : ℚ) = N := by rw [← hNq]; push_cast; ring
  have hDN : D p r N := (D.natCast m).mul_left (D.p_pow r)
  have hDN0 : D p 0 N := hDN.mono (Nat.zero_le _)
  -- the error term
  let ρ : ℕ → ℕ → ℚ := fun K j =>
    N ^ 4 * (((p * K + j : ℕ) : ℚ)⁻¹) ^ 3 * (Nat.choose (N' + K) K : ℚ) ^ 3 *
        (U p N (p * K + j)) ^ 3 +
      2 * N ^ 3 * (Nat.choose (N' + K) K : ℚ) ^ 3 * (((p * K + j : ℕ) : ℚ)⁻¹) ^ 2 *
        ((U p N (p * K + j)) ^ 3 - 1)
  have hterm : ∀ K j : ℕ, j < p → ¬ p ∣ j →
      τ (m * p ^ r) (p * K + j) =
        2 * N ^ 3 * (Nat.choose (N' + K) K : ℚ) ^ 3 * (((p * K + j : ℕ) : ℚ)⁻¹) ^ 2 + ρ K j := by
    intro K j hj hpj
    have hk : ¬ p ∣ p * K + j := fun h => hpj ((Nat.dvd_add_right (dvd_mul_right p K)).1 h)
    have hKdiv : (p * K + j) / p = K := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp.out.pos, Nat.div_eq_of_lt hj]; simp
    unfold τ
    rw [hN, choose_not_dvd N' _ hk, hKdiv, hNq, hNq']
    have hk0 : ((p * K + j : ℕ) : ℚ) ≠ 0 := by
      norm_cast; intro h; rw [h] at hk; exact hk (dvd_zero p)
    have : ((p * N' + 2 * (p * K + j) : ℕ) : ℚ) = N + 2 * ((p * K + j : ℕ) : ℚ) := by
      push_cast; rw [← hNq]; push_cast; ring
    rw [this]
    simp only [ρ]
    field_simp
    ring
  have hρ : ∀ K j : ℕ, ¬ p ∣ j → D p (4 * r) (ρ K j) := by
    intro K j hpj
    have hk : ¬ p ∣ p * K + j := fun h => hpj ((Nat.dvd_add_right (dvd_mul_right p K)).1 h)
    have hU0 : D p 0 (U p N (p * K + j)) := D_U hDN0 _
    have hU : D p r ((U p N (p * K + j)) ^ 3 - 1) := by
      have := D.cube_sub_cube hU0 D.one (D_U_sub_one hp2 hDN _)
      simpa using this
    have hinv : D p 0 (((p * K + j : ℕ) : ℚ)⁻¹) := D.inv_unit hk
    have hC : D p 0 ((Nat.choose (N' + K) K : ℚ) ^ 3) := (D.natCast _).pow0 3
    have e1 : D p (4 * r) (N ^ 4 * (((p * K + j : ℕ) : ℚ)⁻¹) ^ 3 *
        (Nat.choose (N' + K) K : ℚ) ^ 3 * (U p N (p * K + j)) ^ 3) :=
      (((hDN.pow 4).mul_right (hinv.pow0 3)).mul_right hC).mul_right (hU0.pow0 3)
    have e2 : D p (4 * r) (2 * N ^ 3 * (Nat.choose (N' + K) K : ℚ) ^ 3 *
        (((p * K + j : ℕ) : ℚ)⁻¹) ^ 2 * ((U p N (p * K + j)) ^ 3 - 1)) := by
      have := ((((D.natCast 2).mul_left (hDN.pow 3)).mul_right hC).mul_right (hinv.pow0 2)).mul hU
      exact this.mono (by omega)
    exact e1.add e2
  -- split the sum
  have hsplit : ∑ K ∈ range N', ∑ j ∈ range p,
      (if p ∣ j then 0 else τ (m * p ^ r) (p * K + j)) =
      2 * N ^ 3 * Ω p (r - 1) 1 m m +
      ∑ K ∈ range N', ∑ j ∈ range p, (if p ∣ j then (0 : ℚ) else ρ K j) := by
    unfold Ω
    rw [← hN', mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro K _
    simp only [σ_one, Finset.mul_sum]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    by_cases hpj : p ∣ j
    · simp [hpj]
    · simp only [hpj, if_false]
      rw [hterm K j hj hpj]
      ring
  rw [hsplit]
  have hΩ : D p (r - 1 + 1) (Ω p (r - 1) 1 m m) := Ω_bound hp2 hp3 (r - 1) 1 m m le_rfl
  have h1 : D p (4 * r) (2 * N ^ 3 * Ω p (r - 1) 1 m m) := by
    have := ((D.natCast 2).mul_left (hDN.pow 3)).mul hΩ
    exact this.mono (by omega)
  refine h1.add (D.sum fun K _ => D.sum fun j _ => ?_)
  by_cases hpj : p ∣ j
  · simp [hpj]; exact D.zero _
  · simp only [hpj, if_false]; exact hρ K j hpj

/-! ### Assembly -/

lemma sum_split (f : ℕ → ℚ) (N' : ℕ) :
    ∑ k ∈ range (p * N' + 1), f k =
      ∑ k' ∈ range (N' + 1), f (p * k') +
        ∑ K ∈ range N', ∑ j ∈ range p, (if p ∣ j then 0 else f (p * K + j)) := by
  rw [sum_range_succ, sum_range_mul f p N', sum_range_succ, add_right_comm, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro K _
  have e : ∀ j ∈ range p, f (p * K + j) =
      (if p ∣ j then f (p * K + j) else 0) + (if p ∣ j then 0 else f (p * K + j)) := by
    intro j _; split_ifs <;> simp
  rw [sum_congr rfl e, sum_add_distrib]
  congr 1
  have e2 : ∀ j ∈ range p, (if p ∣ j then f (p * K + j) else 0) =
      (if j = 0 then f (p * K + j) else 0) := by
    intro j hj
    rw [mem_range] at hj
    have : p ∣ j ↔ j = 0 := ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hj, fun h => h ▸ dvd_zero p⟩
    simp only [this]
  rw [sum_congr rfl e2, sum_ite_eq']
  simp [hp.out.pos]

lemma a_mul (n : ℕ) (hn : 1 ≤ n) : (n : ℚ) * a n = ∑ k ∈ range (n + 1), τ n k := by
  have hn0 : n ≠ 0 := by omega
  have hdvd : n ∣ ∑ k ∈ range (n + 1), (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3 := by
    apply Finset.dvd_sum
    intro k _
    have h := Nat.choose_succ_right_eq (n + k - 1) (n - 1)
    rw [show n - 1 + 1 = n by omega, show n + k - 1 - (n - 1) = k by omega] at h
    refine ⟨(Nat.choose (n + k - 1) (n - 1)) ^ 3 +
      2 * Nat.choose (n + k - 1) n * (Nat.choose (n + k - 1) (n - 1)) ^ 2, ?_⟩
    calc (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3
        = n * (Nat.choose (n + k - 1) (n - 1)) ^ 3 +
          2 * (Nat.choose (n + k - 1) (n - 1) * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 2 := by ring
      _ = n * (Nat.choose (n + k - 1) (n - 1)) ^ 3 +
          2 * (Nat.choose (n + k - 1) n * n) * (Nat.choose (n + k - 1) (n - 1)) ^ 2 := by rw [h]
      _ = _ := by ring
  have ha : a n = (∑ k ∈ range (n + 1), (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3) / n := by
    simp only [a, if_neg hn0]
  rw [ha, Nat.cast_div hdvd (by exact_mod_cast hn0), mul_div_cancel₀ _ (by exact_mod_cast hn0)]
  push_cast
  apply sum_congr rfl
  intro k _
  unfold τ
  have : n + k - 1 = (n - 1) + k := by omega
  rw [this, Nat.choose_symm_add]
  push_cast
  ring

theorem main_core (hp5 : 5 ≤ p) (m r : ℕ) (hm : ¬ p ∣ m) (hr : 1 ≤ r) :
    a (m * p ^ r) ≡ a (m * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  have hp2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hp3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  set N' := m * p ^ (r - 1) with hN'
  have hN : m * p ^ r = p * N' := by
    rw [hN', ← mul_assoc, mul_comm p m, mul_assoc, ← _root_.pow_succ']
    congr 2; omega
  have hN'pos : 1 ≤ N' := by
    rw [hN']; exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero hm0 (pow_ne_zero _ hp.out.ne_zero))
  have hNpos : 1 ≤ p * N' := Nat.one_le_iff_ne_zero.2 (mul_ne_zero hp.out.ne_zero (by omega))
  have hS := a_mul (p * N') hNpos
  have hS' := a_mul N' hN'pos
  -- the key divisibility
  have key : D p (4 * r) (∑ k ∈ range (p * N' + 1), τ (p * N') k -
      p * ∑ k ∈ range (N' + 1), τ N' k) := by
    rw [sum_split, mul_sum]
    have : ∑ k' ∈ range (N' + 1), τ (p * N') (p * k') +
        (∑ K ∈ range N', ∑ j ∈ range p, if p ∣ j then 0 else τ (p * N') (p * K + j)) -
        ∑ k' ∈ range (N' + 1), (p : ℚ) * τ N' k' =
        ∑ k' ∈ range (N' + 1), (τ (p * N') (p * k') - p * τ N' k') +
        ∑ K ∈ range N', ∑ j ∈ range p, (if p ∣ j then 0 else τ (p * N') (p * K + j)) := by
      rw [sum_sub_distrib]; ring
    rw [this]
    refine (D.sum ?_).add (by rw [← hN]; exact termII hp2 hp3 m r hr)
    intro k' _
    rcases Nat.eq_zero_or_pos k' with rfl | hk'pos
    · simp only [τ, mul_zero, add_zero, Nat.choose_zero_right, Nat.cast_one, one_pow, mul_one]
      push_cast
      rw [sub_self]; exact D.zero _
    · rw [← hN]; exact termI hp2 hp3 m r k' hr hk'pos
  -- convert to a(N) - a(N')
  have hm0' : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
  have hp0 : (p : ℚ) ≠ 0 := p_ne_zero
  have hN'0 : (N' : ℚ) ≠ 0 := by exact_mod_cast (by omega : N' ≠ 0)
  have hdiff : (a (p * N') : ℚ) - a N' =
      (∑ k ∈ range (p * N' + 1), τ (p * N') k - p * ∑ k ∈ range (N' + 1), τ N' k) /
        (m : ℚ) / (p : ℚ) ^ r := by
    rw [← hS, ← hS']
    have hNq : ((p * N' : ℕ) : ℚ) = (m : ℚ) * (p : ℚ) ^ r := by
      rw [← hN]; push_cast; ring
    have hNq' : (p : ℚ) * (N' : ℚ) = (m : ℚ) * (p : ℚ) ^ r := by
      rw [← hNq]; push_cast; ring
    rw [hNq]
    field_simp
    rw [mul_assoc (a N' : ℚ), hNq']
    ring
  have hD3 : D p (3 * r) ((a (p * N') : ℚ) - a N') := by
    rw [hdiff]
    apply D.div_p_pow
    apply D.div_unit hm
    exact key.mono (by omega)
  have hint : ((p ^ (3 * r) : ℕ) : ℤ) ∣ (a (p * N') : ℤ) - a N' := by
    rw [padicNorm.dvd_iff_norm_le]
    push_cast
    exact hD3
  rw [hN]
  exact (Nat.modEq_iff_dvd.2 hint).symm

end Sc

/--
The central binomial coefficients $u(n) := \binom{2n}{n}$ satisfy the supercongruences
$u(n \cdot p^r) \equiv u(n \cdot p^{r-1}) \pmod{p^{3r}}$ for positive integers $n$ and $r$
and all primes $p \ge 5$. We conjecture that the present sequence $a(n)$ satisfies the same congruences.
-/
theorem oeis_361883_conjecture_0 {p n r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  haveI := Fact.mk hp
  obtain ⟨j, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.ne_one
  have h := Sc.main_core hp5 m (j + r) hm (by omega)
  have e1 : p ^ j * m * p ^ r = m * p ^ (j + r) := by ring
  have e2 : p ^ j * m * p ^ (r - 1) = m * p ^ (j + r - 1) := by
    rw [show j + r - 1 = j + (r - 1) by omega, pow_add]; ring
  rw [e1, e2]
  exact Nat.ModEq.of_dvd (pow_dvd_pow p (by omega)) h


theorem oeis_361883_conjecture_0.disproof : ¬ (type_of% @oeis_361883_conjecture_0) := sorry
