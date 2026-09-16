import FormalConjectures.Util.ProblemImports

def R (n : ℕ) := ZMod n × ZMod n

namespace R

variable {n : ℕ}

@[ext] theorem ext (x y : R n) (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y := by
  cases x; cases y; simp_all

def mul (x y : R n) : R n := (x.1 * y.1 + 3 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)
def sub (x y : R n) : R n := (x.1 - y.1, x.2 - y.2)
def zero : R n := (0, 0)
def one : R n := (1, 0)

def pow (x : R n) : ℕ → R n
  | 0 => one
  | k + 1 => mul (pow x k) x

@[simp] theorem mul_one (x : R n) : mul x one = x := by
  ext <;> simp [mul, one]

@[simp] theorem one_mul (x : R n) : mul one x = x := by
  ext <;> simp [mul, one]

@[simp] theorem mul_zero (x : R n) : mul x zero = zero := by
  ext <;> simp [mul, zero]

@[simp] theorem zero_mul (x : R n) : mul zero x = zero := by
  ext <;> simp [mul, zero]

@[simp] theorem sub_self (x : R n) : sub x x = zero := by
  ext <;> simp [sub, zero]

theorem mul_assoc (x y z : R n) : mul (mul x y) z = mul x (mul y z) := by
  ext <;> simp [mul] <;> ring

theorem mul_comm (x y : R n) : mul x y = mul y x := by
  ext <;> simp [mul] <;> ring

theorem pow_add (x : R n) (a b : ℕ) : pow x (a + b) = mul (pow x a) (pow x b) := by
  induction b with
  | zero => simp [pow, mul_one]
  | succ b ih =>
    calc pow x (a + b + 1) = mul (pow x (a + b)) x := rfl
      _ = mul (mul (pow x a) (pow x b)) x := by rw [ih]
      _ = mul (pow x a) (mul (pow x b) x) := mul_assoc _ _ _
      _ = mul (pow x a) (pow x (b + 1)) := rfl

@[simp] theorem pow_one_eq_one (k : ℕ) : pow (one : R n) k = one := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pow, ih]

theorem pow_mul (x : R n) (a b : ℕ) : pow x (a * b) = pow (pow x a) b := by
  induction b with
  | zero => simp [pow]
  | succ b ih =>
    have : a * (b + 1) = a * b + a := by ring
    rw [this, pow_add, ih]
    rfl

def cast {n p : ℕ} [NeZero p] (h : p ∣ n) (x : R n) : R p :=
  (ZMod.castHom h (ZMod p) x.1, ZMod.castHom h (ZMod p) x.2)

@[simp] theorem cast_mul {n p : ℕ} [NeZero n] [NeZero p] (h : p ∣ n) (x y : R n) :
    cast h (mul x y) = mul (cast h x) (cast h y) := by
  ext
  · simp only [cast, mul, map_add, map_mul]
    have h3 : ZMod.castHom h (ZMod p) (3 : ZMod n) = 3 := by
      show ZMod.castHom h (ZMod p) (3 : ℕ) = (3 : ℕ)
      rw [map_natCast]
    rw [h3]
  · simp only [cast, mul, map_add, map_mul]

@[simp] theorem cast_one {n p : ℕ} [NeZero n] [NeZero p] (h : p ∣ n) :
    cast h (one : R n) = (one : R p) := by
  ext <;> simp [cast, one, map_one, map_zero]

@[simp] theorem cast_zero {n p : ℕ} [NeZero n] [NeZero p] (h : p ∣ n) :
    cast h (zero : R n) = (zero : R p) := by
  ext <;> simp [cast, zero, map_zero]

@[simp] theorem cast_sub {n p : ℕ} [NeZero n] [NeZero p] (h : p ∣ n) (x y : R n) :
    cast h (sub x y) = sub (cast h x) (cast h y) := by
  ext <;> simp [cast, sub, map_sub]

theorem cast_pow {n p : ℕ} [NeZero n] [NeZero p] (h : p ∣ n) (x : R n) (k : ℕ) :
    cast h (pow x k) = pow (cast h x) k := by
  induction k with
  | zero => simp [pow]
  | succ k ih => simp [pow, ih]

theorem one_ne_zero {p : ℕ} (hp : 1 < p) : (one : R p) ≠ zero := by
  intro h
  have h1 : (one : R p).1 = (zero : R p).1 := by rw [h]
  have h_ne : (1 : ZMod p) ≠ 0 := by
    haveI : Fact (1 < p) := ⟨hp⟩
    exact zero_ne_one.symm
  exact h_ne h1

theorem unit_ne_zero {p : ℕ} (hp : 1 < p) (x y : R p) (h : mul x y = one) : y ≠ zero := by
  intro hy
  rw [hy, mul_zero] at h
  exact one_ne_zero hp h.symm

theorem pow_ne_one_of_inv {n p : ℕ} [NeZero n] [NeZero p] (h : p ∣ n) (hp : 1 < p)
    (x inv : R n) (h_inv : mul inv (sub x one) = one) :
    cast h x ≠ one := by
  intro heq
  have h1 : cast h (mul inv (sub x one)) = cast h one := by rw [h_inv]
  rw [cast_mul, cast_sub, heq, cast_one, sub_self, mul_zero] at h1
  exact one_ne_zero hp h1.symm

theorem pow_mod {n : ℕ} (x : R n) (k m : ℕ) (hk : pow x k = one) (hm : pow x m = one) :
    pow x (k % m) = one := by
  have h_pow : mul (pow x (m * (k / m))) (pow x (k % m)) = pow x k := by
    calc mul (pow x (m * (k / m))) (pow x (k % m)) = pow x (m * (k / m) + k % m) := (pow_add _ _ _).symm
      _ = pow x k := by congr 1; exact Nat.div_add_mod k m
  have h_pow2 : pow x (m * (k / m)) = one := by
    rw [pow_mul, hm, pow_one_eq_one]
  rw [h_pow2, one_mul, hk] at h_pow
  exact h_pow

theorem pow_sub {n : ℕ} (x : R n) {M i j : ℕ} (hM : pow x M = one)
    (h_iM : i ≤ M) (h_ij : i ≤ j) (h_eq : pow x i = pow x j) :
    pow x (j - i) = one := by
  have hj : j = i + (j - i) := (Nat.add_sub_of_le h_ij).symm
  have hiM : M = M - i + i := (Nat.sub_add_cancel h_iM).symm
  have h1 : mul (pow x (M - i)) (pow x i) = one := by
    calc mul (pow x (M - i)) (pow x i) = pow x (M - i + i) := (pow_add _ _ _).symm
      _ = pow x M := by rw [←hiM]
      _ = one := hM
  have h2 : mul (pow x (M - i)) (pow x j) = pow x (j - i) := by
    calc mul (pow x (M - i)) (pow x j) = mul (pow x (M - i)) (pow x (i + (j - i))) := by rw [←hj]
      _ = mul (pow x (M - i)) (mul (pow x i) (pow x (j - i))) := by rw [pow_add]
      _ = mul (mul (pow x (M - i)) (pow x i)) (pow x (j - i)) := (mul_assoc _ _ _).symm
      _ = mul one (pow x (j - i)) := by rw [h1]
      _ = pow x (j - i) := one_mul _
  rw [h_eq] at h1
  rw [h1] at h2
  exact h2.symm

theorem pow_gcd {n : ℕ} (x : R n) (m k : ℕ) (hm : pow x m = one) (hk : pow x k = one) :
    pow x (m.gcd k) = one := by
  induction m, k using Nat.gcd.induction with
  | H0 k =>
    rw [Nat.gcd_zero_left]
    exact hk
  | H1 m k h_pos ih =>
    rw [Nat.gcd_rec]
    exact ih (pow_mod x k m hk hm) hm

theorem M_div_facts {g M m : ℕ} (hM : M = 2 * (100943 * 3^m))
    (h_dvd : g ∣ M) (h_lt : g < M) :
    g ∣ (M / 2) ∨ g ∣ (M / 3) ∨ g ∣ (M / 100943) := by
  have hM_pos : 0 < M := by rw [hM]; positivity
  obtain ⟨k, hk⟩ := h_dvd
  have hk_gt1 : 1 < k := by
    by_contra! h
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · rw [Nat.mul_zero] at hk; rw [hk] at hM_pos; exact lt_irrefl 0 hM_pos
    · rw [Nat.mul_one] at hk; rw [hk] at h_lt; exact lt_irrefl _ h_lt
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hk_gt1.ne'
  have hpM : p ∣ M := by rw [hk]; exact dvd_mul_of_dvd_right hp_dvd g
  have hp_eq : p = 2 ∨ p = 3 ∨ p = 100943 := by
    rw [hM] at hpM
    rcases hp_prime.dvd_mul.mp hpM with hp2 | hrest
    · exact Or.inl (by
        have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2
        have : 2 ≤ p := hp_prime.two_le
        omega)
    · rcases hp_prime.dvd_mul.mp hrest with hp100943 | h3
      · right; right
        have h100943 : Nat.Prime 100943 := by norm_num
        rcases (Nat.dvd_prime h100943).mp hp100943 with rfl | rfl
        · exact (hp_prime.ne_one rfl).elim
        · rfl
      · right; left
        have hp3 : p ∣ 3 := hp_prime.dvd_of_dvd_pow h3
        have h3 : Nat.Prime 3 := by norm_num
        rcases (Nat.dvd_prime h3).mp hp3 with rfl | rfl
        · exact (hp_prime.ne_one rfl).elim
        · rfl
  rcases hp_eq with rfl | rfl | rfl
  · left
    obtain ⟨c, hc⟩ := hp_dvd
    have : M = 2 * (g * c) := by rw [hk, hc]; ring
    rw [this, Nat.mul_div_right _ (by norm_num)]
    exact dvd_mul_right g c
  · right; left
    obtain ⟨c, hc⟩ := hp_dvd
    have : M = 3 * (g * c) := by rw [hk, hc]; ring
    rw [this, Nat.mul_div_right _ (by norm_num)]
    exact dvd_mul_right g c
  · right; right
    obtain ⟨c, hc⟩ := hp_dvd
    have : M = 100943 * (g * c) := by rw [hk, hc]; ring
    rw [this, Nat.mul_div_right _ (by norm_num)]
    exact dvd_mul_right g c

theorem order_eq_M_rp {n p M m : ℕ} [NeZero n] [NeZero p] (h : p ∣ n) (hp : 1 < p)
    (x : R n) (hM : M = 2 * (100943 * 3^m))
    (h_pow_M : pow x M = one)
    (inv2 : R n) (h_inv2 : mul inv2 (sub (pow x (M / 2)) one) = one)
    (inv3 : R n) (h_inv3 : mul inv3 (sub (pow x (M / 3)) one) = one)
    (invp : R n) (h_invp : mul invp (sub (pow x (M / 100943)) one) = one)
    (k : ℕ) (hk0 : 0 < k) (hkM : k < M) :
    pow (cast h x) k ≠ one := by
  have h_pow_M_p : pow (cast h x) M = one := by
    rw [←cast_pow, h_pow_M, cast_one]
  have h_pow_2_p : pow (cast h x) (M / 2) ≠ one := by
    rw [←cast_pow]
    exact pow_ne_one_of_inv h hp _ inv2 h_inv2
  have h_pow_3_p : pow (cast h x) (M / 3) ≠ one := by
    rw [←cast_pow]
    exact pow_ne_one_of_inv h hp _ inv3 h_inv3
  have h_pow_p_p : pow (cast h x) (M / 100943) ≠ one := by
    rw [←cast_pow]
    exact pow_ne_one_of_inv h hp _ invp h_invp
  intro hk
  have hg := pow_gcd (cast h x) M k h_pow_M_p hk
  set g := M.gcd k
  have hg_dvd : g ∣ M := Nat.gcd_dvd_left M k
  have hg_lt : g < M := by
    have : g ∣ k := Nat.gcd_dvd_right M k
    have : g ≤ k := Nat.le_of_dvd hk0 this
    omega
  rcases M_div_facts hM hg_dvd hg_lt with h2 | h3 | h_p
  · obtain ⟨c, hc⟩ := h2
    have : pow (cast h x) (M / 2) = one := by
      rw [hc, pow_mul, hg, pow_one_eq_one]
    exact h_pow_2_p this
  · obtain ⟨c, hc⟩ := h3
    have : pow (cast h x) (M / 3) = one := by
      rw [hc, pow_mul, hg, pow_one_eq_one]
    exact h_pow_3_p this
  · obtain ⟨c, hc⟩ := h_p
    have : pow (cast h x) (M / 100943) = one := by
      rw [hc, pow_mul, hg, pow_one_eq_one]
    exact h_pow_p_p this



