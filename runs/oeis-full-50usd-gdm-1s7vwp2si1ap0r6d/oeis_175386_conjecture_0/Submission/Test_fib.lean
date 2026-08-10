import FormalConjectures.Util.ProblemImports

@[ext]
structure Q5 (p : ℕ) where
  x : ZMod p
  y : ZMod p
  deriving DecidableEq

namespace Q5

variable {p : ℕ} [Fact (Nat.Prime p)]

def add (a b : Q5 p) : Q5 p := ⟨a.x + b.x, a.y + b.y⟩
def neg (a : Q5 p) : Q5 p := ⟨-a.x, -a.y⟩
def sub (a b : Q5 p) : Q5 p := ⟨a.x - b.x, a.y - b.y⟩
def mul (a b : Q5 p) : Q5 p := ⟨a.x * b.x + 5 * a.y * b.y, a.x * b.y + a.y * b.x⟩
def zero : Q5 p := ⟨0, 0⟩
def one : Q5 p := ⟨1, 0⟩

instance : Add (Q5 p) := ⟨add⟩
instance : Neg (Q5 p) := ⟨neg⟩
instance : Sub (Q5 p) := ⟨sub⟩
instance : Mul (Q5 p) := ⟨mul⟩
instance : Zero (Q5 p) := ⟨zero⟩
instance : One (Q5 p) := ⟨one⟩

@[simp] lemma add_x (a b : Q5 p) : (a + b).x = a.x + b.x := rfl
@[simp] lemma add_y (a b : Q5 p) : (a + b).y = a.y + b.y := rfl
@[simp] lemma mul_x (a b : Q5 p) : (a * b).x = a.x * b.x + 5 * a.y * b.y := rfl
@[simp] lemma mul_y (a b : Q5 p) : (a * b).y = a.x * b.y + a.y * b.x := rfl
@[simp] lemma neg_x (a : Q5 p) : (-a).x = -a.x := rfl
@[simp] lemma neg_y (a : Q5 p) : (-a).y = -a.y := rfl
@[simp] lemma sub_x (a b : Q5 p) : (a - b).x = a.x - b.x := rfl
@[simp] lemma sub_y (a b : Q5 p) : (a - b).y = a.y - b.y := rfl
@[simp] lemma zero_x : (0 : Q5 p).x = 0 := rfl
@[simp] lemma zero_y : (0 : Q5 p).y = 0 := rfl
@[simp] lemma one_x : (1 : Q5 p).x = 1 := rfl
@[simp] lemma one_y : (1 : Q5 p).y = 0 := rfl

instance : CommRing (Q5 p) where
  add_assoc a b c := by ext <;> (simp; try ring)
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> (simp; try ring)
  mul_assoc a b c := by ext <;> (simp; try ring)
  one_mul a := by ext <;> (simp; try ring)
  mul_one a := by ext <;> (simp; try ring)
  left_distrib a b c := by ext <;> (simp; try ring)
  right_distrib a b c := by ext <;> (simp; try ring)
  mul_comm a b := by ext <;> (simp; try ring)
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  neg_add_cancel a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> (simp; try ring)
  nsmul n a := ⟨(n : ZMod p) * a.x, (n : ZMod p) * a.y⟩
  nsmul_zero a := by ext <;> simp
  nsmul_succ n a := by ext <;> (simp; try ring)
  zsmul n a := ⟨(n : ZMod p) * a.x, (n : ZMod p) * a.y⟩
  zsmul_zero' a := by ext <;> simp
  zsmul_succ' n a := by ext <;> (simp; try ring)
  zsmul_neg' n a := by ext <;> (simp; try ring)

@[simp] lemma natCast_x {p : ℕ} [Fact (Nat.Prime p)] (n : ℕ) : (n : Q5 p).x = (n : ZMod p) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]

@[simp] lemma natCast_y {p : ℕ} [Fact (Nat.Prime p)] (n : ℕ) : (n : Q5 p).y = (0 : ZMod p) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]

@[simp] lemma intCast_x {p : ℕ} [Fact (Nat.Prime p)] (n : ℤ) : (n : Q5 p).x = (n : ZMod p) := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, Int.cast_natCast]
    simp [natCast_x (p := p)]
  | negSucc n =>
    have h_cast : (Int.negSucc n : Q5 p) = - (n + 1 : Q5 p) := Int.cast_negSucc n
    rw [h_cast]
    simp [natCast_x (p := p)]

@[simp] lemma intCast_y {p : ℕ} [Fact (Nat.Prime p)] (n : ℤ) : (n : Q5 p).y = (0 : ZMod p) := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, Int.cast_natCast]
    simp [natCast_y (p := p)]
  | negSucc n =>
    have h_cast : (Int.negSucc n : Q5 p) = - (n + 1 : Q5 p) := Int.cast_negSucc n
    rw [h_cast]
    simp [natCast_y (p := p)]

@[simp] lemma ofNat_x {p : ℕ} [Fact (Nat.Prime p)] (n : ℕ) [h : Nat.AtLeastTwo n] : (no_index (OfNat.ofNat n : Q5 p)).x = OfNat.ofNat n := by
  change (n : Q5 p).x = (n : ZMod p)
  exact natCast_x (p := p) n

@[simp] lemma ofNat_y {p : ℕ} [Fact (Nat.Prime p)] (n : ℕ) [h : Nat.AtLeastTwo n] : (no_index (OfNat.ofNat n : Q5 p)).y = 0 := by
  change (n : Q5 p).y = (0 : ZMod p)
  exact natCast_y (p := p) n

instance (p' : ℕ) [Fact (Nat.Prime p')] : CharP (Q5 p') p' where
  cast_eq_zero_iff n := by
    constructor
    · intro h
      have h_x : (n : Q5 p').x = 0 := by rw [h]; rfl
      rw [natCast_x (p := p')] at h_x
      rwa [CharP.cast_eq_zero_iff (ZMod p') p'] at h_x
    · intro h
      have h_z : (n : ZMod p') = 0 := by rwa [CharP.cast_eq_zero_iff (ZMod p') p']
      ext
      · rw [natCast_x (p := p'), h_z]; rfl
      · rw [natCast_y (p := p')]; rfl

def cast_ZMod (d : ZMod p) : Q5 p := ⟨d, 0⟩
@[simp] lemma cast_ZMod_x (d : ZMod p) : (cast_ZMod d).x = d := rfl
@[simp] lemma cast_ZMod_y (d : ZMod p) : (cast_ZMod d).y = 0 := rfl

-- Let's define the elements
def half (p : ℕ) [Fact (Nat.Prime p)] : ZMod p := (2 : ZMod p)⁻¹

theorem h2_nz (hp_gt : p ≥ 13) : (2 : ZMod p) ≠ 0 := by
  intro hc
  have hp : Nat.Prime p := Fact.out
  have h_cast : ((2 : ℕ) : ZMod p) = 0 := hc
  rw [CharP.cast_eq_zero_iff (ZMod p) p] at h_cast
  have h_le : p ≤ 2 := Nat.le_of_dvd (by decide) h_cast
  omega

def phi (p : ℕ) [Fact (Nat.Prime p)] : Q5 p := ⟨half p, half p⟩
def psi (p : ℕ) [Fact (Nat.Prime p)] : Q5 p := ⟨half p, -half p⟩
def omega (p : ℕ) [Fact (Nat.Prime p)] : Q5 p := ⟨0, 1⟩

-- Basic properties
theorem phi_add_psi (hp_gt : p ≥ 13) : phi p + psi p = 1 := by
  ext
  · simp [phi, psi, half]
    have : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ (h2_nz hp_gt)
    linear_combination this
  · simp [phi, psi, half]

theorem phi_mul_psi (hp_gt : p ≥ 13) : phi p * psi p = -1 := by
  ext
  · simp [phi, psi, half]
    have : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ (h2_nz hp_gt)
    linear_combination -(2 * (2 : ZMod p)⁻¹ + 1) * this
  · simp [phi, psi, half]

theorem phi_sq (hp_gt : p ≥ 13) : phi p * phi p = phi p + 1 := by
  ext
  · simp [phi, half]
    have : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ (h2_nz hp_gt)
    linear_combination (3 * (2 : ZMod p)⁻¹ + 1) * this
  · simp [phi, half]
    have : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ (h2_nz hp_gt)
    linear_combination (2 : ZMod p)⁻¹ * this

theorem psi_sq (hp_gt : p ≥ 13) : psi p * psi p = psi p + 1 := by
  ext
  · simp [psi, half]
    have : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ (h2_nz hp_gt)
    linear_combination (3 * (2 : ZMod p)⁻¹ + 1) * this
  · simp [psi, half]
    have : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ (h2_nz hp_gt)
    linear_combination -(2 : ZMod p)⁻¹ * this

theorem fib_step_identity (A B : Q5 p) (hp_gt : p ≥ 13) :
    (phi p) ^ 2 * A - (psi p) ^ 2 * B = (phi p * A - psi p * B) + (A - B) := by
  have h_phi := phi_sq (p := p) hp_gt
  have h_psi := psi_sq (p := p) hp_gt
  rw [pow_two (phi p), pow_two (psi p)] at *
  rw [h_phi, h_psi]
  ext <;> (simp; try ring)

theorem fib_formula_simult (hp_gt : p ≥ 13) (n : ℕ) :
    (phi p) ^ n - (psi p) ^ n = omega p * cast_ZMod (Nat.fib n : ZMod p) ∧
    (phi p) ^ (n + 1) - (psi p) ^ (n + 1) = omega p * cast_ZMod (Nat.fib (n + 1) : ZMod p) := by
  induction n with
  | zero =>
    constructor
    · ext <;> (simp [phi, psi, half, omega]; try ring)
    · ext
      · simp [phi, psi, half, omega]
      · simp [phi, psi, half, omega]
        have : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ (h2_nz hp_gt)
        linear_combination this
  | succ n ih =>
    rcases ih with ⟨ih1, ih2⟩
    refine ⟨ih2, ?_⟩
    have h_rec := fib_step_identity ((phi p) ^ n) ((psi p) ^ n) hp_gt
    have h_pow1 : (phi p) ^ (n + 2) = (phi p) ^ 2 * (phi p) ^ n := by ring
    have h_pow2 : (psi p) ^ (n + 2) = (psi p) ^ 2 * (psi p) ^ n := by ring
    rw [h_pow1, h_pow2, h_rec]
    have h_pow3 : phi p * (phi p) ^ n = (phi p) ^ (n + 1) := by ring
    have h_pow4 : psi p * (psi p) ^ n = (psi p) ^ (n + 1) := by ring
    rw [h_pow3, h_pow4]
    rw [ih1, ih2]
    ext
    · simp [omega]
    · simp [omega]
      rw [Nat.fib_add_two]
      push_cast
      ring

theorem fib_formula (hp_gt : p ≥ 13) (n : ℕ) :
    (phi p) ^ n - (psi p) ^ n = omega p * cast_ZMod (Nat.fib n : ZMod p) :=
  (fib_formula_simult hp_gt n).1

theorem fib_dvd_iff_pow_eq (hp_gt : p ≥ 13) (a : ℕ) :
    p ∣ Nat.fib a ↔ (phi p) ^ a = (psi p) ^ a := by
  have : p ∣ Nat.fib a ↔ (Nat.fib a : ZMod p) = 0 := by
    rw [CharP.cast_eq_zero_iff (ZMod p) p]
  rw [this]
  constructor
  · intro h
    have h1 := fib_formula hp_gt a
    rw [h] at h1
    have h_sub : (phi p) ^ a - (psi p) ^ a = 0 := by
      have h_zero : omega p * cast_ZMod (0 : ZMod p) = 0 := by
        ext <;> simp [omega]
      rw [h1, h_zero]
    ext
    · have hx : ((phi p) ^ a - (psi p) ^ a).x = 0 := by rw [h_sub]; rfl
      simp at hx
      linear_combination hx
    · have hy : ((phi p) ^ a - (psi p) ^ a).y = 0 := by rw [h_sub]; rfl
      simp at hy
      linear_combination hy
  · intro h
    have h1 := fib_formula hp_gt a
    rw [h] at h1
    have h_zero : (psi p) ^ a - (psi p) ^ a = 0 := by
      ext <;> simp
    rw [h_zero] at h1
    have h_y : (omega p * cast_ZMod (Nat.fib a : ZMod p)).y = 0 := by
      rw [← h1]
      rfl
    simp [omega] at h_y
    exact h_y

theorem sq_eq_one (x : ZMod p) (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by
    calc (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
    _ = 0 := by linear_combination h
  cases mul_eq_zero.mp this with
  | inl h1 => left; linear_combination h1
  | inr h2 => right; linear_combination h2

theorem h5_pow_eq_one (hp_gt : p ≥ 13) : (5 : ZMod p) ^ (p - 1) = 1 := by
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro hc
    have hp : Nat.Prime p := Fact.out
    have h_cast : ((5 : ℕ) : ZMod p) = 0 := hc
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h_cast
    have : p ≤ 5 := Nat.le_of_dvd (by decide) h_cast
    omega
  exact ZMod.pow_card_sub_one_eq_one h5

theorem omega_sq : omega p * omega p = 5 := by
  ext <;> (simp [omega]; try ring)

theorem omega_pow_simult (n : ℕ) :
    (omega p) ^ (2 * n) = cast_ZMod ((5 : ZMod p) ^ n) ∧
    (omega p) ^ (2 * n + 1) = cast_ZMod ((5 : ZMod p) ^ n) * omega p := by
  induction n with
  | zero =>
    constructor
    · ext <;> (simp [omega]; try ring)
    · ext <;> (simp [omega]; try ring)
  | succ n ih =>
    rcases ih with ⟨ih1, ih2⟩
    have h_rec1 : (omega p) ^ (2 * (n + 1)) = (omega p) ^ (2 * n + 1) * omega p := by
      have : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
      rw [this, pow_succ]
    have h_rec2 : (omega p) ^ (2 * (n + 1) + 1) = (omega p) ^ (2 * (n + 1)) * omega p := by
      rw [pow_succ]
    constructor
    · rw [h_rec1, ih2]
      rw [mul_assoc, omega_sq]
      ext <;> (simp; try ring)
    · rw [h_rec2]
      have h_first : (omega p) ^ (2 * (n + 1)) = cast_ZMod ((5 : ZMod p) ^ (n + 1)) := by
        rw [h_rec1, ih2, mul_assoc, omega_sq]
        ext <;> (simp; try ring)
      rw [h_first]

theorem omega_pow_p (hp_gt : p ≥ 13) :
    (omega p) ^ p = cast_ZMod ((5 : ZMod p) ^ ((p - 1) / 2)) * omega p := by
  have hp : Nat.Prime p := Fact.out
  have h_div : p = 2 * ((p - 1) / 2) + 1 := by
    have h_odd : p % 2 = 1 := by
      have : p > 2 := by omega
      have h_even : ¬ 2 ∣ p := by
        intro hc
        have : p = 2 := (hp.eq_one_or_self_of_dvd 2 hc).resolve_left (by decide) |>.symm
        omega
      have h_mod : p % 2 < 2 := Nat.mod_lt p (by decide)
      have : p % 2 ≠ 0 := by
        intro hc
        have : 2 ∣ p := Nat.dvd_of_mod_eq_zero hc
        have : p = 2 := (hp.eq_one_or_self_of_dvd 2 this).resolve_left (by decide) |>.symm
        omega
      omega
    omega
  have h_eq : (omega p) ^ p = (omega p) ^ (2 * ((p - 1) / 2) + 1) := by
    congr 1
  rw [h_eq]
  exact (omega_pow_simult ((p - 1) / 2)).2

theorem cast_ZMod_pow (x : ZMod p) (k : ℕ) : (cast_ZMod x) ^ k = cast_ZMod (x ^ k) := by
  induction k with
  | zero => ext <;> (simp; try ring)
  | succ k ih =>
    rw [pow_succ, pow_succ, ih]
    ext <;> (simp; try ring)

theorem natCast_pow_p (n : ℕ) : (n : Q5 p) ^ p = (n : Q5 p) := by
  have h_eq : (n : Q5 p) = cast_ZMod (p := p) (n : ZMod p) := by ext <;> simp
  rw [h_eq]
  rw [cast_ZMod_pow]
  rw [ZMod.pow_card]

theorem cast_ZMod_pow_p (x : ZMod p) : (cast_ZMod x) ^ p = cast_ZMod x := by
  rw [cast_ZMod_pow, ZMod.pow_card]

lemma phi_eq_cast (hp_gt : p ≥ 13) : phi p = cast_ZMod (half p) + cast_ZMod (half p) * omega p := by
  ext <;> (simp [phi, omega]; try ring)

lemma psi_eq_cast (hp_gt : p ≥ 13) : psi p = cast_ZMod (half p) + cast_ZMod (-half p) * omega p := by
  ext <;> (simp [psi, omega]; try ring)

lemma phi_pow_p (hp_gt : p ≥ 13) :
    (phi p) ^ p = cast_ZMod (half p) + cast_ZMod (half p) * (cast_ZMod ((5 : ZMod p) ^ ((p - 1) / 2)) * omega p) := by
  rw [phi_eq_cast hp_gt, add_pow_char, mul_pow, cast_ZMod_pow_p, omega_pow_p hp_gt]

lemma psi_pow_p (hp_gt : p ≥ 13) :
    (psi p) ^ p = cast_ZMod (half p) + cast_ZMod (-half p) * (cast_ZMod ((5 : ZMod p) ^ ((p - 1) / 2)) * omega p) := by
  rw [psi_eq_cast hp_gt, add_pow_char, mul_pow, cast_ZMod_pow_p, cast_ZMod_pow_p, omega_pow_p hp_gt]

lemma phi_pow_p_sub_psi_pow_p (hp_gt : p ≥ 13) :
    (phi p) ^ p - (psi p) ^ p = cast_ZMod ((5 : ZMod p) ^ ((p - 1) / 2)) * omega p := by
  rw [phi_pow_p hp_gt, psi_pow_p hp_gt]
  have h_half : half p * 2 = 1 := by
    rw [mul_comm]
    exact mul_inv_cancel₀ (h2_nz hp_gt)
  ext
  · simp [omega]
  · simp [omega]
    linear_combination (5 : ZMod p) ^ ((p - 1) / 2) * h_half

lemma phi_psi_pow_p_cases (hp_gt : p ≥ 13) :
    ((5 : ZMod p) ^ ((p - 1) / 2) = 1 ∧ (phi p) ^ p = phi p ∧ (psi p) ^ p = psi p) ∨
    ((5 : ZMod p) ^ ((p - 1) / 2) = -1 ∧ (phi p) ^ p = psi p ∧ (psi p) ^ p = phi p) := by
  have hc_sq : ((5 : ZMod p) ^ ((p - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, ← h5_pow_eq_one (p := p) hp_gt]
    congr 1
    have hp : Nat.Prime p := Fact.out
    have h_odd : p % 2 = 1 := by
      have : p > 2 := by omega
      have h_even : ¬ 2 ∣ p := by
        intro hc
        have : p = 2 := (hp.eq_one_or_self_of_dvd 2 hc).resolve_left (by decide) |>.symm
        omega
      omega
    omega
  have hc_cases := sq_eq_one ((5 : ZMod p) ^ ((p - 1) / 2)) hc_sq
  rcases hc_cases with hc1 | hc2
  · left
    refine ⟨hc1, ?_, ?_⟩
    · rw [phi_pow_p hp_gt, hc1]
      ext <;> (simp [phi, omega]; try ring)
    · rw [psi_pow_p hp_gt, hc1]
      ext <;> (simp [psi, omega]; try ring)
  · right
    refine ⟨hc2, ?_, ?_⟩
    · rw [phi_pow_p hp_gt, hc2]
      ext <;> (simp [phi, psi, omega]; try ring)
    · rw [psi_pow_p hp_gt, hc2]
      ext <;> (simp [phi, psi, omega]; try ring)

lemma prime_entry_point_bound_helper (hp_gt : p ≥ 13) :
    p ∣ Nat.fib (p - 1) ∨ p ∣ Nat.fib (p + 1) := by
  have hc_cases := phi_psi_pow_p_cases hp_gt
  rcases hc_cases with h_one | h_neg_one
  · left
    rw [fib_dvd_iff_pow_eq hp_gt]
    have h_phi : (phi p) ^ (p - 1) * phi p = phi p := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      exact h_one.2.1
    have h_psi : (psi p) ^ (p - 1) * psi p = psi p := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      exact h_one.2.2
    have h_phi_eq : (phi p) ^ (p - 1) = 1 := by
      have h_eq : (phi p) ^ (p - 1) * -1 = -1 := by
        calc (phi p) ^ (p - 1) * -1 = (phi p) ^ (p - 1) * (phi p * psi p) := by rw [← phi_mul_psi hp_gt]
        _ = (phi p) ^ (p - 1) * phi p * psi p := by ring
        _ = phi p * psi p := by rw [h_phi]
        _ = -1 := phi_mul_psi hp_gt
      calc (phi p) ^ (p - 1) = (phi p) ^ (p - 1) * -1 * -1 := by ring
      _ = -1 * -1 := by rw [h_eq]
      _ = 1 := by ring
    have h_psi_eq : (psi p) ^ (p - 1) = 1 := by
      have h_eq : (psi p) ^ (p - 1) * -1 = -1 := by
        calc (psi p) ^ (p - 1) * -1 = (psi p) ^ (p - 1) * (psi p * phi p) := by rw [← phi_mul_psi hp_gt, mul_comm (phi p) (psi p)]
        _ = (psi p) ^ (p - 1) * psi p * phi p := by ring
        _ = psi p * phi p := by rw [h_psi]
        _ = -1 := by rw [mul_comm, phi_mul_psi hp_gt]
      calc (psi p) ^ (p - 1) = (psi p) ^ (p - 1) * -1 * -1 := by ring
      _ = -1 * -1 := by rw [h_eq]
      _ = 1 := by ring
    rw [h_phi_eq, h_psi_eq]
  · right
    rw [fib_dvd_iff_pow_eq hp_gt]
    have h_phi_eq : (phi p) ^ (p + 1) = -1 := by
      calc (phi p) ^ (p + 1) = (phi p) ^ p * phi p := by ring
      _ = psi p * phi p := by rw [h_neg_one.2.1]
      _ = phi p * psi p := by ring
      _ = -1 := phi_mul_psi hp_gt
    have h_psi_eq : (psi p) ^ (p + 1) = -1 := by
      calc (psi p) ^ (p + 1) = (psi p) ^ p * psi p := by ring
      _ = phi p * psi p := by rw [h_neg_one.2.2]
      _ = -1 := phi_mul_psi hp_gt
    rw [h_phi_eq, h_psi_eq]

end Q5
