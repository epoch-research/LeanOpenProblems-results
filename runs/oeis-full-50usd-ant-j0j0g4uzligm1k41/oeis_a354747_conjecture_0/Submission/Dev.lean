import FormalConjectures.Util.ProblemImports

open Nat Set

namespace NPlusOne

/-- The quadratic ring `R[θ]/(θ² - p·θ + 1)`, elements `re + im·θ`. -/
structure QQ (R : Type*) (p : R) where
  re : R
  im : R
deriving DecidableEq

namespace QQ

variable {R : Type*} [CommRing R] {p : R}

@[ext] theorem ext' {x y : QQ R p} (h1 : x.re = y.re) (h2 : x.im = y.im) : x = y := by
  cases x; cases y; simp_all

instance : Zero (QQ R p) := ⟨⟨0, 0⟩⟩
instance : One (QQ R p) := ⟨⟨1, 0⟩⟩
instance : Add (QQ R p) := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg (QQ R p) := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Sub (QQ R p) := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
-- (a+bθ)(c+dθ) = ac + (ad+bc)θ + bd θ², θ² = pθ - 1
-- = (ac - bd) + (ad+bc+ p·bd)θ
instance : Mul (QQ R p) := ⟨fun x y => ⟨x.re*y.re - x.im*y.im, x.re*y.im + x.im*y.re + p*(x.im*y.im)⟩⟩

@[simp] theorem zero_re : (0 : QQ R p).re = 0 := rfl
@[simp] theorem zero_im : (0 : QQ R p).im = 0 := rfl
@[simp] theorem one_re : (1 : QQ R p).re = 1 := rfl
@[simp] theorem one_im : (1 : QQ R p).im = 0 := rfl
@[simp] theorem add_re (x y : QQ R p) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : QQ R p) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : QQ R p) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : QQ R p) : (-x).im = -x.im := rfl
@[simp] theorem sub_re (x y : QQ R p) : (x - y).re = x.re - y.re := rfl
@[simp] theorem sub_im (x y : QQ R p) : (x - y).im = x.im - y.im := rfl
@[simp] theorem mul_re (x y : QQ R p) : (x * y).re = x.re*y.re - x.im*y.im := rfl
@[simp] theorem mul_im (x y : QQ R p) : (x * y).im = x.re*y.im + x.im*y.re + p*(x.im*y.im) := rfl

instance : CommRing (QQ R p) where
  add_assoc := by intros; ext <;> simp <;> ring
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp <;> ring
  mul_assoc := by intros; ext <;> simp <;> ring
  zero_mul := by intros; ext <;> simp
  mul_zero := by intros; ext <;> simp
  one_mul := by intros; ext <;> simp
  mul_one := by intros; ext <;> simp
  left_distrib := by intros; ext <;> simp <;> ring
  right_distrib := by intros; ext <;> simp <;> ring
  mul_comm := by intros; ext <;> simp <;> ring
  neg_add_cancel := by intros; ext <;> simp
  sub_eq_add_neg := by intros; ext <;> simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

@[simp] theorem natCast_re (n : ℕ) : ((n : QQ R p)).re = (n : R) := by
  induction n with
  | zero => simp
  | succ k ih => push_cast; simp [ih]
@[simp] theorem natCast_im (n : ℕ) : ((n : QQ R p)).im = 0 := by
  induction n with
  | zero => simp
  | succ k ih => push_cast; simp [ih]
@[simp] theorem intCast_re (n : ℤ) : ((n : QQ R p)).re = (n : R) := by
  cases n with
  | ofNat k => simp
  | negSucc k => push_cast; simp
@[simp] theorem intCast_im (n : ℤ) : ((n : QQ R p)).im = 0 := by
  cases n with
  | ofNat k => simp
  | negSucc k => push_cast; simp

/-- The scalar (constant) embedding `R → QQ R p` as a ring hom. -/
def C : R →+* QQ R p where
  toFun c := ⟨c, 0⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp <;> ring
  map_zero' := rfl
  map_add' a b := by ext <;> simp

@[simp] theorem C_re (c : R) : (C c : QQ R p).re = c := rfl
@[simp] theorem C_im (c : R) : (C c : QQ R p).im = 0 := rfl

/-- The distinguished element `θ`. -/
def theta : QQ R p := ⟨0, 1⟩

/-- The conjugate `p - θ`, which is the inverse of `θ`. -/
def thetaBar : QQ R p := ⟨p, -1⟩

@[simp] theorem theta_re : (theta : QQ R p).re = 0 := rfl
@[simp] theorem theta_im : (theta : QQ R p).im = 1 := rfl

theorem theta_mul_bar : (theta : QQ R p) * thetaBar = 1 := by
  ext <;> simp [theta, thetaBar] <;> ring

theorem theta_sq : (theta : QQ R p) ^ 2 = C p * theta - 1 := by
  rw [sq]; ext <;> simp [theta, C] <;> ring

theorem bar_mul_theta : (thetaBar : QQ R p) * theta = 1 := by
  rw [mul_comm]; exact theta_mul_bar

/-- `θ` as a unit. -/
def thetaU : (QQ R p)ˣ := ⟨theta, thetaBar, theta_mul_bar, bar_mul_theta⟩

theorem isUnit_theta : IsUnit (theta : QQ R p) := ⟨thetaU, rfl⟩

/-- Base change along a ring hom `f : R →+* R'`. -/
def map {R' : Type*} [CommRing R'] (f : R →+* R') : QQ R p →+* QQ R' (f p) where
  toFun x := ⟨f x.re, f x.im⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp [map_sub, map_add, map_mul] <;> ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp] theorem map_re {R' : Type*} [CommRing R'] (f : R →+* R') (x : QQ R p) :
    (map f x).re = f x.re := rfl
@[simp] theorem map_im {R' : Type*} [CommRing R'] (f : R →+* R') (x : QQ R p) :
    (map f x).im = f x.im := rfl

theorem map_theta {R' : Type*} [CommRing R'] (f : R →+* R') :
    map f (theta : QQ R p) = (theta : QQ R' (f p)) := by ext <;> simp [theta]

theorem eq_zero_iff (x : QQ R p) : x = 0 ↔ x.re = 0 ∧ x.im = 0 := by
  constructor
  · intro h; subst h; simp
  · intro ⟨h1, h2⟩; ext <;> simp [h1, h2]

instance charP (c : ℕ) [CharP R c] : CharP (QQ R p) c := CharP.mk fun n => by
  rw [eq_zero_iff]
  simp only [natCast_re, natCast_im, and_true]
  exact CharP.cast_eq_zero_iff R c n

/-- Frobenius identity: over `ZMod r` (r prime), `(θ^r)` again satisfies the quadratic. -/
theorem frob_theta_sq {r : ℕ} [Fact r.Prime] (p : ZMod r) :
    ((theta : QQ (ZMod r) p) ^ r) ^ 2 = C p * theta ^ r - 1 := by
  have key : ((theta : QQ (ZMod r) p) ^ 2) ^ r = C p * theta ^ r - 1 := by
    rw [theta_sq, sub_pow_char, mul_pow, one_pow, ← map_pow, ZMod.pow_card]
  rw [← pow_mul, Nat.mul_comm, pow_mul] at key
  exact key

theorem theta_add_bar : (theta : QQ R p) + thetaBar = C p := by
  ext <;> simp [theta, thetaBar]

/-- Key factorization coming from Frobenius. -/
theorem frob_factor {r : ℕ} [Fact r.Prime] (p : ZMod r) :
    ((theta : QQ (ZMod r) p) ^ r - theta) * (theta ^ r - thetaBar) = 0 := by
  have hy := frob_theta_sq p
  have hsum : (theta : QQ (ZMod r) p) + thetaBar = C p := theta_add_bar
  have hprod : (theta : QQ (ZMod r) p) * thetaBar = 1 := theta_mul_bar
  have expand : ((theta : QQ (ZMod r) p) ^ r - theta) * (theta ^ r - thetaBar)
      = (theta ^ r) ^ 2 - C p * theta ^ r + 1 := by
    rw [← hsum, ← hprod]; ring
  rw [expand, hy]; ring

/-- One root yields a one–dimensional representation `QQ R p →+* R`. -/
def evalAt (u : R) (hu : u * u = p * u - 1) : QQ R p →+* R where
  toFun x := x.re + x.im * u
  map_one' := by simp
  map_mul' x y := by
    simp only [mul_re, mul_im]; linear_combination (-(x.im * y.im)) * hu
  map_zero' := by simp
  map_add' x y := by simp only [add_re, add_im]; ring

@[simp] theorem evalAt_theta (u : R) (hu : u * u = p * u - 1) :
    evalAt u hu (theta : QQ R p) = u := by simp [evalAt, theta]

theorem evalAt_apply (u : R) (hu : u * u = p * u - 1) (x : QQ R p) :
    evalAt u hu x = x.re + x.im * u := rfl

/-- The norm form. -/
def nrm (x : QQ R p) : R := x.re ^ 2 + p * x.re * x.im + x.im ^ 2

/-- Conjugation `a + bθ ↦ a + b(p - θ)`. -/
def conj : QQ R p →+* QQ R p where
  toFun x := ⟨x.re + p * x.im, -x.im⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp <;> ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp <;> ring

theorem mul_conj (x : QQ R p) : x * conj x = C (nrm x) := by
  ext <;> simp [conj, nrm, C] <;> ring

/-- `(r-1, r+1)` factorisation. -/
theorem factor_pm {r : ℕ} [Fact r.Prime] (p : ZMod r) :
    ((theta : QQ (ZMod r) p) ^ (r - 1) - 1) * (theta ^ (r + 1) - 1) = 0 := by
  have hr1 : 1 ≤ r := (Fact.out (p := r.Prime)).one_lt.le
  have hpow : (theta : QQ (ZMod r) p) ^ r = theta ^ (r - 1) * theta := by
    rw [← pow_succ, Nat.sub_add_cancel hr1]
  have key : (thetaBar : QQ (ZMod r) p) * theta ^ r = theta ^ (r - 1) := by
    rw [hpow, show (thetaBar : QQ (ZMod r) p) * (theta ^ (r-1) * theta)
      = (thetaBar * theta) * theta ^ (r-1) from by ring, bar_mul_theta, one_mul]
  have e1 : (thetaBar : QQ (ZMod r) p) * (theta ^ r - theta) = theta ^ (r - 1) - 1 := by
    rw [mul_sub, key, bar_mul_theta]
  have e2 : (theta : QQ (ZMod r) p) * (theta ^ r - thetaBar) = theta ^ (r + 1) - 1 := by
    rw [mul_sub, theta_mul_bar, ← _root_.pow_succ']
  rw [← e1, ← e2]
  calc (thetaBar : QQ (ZMod r) p) * (theta ^ r - theta) * (theta * (theta ^ r - thetaBar))
      = (thetaBar * theta) * ((theta ^ r - theta) * (theta ^ r - thetaBar)) := by ring
    _ = 0 := by rw [frob_factor]; ring

/-- If the quadratic has no root, the norm vanishes only at `0`. -/
theorem nrm_eq_zero_imp {r : ℕ} [Fact r.Prime] {p : ZMod r}
    (hno : ∀ u : ZMod r, u * u ≠ p * u - 1) (x : QQ (ZMod r) p) (h : nrm x = 0) : x = 0 := by
  by_cases hb : x.im = 0
  · rw [eq_zero_iff]
    refine ⟨?_, hb⟩
    have hre : x.re ^ 2 = 0 := by rw [nrm, hb] at h; linear_combination h
    exact pow_eq_zero_iff (by norm_num) |>.mp hre
  · exfalso
    apply hno (-x.re / x.im)
    have hb' : x.im ≠ 0 := hb
    field_simp
    rw [nrm] at h
    linear_combination h

/-- If the quadratic has no root, every nonzero element is a unit. -/
theorem isUnit_of_ne_zero {r : ℕ} [Fact r.Prime] {p : ZMod r}
    (hno : ∀ u : ZMod r, u * u ≠ p * u - 1) (x : QQ (ZMod r) p) (hx : x ≠ 0) : IsUnit x := by
  have hnrm : nrm x ≠ 0 := fun h => hx (nrm_eq_zero_imp hno x h)
  have : IsUnit (C (nrm x) : QQ (ZMod r) p) := by
    have := (isUnit_iff_ne_zero (a := nrm x)).2 hnrm
    exact this.map (C : ZMod r →+* QQ (ZMod r) p)
  rw [← mul_conj] at this
  exact (isUnit_of_mul_isUnit_left this)

/-- The core order dichotomy: `θ^(r-1) = 1` or `θ^(r+1) = 1`. -/
theorem theta_pow_pm {r : ℕ} [Fact r.Prime] (p : ZMod r) (hD : (p ^ 2 - 4 : ZMod r) ≠ 0) :
    (theta : QQ (ZMod r) p) ^ (r - 1) = 1 ∨ (theta : QQ (ZMod r) p) ^ (r + 1) = 1 := by
  by_cases hroot : ∃ u : ZMod r, u * u = p * u - 1
  · -- split case
    obtain ⟨u, hu⟩ := hroot
    left
    set u' := p - u with hu'def
    have hu' : u' * u' = p * u' - 1 := by rw [hu'def]; linear_combination hu
    have huu' : u * u' = 1 := by rw [hu'def]; linear_combination -hu
    have hune : u ≠ 0 := by intro h; rw [h] at huu'; simp at huu'
    have hu'ne : u' ≠ 0 := by intro h; rw [h] at huu'; simp at huu'
    have hdiff : u - u' ≠ 0 := by
      intro hcon
      apply hD
      have hp : p = 2 * u := by rw [hu'def] at hcon; linear_combination -hcon
      rw [hp] at hu ⊢
      linear_combination (-4 : ZMod r) * hu
    set x := (theta : QQ (ZMod r) p) ^ (r - 1) with hxdef
    have h1 : x.re + x.im * u = 1 := by
      rw [hxdef, ← evalAt_apply u hu, map_pow, evalAt_theta]
      exact ZMod.pow_card_sub_one_eq_one hune
    have h2 : x.re + x.im * u' = 1 := by
      rw [hxdef, ← evalAt_apply u' hu', map_pow, evalAt_theta]
      exact ZMod.pow_card_sub_one_eq_one hu'ne
    have hzero : x.im * (u - u') = 0 := by linear_combination h1 - h2
    have him : x.im = 0 := by
      rcases mul_eq_zero.mp hzero with h | h
      · exact h
      · exact absurd h hdiff
    have hre : x.re = 1 := by rw [him] at h1; simpa using h1
    ext
    · simpa using hre
    · simpa using him
  · -- no-root case: domain
    push_neg at hroot
    have hfac := factor_pm p
    by_cases hA : (theta : QQ (ZMod r) p) ^ (r - 1) - 1 = 0
    · left; exact sub_eq_zero.mp hA
    · right
      have hAU := isUnit_of_ne_zero hroot _ hA
      have hB : (theta : QQ (ZMod r) p) ^ (r + 1) - 1 = 0 :=
        (hAU.mul_right_eq_zero).mp hfac
      exact sub_eq_zero.mp hB

end QQ

open QQ

/-- Valuation lemma: if `d ∣ N₁`, `¬ d ∣ N₁/3`, and `3^m ∣ N₁`, then `3^m ∣ d`. -/
theorem pow_three_dvd_orderOf {d N1 : ℕ} (hd0 : 0 < d) (hN1 : 0 < N1) (m : ℕ)
    (hdvd : d ∣ N1) (h3 : 3 ∣ N1) (hndvd : ¬ d ∣ (N1 / 3)) (hm3 : 3 ^ m ∣ N1) :
    3 ^ m ∣ d := by
  have hp3 : Nat.Prime 3 := by norm_num
  rw [hp3.pow_dvd_iff_le_factorization hd0.ne']
  rw [hp3.pow_dvd_iff_le_factorization hN1.ne'] at hm3
  have hle : d.factorization 3 ≤ N1.factorization 3 :=
    (Nat.factorization_le_iff_dvd hd0.ne' hN1.ne').2 hdvd 3
  have h0 : N1 / 3 ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd hN1 h3) (by norm_num); omega
  have hge : N1.factorization 3 ≤ d.factorization 3 := by
    by_contra hlt
    push_neg at hlt
    apply hndvd
    rw [← Nat.factorization_le_iff_dvd hd0.ne' h0, Finsupp.le_def]
    intro p
    rw [Nat.factorization_div h3, Finsupp.tsub_apply]
    by_cases hp : p = 3
    · subst hp; rw [Nat.Prime.factorization_self hp3]; omega
    · have hz : (Nat.factorization 3) p = 0 := by
        rw [hp3.factorization, Finsupp.single_apply, if_neg (fun h => hp h.symm)]
      rw [hz, Nat.sub_zero]
      exact (Nat.factorization_le_iff_dvd hd0.ne' hN1.ne').2 hdvd p
  omega

/-- For a prime factor `r` of `N`, the certificate forces `3^m ∣ r-1 ∨ 3^m ∣ r+1`. -/
theorem key_dvd {N : ℕ} (hN1 : 1 < N) {P : ZMod N} {m : ℕ}
    (hpow : (theta : QQ (ZMod N) P) ^ (N + 1) = 1)
    (hunit : IsUnit (((theta : QQ (ZMod N) P) ^ ((N + 1) / 3)).im))
    (hDcop : IsUnit ((P ^ 2 - 4 : ZMod N)))
    (h3 : 3 ∣ (N + 1)) (hm3 : 3 ^ m ∣ (N + 1))
    {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ N) :
    3 ^ m ∣ (r - 1) ∨ 3 ^ m ∣ (r + 1) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hrN : (r : ℕ) ∣ N := hrdvd
  let f : ZMod N →+* ZMod r := ZMod.castHom hrN (ZMod r)
  set Q := f P with hQ
  -- transfer θ^(N+1)=1
  have hpow' : (theta : QQ (ZMod r) Q) ^ (N + 1) = 1 := by
    have := congrArg (QQ.map f) hpow
    rwa [map_pow, map_theta, map_one] at this
  have hfin : IsOfFinOrder (theta : QQ (ZMod r) Q) :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨N + 1, by omega, hpow'⟩
  have hord_pos : 0 < orderOf (theta : QQ (ZMod r) Q) := hfin.orderOf_pos
  have hdvd_ord : orderOf (theta : QQ (ZMod r) Q) ∣ (N + 1) :=
    orderOf_dvd_of_pow_eq_one hpow'
  -- transfer the unit / non-triviality
  have hne1 : (theta : QQ (ZMod r) Q) ^ ((N + 1) / 3) ≠ 1 := by
    intro hcon
    have him : (((theta : QQ (ZMod r) Q) ^ ((N + 1) / 3)).im) = 0 := by
      rw [hcon]; simp
    have htrans : (((theta : QQ (ZMod r) Q) ^ ((N + 1) / 3)).im)
        = f (((theta : QQ (ZMod N) P) ^ ((N + 1) / 3)).im) := by
      rw [← map_theta f, ← map_pow, map_im]
    rw [htrans] at him
    exact (hunit.map f).ne_zero him
  have hndvd_ord : ¬ orderOf (theta : QQ (ZMod r) Q) ∣ ((N + 1) / 3) := by
    intro hcon
    exact hne1 (orderOf_dvd_iff_pow_eq_one.1 hcon)
  have h3m_ord : 3 ^ m ∣ orderOf (theta : QQ (ZMod r) Q) :=
    pow_three_dvd_orderOf hord_pos (by omega) m hdvd_ord h3 hndvd_ord hm3
  -- D ≠ 0 in ZMod r
  have hD : (Q ^ 2 - 4 : ZMod r) ≠ 0 := by
    have hu : IsUnit (f (P ^ 2 - 4)) := hDcop.map f
    rw [map_sub, map_pow, map_ofNat, ← hQ] at hu
    exact hu.ne_zero
  rcases theta_pow_pm Q hD with h | h
  · left; exact h3m_ord.trans (orderOf_dvd_of_pow_eq_one h)
  · right; exact h3m_ord.trans (orderOf_dvd_of_pow_eq_one h)

/-! ### Concrete `ℕ`-based computation, bridged to `QQ (ZMod n) p`. -/

/-- Multiplication of representatives `(a,b) ↦ a + bθ`, reduced mod `n`. -/
def qmul (n p : ℕ) (x y : ℕ × ℕ) : ℕ × ℕ :=
  ( (x.1 * y.1 + (n - x.2 * y.2 % n)) % n,
    (x.1 * y.2 + x.2 * y.1 + p * (x.2 * y.2)) % n )

/-- The bridge map to the abstract ring. -/
def toQ (n p : ℕ) (x : ℕ × ℕ) : QQ (ZMod n) (p : ZMod n) := ⟨(x.1 : ZMod n), (x.2 : ZMod n)⟩

theorem toQ_qmul {n p : ℕ} (hn : 0 < n) (x y : ℕ × ℕ) :
    toQ n p (qmul n p x y) = toQ n p x * toQ n p y := by
  have hle : x.2 * y.2 % n ≤ n := le_of_lt (Nat.mod_lt _ hn)
  apply QQ.ext'
  · simp only [toQ, qmul, QQ.mul_re]
    rw [ZMod.natCast_mod]
    push_cast [Nat.cast_sub hle, ZMod.natCast_mod, ZMod.natCast_self]
    ring
  · simp only [toQ, qmul, QQ.mul_im]
    rw [ZMod.natCast_mod]
    push_cast [ZMod.natCast_mod]
    ring

theorem toQ_one (n p : ℕ) : toQ n p (1, 0) = 1 := by
  apply QQ.ext' <;> simp [toQ]

theorem toQ_theta (n p : ℕ) : toQ n p (0, 1) = QQ.theta := by
  apply QQ.ext' <;> simp [toQ, QQ.theta]

/-- Cubing a representative. -/
def cube (n p : ℕ) (x : ℕ × ℕ) : ℕ × ℕ := qmul n p (qmul n p x x) x

theorem toQ_cube {n p : ℕ} (hn : 0 < n) (x : ℕ × ℕ) :
    toQ n p (cube n p x) = (toQ n p x) ^ 3 := by
  rw [cube, toQ_qmul hn, toQ_qmul hn]; ring

/-- `toQ (cube^[k] x) = (toQ x) ^ (3^k)`. -/
theorem toQ_iterate_cube {n p : ℕ} (hn : 0 < n) (k : ℕ) (x : ℕ × ℕ) :
    toQ n p ((cube n p)^[k] x) = (toQ n p x) ^ (3 ^ k) := by
  induction k generalizing x with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ', Function.comp_apply, toQ_cube hn, ih, ← pow_mul, ← pow_succ]

/-- Binary exponentiation on representatives. -/
def qpowAux (n p : ℕ) (base : ℕ × ℕ) (e fuel : ℕ) (acc : ℕ × ℕ) : ℕ × ℕ :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
    if e = 0 then acc
    else qpowAux n p (qmul n p base base) (e / 2) fuel
      (if e % 2 = 1 then qmul n p acc base else acc)

def qpowNat (n p : ℕ) (base : ℕ × ℕ) (e : ℕ) : ℕ × ℕ :=
  qpowAux n p base e (e + 1) (1, 0)

theorem toQ_qpowAux {n p : ℕ} (hn : 0 < n) (base : ℕ × ℕ) :
    ∀ (fuel e : ℕ) (acc : ℕ × ℕ), e < fuel →
      toQ n p (qpowAux n p base e fuel acc) = toQ n p acc * (toQ n p base) ^ e := by
  intro fuel
  induction fuel generalizing base with
  | zero => intro e acc h; omega
  | succ f ih =>
    intro e acc h
    rw [qpowAux]
    by_cases he : e = 0
    · subst he; simp
    · simp only [he, if_false]
      have he2 : e / 2 < f := by
        have : 1 ≤ e := Nat.one_le_iff_ne_zero.2 he
        omega
      rw [ih _ _ _ he2]
      have hb2 : toQ n p (qmul n p base base) = (toQ n p base) ^ 2 := by
        rw [toQ_qmul hn]; ring
      by_cases hpar : e % 2 = 1
      · simp only [hpar, if_true]
        rw [toQ_qmul hn, hb2, ← pow_mul]
        have hk : 2 * (e / 2) + 1 = e := by omega
        conv_rhs => rw [← hk, pow_succ]
        ring
      · simp only [hpar, if_false]
        rw [hb2, ← pow_mul]
        have hk : 2 * (e / 2) = e := by omega
        rw [hk]

theorem toQ_qpowNat {n p : ℕ} (hn : 0 < n) (base : ℕ × ℕ) (e : ℕ) :
    toQ n p (qpowNat n p base e) = (toQ n p base) ^ e := by
  rw [qpowNat, toQ_qpowAux hn base (e + 1) e (1, 0) (by omega), toQ_one, one_mul]

/-- The N+1 primality certificate (single prime `3`). -/
theorem prime_of_cert (N : ℕ) (hN1 : 1 < N) (P : ZMod N) (m : ℕ)
    (hpow : (theta : QQ (ZMod N) P) ^ (N + 1) = 1)
    (hunit : IsUnit (((theta : QQ (ZMod N) P) ^ ((N + 1) / 3)).im))
    (hDcop : IsUnit ((P ^ 2 - 4 : ZMod N)))
    (h3 : 3 ∣ (N + 1)) (hm3 : 3 ^ m ∣ (N + 1))
    (hsize : N < (3 ^ m - 1) ^ 2) : N.Prime := by
  by_contra hnp
  have hrp : (N.minFac).Prime := Nat.minFac_prime (by omega)
  have hrdvd : N.minFac ∣ N := Nat.minFac_dvd N
  have hr2 : 2 ≤ N.minFac := hrp.two_le
  have hge : 3 ^ m - 1 ≤ N.minFac := by
    rcases key_dvd hN1 hpow hunit hDcop h3 hm3 hrp hrdvd with h | h
    · have := Nat.le_of_dvd (by omega) h
      omega
    · have := Nat.le_of_dvd (by omega) h
      omega
  have hrr : N.minFac ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hnp
  have : (3 ^ m - 1) ^ 2 ≤ N := le_trans (Nat.pow_le_pow_left hge 2) hrr
  omega

end NPlusOne
