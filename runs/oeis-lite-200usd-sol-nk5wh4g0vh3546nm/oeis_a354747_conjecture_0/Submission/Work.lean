import FormalConjectures.Util.ProblemImports

open Nat Set
open LucasLehmer

namespace LucasCert

open LucasLehmer.X

/-- Reduction of the quadratic ring modulo a divisor. -/
def mapX {n q : ℕ} (h : q ∣ n) : X n →+* X q where
  toFun x := (ZMod.castHom h (ZMod q) x.1, ZMod.castHom h (ZMod q) x.2)
  map_one' := by
    ext <;> simp only [X.one_fst, X.one_snd, map_one, map_zero]
  map_mul' x y := by
    ext <;> simp only [X.mul_fst, X.mul_snd, map_add, map_mul, map_ofNat]
  map_zero' := by
    ext <;> simp only [X.zero_fst, X.zero_snd, map_zero]
  map_add' x y := by
    ext <;> simp only [X.add_fst, X.add_snd, map_add]

@[simp] lemma mapX_fst {n q : ℕ} (h : q ∣ n) (x : X n) :
    (mapX h x).1 = ZMod.castHom h (ZMod q) x.1 := rfl
@[simp] lemma mapX_snd {n q : ℕ} (h : q ∣ n) (x : X n) :
    (mapX h x).2 = ZMod.castHom h (ZMod q) x.2 := rfl
@[simp] lemma mapX_omega {n q : ℕ} (h : q ∣ n) :
    mapX h (ω : X n) = (ω : X q) := by
  ext
  · change ZMod.castHom h (ZMod q) 2 = 2
    exact map_ofNat _ _
  · change ZMod.castHom h (ZMod q) 1 = 1
    exact map_one _

/-- `2 + √3`, regarded as a unit in the quadratic ring. -/
def omegaUnit (q : ℕ) : Units (X q) where
  val := ω
  inv := ωb
  val_inv := X.ω_mul_ωb
  inv_val := X.ωb_mul_ω

@[simp] lemma omegaUnit_val (q : ℕ) : ((omegaUnit q : Units (X q)) : X q) = ω := rfl


/-- A quadratic Lucas certificate based on the complete factorization of `N+1`.
The second coordinate being a unit is a convenient, readily checkable version
of the usual Lucas nonvanishing/gcd condition. -/
theorem prime_of_full_order_omega (N : ℕ) (hN : 1 < N)
    (ha : (ω : X N) ^ (N + 1) = 1)
    (hd : ∀ r : ℕ, r.Prime → r ∣ N + 1 →
      IsUnit ((((ω : X N) ^ ((N + 1) / r)).1) - 1) ∨
      IsUnit (((ω : X N) ^ ((N + 1) / r)).2)) : N.Prime := by
  by_contra hn
  let q := N.minFac
  have hqprime : q.Prime := Nat.minFac_prime (by omega : N ≠ 1)
  have hqdvd : q ∣ N := Nat.minFac_dvd N
  have hq1 : 1 < q := hqprime.one_lt
  letI : NeZero q := ⟨hqprime.ne_zero⟩
  letI : Fact (1 < q) := ⟨hq1⟩
  have hpowX : (ω : X q) ^ (N + 1) = 1 := by
    simpa only [map_pow, map_one, mapX_omega] using congrArg (mapX hqdvd) ha
  have hnonX : ∀ r : ℕ, r.Prime → r ∣ N + 1 →
      (ω : X q) ^ ((N + 1) / r) ≠ 1 := by
    intro r hr hrd heq
    rcases hd r hr hrd with hu | hu
    · have hu0 : IsUnit (0 : ZMod q) := by
        have hu' := hu.map (ZMod.castHom hqdvd (ZMod q))
        rw [map_sub, map_one,
          ← mapX_fst hqdvd ((ω : X N) ^ ((N + 1) / r)),
          map_pow, mapX_omega, heq, X.one_fst, sub_self] at hu'
        exact hu'
      exact (not_isUnit_zero : ¬ IsUnit (0 : ZMod q)) hu0
    · have hu0 : IsUnit (0 : ZMod q) := by
        have hu' := hu.map (ZMod.castHom hqdvd (ZMod q))
        rw [← mapX_snd hqdvd ((ω : X N) ^ ((N + 1) / r)),
          map_pow, mapX_omega, heq, X.one_snd] at hu'
        exact hu'
      exact (not_isUnit_zero : ¬ IsUnit (0 : ZMod q)) hu0
  have hpowU : (omegaUnit q) ^ (N + 1) = 1 := by
    apply Units.ext
    simpa using hpowX
  have hnonU : ∀ r : ℕ, r.Prime → r ∣ N + 1 →
      (omegaUnit q) ^ ((N + 1) / r) ≠ 1 := by
    intro r hr hrd heq
    apply hnonX r hr hrd
    exact congrArg Units.val heq
  have hord : orderOf (omegaUnit q) = N + 1 :=
    orderOf_eq_of_pow_and_pow_div_prime (by omega) hpowU hnonU
  have hlarge : N + 1 < q ^ 2 := by
    calc
      N + 1 = orderOf (omegaUnit q) := hord.symm
      _ ≤ Fintype.card (X q)ˣ := orderOf_le_card_univ
      _ < q ^ 2 := X.card_units_lt hq1
  have hsmall : q ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hn
  omega

end LucasCert

namespace Compute

open LucasLehmer.X


abbrev Pair := ℕ × ℕ

def pmul (n : ℕ) (x y : Pair) : Pair :=
  ((x.1 * y.1 + 3 * x.2 * y.2) % n,
   (x.1 * y.2 + x.2 * y.1) % n)

def pcube (n : ℕ) (x : Pair) : Pair := pmul n x (pmul n x x)

/-- Tail-recursive iteration of cubing in the quadratic ring. -/
def psteps (n : ℕ) : ℕ → Pair → Pair
  | 0, x => x
  | k + 1, x => psteps n k (pcube n x)

/-- Little-endian binary powering. -/
def ppowBits (n : ℕ) (x : Pair) : List Bool → Pair
  | [] => (1 % n, 0)
  | b :: bs =>
      let y := ppowBits n x bs
      if b then pmul n x (pmul n y y) else pmul n y y

def bitsValue : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsValue bs

def toX (n : ℕ) (x : Pair) : X n := (x.1, x.2)

lemma toX_pmul (n : ℕ) (x y : Pair) :
    toX n (pmul n x y) = toX n x * toX n y := by
  ext <;> simp [toX, pmul, ZMod.natCast_mod, X.mul_fst, X.mul_snd]

lemma toX_pcube (n : ℕ) (x : Pair) :
    toX n (pcube n x) = (toX n x) ^ 3 := by
  rw [pcube, toX_pmul, toX_pmul]
  noncomm_ring

lemma toX_psteps (n k : ℕ) (x : Pair) :
    toX n (psteps n k x) = (toX n x) ^ (3 ^ k) := by
  induction k generalizing x with
  | zero => simp [psteps]
  | succ k ih =>
      rw [psteps, ih, toX_pcube, ← pow_mul]
      congr 1
      omega

lemma toX_ppowBits (n : ℕ) (x : Pair) (bs : List Bool) :
    toX n (ppowBits n x bs) = (toX n x) ^ (bitsValue bs) := by
  induction bs with
  | nil =>
      ext <;> simp [ppowBits, bitsValue, toX, ZMod.natCast_mod]
  | cons b bs ih =>
      cases b
      · simp only [ppowBits, bitsValue, Bool.false_eq_true, ↓reduceIte,
          toX_pmul, ih]
        rw [← pow_add]
        congr 1
        omega
      · simp only [ppowBits, bitsValue, ↓reduceIte, toX_pmul, ih]
        rw [← pow_add]
        nth_rewrite 1 [← pow_one (toX n x)]
        rw [← pow_add]
        congr 1
        omega

lemma toX_omegaPair (n : ℕ) : toX n (2, 1) = (ω : X n) := by
  ext <;> simp [toX, ω]

lemma certPower (n k : ℕ) (bs : List Bool) :
    toX n (psteps n k (ppowBits n (2, 1) bs)) =
      (ω : X n) ^ (bitsValue bs * 3 ^ k) := by
  rw [toX_psteps, toX_ppowBits, toX_omegaPair, pow_mul]

def bits201886 : List Bool :=
  [false, true, true, true, true, false, false, true, false,
   false, true, false, true, false, false, false, true, true]

def bits100943 : List Bool :=
  [true, true, true, true, false, false, true, false, false,
   true, false, true, false, false, false, true, true]

def bits2 : List Bool := [false, true]

lemma value_bits201886 : bitsValue bits201886 = 201886 := by norm_num [bitsValue, bits201886, bits100943, bits2]
lemma value_bits100943 : bitsValue bits100943 = 100943 := by norm_num [bitsValue, bits201886, bits100943, bits2]
lemma value_bits2 : bitsValue bits2 = 2 := by norm_num [bitsValue, bits201886, bits100943, bits2]

/-- Cubing in blocks keeps kernel reduction stack depth bounded. -/
def pchunks (n block : ℕ) : ℕ → Pair → Pair
  | 0, x => x
  | k + 1, x => pchunks n block k (psteps n block x)

def pfast39101 (n : ℕ) (x : Pair) : Pair :=
  psteps n 101 (pchunks n 1000 39 x)

def pfast39100 (n : ℕ) (x : Pair) : Pair :=
  psteps n 100 (pchunks n 1000 39 x)

lemma psteps_comp (n a b : ℕ) (x : Pair) :
    psteps n a (psteps n b x) = psteps n (b + a) x := by
  induction b generalizing x with
  | zero => simp [psteps]
  | succ b ih =>
      rw [psteps, ih]
      simp only [Nat.add_eq, Nat.succ_add]
      rfl

lemma pchunks_eq_psteps (n block k : ℕ) (x : Pair) :
    pchunks n block k x = psteps n (block * k) x := by
  induction k generalizing x with
  | zero => simp [pchunks, psteps]
  | succ k ih =>
      rw [pchunks, ih, psteps_comp]
      congr 1
      ring

lemma toX_pfast39101 (n : ℕ) (x : Pair) :
    toX n (pfast39101 n x) = (toX n x) ^ (3 ^ 39101) := by
  rw [pfast39101, pchunks_eq_psteps, psteps_comp]
  norm_num
  exact toX_psteps n 39101 x

lemma toX_pfast39100 (n : ℕ) (x : Pair) :
    toX n (pfast39100 n x) = (toX n x) ^ (3 ^ 39100) := by
  rw [pfast39100, pchunks_eq_psteps, psteps_comp]
  norm_num
  exact toX_psteps n 39100 x

lemma certFast39101 (n : ℕ) (bs : List Bool) :
    toX n (pfast39101 n (ppowBits n (2, 1) bs)) =
      (ω : X n) ^ (bitsValue bs * 3 ^ 39101) := by
  rw [toX_pfast39101, toX_ppowBits, toX_omegaPair, pow_mul]

lemma certFast39100 (n : ℕ) (bs : List Bool) :
    toX n (pfast39100 n (ppowBits n (2, 1) bs)) =
      (ω : X n) ^ (bitsValue bs * 3 ^ 39100) := by
  rw [toX_pfast39100, toX_ppowBits, toX_omegaPair, pow_mul]




end Compute

