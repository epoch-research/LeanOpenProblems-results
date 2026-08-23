import FormalConjectures.Util.ProblemImports

/-!
# Riesel primality test

For `N = k * 2^n - 1` with `k` odd and `0 < k < 2^n`, a single Lucas
`V`-sequence computation certifies primality of `N`.
-/

open Nat jacobiSym

/-- Lucas `V`-sequence for `Q = 1`: `V_0 = 2`, `V_1 = P`, `V_{n+2} = P V_{n+1} - V_n`. -/
def lucasV (P : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => P
  | n + 2 => P * lucasV P (n + 1) - lucasV P n

@[simp] theorem lucasV_zero (P : ℤ) : lucasV P 0 = 2 := rfl
@[simp] theorem lucasV_one (P : ℤ) : lucasV P 1 = P := rfl

theorem lucasV_succ_succ (P : ℤ) (n : ℕ) :
    lucasV P (n + 2) = P * lucasV P (n + 1) - lucasV P n := rfl

/-- Recurrence in the form `V_{j+1} = P V_j - V_{j-1}` for `j ≥ 1`. -/
theorem lucasV_succ (P : ℤ) {j : ℕ} (hj : 1 ≤ j) :
    lucasV P (j + 1) = P * lucasV P j - lucasV P (j - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj
  rw [Nat.add_sub_cancel]
  exact lucasV_succ_succ P n

/-- Addition formula: `V_{m+n} + V_{m-n} = V_m V_n` when `n ≤ m`. -/
theorem lucasV_add (P : ℤ) : ∀ n m, n ≤ m →
    lucasV P (m + n) + lucasV P (m - n) = lucasV P m * lucasV P n
  | 0, m, _ => by
    simp [lucasV]
    ring
  | 1, m, hm => by
    have hm1 : 1 ≤ m := hm
    have : lucasV P (m + 1) = P * lucasV P m - lucasV P (m - 1) := lucasV_succ P hm1
    simp only [lucasV_one]
    rw [this]
    ring
  | n + 2, m, hm => by
    have hn1 : n + 1 ≤ m := by omega
    have hn0 : n ≤ m := by omega
    have hstep1 := lucasV_add P (n + 1) m hn1
    have hstep0 := lucasV_add P n m hn0
    have hL : lucasV P (m + (n + 2)) = P * lucasV P (m + (n + 1)) - lucasV P (m + n) := by
      rw [show m + (n + 2) = (m + n) + 2 from add_assoc _ n 2]
      rw [lucasV_succ_succ, add_assoc]
    have hr : 1 ≤ m - (n + 1) := by omega
    have hR : lucasV P (m - (n + 2)) = P * lucasV P (m - (n + 1)) - lucasV P (m - n) := by
      have := lucasV_succ P hr
      have h1 : (m - (n + 1)) + 1 = m - n := by omega
      have h2 : m - (n + 1) - 1 = m - (n + 2) := by omega
      rw [h1, h2] at this
      linarith
    rw [hL, hR]
    have : P * lucasV P (m + (n + 1)) - lucasV P (m + n)
         + (P * lucasV P (m - (n + 1)) - lucasV P (m - n))
         = P * (lucasV P (m + (n + 1)) + lucasV P (m - (n + 1)))
           - (lucasV P (m + n) + lucasV P (m - n)) := by ring
    rw [this, hstep1, hstep0, lucasV_succ_succ]
    ring

/-- Doubling: `V_{2m} = V_m^2 - 2`. -/
theorem lucasV_dbl (P : ℤ) (m : ℕ) : lucasV P (2 * m) = lucasV P m ^ 2 - 2 := by
  have h := lucasV_add P m m le_rfl
  rw [Nat.sub_self, lucasV_zero] at h
  rw [two_mul]
  linarith

/-- Iterated doubling from `V_k`. -/
def lucasV_pow2 (P : ℤ) (k : ℕ) : ℕ → ℤ
  | 0 => lucasV P k
  | i + 1 => lucasV_pow2 P k i ^ 2 - 2

theorem lucasV_pow2_eq (P : ℤ) (k i : ℕ) :
    lucasV_pow2 P k i = lucasV P (k * 2 ^ i) := by
  induction i with
  | zero => simp [lucasV_pow2]
  | succ i ih =>
    rw [lucasV_pow2, ih, show k * 2 ^ (i + 1) = 2 * (k * 2 ^ i) from by ring, lucasV_dbl]


/-! ## Quadratic ring `ℤ/qℤ[√D]` as a commutative ring -/

/-- Elements `a + b √D`. -/
def XD (q : ℕ) (D : ZMod q) : Type := ZMod q × ZMod q

namespace XD

variable {q : ℕ} {D : ZMod q}

instance : Inhabited (XD q D) := inferInstanceAs (Inhabited (ZMod q × ZMod q))
instance : DecidableEq (XD q D) := inferInstanceAs (DecidableEq (ZMod q × ZMod q))
instance : AddCommGroup (XD q D) := inferInstanceAs (AddCommGroup (ZMod q × ZMod q))

@[ext] theorem ext {x y : XD q D} (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y := by
  cases x; cases y; congr

instance : Mul (XD q D) where
  mul x y := (x.1 * y.1 + D * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

instance : One (XD q D) where one := (1, 0)

@[simp] lemma fst_one : (1 : XD q D).1 = 1 := rfl
@[simp] lemma snd_one : (1 : XD q D).2 = 0 := rfl
@[simp] lemma fst_add (x y : XD q D) : (x + y).1 = x.1 + y.1 := rfl
@[simp] lemma snd_add (x y : XD q D) : (x + y).2 = x.2 + y.2 := rfl
@[simp] lemma fst_zero : (0 : XD q D).1 = 0 := rfl
@[simp] lemma snd_zero : (0 : XD q D).2 = 0 := rfl
@[simp] lemma fst_neg (x : XD q D) : (-x).1 = -x.1 := rfl
@[simp] lemma snd_neg (x : XD q D) : (-x).2 = -x.2 := rfl
@[simp] lemma fst_mul (x y : XD q D) : (x * y).1 = x.1 * y.1 + D * x.2 * y.2 := rfl
@[simp] lemma snd_mul (x y : XD q D) : (x * y).2 = x.1 * y.2 + x.2 * y.1 := rfl

instance : Monoid (XD q D) where
  mul_assoc x y z := by ext <;> simp <;> ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp

instance : NatCast (XD q D) where
  natCast n := (n, 0)

@[simp] lemma fst_natCast (n : ℕ) : ((n : XD q D).1) = n := rfl
@[simp] lemma snd_natCast (n : ℕ) : ((n : XD q D).2) = 0 := rfl

instance : AddGroupWithOne (XD q D) where
  natCast_zero := by ext <;> simp
  natCast_succ _ := by ext <;> simp
  intCast n := (n, 0)
  intCast_ofNat n := by ext <;> simp
  intCast_negSucc n := by ext <;> simp

@[simp] lemma fst_intCast (n : ℤ) : ((n : XD q D).1) = n := rfl
@[simp] lemma snd_intCast (n : ℤ) : ((n : XD q D).2) = 0 := rfl

instance : Ring (XD q D) where
  left_distrib x y z := by ext <;> simp <;> ring
  right_distrib x y z := by ext <;> simp <;> ring
  mul_zero x := by ext <;> simp
  zero_mul x := by ext <;> simp

instance : CommRing (XD q D) where
  mul_comm x y := by ext <;> simp <;> ring

instance [Fact (1 < q)] : Nontrivial (XD q D) :=
  ⟨⟨0, 1, ne_of_apply_ne Prod.fst zero_ne_one⟩⟩

/-- Scalar embedding of `ZMod q`. -/
def ofZMod (a : ZMod q) : XD q D := (a, 0)

instance : Coe (ZMod q) (XD q D) where coe := ofZMod

@[simp] lemma fst_ofZMod (a : ZMod q) : (ofZMod a : XD q D).1 = a := rfl
@[simp] lemma snd_ofZMod (a : ZMod q) : (ofZMod a : XD q D).2 = 0 := rfl

lemma intCast_eq_ofZMod (n : ℤ) : (n : XD q D) = ofZMod (n : ZMod q) := rfl

lemma ofZMod_mul (a b : ZMod q) : (ofZMod a : XD q D) * ofZMod b = ofZMod (a * b) := by
  refine ext ?_ ?_
  · simp [ofZMod]
  · simp [ofZMod]

lemma ofZMod_sub (a b : ZMod q) : (ofZMod a : XD q D) - ofZMod b = ofZMod (a - b) := by
  refine ext ?_ ?_
  · simp [ofZMod, sub_eq_add_neg]
  · simp [ofZMod, sub_eq_add_neg]

/-- `√D`. -/
def δ : XD q D := (0, 1)

@[simp] lemma δ_sq : (δ : XD q D) ^ 2 = ofZMod D := by
  ext <;> simp [δ, sq, ofZMod]

/-- `α = (P + √D)/2`. -/
def αX (P two_inv : ZMod q) : XD q D := (two_inv * P, two_inv)

/-- `β = (P - √D)/2`. -/
def βX (P two_inv : ZMod q) : XD q D := (two_inv * P, -two_inv)

lemma two_inv_mul (two_inv : ZMod q) (h2 : (2 : ZMod q) * two_inv = 1) :
    two_inv * two_inv * 4 = 1 := by
  have : (2 * two_inv) * (2 * two_inv) = 1 := by rw [h2, one_mul]
  convert this using 1; ring

lemma αX_mul_βX (P two_inv : ZMod q)
    (h2 : (2 : ZMod q) * two_inv = 1) (hD : D = P ^ 2 - 4) :
    αX (D := D) P two_inv * βX (D := D) P two_inv = 1 := by
  apply ext
  · have hsq := two_inv_mul two_inv h2
    change two_inv * P * (two_inv * P) + D * two_inv * (-two_inv) = 1
    calc
      two_inv * P * (two_inv * P) + D * two_inv * (-two_inv)
          = two_inv * two_inv * (P * P - D) := by ring
      _ = two_inv * two_inv * 4 := by rw [hD]; ring
      _ = 1 := hsq
  · change two_inv * P * (-two_inv) + two_inv * (two_inv * P) = 0
    ring

lemma αX_add_βX (P two_inv : ZMod q)
    (h2 : (2 : ZMod q) * two_inv = 1) :
    αX (D := D) P two_inv + βX (D := D) P two_inv = ofZMod P := by
  apply ext
  · change two_inv * P + two_inv * P = P
    have : (2 * two_inv) * P = P := by rw [h2, one_mul]
    convert this using 1; ring
  · change two_inv + (-two_inv) = 0
    ring

/-- `x^{n+2} + y^{n+2} = (x+y)(x^{n+1}+y^{n+1}) - xy (x^n+y^n)`. -/
lemma pow_add_two_formula (x y : XD q D) (n : ℕ) :
    x ^ (n + 2) + y ^ (n + 2) =
      (x + y) * (x ^ (n + 1) + y ^ (n + 1)) - x * y * (x ^ n + y ^ n) := by
  ring

lemma V_closed (Pz : ℤ) (n : ℕ) (two_inv : ZMod q)
    (h2 : (2 : ZMod q) * two_inv = 1) (hD : D = (Pz : ZMod q) ^ 2 - 4) :
    (αX (D := D) (Pz : ZMod q) two_inv) ^ n + (βX (D := D) (Pz : ZMod q) two_inv) ^ n
      = (lucasV Pz n : XD q D) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 =>
      apply ext
      · simp [lucasV]; norm_num
      · simp [lucasV]
    | 1 =>
      simpa [lucasV, pow_one] using αX_add_βX (Pz : ZMod q) two_inv h2
    | n + 2 =>
      have ih1 := ih (n + 1) (by omega)
      have ih0 := ih n (by omega)
      rw [pow_add_two_formula, ih1, ih0, αX_add_βX _ two_inv h2,
          αX_mul_βX _ two_inv h2 hD]
      -- LHS = ofZMod P * ↑V_{n+1} - ↑V_n
      -- RHS = ↑(P * V_{n+1} - V_n)
      simp only [lucasV_succ_succ, intCast_eq_ofZMod, ofZMod_mul, ofZMod_sub, Int.cast_sub,
        Int.cast_mul, one_mul]

end XD

open XD

/-- If `V_m ≡ 0 (mod q)` then `α^m = -β^m`. -/
lemma α_pow_eq_neg_β (Pz : ℤ) {q : ℕ} (two_inv : ZMod q)
    (h2 : (2 : ZMod q) * two_inv = 1)
    {D : ZMod q} (hD : D = (Pz : ZMod q) ^ 2 - 4)
    {m : ℕ} (hV : (lucasV Pz m : ZMod q) = 0) :
    (αX (D := D) (Pz : ZMod q) two_inv) ^ m = - (βX (D := D) (Pz : ZMod q) two_inv) ^ m := by
  have h := V_closed (D := D) Pz m two_inv h2 hD
  have hz : (αX (D := D) (Pz : ZMod q) two_inv) ^ m + (βX (D := D) (Pz : ZMod q) two_inv) ^ m = 0 := by
    rw [h, intCast_eq_ofZMod, hV]
    rfl
  exact eq_neg_iff_add_eq_zero.mpr hz

/-- Hence `α^{2m} = -1` when `V_m ≡ 0` (using `αβ = 1`). -/
lemma α_pow_two_eq_neg_one (Pz : ℤ) {q : ℕ} (two_inv : ZMod q)
    (h2 : (2 : ZMod q) * two_inv = 1)
    {D : ZMod q} (hD : D = (Pz : ZMod q) ^ 2 - 4)
    {m : ℕ} (hV : (lucasV Pz m : ZMod q) = 0) :
    (αX (D := D) (Pz : ZMod q) two_inv) ^ (2 * m) = -1 := by
  set α := αX (D := D) (Pz : ZMod q) two_inv
  set β := βX (D := D) (Pz : ZMod q) two_inv
  have hαβ : α * β = 1 := αX_mul_βX (D := D) (Pz : ZMod q) two_inv h2 hD
  have hneg : α ^ m = - β ^ m := α_pow_eq_neg_β Pz two_inv h2 hD hV
  have hpow : α ^ m * β ^ m = 1 := by rw [← mul_pow, hαβ, one_pow]
  calc
    α ^ (2 * m) = α ^ m * α ^ m := by rw [two_mul, pow_add]
    _ = α ^ m * (-β ^ m) := by rw [hneg]
    _ = - (α ^ m * β ^ m) := by rw [mul_neg]
    _ = -1 := by rw [hpow]

/-- `2^n` divides the order of an element `α` with `α^{k 2^{n-1}} = -1` and `k` odd. -/
lemma two_pow_dvd_orderOf_XD {q : ℕ} {D : ZMod q}
    (α : XD q D) {k n : ℕ} (hn : 0 < n) (hodd : Odd k)
    (ha : α ^ (k * 2 ^ (n - 1)) = -1)
    (hne : (1 : XD q D) ≠ -1) :
    2 ^ n ∣ orderOf α := by
  have hd_dvd : orderOf α ∣ k * 2 ^ n := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have hsucc : (n - 1) + 1 = n := Nat.sub_add_cancel hn
    rw [← hsucc, pow_succ, ← mul_assoc, pow_mul, ha, neg_one_sq]
  have hd_ndvd : ¬ orderOf α ∣ k * 2 ^ (n - 1) := by
    intro h
    have h1 : α ^ (k * 2 ^ (n - 1)) = 1 :=
      (orderOf_dvd_iff_pow_eq_one (x := α)).mp h
    exact hne (h1.symm.trans ha)
  let d := orderOf α
  have dpos : d ≠ 0 := by
    intro h0
    have hpow1 : α ^ (k * 2 ^ n) = 1 :=
      (orderOf_dvd_iff_pow_eq_one).mp hd_dvd
    have hpos : 0 < k * 2 ^ n :=
      Nat.mul_pos (Odd.pos hodd) (pow_pos (by decide) n)
    exact (orderOf_eq_zero_iff').mp h0 _ hpos hpow1
  obtain ⟨v, t, htodd, hdt⟩ := Nat.exists_eq_two_pow_mul_odd dpos
  have ht_k : t ∣ k := by
    have h1 : t ∣ d := by rw [hdt]; exact dvd_mul_left t _
    have h2 : t ∣ 2 ^ n * k := by
      rw [mul_comm]; exact dvd_trans h1 hd_dvd
    have hcop : Nat.Coprime t (2 ^ n) :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr htodd.not_two_dvd_nat).symm.pow_right n
    exact hcop.dvd_of_dvd_mul_left h2
  have hv : n ≤ v := by
    by_contra hlt
    have hvle : v ≤ n - 1 := Nat.le_sub_one_of_lt (lt_of_not_ge hlt)
    have : d ∣ k * 2 ^ (n - 1) := by
      rw [hdt, mul_comm k]
      exact mul_dvd_mul (Nat.pow_dvd_pow 2 hvle) ht_k
    exact hd_ndvd this
  have hv2 : 2 ^ n ∣ 2 ^ v := Nat.pow_dvd_pow 2 hv
  have : 2 ^ n ∣ d := by
    rw [hdt]
    exact dvd_mul_of_dvd_left hv2 t
  exact this


namespace XD

variable {q : ℕ} {D : ZMod q}

instance [NeZero q] : CharP (XD q D) q where
  cast_eq_zero_iff x := by
    constructor
    · intro h
      have h1 : ((x : XD q D).1 : ZMod q) = 0 := by
        rw [h]; simp
      -- (x : XD q D) = (x, 0), first component is ↑x
      simpa using (ZMod.natCast_eq_zero_iff x q).mp (by
        simpa [fst_natCast] using congrArg Prod.fst h)
    · intro h
      apply ext
      · simpa [fst_natCast] using (ZMod.natCast_eq_zero_iff x q).mpr h
      · simp

lemma ofZMod_pow (a : ZMod q) : ∀ n, (ofZMod a : XD q D) ^ n = ofZMod (a ^ n)
  | 0 => by refine ext ?_ ?_ <;> simp [ofZMod]
  | n + 1 => by rw [pow_succ, pow_succ, ofZMod_pow, ofZMod_mul]

/-- `δ^q = D^{q/2} • δ` for odd `q`. -/
lemma δ_pow_odd (hodd : Odd q) :
    (δ : XD q D) ^ q = ofZMod (D ^ (q / 2)) * δ := by
  have hq : 2 * (q / 2) + 1 = q := by
    have h2 : 2 * (q / 2) = q - 1 := Nat.two_mul_odd_div_two (odd_iff.mp hodd)
    have hq0 : 1 ≤ q := by
      have : q % 2 = 1 := odd_iff.mp hodd
      omega
    omega
  have hpow : (δ : XD q D) ^ q = δ ^ (2 * (q / 2) + 1) := by rw [hq]
  rw [hpow, pow_succ, pow_mul, δ_sq, ofZMod_pow]

/-- If `J(D | q) = -1` for an odd prime `q`, then `δ^q = -δ`. -/
lemma δ_pow_jacobi [Fact q.Prime] (hodd : Odd q) {Dz : ℤ}
    (hD : D = (Dz : ZMod q)) (hjac : jacobiSym Dz q = -1) :
    (δ : XD q D) ^ q = -δ := by
  have hpow : (Dz : ZMod q) ^ (q / 2) = -1 := by
    have := legendreSym.eq_pow (p := q) Dz
    have hleg : legendreSym q Dz = -1 := by
      rwa [legendreSym.to_jacobiSym]
    simpa [hleg] using this.symm
  rw [δ_pow_odd hodd, hD, hpow]
  refine ext ?_ ?_ <;> simp [δ, ofZMod]

end XD

namespace XD

variable {q : ℕ} {D : ZMod q}

lemma αX_eq (P two_inv : ZMod q) :
    αX (D := D) P two_inv = ofZMod two_inv * (ofZMod P + δ) := by
  refine ext ?_ ?_ <;> simp [αX, δ, ofZMod]

lemma βX_eq (P two_inv : ZMod q) :
    βX (D := D) P two_inv = ofZMod two_inv * (ofZMod P - δ) := by
  refine ext ?_ ?_ <;> simp [βX, δ, ofZMod, sub_eq_add_neg]

/-- Frobenius: `α^q = β` when `J(D|q) = -1`. -/
lemma αX_pow_prime [Fact q.Prime] [NeZero q] (hodd : Odd q)
    (P two_inv : ZMod q) {Dz : ℤ}
    (hD : D = (Dz : ZMod q)) (hjac : jacobiSym Dz q = -1)
    (h2 : (2 : ZMod q) * two_inv = 1) :
    (αX (D := D) P two_inv) ^ q = βX (D := D) P two_inv := by
  have hδ := δ_pow_jacobi (D := D) hodd hD hjac
  have hchar : (ofZMod P + δ : XD q D) ^ q = ofZMod P ^ q + δ ^ q := by
    simpa using add_pow_char (R := XD q D) (p := q) (ofZMod P) δ
  have hP : (ofZMod P : XD q D) ^ q = ofZMod P := by
    rw [ofZMod_pow, ZMod.pow_card]
  have ht : (ofZMod two_inv : XD q D) ^ q = ofZMod two_inv := by
    rw [ofZMod_pow, ZMod.pow_card]
  rw [αX_eq, βX_eq, mul_pow, ht, hchar, hP, hδ, sub_eq_add_neg]

/-- Consequently `α^{q+1} = 1`. -/
lemma αX_pow_succ [Fact q.Prime] [NeZero q] (hodd : Odd q)
    (P two_inv : ZMod q) {Dz : ℤ}
    (hDint : D = (Dz : ZMod q)) (hjac : jacobiSym Dz q = -1)
    (h2 : (2 : ZMod q) * two_inv = 1)
    (hD : D = P ^ 2 - 4) :
    (αX (D := D) P two_inv) ^ (q + 1) = 1 := by
  rw [pow_succ, αX_pow_prime hodd P two_inv hDint hjac h2, mul_comm]
  exact αX_mul_βX P two_inv h2 hD

end XD

open XD


/-- `N = k * 2^n - 1` is odd for `n ≥ 1`. -/
lemma odd_of_riesel {k n N : ℕ} (hn : 1 ≤ n) (hkpos : 0 < k) (hN : N = k * 2 ^ n - 1) :
    Odd N := by
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hn]
      _ = 2 ^ (n - 1) * 2 := pow_succ _ _
      _ = 2 * 2 ^ (n - 1) := mul_comm _ _
  have hx : 0 < k * 2 ^ (n - 1) := Nat.mul_pos hkpos (pow_pos (by decide) _)
  refine ⟨k * 2 ^ (n - 1) - 1, ?_⟩
  have : 2 * (k * 2 ^ (n - 1) - 1) + 1 = 2 * (k * 2 ^ (n - 1)) - 1 := by omega
  rw [this, hN, hpow]
  ring

/-- Algebraic identity used to bound the cofactor. -/
lemma riesel_div_identity {k n : ℕ} (hk : 0 < k) (_hn : 1 ≤ n) :
    k * 2 ^ n - 1 = k * (2 ^ n - 1) + (k - 1) := by
  have h1 : 1 ≤ k * 2 ^ n := Nat.succ_le_of_lt (Nat.mul_pos hk (pow_pos (by decide) n))
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hk' : 1 ≤ k := hk
  zify [h1, h2, hk']
  ring

lemma riesel_div_eq {k n : ℕ} (hk : 0 < k) (hn : 1 ≤ n) (hklt : k < 2 ^ n) :
    (k * 2 ^ n - 1) / (2 ^ n - 1) = k := by
  have hq : 0 < 2 ^ n - 1 := by
    have : 2 ≤ 2 ^ n :=
      calc 2 = 2 ^ 1 := by decide
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    omega
  have hr : k - 1 < 2 ^ n - 1 := by omega
  rw [riesel_div_identity hk hn, add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt hr,
    zero_add]

/-- **Riesel primality test.**
Let `N = k * 2^n - 1` with `k` odd and `0 < k < 2^n`. If there is an integer `P`
such that `J(P^2-4 | N) = -1` and `V_{k * 2^{n-2}}(P, 1) ≡ 0 (mod N)`, then `N`
is prime. -/
theorem riesel_primality {k n : ℕ} {P : ℤ} {N : ℕ}
    (hn : 2 ≤ n) (hodd : Odd k) (hkpos : 0 < k) (hklt : k < 2 ^ n)
    (hN : N = k * 2 ^ n - 1)
    (hjac : jacobiSym (P ^ 2 - 4) N = -1)
    (hV : (lucasV P (k * 2 ^ (n - 2)) : ZMod N) = 0) :
    Nat.Prime N := by
  have hn1 : 1 ≤ n := by omega
  have hNodd : Odd N := odd_of_riesel hn1 hkpos hN
  have hNpos : 1 < N := by
    have h4 : 4 ≤ 2 ^ n :=
      calc 4 = 2 ^ 2 := by decide
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    have : 4 ≤ k * 2 ^ n := le_trans h4 (Nat.le_mul_of_pos_left (2 ^ n) hkpos)
    omega
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨p, hp, hpdvd, hpjac⟩ :=
    jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one hjac
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpne2 : p ≠ 2 := by
    intro h2
    subst h2
    exact hNodd.not_two_dvd_nat hpdvd
  have hpodd : Odd p := hp.odd_of_ne_two hpne2
  have h2inv : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := by
    apply mul_inv_cancel₀
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h2'
    · exact hp.ne_one h1
    · exact hpne2 h2'
  have hVp : (lucasV P (k * 2 ^ (n - 2)) : ZMod p) = 0 := by
    have hdivN : (N : ℤ) ∣ lucasV P (k * 2 ^ (n - 2)) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hV
    have hdivp : (p : ℤ) ∣ lucasV P (k * 2 ^ (n - 2)) :=
      dvd_trans (Int.natCast_dvd_natCast.mpr hpdvd) hdivN
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdivp
  set Dp : ZMod p := (P : ZMod p) ^ 2 - 4
  have hDint : Dp = ((P ^ 2 - 4 : ℤ) : ZMod p) := by
    simp [Dp, Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
  have npos : 0 < n := by omega
  have hneg : (αX (D := Dp) (P : ZMod p) (2 : ZMod p)⁻¹) ^ (k * 2 ^ (n - 1)) = -1 := by
    have hα := α_pow_two_eq_neg_one (q := p) P (2 : ZMod p)⁻¹ h2inv (by rfl) hVp
    convert hα using 2
    have : 2 * (k * 2 ^ (n - 2)) = k * 2 ^ (n - 1) := by
      have : n - 1 = n - 2 + 1 := by omega
      rw [this, pow_succ]
      ring
    rw [← this, mul_comm (2 : ℕ)]
  have hne : (1 : XD p Dp) ≠ -1 := by
    intro h
    have hsum : (1 + 1 : XD p Dp) = 0 := by
      have := congrArg (fun x : XD p Dp => x + 1) h
      simpa using this
    have h2z : (2 : XD p Dp) = 0 := by
      have : (2 : XD p Dp) = 1 + 1 := by
        refine ext ?_ ?_ <;> simp
        norm_num
      rw [this, hsum]
    have : (2 : ZMod p) = 0 := by
      simpa [XD.fst_natCast] using congrArg Prod.fst h2z
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp this
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h2'
    · exact hp.ne_one h1
    · exact hpne2 h2'
  have hord : 2 ^ n ∣ orderOf (αX (D := Dp) (P : ZMod p) (2 : ZMod p)⁻¹) :=
    two_pow_dvd_orderOf_XD _ npos hodd hneg hne
  have hα1 : (αX (D := Dp) (P : ZMod p) (2 : ZMod p)⁻¹) ^ (p + 1) = 1 :=
    αX_pow_succ hpodd (P : ZMod p) (2 : ZMod p)⁻¹ hDint hpjac h2inv (by rfl)
  have hdivp1 : orderOf (αX (D := Dp) (P : ZMod p) (2 : ZMod p)⁻¹) ∣ p + 1 :=
    orderOf_dvd_of_pow_eq_one hα1
  have h2n : 2 ^ n ∣ p + 1 := dvd_trans hord hdivp1
  obtain ⟨t, ht⟩ := h2n
  obtain ⟨m, hmN⟩ := hpdvd
  have hmpos : 0 < m := by
    have : 0 < N := by omega
    rw [hmN] at this
    exact Nat.pos_of_mul_pos_left this
  have hN1 : (N : ℤ) + 1 = (k : ℤ) * 2 ^ n := by
    have hle : 1 ≤ k * 2 ^ n := Nat.succ_le_of_lt (Nat.mul_pos hkpos (pow_pos (by decide) n))
    have : N + 1 = k * 2 ^ n := by
      rw [hN]
      exact Nat.sub_add_cancel hle
    exact_mod_cast this
  have hpt : (p : ℤ) + 1 = (2 ^ n : ℤ) * t := by
    exact_mod_cast ht
  have hNm : (N : ℤ) = (p : ℤ) * m := by
    exact_mod_cast hmN
  have hrel : ((m : ℤ) - 1) = (2 ^ n : ℤ) * ((t : ℤ) * m - k) := by
    have hpz : (p : ℤ) = (2 ^ n : ℤ) * t - 1 := by linarith [hpt]
    have hpm : (p : ℤ) * m + 1 = (k : ℤ) * 2 ^ n := by
      rw [← hNm]; exact hN1
    rw [hpz] at hpm
    linarith
  have hmdvd : 2 ^ n ∣ m - 1 := by
    have hz : (2 ^ n : ℤ) ∣ ((m : ℤ) - 1) := ⟨(t : ℤ) * m - k, hrel⟩
    have hcast : ((m : ℤ) - 1) = ((m - 1 : ℕ) : ℤ) := (Int.natCast_sub hmpos).symm
    rw [hcast] at hz
    exact Int.natCast_dvd_natCast.mp hz
  have hpge : 2 ^ n - 1 ≤ p := by
    have : 2 ^ n ≤ p + 1 := Nat.le_of_dvd (Nat.succ_pos _) ⟨t, ht⟩
    omega
  have hpowpos : 0 < 2 ^ n - 1 := by
    have : 2 ≤ 2 ^ n :=
      calc 2 = 2 ^ 1 := by decide
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) hn1
    omega
  have hmle : m ≤ k := by
    have hmul : (2 ^ n - 1) * m ≤ N := by
      rw [hmN]
      exact Nat.mul_le_mul_right m hpge
    have hle : m ≤ N / (2 ^ n - 1) :=
      (Nat.le_div_iff_mul_le hpowpos).2 (by rwa [mul_comm])
    have hdiv : N / (2 ^ n - 1) = k := by
      rw [hN]
      exact riesel_div_eq hkpos hn1 hklt
    omega
  have hm1lt : m - 1 < 2 ^ n := by omega
  have hm1eq : m - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hmdvd hm1lt
  have hm1 : m = 1 := by omega
  have hNp : N = p := by
    rw [hmN, hm1, mul_one]
  rw [hNp]
  exact hp

/-! ## Kernel-reducible modular evaluation of `lucasV` -/

/-- One recurrence step modulo `N`: `(V_i, V_{i+1}) ↦ (V_{i+1}, V_{i+2})`. -/
def vStep (P N : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.2, ((P % N) * p.2 + (N - p.1 % N)) % N)

/-- `(V_n mod N, V_{n+1} mod N)`. -/
def vPair (P N : ℕ) : ℕ → ℕ × ℕ
  | 0 => (2 % N, P % N)
  | n + 1 => vStep P N (vPair P N n)

lemma nat_cast_sub_mod (N a : ℕ) [NeZero N] :
    ((N - a % N : ℕ) : ZMod N) = - (a : ZMod N) := by
  have hN : 0 < N := NeZero.pos N
  have hle : a % N ≤ N := Nat.le_of_lt (Nat.mod_lt a hN)
  have hcast : ((a % N : ℕ) : ZMod N) = (a : ZMod N) := ZMod.natCast_mod a N
  rw [Nat.cast_sub hle, ZMod.natCast_self, zero_sub, hcast]

lemma vStep_snd_zmod (P N v0 v1 : ℕ) [NeZero N] :
    ((vStep P N (v0, v1)).2 : ZMod N) =
      (P : ZMod N) * (v1 : ZMod N) - (v0 : ZMod N) := by
  change (((P % N) * v1 + (N - v0 % N)) % N : ZMod N) = _
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, nat_cast_sub_mod, ZMod.natCast_mod]
  ring

lemma vPair_spec (P N n : ℕ) [NeZero N] :
    ((vPair P N n).1 : ZMod N) = (lucasV (P : ℤ) n : ZMod N) ∧
    ((vPair P N n).2 : ZMod N) = (lucasV (P : ℤ) (n + 1) : ZMod N) := by
  induction n with
  | zero =>
    constructor
    · simp [vPair, lucasV]
    · simp [vPair, lucasV]
  | succ n ih =>
    constructor
    · simpa [vPair, vStep] using ih.2
    · have hstep := vStep_snd_zmod P N (vPair P N n).1 (vPair P N n).2
      simpa [vPair, lucasV_succ_succ, ih.1, ih.2, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
        using hstep

/-- Doubling step `x ↦ x² - 2` modulo `N` (requires `2 < N`). -/
def sqm2 (N x : ℕ) : ℕ := (x * x + (N - 2)) % N

/-- `i`-fold doubling starting from `acc`. -/
def vpow2mod (N acc : ℕ) : ℕ → ℕ
  | 0 => acc % N
  | i + 1 => sqm2 N (vpow2mod N acc i)

lemma sqm2_zmod (N x : ℕ) [NeZero N] (hN : 2 ≤ N) :
    (sqm2 N x : ZMod N) = (x : ZMod N) ^ 2 - 2 := by
  change (((x * x + (N - 2)) % N : ZMod N) = _)
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hN, ZMod.natCast_self, zero_sub]
  simp [pow_two, sub_eq_add_neg]

lemma vpow2mod_spec (P : ℤ) (k N i : ℕ) [NeZero N] (hN : 2 ≤ N)
    {acc : ℕ} (hacc : (acc : ZMod N) = (lucasV P k : ZMod N)) :
    (vpow2mod N acc i : ZMod N) = (lucasV P (k * 2 ^ i) : ZMod N) := by
  induction i with
  | zero =>
    simp [vpow2mod, hacc]
  | succ i ih =>
    rw [vpow2mod, sqm2_zmod N _ hN, ih,
      show k * 2 ^ (i + 1) = 2 * (k * 2 ^ i) by rw [pow_succ]; ring, lucasV_dbl]
    simp [pow_two]

lemma vpow2mod_zero (P : ℤ) (k N i : ℕ) [NeZero N] (hN : 2 ≤ N)
    {acc : ℕ} (hacc : (acc : ZMod N) = (lucasV P k : ZMod N))
    (hz : vpow2mod N acc i = 0) :
    (lucasV P (k * 2 ^ i) : ZMod N) = 0 := by
  rw [← vpow2mod_spec P k N i hN hacc, hz, Nat.cast_zero]

/-! ## A small sanity-check: `191 = 3 * 2^6 - 1` is Riesel-prime. -/

lemma jac_2_3 : jacobiSym 2 3 = -1 := by
  rw [jacobiSym.at_two (by decide), ZMod.χ₈_nat_eq_if_mod_eight]
  decide

lemma jac_2_7 : jacobiSym 2 7 = 1 := by
  rw [jacobiSym.at_two (by decide), ZMod.χ₈_nat_eq_if_mod_eight]
  decide

lemma jac_3_191 : jacobiSym (3 : ℤ) 191 = 1 := by
  have h : jacobiSym (3 : ℕ) 191 = - jacobiSym 191 3 :=
    jacobiSym.quadratic_reciprocity_three_mod_four (a := 3) (b := 191) (by decide) (by decide)
  have hmod : jacobiSym (191 : ℤ) 3 = jacobiSym (2 : ℤ) 3 := by
    rw [jacobiSym.mod_left]
    have : (191 : ℤ) % (3 : ℕ) = (2 : ℤ) := by norm_num
    rw [this]
  rw [show jacobiSym (3 : ℤ) 191 = jacobiSym (3 : ℕ) 191 from rfl, h, hmod, jac_2_3]
  norm_num

lemma jac_7_191 : jacobiSym (7 : ℤ) 191 = -1 := by
  have h : jacobiSym (7 : ℕ) 191 = - jacobiSym 191 7 :=
    jacobiSym.quadratic_reciprocity_three_mod_four (a := 7) (b := 191) (by decide) (by decide)
  have hmod : jacobiSym (191 : ℤ) 7 = jacobiSym (2 : ℤ) 7 := by
    rw [jacobiSym.mod_left]
    have : (191 : ℤ) % (7 : ℕ) = (2 : ℤ) := by norm_num
    rw [this]
  rw [show jacobiSym (7 : ℤ) 191 = jacobiSym (7 : ℕ) 191 from rfl, h, hmod, jac_2_7]

lemma jac_21_191 : jacobiSym 21 191 = -1 := by
  have hmul : jacobiSym (3 * 7) 191 = jacobiSym 3 191 * jacobiSym 7 191 :=
    jacobiSym.mul_left 3 7 191
  have : (21 : ℤ) = 3 * 7 := by decide
  rw [this, hmul, jac_3_191, jac_7_191]
  norm_num

lemma jac_5_191 : jacobiSym (5 ^ 2 - 4) 191 = -1 := by
  have : (5 ^ 2 - 4 : ℤ) = 21 := by decide
  rw [this, jac_21_191]

lemma v_191 : (lucasV 5 (3 * 2 ^ 4) : ZMod 191) = 0 := by
  haveI : NeZero 191 := ⟨by decide⟩
  have hacc : ((vPair 5 191 3).1 : ZMod 191) = (lucasV (5 : ℤ) 3 : ZMod 191) :=
    (vPair_spec 5 191 3).1
  have h0 : vpow2mod 191 (vPair 5 191 3).1 4 = 0 := rfl
  exact vpow2mod_zero (5 : ℤ) 3 191 4 (by decide) hacc h0

lemma prime_191_riesel : Nat.Prime 191 := by
  refine riesel_primality (k := 3) (n := 6) (P := 5) (N := 191)
    (by decide) (by decide) (by decide) (by decide) (by decide) jac_5_191 ?_
  simpa using v_191

set_option maxRecDepth 10000

/-! Medium certificate: `213 * 2^80 - 1`. -/

def A80 : ℕ := 257501199577916014212415487

lemma jac_3_A80 : jacobiSym (3 ^ 2 - 4) A80 = -1 := by
  unfold A80
  norm_num

lemma v_A80 : (lucasV 3 (213 * 2 ^ 78) : ZMod A80) = 0 := by
  haveI : NeZero A80 := ⟨by decide⟩
  have hacc : ((vPair 3 A80 213).1 : ZMod A80) = (lucasV (3 : ℤ) 213 : ZMod A80) :=
    (vPair_spec 3 A80 213).1
  have h0 : vpow2mod A80 (vPair 3 A80 213).1 78 = 0 := rfl
  exact vpow2mod_zero (3 : ℤ) 213 A80 78 (by decide) hacc h0

lemma prime_A80 : Nat.Prime A80 := by
  have hN : A80 = 213 * 2 ^ 80 - 1 := by
    unfold A80
    norm_num
  refine riesel_primality (k := 213) (n := 80) (P := 3) (N := A80)
    (by decide) (by decide) (by decide) (by decide) hN jac_3_A80 ?_
  -- 213 * 2^(80-2) = 213 * 2^78
  simpa using v_A80

/-! ## Kernel-reducible modular exponentiation for Proth -/

def mulmod (N a b : ℕ) : ℕ := (a * b) % N

def powSmall (N a : ℕ) : ℕ → ℕ
  | 0 => 1 % N
  | k + 1 => mulmod N (powSmall N a k) a

def sqmod (N x : ℕ) : ℕ := (x * x) % N

def pow2mod (N acc : ℕ) : ℕ → ℕ
  | 0 => acc % N
  | i + 1 => sqmod N (pow2mod N acc i)

lemma powSmall_spec (N a k : ℕ) [NeZero N] :
    (powSmall N a k : ZMod N) = (a : ZMod N) ^ k := by
  induction k with
  | zero => simp [powSmall]
  | succ k ih =>
    simp only [powSmall, mulmod, pow_succ]
    rw [ZMod.natCast_mod, Nat.cast_mul, ih]

lemma sqmod_zmod (N x : ℕ) [NeZero N] :
    (sqmod N x : ZMod N) = (x : ZMod N) ^ 2 := by
  change (((x * x) % N : ZMod N) = _)
  rw [ZMod.natCast_mod, Nat.cast_mul, pow_two]

lemma pow2mod_spec (N acc i : ℕ) [NeZero N]
    {a : ZMod N} (hacc : (acc : ZMod N) = a) :
    (pow2mod N acc i : ZMod N) = a ^ (2 ^ i) := by
  induction i with
  | zero => simp [pow2mod, hacc]
  | succ i ih =>
    calc (pow2mod N acc (i + 1) : ZMod N)
        = ((pow2mod N acc i : ZMod N) ^ 2) := by
          simp only [pow2mod]; exact sqmod_zmod N _
      _ = (a ^ (2 ^ i)) ^ 2 := by rw [ih]
      _ = a ^ (2 ^ i * 2) := (pow_mul _ _ _).symm
      _ = a ^ (2 ^ (i + 1)) := by rw [← pow_succ (2 : ℕ) i]

lemma cast_pred_neg_one (N : ℕ) [NeZero N] (hN : 1 ≤ N) :
    ((N - 1 : ℕ) : ZMod N) = -1 := by
  rw [Nat.cast_sub hN, Nat.cast_one, ZMod.natCast_self, zero_sub]

lemma pow2mod_neg_one (N acc i : ℕ) [NeZero N] {a : ℕ}
    (hacc : (acc : ZMod N) = (a : ZMod N))
    (h : pow2mod N acc i = N - 1) (hN : 1 ≤ N) :
    (a : ZMod N) ^ (2 ^ i) = -1 := by
  have hspec := pow2mod_spec N acc i hacc
  rw [← hspec, h, cast_pred_neg_one N hN]

lemma proth_pow_neg_one (k n a N : ℕ) [NeZero N]
    (hN : N = k * 2 ^ n + 1) (hn : 0 < n)
    (hpow : pow2mod N (powSmall N a k) (n - 1) = N - 1) :
    (a : ZMod N) ^ ((N - 1) / 2) = -1 := by
  have hN1 : N - 1 = k * 2 ^ n := by
    have : 1 ≤ N := by
      rw [hN]; exact Nat.succ_le_succ (Nat.zero_le _)
    omega
  have hhalf : (N - 1) / 2 = k * 2 ^ (n - 1) := by
    have : k * 2 ^ n = k * 2 ^ (n - 1) * 2 := by
      calc
        k * 2 ^ n = k * 2 ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hn]
        _ = k * (2 ^ (n - 1) * 2) := by rw [pow_succ]
        _ = k * 2 ^ (n - 1) * 2 := by ring
    rw [hN1, this, Nat.mul_div_cancel _ two_pos]
  have hacc : (powSmall N a k : ZMod N) = (a : ZMod N) ^ k := powSmall_spec N a k
  have hspec := pow2mod_spec (a := (a : ZMod N) ^ k) N (powSmall N a k) (n - 1) hacc
  have h1 : 1 ≤ N := by omega
  rw [hhalf, pow_mul, ← hspec, hpow, cast_pred_neg_one N h1]

def B80 : ℕ := 257501199577916014212415489

lemma pow_B80 : pow2mod B80 (powSmall B80 7 213) 79 = B80 - 1 := rfl

lemma proth_B80_pow : (7 : ZMod B80) ^ ((B80 - 1) / 2) = -1 := by
  haveI : NeZero B80 := ⟨by decide⟩
  have hN : B80 = 213 * 2 ^ 80 + 1 := by unfold B80; norm_num
  exact proth_pow_neg_one 213 80 7 B80 hN (by decide) pow_B80

/-! ## Proth primality (copied) -/

lemma zmod_pow_neg_one_of_dvd {a e N p : ℕ} [NeZero N] (hp : p.Prime) (hdvd : p ∣ N)
    (ha : (a : ZMod N) ^ e = -1) : (a : ZMod p) ^ e = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hzero : ((a ^ e + 1 : ℕ) : ZMod N) = 0 := by
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, ha, neg_add_cancel]
  have hdivN : N ∣ a ^ e + 1 := (ZMod.natCast_eq_zero_iff (a ^ e + 1) N).mp hzero
  have hdivp : p ∣ a ^ e + 1 := dvd_trans hdvd hdivN
  have : ((a ^ e + 1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (a ^ e + 1) p).mpr hdivp
  rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one] at this
  exact add_eq_zero_iff_eq_neg.mp this

lemma odd_coprime_two {k : ℕ} (h : Odd k) : Nat.Coprime k 2 := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  exact h.not_two_dvd_nat

lemma one_ne_neg_one_of_odd_prime {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) :
    (1 : ZMod p) ≠ -1 := by
  intro h
  have hsum : (1 + 1 : ZMod p) = 0 := by
    have := congrArg (fun x : ZMod p => x + 1) h
    simpa using this
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by
    have : ((2 : ℕ) : ZMod p) = 1 + 1 := by norm_num
    rw [this, hsum]
  have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
  rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h2'
  · exact (Fact.out (p := p.Prime)).ne_one h1
  · exact hodd h2'

lemma two_pow_dvd_orderOf (a : ℕ) (p k n : ℕ) [Fact p.Prime]
    (hn : 0 < n) (hkodd : Odd k)
    (ha : (a : ZMod p) ^ (k * 2 ^ (n - 1)) = -1)
    (hne : (1 : ZMod p) ≠ -1) :
    2 ^ n ∣ orderOf (a : ZMod p) := by
  let d : ℕ := orderOf (a : ZMod p)
  have hd_dvd : d ∣ k * 2 ^ n := by
    change orderOf (a : ZMod p) ∣ k * 2 ^ n
    rw [orderOf_dvd_iff_pow_eq_one]
    have hsucc : (n - 1) + 1 = n := Nat.sub_add_cancel hn
    rw [← hsucc, pow_succ, ← mul_assoc, pow_mul, ha, neg_one_sq]
  have hd_ndvd : ¬ d ∣ k * 2 ^ (n - 1) := by
    intro h
    have h1 : (a : ZMod p) ^ (k * 2 ^ (n - 1)) = 1 :=
      (orderOf_dvd_iff_pow_eq_one (x := (a : ZMod p))).mp h
    exact hne (h1.symm.trans ha)
  have dpos : d ≠ 0 := by
    intro h0
    have : ∀ n : ℕ, 0 < n → (a : ZMod p) ^ n ≠ 1 :=
      (orderOf_eq_zero_iff').mp h0
    have hpow1 : (a : ZMod p) ^ (k * 2 ^ n) = 1 :=
      (orderOf_dvd_iff_pow_eq_one).mp hd_dvd
    have hpos : 0 < k * 2 ^ n :=
      Nat.mul_pos (Odd.pos hkodd) (pow_pos (by decide) n)
    exact this _ hpos hpow1
  obtain ⟨v, t, htodd, hdt⟩ := Nat.exists_eq_two_pow_mul_odd dpos
  have ht_k : t ∣ k := by
    have h1 : t ∣ d := by
      rw [hdt]; exact dvd_mul_left t _
    have h2 : t ∣ 2 ^ n * k := by
      rw [mul_comm]
      exact dvd_trans h1 hd_dvd
    have hcop : Nat.Coprime t (2 ^ n) :=
      (odd_coprime_two htodd).pow_right n
    exact hcop.dvd_of_dvd_mul_left h2
  have hv : n ≤ v := by
    by_contra hlt
    have hvle : v ≤ n - 1 := Nat.le_sub_one_of_lt (lt_of_not_ge hlt)
    have : d ∣ k * 2 ^ (n - 1) := by
      rw [hdt, mul_comm k]
      exact mul_dvd_mul (Nat.pow_dvd_pow 2 hvle) ht_k
    exact hd_ndvd this
  have : 2 ^ n ∣ 2 ^ v := Nat.pow_dvd_pow 2 hv
  have : 2 ^ n ∣ d := by
    rw [hdt]
    exact dvd_mul_of_dvd_left this t
  exact this

lemma proth_prime_ne_two {k n N p : ℕ} (hn : 0 < n) (hkodd : Odd k)
    (hN : N = k * 2 ^ n + 1) (hp : p.Prime) (hdvd : p ∣ N) : p ≠ 2 := by
  intro h2
  subst h2
  have hNodd : ¬ 2 ∣ N := by
    have heven : 2 ∣ k * 2 ^ n := by
      have : 2 ∣ 2 ^ n := (dvd_pow_self 2 (Nat.ne_of_gt hn))
      exact dvd_mul_of_dvd_right this k
    have : N = k * 2 ^ n + 1 := hN
    intro h
    have : 2 ∣ 1 := (Nat.dvd_add_right heven).mp (hN ▸ h)
    exact (by decide : ¬ 2 ∣ 1) this
  exact hNodd hdvd

lemma proth_prime_factor_large {k n a N p : ℕ} [NeZero N]
    (hn : 0 < n) (hkodd : Odd k) (hN : N = k * 2 ^ n + 1)
    (ha : (a : ZMod N) ^ ((N - 1) / 2) = -1)
    (hp : p.Prime) (hdvd : p ∣ N) : 2 ^ n + 1 ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpne2 : p ≠ 2 := proth_prime_ne_two hn hkodd hN hp hdvd
  have hN1 : N - 1 = k * 2 ^ n := by
    have : 1 ≤ N := by
      rw [hN]; exact Nat.succ_le_succ (Nat.zero_le _)
    omega
  have hhalf : (N - 1) / 2 = k * 2 ^ (n - 1) := by
    have hsucc : (n - 1) + 1 = n := Nat.sub_add_cancel hn
    have : k * 2 ^ n = (k * 2 ^ (n - 1)) * 2 := by
      calc
        k * 2 ^ n = k * 2 ^ ((n - 1) + 1) := by rw [hsucc]
        _ = k * (2 ^ (n - 1) * 2) := by rw [pow_succ]
        _ = k * 2 ^ (n - 1) * 2 := by rw [mul_assoc]
    rw [hN1, this, Nat.mul_div_cancel _ two_pos]
  have ha' : (a : ZMod p) ^ (k * 2 ^ (n - 1)) = -1 := by
    rw [← hhalf]
    exact zmod_pow_neg_one_of_dvd hp hdvd ha
  have hne : (1 : ZMod p) ≠ -1 := one_ne_neg_one_of_odd_prime hpne2
  have hpow : 2 ^ n ∣ orderOf (a : ZMod p) :=
    two_pow_dvd_orderOf a p k n hn hkodd ha' hne
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro h0
    have hpos : k * 2 ^ (n - 1) ≠ 0 :=
      Nat.mul_ne_zero (Odd.pos hkodd).ne' (pow_ne_zero _ (by decide))
    rw [h0, zero_pow hpos] at ha'
    have : (0 : ZMod p) = -1 := ha'
    have : (1 : ZMod p) = 0 := by
      have := congrArg (fun x : ZMod p => x + 1) this
      simpa using this
    have : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp (by
      exact_mod_cast this)
    exact hp.not_dvd_one this
  have hdivp1 : orderOf (a : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one ha0
  have : 2 ^ n ∣ p - 1 := dvd_trans hpow hdivp1
  have : 2 ^ n ≤ p - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) this
  omega

theorem proth_primality {k n a N : ℕ} (hn : 0 < n) (hkodd : Odd k) (hklt : k < 2 ^ n)
    (hN : N = k * 2 ^ n + 1)
    (ha : (a : ZMod N) ^ ((N - 1) / 2) = -1) : Nat.Prime N := by
  have hNgt : 1 < N := by
    rw [hN]
    have : 0 < k * 2 ^ n := Nat.mul_pos (Odd.pos hkodd) (pow_pos (by decide) n)
    omega
  haveI : NeZero N := ⟨by omega⟩
  by_contra hnp
  have hminP : Nat.Prime N.minFac := Nat.minFac_prime (show N ≠ 1 by omega)
  have hge : 2 ^ n + 1 ≤ N.minFac :=
    proth_prime_factor_large hn hkodd hN ha hminP (Nat.minFac_dvd N)
  have hsq : N.minFac ^ 2 ≤ N := Nat.minFac_sq_le_self (Nat.zero_lt_of_lt hNgt) hnp
  have hNbound : N < (2 ^ n + 1) ^ 2 := by
    rw [hN, add_sq]
    have hmul : k * 2 ^ n < 2 ^ n * 2 ^ n :=
      Nat.mul_lt_mul_of_pos_right hklt (pow_pos (by decide) n)
    have : 0 < 2 * 2 ^ n := Nat.mul_pos two_pos (pow_pos (by decide) n)
    -- N = k*2^n + 1 < 2^n*2^n + 1
    -- (2^n+1)^2 = 2^{2n} + 2*2^n + 1
    have : k * 2 ^ n + 1 < 2 ^ n * 2 ^ n + 2 * 2 ^ n + 1 := by
      have : k * 2 ^ n < 2 ^ n * 2 ^ n + 2 * 2 ^ n := by omega
      omega
    simpa [pow_two] using this
  have : (2 ^ n + 1) ^ 2 ≤ N.minFac ^ 2 := Nat.pow_le_pow_left hge 2
  omega

set_option exponentiation.threshold 800
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000



theorem lucasV_odd_step (P : ℤ) (d : ℕ) :
    lucasV P (2 * d + 1) = lucasV P d * lucasV P (d + 1) - P := by
  have h := lucasV_add P d (d + 1) (Nat.le_succ d)
  have h1 : d + 1 + d = 2 * d + 1 := by ring
  have h2 : d + 1 - d = 1 := by omega
  rw [h1, h2, lucasV_one] at h
  linarith

def mulsub (P N v0 v1 : ℕ) : ℕ :=
  ((v0 % N) * (v1 % N) + (N - P % N)) % N

lemma mulsub_zmod (P N v0 v1 : ℕ) [NeZero N] :
    (mulsub P N v0 v1 : ZMod N) =
      (v0 : ZMod N) * (v1 : ZMod N) - (P : ZMod N) := by
  change ((((v0 % N) * (v1 % N) + (N - P % N)) % N : ZMod N) = _)
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, nat_cast_sub_mod, ZMod.natCast_mod,
    ZMod.natCast_mod]
  ring

def bitsVal : List Bool → ℕ
  | [] => 0
  | true :: bs => 1 + 2 * bitsVal bs
  | false :: bs => 2 * bitsVal bs

def vStepBit (P N : ℕ) (p : ℕ × ℕ) (bit : Bool) : ℕ × ℕ :=
  if bit then
    (mulsub P N p.1 p.2, sqm2 N p.2)
  else
    (sqm2 N p.1, mulsub P N p.1 p.2)

def vBits (P N : ℕ) : List Bool → ℕ × ℕ
  | [] => (2 % N, P % N)
  | b :: bs => vStepBit P N (vBits P N bs) b

lemma vBits_spec (P N : ℕ) [NeZero N] (hN : 2 ≤ N) (bits : List Bool) :
    ((vBits P N bits).1 : ZMod N) = (lucasV (P : ℤ) (bitsVal bits) : ZMod N) ∧
    ((vBits P N bits).2 : ZMod N) = (lucasV (P : ℤ) (bitsVal bits + 1) : ZMod N) := by
  induction bits with
  | nil =>
    constructor
    · simp [vBits, bitsVal]
    · simp [vBits, bitsVal]
  | cons b bs ih =>
    cases b with
    | false =>
      constructor
      · have : (vBits P N (false :: bs)).1 = sqm2 N (vBits P N bs).1 := by
          simp [vBits, vStepBit]
        rw [this, sqm2_zmod N _ hN, ih.1]
        simp only [bitsVal]
        rw [lucasV_dbl]
        simp [pow_two, Int.cast_sub, Int.cast_mul]
      · have : (vBits P N (false :: bs)).2 = mulsub P N (vBits P N bs).1 (vBits P N bs).2 := by
          simp [vBits, vStepBit]
        rw [this, mulsub_zmod, ih.1, ih.2]
        simp only [bitsVal]
        rw [lucasV_odd_step]
        simp [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    | true =>
      constructor
      · have : (vBits P N (true :: bs)).1 = mulsub P N (vBits P N bs).1 (vBits P N bs).2 := by
          simp [vBits, vStepBit]
        rw [this, mulsub_zmod, ih.1, ih.2]
        have hval : bitsVal (true :: bs) = 2 * bitsVal bs + 1 := by
          simp [bitsVal]; ring
        rw [hval, lucasV_odd_step]
        simp [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      · have : (vBits P N (true :: bs)).2 = sqm2 N (vBits P N bs).2 := by
          simp [vBits, vStepBit]
        have hval : bitsVal (true :: bs) + 1 = 2 * (bitsVal bs + 1) := by
          simp [bitsVal]; ring
        rw [this, sqm2_zmod N _ hN, ih.2, hval, lucasV_dbl]
        simp [pow_two, Int.cast_sub, Int.cast_mul]

def powStepBit (N a : ℕ) (acc : ℕ) (bit : Bool) : ℕ :=
  let sq := sqmod N acc
  if bit then mulmod N sq a else sq

def powBits (N a : ℕ) : List Bool → ℕ
  | [] => 1 % N
  | b :: bs => powStepBit N a (powBits N a bs) b

lemma powBits_spec (N a : ℕ) [NeZero N] (bits : List Bool) :
    (powBits N a bits : ZMod N) = (a : ZMod N) ^ bitsVal bits := by
  induction bits with
  | nil => simp [powBits, bitsVal]
  | cons b bs ih =>
    cases b with
    | false =>
      simp only [powBits, powStepBit, bitsVal]
      change ((sqmod N (powBits N a bs) : ZMod N) = _)
      rw [show (sqmod N (powBits N a bs) : ZMod N) = (powBits N a bs : ZMod N) ^ 2 by
        change (((powBits N a bs * powBits N a bs) % N : ZMod N) = _)
        rw [ZMod.natCast_mod, Nat.cast_mul, pow_two]]
      rw [ih, ← pow_mul, Nat.mul_comm]
    | true =>
      simp only [powBits, powStepBit, bitsVal]
      change ((mulmod N (sqmod N (powBits N a bs)) a : ZMod N) = _)
      have hsq : (sqmod N (powBits N a bs) : ZMod N) = (powBits N a bs : ZMod N) ^ 2 := by
        change (((powBits N a bs * powBits N a bs) % N : ZMod N) = _)
        rw [ZMod.natCast_mod, Nat.cast_mul, pow_two]
      have hmul : (mulmod N (sqmod N (powBits N a bs)) a : ZMod N) =
          (sqmod N (powBits N a bs) : ZMod N) * (a : ZMod N) := by
        change ((((sqmod N (powBits N a bs) * a) % N) : ZMod N) = _)
        rw [ZMod.natCast_mod, Nat.cast_mul]
      rw [hmul, hsq, ih]
      have hpow : (a : ZMod N) ^ (1 + 2 * bitsVal bs) =
          ((a : ZMod N) ^ bitsVal bs) ^ 2 * a := by
        rw [pow_add, pow_one, two_mul, pow_add, pow_two]
        ring
      rw [hpow]

/-! ## Chunking helpers -/

lemma vpow2mod_mod (N acc i : ℕ) (hN : 0 < N) :
    vpow2mod N acc i % N = vpow2mod N acc i := by
  cases i with
  | zero => simp [vpow2mod, Nat.mod_mod]
  | succ _ => simp [vpow2mod, sqm2, Nat.mod_mod]

lemma vpow2mod_add (N acc i j : ℕ) (hN : 0 < N) :
    vpow2mod N acc (i + j) = vpow2mod N (vpow2mod N acc i) j := by
  induction j with
  | zero =>
    rw [add_zero, vpow2mod, vpow2mod_mod N acc i hN]
  | succ j ih =>
    rw [Nat.add_succ, vpow2mod, vpow2mod, ih]

lemma pow2mod_mod (N acc i : ℕ) (hN : 0 < N) :
    pow2mod N acc i % N = pow2mod N acc i := by
  cases i with
  | zero => simp [pow2mod, Nat.mod_mod]
  | succ _ => simp [pow2mod, sqmod, Nat.mod_mod]

lemma pow2mod_add (N acc i j : ℕ) (hN : 0 < N) :
    pow2mod N acc (i + j) = pow2mod N (pow2mod N acc i) j := by
  induction j with
  | zero =>
    rw [add_zero, pow2mod, pow2mod_mod N acc i hN]
  | succ j ih =>
    rw [Nat.add_succ, pow2mod, pow2mod, ih]


set_option exponentiation.threshold 6100
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

def bits6000 : List Bool := [true, false, false, true, false, false, true, true, false, true, false, false, true, true, true, true, true, true, true]
lemma bitsVal_6000 : bitsVal bits6000 = 520905 := rfl
def A6000 : ℕ := 788374393675188612257597871122216916539869076976223284740419429078447874459482733914477452081804557001085229621810881330730197628966279171399502678192266479777145399927086170870698819671085127899988261900953619912005589345156234057954252240991698025613470335829118576650384206277522915885254862180219963090366970296673411203883511587961740647185757226868989829866972761670218248402924352481694732353732323060440629735081628382273170502859833524097884052833887311612857717282773069277688417573497196985432896608178179576087042832650777557339542248894403241570084512873975632939126611987661897420035789453757060803912816125665417382082310748930236311500968710825896385160996966030855262050994024148340120772199094384730698662541808055363598423975435435816725170822071163805492339416331738407433485125186360619621784252031528931982082855307758088257238032987081907164443679609565187302601524342448825426596191680744594779466810509628950529182130868648897956685577309906913501486993770543049935616855825022522863392312492234841392476476939442310203202349013289946586384791684755344878083007733602499702566982935973024575301758649244194439526388880065643320573957820756079797566295670640698857830868442990366833232626873082367971861474299919429757089489288834707649316357735323157283917712935936509407198001652263129118384733743695825717273156614045349979238995565716577696678991622067846409120766347013443902509980672279523231542770734059023088203329114499983235959601175567302127706977974692749850727713018142643838221485924673477304500808812115843401248593849230246704338834252125258617628177010109167107102183048822897260394197161012514267280327091172797981509345060585636067597405791371196801935023189681566841494158048242587115306099199771442678270736573413829157161277851105188122222935199576862105303022305279
def B6000 : ℕ := 788374393675188612257597871122216916539869076976223284740419429078447874459482733914477452081804557001085229621810881330730197628966279171399502678192266479777145399927086170870698819671085127899988261900953619912005589345156234057954252240991698025613470335829118576650384206277522915885254862180219963090366970296673411203883511587961740647185757226868989829866972761670218248402924352481694732353732323060440629735081628382273170502859833524097884052833887311612857717282773069277688417573497196985432896608178179576087042832650777557339542248894403241570084512873975632939126611987661897420035789453757060803912816125665417382082310748930236311500968710825896385160996966030855262050994024148340120772199094384730698662541808055363598423975435435816725170822071163805492339416331738407433485125186360619621784252031528931982082855307758088257238032987081907164443679609565187302601524342448825426596191680744594779466810509628950529182130868648897956685577309906913501486993770543049935616855825022522863392312492234841392476476939442310203202349013289946586384791684755344878083007733602499702566982935973024575301758649244194439526388880065643320573957820756079797566295670640698857830868442990366833232626873082367971861474299919429757089489288834707649316357735323157283917712935936509407198001652263129118384733743695825717273156614045349979238995565716577696678991622067846409120766347013443902509980672279523231542770734059023088203329114499983235959601175567302127706977974692749850727713018142643838221485924673477304500808812115843401248593849230246704338834252125258617628177010109167107102183048822897260394197161012514267280327091172797981509345060585636067597405791371196801935023189681566841494158048242587115306099199771442678270736573413829157161277851105188122222935199576862105303022305281

lemma jac_11_A6000 : jacobiSym (11 ^ 2 - 4) A6000 = -1 := by
  unfold A6000
  norm_num

lemma A6000_eq : A6000 = 520905 * 2 ^ 6000 - 1 := by
  unfold A6000
  norm_num

lemma B6000_eq : B6000 = 520905 * 2 ^ 6000 + 1 := by
  unfold B6000
  norm_num

lemma vBits_A6000 : vBits 11 A6000 bits6000 = (309489095254515246921283984636764660086666015399952834541700678815830933665959491215898376055054873752970996007421544537790657488704891024290512972088102679326579439768959544684782484119591583064146038158133804720253059141200262070903961970211698469698167233284340253870823770600471509140811229136913245947611471743241481701558751454801926194419919562087716308757341747269484575836425243601255669572904564036190890233167441153067317642700864000656420660667467671973673503145977321721443390021305915216977769890569555491656922445584205919355965505914745143351106993219332850331223241924002153324950070659585685977621773110381326118823047922476665054457844484532617905326649638814050661475856769984207936667926990136173029529780080996864970263714448516302394395429273570318050845821362445136886338886416255775959790880498526093986094243860041144599955927548377184224824470377947182398408704165053278261945419098566694581464273282289096202411965364129834925016993618276746885418372291376221546455864233340295707016286796453118366538332963877092720327327027811608749106502819808807755657023568329621426787387377104347513747350462192058019558082781258208831675269356869605091994779268140076544427132437383563430838781501192334662665731965498310075641460127218545842932331961407062819982204428250451631289768103996403813504875944489366649294574607299768542249512495698286906822699429777362212199814636019278527620946575202010517125922776075778675354217896963022991047620413110032953062592127837916915497631206958928350012071433415672497308376156262217236222829882840641255845404668777828617897938618640271253137857223252055312140698456475967765646771309255238584435861485823620835468473083627262875485703031873915450904874103629780837198488231274380782997994743468192473651612153830400791726810094629758960887584547319, 57374609349491457209224459415403255940846754390282521599032809325568737022730220593365945439240251984072901281208747397738709824524360999458738260111933924409509990563405071521797366032945828040876427891147159204570308672444411330405971757249410899462113436911938391915245316629994846607621205887091600642092093984090804336687780046016314051926266624515646080275938054241995496744262797192568911872064789888310311668828647405707977538041342315350368389180452511423155181020825955858281561612846645002564450817587951266758581872309446895026428924093847770563240398544962965442121789667488282082992327304245694970575393996929640233403936114106655769977645567229542636876493404614422742409515892897254926333490899684007068236218410942918099575483684972667877374840078503582291236238865284191918485910657339774279396100118472865077923631220426019255730052433007623801923750248460504279463548511522783143575094528311996960374931213373645470927623646959696624980284480013821769420558446261480577084881762020247057712665468557975390320052781465692040950430522700729610328600913281896314229746019714300350406460012189971966927786700989287974129214417802653263122013964462415519304583648064463264489646679659099257271788204238625240420978632458783524185584364507491838076059352077458290695406040494573852489170057774536854017826963445831456923596567180592254279262517065866510319237630388790172183995729600848793287162888716204477712051825912552661947199336049154140404946356180471135333815979389389809370924113200113855670563111865387459290589201620163363369649036044949613928486302893809830192218882004037988456905820193728864217382755700078215944645242250339526617847953016285691219921420111022750055634755348901676493423017086566925535275895911824149908933591465058105871737194009663358567100432494934272693767645780) := rfl

lemma acc_A6000 : ((vBits 11 A6000 bits6000).1 : ZMod A6000) = (lucasV (11 : ℤ) 520905 : ZMod A6000) := by
  haveI : NeZero A6000 := ⟨by decide⟩
  have h := (vBits_spec 11 A6000 (by decide) bits6000).1
  rwa [bitsVal_6000] at h

private lemma vd6000_1 : vpow2mod A6000 (vBits 11 A6000 bits6000).1 400 = 559504689118988767958428445087521820731035355618052927956549077938535096103560875779894176334105673241130396960167444714001617828313378185097512669968150074792514694429425021157694808232696398445964445634242097557007712785509211066458370932703898295381560809740218569641368945859949525746493647379078482228506025324913623551779429907226596968624981953185089923580931617158636544789207302555650545644763719548139919323647611043687571272778970051563753974265722370297259197534937202579798191998198613403425123450808889991664850227697734231996212293362304874876623530063728915087427293373228144436467173651501464538772627538521621377441598193044598180137577771326197244619419501861299927777667262970406627554388089805152540826768709385545442821896655943817644922578325947963006207112203116761901332085493264810871379929132836889219332235726419610040984161122435886918605828889029370450303526986350914217132408488947127911297999486649086716866027685994365357197112436401341977843295056863694174660205825311091967404054294689118221950762732972233701622620998139953530382198178916269656631061782808704109081110903231141758251364119458361684326062021845820388773055539214571472825349746431277296757834046227910681121187395015143750345803778643955392497531262350433442880348107614826213333227378807613638720421508017537709895339291271179775811874099138001435555418842903680776195639652754904176452774588949046526374012735395691370287876341838433479100347871127847589783265766474197717786833140212105987845482280920983420085308203079935949432562109407344930707311379426233824086640489482604491798045659871753815693557400242943247282444925075469464283720763831845669210721737384450721776493986694002364521161883560232880849142811390718993913261968858251636083679001834112112071949794928180046110001457995065131775229490844 := by
  rw [vBits_A6000]
  rfl
private lemma vd6000_2 : vpow2mod A6000 (vBits 11 A6000 bits6000).1 800 = 357692856131467486754807676062410282354549453381180348329701676680394658483011753462934263523634480220381264223649576737875157070591417320228314158617547308088568422454289265863947893617958140751032230834156066762063890671169224402513241745533066047840629504650772259023598297452766157785587745026240263069990888281990737514165097829527891652902686547827199506939199717304824470784577125028722030439163942849133076847327696763112460057242212802538575233494947800540301325797381659185461602467509025053911894077811496655192073101923195031725420818389831438712885355827108331856700265016321699199346975418088462207082202567207443400157596626101275183184334809430871604644956936522507636323353279620844652098933924195963381193867952578334111948917563049097173291643075138442423879927549011775538846591940665382335537124990911593464618696314238099736294284064436239238151079799704911855719553574249095240475401509437013590075523188662193629048982642931807792263183129976674508744268096658177089946569088880910632182642772982065328596310271028215130189718586136736102692287131980453089614409191431764160330664708693910599354029159660379519057155120838989097206095252901715406495204749379491137978859415446063528557755146910454817055830694878980146928023480106153019230876745022513096196949061575256149324528064488866102918229107861607216991646413924852578835504569842820143824647915074022228650741025738478297789990142407256984479517255332055751850289005675111734581942368410450579117703492383221144240027077877991734282786550682041593570877769065396742839886745220391919612256805518124302906006738666658440752995127567378104730018616302147659705650794064629388753777351472339285591513556132279987365348686959009191641219394302536256066664839032310023974514039587060527687560812946548669396305331145962223882880887348 := by
  have hadd := vpow2mod_add A6000 (vBits 11 A6000 bits6000).1 400 400 (by decide)
  rw [hadd, vd6000_1]
  rfl
private lemma vd6000_3 : vpow2mod A6000 (vBits 11 A6000 bits6000).1 1200 = 279518729342590766502682233871627233953045266936119256126656365285972114700215601736464013000390492557419481377594023335701148236953120858096505804773045338808156484882025500797552911229982311969311477024002018729764231850235745067756874387804808459265214313442389363650508748402479982986330366063667891603922326761032241528957757496563741157606316270977324940120340700624300245526230010280450008368835611201088395660034328290499675186065155510341985957155773362913930711735033024571910499738240864272184093599052962018063331153817772061774212533743084206900394955111268087478272254148728742802984396901857155507525956934146284425379032448585098813301554526388045112052764371341269076735432831843852355615277251732208066800828314821037384561342734438534474919084576627726630518814026105835418428348448560552531793477531202434024577684504251974025828593478849633268192406143619719670421497816569741145556194498368545850705492565804356359585956319782397212435598447481005277678221980882013299611489055382626901553386791347659503090001155653548990803334708467732636866385994152193092139431537799021823192575125971843404606195258155629267747599753971299796658301890754991911531085153270705368613168317037769758099499790505796968668066876157725069365330249122303668827579368061039370833913960860736635762725234603945744398024248225707091490534575162181389327984886482885528751272258589139674949547623587395529470312909834119627779476155487393753480493621933167963570787044693687976588563730050875530678412316922885987187176568047264000590274235550290553620945670967861119312297791500030237132197759113879429321821411059940970292211186578218755251436954782003166825988165292520692008877667551770878862922897824831913339372436448789090980113962569904296068735898649708480098480933063274169201173464728159640687028099037 := by
  have hadd := vpow2mod_add A6000 (vBits 11 A6000 bits6000).1 800 400 (by decide)
  rw [hadd, vd6000_2]
  rfl
private lemma vd6000_4 : vpow2mod A6000 (vBits 11 A6000 bits6000).1 1600 = 536687011030008511081275756431846040715160402197295478196080858013861757256966058239570815311285267873194166523228968322529643865753452761822011976499642403557741239961500075650346173762633984443256627988735382106687700598711778830007214759669939709067241093674444168244345682732664036066174914796901285979731262173088100267301223139062372874569154784216154562205036984969466984654148832235289121932867581928152169270227370873036841476967329363615538176119172891072673239878420441244260808535461994424520913585809066469377154161859949856718959678722889260629226136144352567967957881084464938627702972370307083506952408447847016255202484847229593848414919013386878769786085729454360448094202823561733333689978152066103875521622410326195404451879819219337022119588814016060000969145341812572414349661692882275299549843747557340569364906185616875235430627644691096217030126843448498742882717481792526985172769268237183257810409353772475377598910378568682673823295344784062228533848062644048334825012298798347774531525963426041065400251469770555477251242666283212073647951356884728035022903018889511007892901564830618747277713738644338269855089000231605420959637810573769009328742277607617526089725822784827019968685399677170512277021022112503768246473324185606476004917069560454411980717853864523031428383372371524854481959196272904591139184746753747054386576031300062769311367280559828989272021415322912773206085557934571739420397050991657411920761913337557350651469704795783015863255688577893035367189196623825371807552528264874522848773561176185978676270703603328723081976797332061968433131647847204640239753622790400598805434885588033797540811676352708376607993811807190722864721833097725924561688799114830846011562519901338054625494275086774779598939590003192565154717018988501699540722383639110878869637858617 := by
  have hadd := vpow2mod_add A6000 (vBits 11 A6000 bits6000).1 1200 400 (by decide)
  rw [hadd, vd6000_3]
  rfl
private lemma vd6000_5 : vpow2mod A6000 (vBits 11 A6000 bits6000).1 2000 = 184945037508066380522433920071511202714474801566806185280832403277976460083231186854269777449937285187377700596266494029706584834750535498262628987103353885185776047937339333239568428836696414157720220812425031457864096646128835781640470964865085027528249179786297600943199981466152527110763819984436178939858772391502062829565687842002762144197414879494850446551189780341365887135182588927547874741247802843146810668793159576936130013675183582288739869454491554169130113821647680998176439575294553276476952791653915383947172266101519424988532177538930038685790773968262811919918499132948307676996263350912122098602878879708085161180838258336708097132290134242961255271550148761041246080777711502789059625999004437012642710723125556868571639072703246132150041923642689566217154684153700746004410051029087639016024415499120569337746510502157147905181406072700889157406102528185939989980049915283843980760930744400873811011290632490067282224600391692758344676923972575486684941977321346695454201958804645939110086758411929425501194933554894025498991053128605116258841623287342262788580703195333599924208586335112231653911426897209954840654574442871579718246362196797081467727393292195898145505963294829410295606679299947790759400086553861266128983635308861561387482766736585223344140525120902292130792706240818792981982398028931078158963835294993405514289801829115121818858934032651198605549260720203249372726371324383752697458307514437327425216398791239410889645030201943493924886383551435700130779105033733750630652323532959973882496615399896577485897278142301513766771037798753394782629682626287476612994528094240633696045589849230733472888959919836896233283778370547821541693804189412166011746031259144702157555277920332311875062851514019818366859767690752328809820544012850920151004152189057752948506261364808 := by
  have hadd := vpow2mod_add A6000 (vBits 11 A6000 bits6000).1 1600 400 (by decide)
  rw [hadd, vd6000_4]
  rfl
private lemma vd6000_6 : vpow2mod A6000 (vBits 11 A6000 bits6000).1 2400 = 308910327603515914147595996872949044026836175098879320884407822963287335719410214424691597367389478043845825730529610279050434355485738689239038471050416732783675918142618854479190705227973589381792222481604000650279130007727160127893602418542452806805723098459577828127369823661608160616703878554255199796019310903017388087629361834291287218931223916090329804738411874452525369686391716642391046071658550016195164467982320894387327497160605858343583357211248416309741736214465494695984443172363178311746138195197179113651335258702790197600890982536083738536711743907855697438259908949071414363851570451814140547817797060584287148198274225091956559737455685101638684447085592630151797203026599214679386416323406393107019287319475423375463803536643654891762241370712505967357661142027110743502249975486961829638046013398990494895144607765808431790837119335808759090139234030637319638947089350250720662946916728451314081499202190014312821928157214934478324704234378136033405205100397889483362532213570551534603529956377644077642478892487148245670877979796573363880040020604919607078112561328353150194779760396238238200496454478222342953361583011392660082180543452313322010079189020774380750299750982573603826624306455144716371464542263716937631723692250140658491938158978614852830413723709048068090307126462424618921271596418119556403218046444529995434573834938230722549475252786655739177001642487319490527634198502289616276125985703876709094060764650957837556118538660753149798554425629435558423311795225312903837459192143767853099265895107047735046961638751115200443820226943508170091363945864199119802320004662361415168811170931862999264514943469823533543217586335391301179244559894634770460365324407279229470982569631225898596375609313732517794329061203626885594971383898111030063095147455893130405449806580684 := by
  have hadd := vpow2mod_add A6000 (vBits 11 A6000 bits6000).1 2000 400 (by decide)
  rw [hadd, vd6000_5]
  rfl
private lemma vd6000_7 : vpow2mod A6000 (vBits 11 A6000 bits6000).1 2800 = 552580984959096776166391970260404163672718995352142373828619076313912909138115940019243504576785395723050322898808592542362042832769289288105715655894560544745466340181502234007684544985350587908666556633193476405203284178042042680567754682126603117142584415280103772968851178430705148805732170419613676515400015779892888563485434768191251438190540166920049437241541044134264247597942899890561699242815842732311210941299623563901460133470211998971911613909423644862224415045157126703706848651105636982552723705593311960973562152130632755302933731404545713937214904866517179345553736393666060638888178764490714599992027065529285341191520259183024559707461396562301894247796953351330061212107974932187720103480582544389477142897617005998433346673179585381648660584401220415181814183946363685880929671819170224076076823589354971342801045289490553342613689708433156688308247732073783101115744337170540750538153783724445465230624238445409914534259818951680824863167424922913897870482267755374661654235999756537684911049749186227358512487014411529473886692255758557802188403952033035307584769760655478258872548640552719490848783932099562746329291857037449407009316910543615828096082180624599990218969033180540134777134087295298751885170363354327329152800847183502132353320976851056637371206536018860963967945257549002681347525675235656852578191104391007775867466468628657361923858973763981822836647138089618302658965093572053687348916845356561939868714088363367796675418275007832894343465888504719350177364450594061361889620480182122158387550961783554597815192631495874211207530521945755080195264329869633319537447263549775281131412370362120238882029666647000169887149310306964471382062448934911972597051256163872420386340066040384579331035475248578483034372562193021840017675259628778732980583324626751468653612718917 := by
  have hadd := vpow2mod_add A6000 (vBits 11 A6000 bits6000).1 2400 400 (by decide)
  rw [hadd, vd6000_6]
  rfl
private lemma vd6000_8 : vpow2mod A6000 (vBits 11 A6000 bits6000).1 3200 = 47424838869197389792709244335637828181941797235190715887804247713126571224058406368400835474850692864795557469498615536085345601263104181497600304721434362115773549798251647176893178553368139725076797803281238260843566101268678928533004370193881373420411076092071208933868174651079123036642634368474403769324864626285992455733606123041749731258362094316049820423210774553659218705871956731252363400092817711912485226094408185438896004939544853935164626115756649591115604933102329834469505041161901212067411385191935265477463334947080558329331762916745255036059614609039427969435190251261879743149522790239377310534302560484964763546715170111747275732189569385662024067879986765788209606464126944465599166764255491922421899517044807795077604683861134312981221873674270755956525258415442871440776628308072566040725418265035963475320832582415007779689130256816265996179717747589414317466593531842378789826701355207648402177066105718475346032899555443026739891740614631000934490238558994199183240916752403756139981689767213839599489616176897934115338539538319780546195674230911923573608940543751415504557862226624176627009174090265295490280370460014699313643305645694141401829629414586455730552936910651066449308430957400145305369077338264243614146651084217240263698727211452890955926386077431073093659096388357932584664871048920331924280762623287868986129080673759269578724590808718448089455487694339409600873034637665058402587000512316409430130427231402379023278355296047549053183394913960348141658390239425149143401867061914793047233251163320276802830756559981048111212133905653724164324855295456852987031986017349632617103122154613502168672982238833310897757645413902211740669272948400576144784224534656055077329990209362762859873698358275034121717013439632888717732963100476921881091222687677851439850109953343 := by
  have hadd := vpow2mod_add A6000 (vBits 11 A6000 bits6000).1 2800 400 (by decide)
  rw [hadd, vd6000_7]
  rfl
private lemma vd6000_9 : vpow2mod A6000 (vBits 11 A6000 bits6000).1 3600 = 361923919190127988360647227283041394509076056606050408157379409912373935737718320728832867676848724515511404487786522688233476926783730034708077219073138691594242888615285100240557995401179645627935803114577114506671129955067792158808021564567558728672487931582868150533598781803717122324777569038877389115872657866613059521263041286575810129292309146446137919217811323567299318945969386668767922335631568748258821497033556412800349703996286771688504832560077222590840128216434134393495303884627952864458046626023112629804891521034303446169928319769964697542190938917167542690135340138813785421108465345430091657705790707708010502103872108328772840087985215898888857396606269528470346402629434141480545202267333242703328582236661435372527829587488111373443015301989690877870641219378428987726659100046051920577662634817801118976712885915287480384607334655501726738143695374538521138030664806440381946629126497700629513804967184752410253685817328413024989124016737788932703153321302674853284509993255602317142761040489613279221531448227125318965433294892258564821665477206983764766831278839140578207363436382484191650319037614505572013341106636902248888994413698962564417053791240826164503251899579616134402245092648525412176337665457825930457719386825512360941352404285954461230008155614915669300431034177648233234180919293462974373280905120242501412890995784437070246409552610710325331741480149398447595109119291371718048024704559042636117160113461981420094940393944791243023050164964960815330097746926972392929655475254431673746013550786766991814047575886347860148151511069817274712834743087191747404157408692258513900255832981349686472326615615807531248015366272019068765775087714031597774689863034194158540026289112325497271677893247588668236865867397108453826138920431475210491880073006505400715111008310671 := by
  have hadd := vpow2mod_add A6000 (vBits 11 A6000 bits6000).1 3200 400 (by decide)
  rw [hadd, vd6000_8]
  rfl
private lemma vd6000_10 : vpow2mod A6000 (vBits 11 A6000 bits6000).1 4000 = 365465654130928990586893060343960521694299183705543266228158911306791479135517292967661956625786436859378519854484475293244386066916656994402931681216112840805161844876410544733929999202244011221128982433535969382631321340403810648381620041080382445301164641970764015922820760560443587402051041464711659707176366677776704403861898115637020883759120813318256941864636391420636908777206444383961581504146189862260434032675377194941529827982988846552276690026457379894869711097535631974925011183424028113190730068068376635959011866544739295952613937944967191265236467662578032650368401818900538490231187182922946984622934739208336281785796553723060140291276404545829056715649049837559402477978361261018221055183716958401624864415299609662960471986702721356261425043744664901501195108053947668979485974269406947163734354034056276561652710993792907691848626086709866801551018466057661494469060290064583809283351550429680868758959223725092502209171464073739804325015382514443326948146661994588466902710761159043885155240281225162135595527989419473949078580576662872264947566229082383083537186690247216081133774626434381183730073389256271759564349145477286925302982930976254955822542995241040658772899198122598681330576955888940911368562732564668484922496757858154797800760028131805070856773544082966710441240139022717743998704986181383061764438497117351906185508524530176025195688554466614339704835111612159072191205641243987124583470027728033485554632307254007843836500085642175203125992435096098968193538295211125914403351843745091392123413691698188446144982643881803284608763966204105892352499134201768808603899814250178383681876291126357807121828020231453774354272622879564270842208808006494282309654514133753569435937258160041366295602942546395646838546233606470244725933655357072164320928328987474188276942380294 := by
  have hadd := vpow2mod_add A6000 (vBits 11 A6000 bits6000).1 3600 400 (by decide)
  rw [hadd, vd6000_9]
  rfl
private lemma vd6000_11 : vpow2mod A6000 (vBits 11 A6000 bits6000).1 4400 = 388987872213017024559195156536818156517381390075024234427460773095792597926875457782356933964615307184091305770539360920253431302863947171322863094212437608682329058739545323465583620802154565435112223389174830994797590614189128440798504116514438468522925784206176073779701142767306153387006963204847986984149542843132216559733447168036739862166405408866466967489515220332427812815397470804378563660351416985203368439095409464359975998635393760740467855934339525015310005146466888572930886544117417993183266577925298853805288640843791580787567614949276883431063511908030542353367121824597988936367726667582761166203788735005119797694786829059012959595641481508637290902241694836468924353407972407241356297164230930073094974804068454910325391041547266735165453171079942968869565073928599009252262922797956599521094352529716261621886100823537904980954630268741149670467300102806921860901605123500794195606841518135919907949284545780400384943893405071645468321385538074474422059280616178150579676759648081751717467519780763654559929365132816492284462558505941974794896449069437511532472384490036083421526232331921009387374062885362070258669958759533977364059314776082600905921770971049121897391357253776092282192802576577694940035203259462230038199573498828485736969429201327190205259871133027409142204774403042030261097362559361623429346617371658452620127504291713373896341079136897054713474717412679515157474728195777180512295168958858056896591436572749368917459337341446543040393260575204087633971534800763602543355436796772111983740416745026078309525357189980835208767458764586194306299105122294895240863784940961517338773382430912383068931135013331108194270731795584659399622953304564091770289523262347349258594622344093700162279796133147580340160900845065329700943689922254642102420947514567832987999146669104 := by
  have hadd := vpow2mod_add A6000 (vBits 11 A6000 bits6000).1 4000 400 (by decide)
  rw [hadd, vd6000_10]
  rfl
private lemma vd6000_12 : vpow2mod A6000 (vBits 11 A6000 bits6000).1 4800 = 721518953026457628737794620342238341707717777993803583995830876057266618796690370097890754285732071484066292771977934332804126772110439553641989247476848624096785978179994976359660575760653870488527571425723169065578303163802855524687204904128770057655906401638692483797040115676494335166420774669609083792978181592099377574738155013149162321172680334327787252676491991351031897501341929254550610809442103660444214420212977401516627014799191745208181116444609627613182399746996744857458026971238433017276679834395510089022893970758003255830490661589471142254122925679531100648030522337310644165854252547080517999088801597651711687744416187417792548044654006687137169110924149724001659094823512636189857378904563504585912524897194860030754104083064336628734030086250538482420940268140606772297924289430378369563222183081064308474250053588496651475975920347365338188572590740655209515730763204684989924846104586247779573550215409364609006870875279814431552019666178442034406509750268941862120567763926974905870030334337521598650826926885384938129828231325787238648649776354292047198088078700265363948909997710345568391053238561010116917744332755362065995455712994473456555295895419820046645397895068174000432052559849106316414167510062763866234538583422399390058274764102256104770830668959771134916208849106616390366956681427609498871064809722123229627928255605619206396571675641075287758592220725607222137002373836060116140031360893103648402219152501218953537971182412484077204025827529569723396209861023556751860116796678067794135886169944329610190092936984575053661828651432192870528235300311940513445310851074086151857371604874271016747564595291713644068806152341243386250738016315092350961606345663695400048133391624193922325366769046485857190167321906486963126682640346689699962974040409401711500679677606486 := by
  have hadd := vpow2mod_add A6000 (vBits 11 A6000 bits6000).1 4400 400 (by decide)
  rw [hadd, vd6000_11]
  rfl
private lemma vd6000_13 : vpow2mod A6000 (vBits 11 A6000 bits6000).1 5200 = 541651195085735146446631156370286597119887678939933584015155088027720468802094498291166604595491165498070915737944586100798259268091620519567992157548518678092070471123934045220276694793417714417364095857308821466691019059068752926345594193524354698331747256114503048090267775815332740971443514461217895274275973184994678352409980018390403390112054803150010100269075221086615231168351099124900027639575357632749408464794408995741790499302760122966624810227215836383011655235048435042901909853007208505515778026454002901696343189007761040499619092151316695713241892150429178967400963779959446572269526836130036208649925966713228957509234605079528987785463999484118216026539254757627333336697097677788784544399537325681685602455934853752245871853001917039122248025816567058790358153175758975229034106952031825819163841403430443259080924563299961773567572863014513895035483462452163925525808270751810680667232972103938687882975570687857296000805863977947110134221191149011168604399238451319475638792959433560500814477644182702654551919330493474513195408822965945501734155842282284418511293377765253228443918630290986273748218686558828937787872414343566956767509215068689888387461098438228366628828959166375742544495340430520258960962475755633647154945409338073105310206312696225473904392533199116975601318337738361376402527455400949943524468143670018825993220662230086599369001397181589163254391513688707397132708447497811425400596592898696625174454639496535788120587294860514117968250950591091630204831763121279319781045465935672218622622014933808487630201848128131861322947623907783055234922974955259903029665894420638237645683910775055010073040848375361617548429551629312301351374995250111673340568974088342711848965297594036325853991433768299685298979960833217462762447647397737652157398108823231983107001668366 := by
  have hadd := vpow2mod_add A6000 (vBits 11 A6000 bits6000).1 4800 400 (by decide)
  rw [hadd, vd6000_12]
  rfl
private lemma vd6000_14 : vpow2mod A6000 (vBits 11 A6000 bits6000).1 5600 = 650936818091428121228634268135979866112479692168988256375901219901526037654168945532984991953601078472855297820799434480492287743625731594388536892695890090528589803759538524093742083283810017042700557379175321592811073541918567148052215522271152366059804291752905298198494719807109452824815684721627645660310783274247880328071435113377518869480104051910958113605792981513114140619508182949100693756283377498358523310553040047348170069001715664840985207959963317659453508482064202042824330428932698422769768700569439188297278654940266260792545899037113182744256394232707056548624995003674912548315932037838257967969680867809339574057853388207632487968174070255345272348715430217228915823065263754165392827053056798591232054783901203285639775700819760837524122257706456820908294039078167237909446925872203605067577273888895761471522334506927404958485464885637168792866396466807116519063821033260386156926537658068842319231414160091951788812980199903793751364797889000734167812097191043734696308222024126528480025788009580899535648530776890196068971432271694207283283855991859682050831331892223522506966774952466235178543409835584090181944628530052061937318940040685489509629882910887958394527735551645382223351039624623889647659072304398869909393346665515853925212955717846931715831799518220622740715476460885008767557864525872891533203092084727691173985583918769812234064883710044755724500952544306837987464058403776078501827433047402697950589769136152761762768095263557174328075113198684228813317723810024719617372795988596181919024240101628228286667567201434058781060012934593842332658393243327825139111422940119542761385979184371893304089754541901922172756764754881775731355383109993756383743816112612469259790056837220387091121735126263095882695426431452204174633557935297839947876323673665762573218705955533 := by
  have hadd := vpow2mod_add A6000 (vBits 11 A6000 bits6000).1 5200 400 (by decide)
  rw [hadd, vd6000_13]
  rfl
private lemma vd6000_15 : vpow2mod A6000 (vBits 11 A6000 bits6000).1 5998 = 0 := by
  have hadd := vpow2mod_add A6000 (vBits 11 A6000 bits6000).1 5600 398 (by decide)
  rw [hadd, vd6000_14]
  rfl

lemma v_A6000 : vpow2mod A6000 (vBits 11 A6000 bits6000).1 5998 = 0 := vd6000_15

lemma lucasV_A6000 : (lucasV 11 (520905 * 2 ^ 5998) : ZMod A6000) = 0 := by
  haveI : NeZero A6000 := ⟨by decide⟩
  exact vpow2mod_zero (11 : ℤ) 520905 A6000 5998 (by decide) acc_A6000 v_A6000

lemma prime_A6000 : Nat.Prime A6000 := by
  refine riesel_primality (k := 520905) (n := 6000) (P := 11) (N := A6000)
    (by decide) (by decide) (by decide) (by decide) A6000_eq jac_11_A6000 ?_
  simpa using lucasV_A6000

lemma powBits_B6000 : powBits B6000 19 bits6000 = 653744375591018926079277181180548869943510178796405090321579417025856622839979501417644913567211484406998674472267980986951519692004981877681497345494802244450213182190706997747077303844592234606254617814843816466447881755008511948572258563969487939426859774801699402312331757521297645777074204106798576620478785231330348059976299842594048169864371940552358943776379934793094712531975840721442124543774181747237747079198315758309331511886954438362358825419150508440417088656285844280069926710250456607800545386228851759954779264247048860856546650902797672584659117883932899413422051661784090092620043542701068104241495276403642701541395060721380278705754649230659043360370786278377591041375773161031931325349281245817657626013350855520171789258389561824110495698274053651970020541065863906878467578328906925116026425517702070141440302622148394400417631159643929944371359731368481935604729548866757983807838415214284224056167777388446721158320833791295084948369704641609974892047696667092821215517915186532392679079170393002297778475908208996899166710365011088995928817431103261429265854371114856973072724762175158739577271098844866758216647482961658495392615775146766256340070233433987006925651898987976169661908134035489497751437165318644114833769750328152273867838828425303592806789157303284286799703634970314306539626275656070124354226921457098346112491093261295114047059933942552935864779667368033212801330445716446014160583313755463768862403975852367893789687076592026604033919996210858836025077615468296210411538226275975797229389192556079954264385290359580477696370634988205092905162768439835689947009996167662698299570879456056480561371350278107140381335036418254006939245288374454878565019443486212191312708161767096592531655680535000065735835896048908362882983858665431773859829507769641637210276165947 := rfl

lemma acc_B6000 : (powBits B6000 19 bits6000 : ZMod B6000) = (19 : ZMod B6000) ^ 520905 := by
  haveI : NeZero B6000 := ⟨by decide⟩
  have h := powBits_spec B6000 19 bits6000
  rwa [bitsVal_6000] at h

private lemma pb6000_1 : pow2mod B6000 (powBits B6000 19 bits6000) 400 = 449012149653334043752476788838002377415883645661400131874552923273181379440740664125813290810940877343025251575765377430728810008868557568670624552126181533751616151214888356087818434764978114376978224659705324772448744636705726169873574141147640763629483869466447345528141520625373415422180761101216710324220482441654935853499266356153209840440517369578594551373387104849000826911747599702447643812958197281980304194698943892008531615553721762279457468007790034950989950063694191808649438351261393775211261713902993245732844756850228986714949116438530671948010796431011773714012224262631474518416275244949303030335255197562833881818510306819629652479644482909770073318809879793196274631797415594964092805047601272089036359233144850424683556961278706535424867394185534787542018434563285467568696431038972892403363620452027835089920763184422573712614161148878762524069399999754060096315063880576348746064049722930943829071803815545676109260392898314530860495835801367131891527509868804417361326639500252812688552331190032355678122509118552651555748436321837615008075757150431398101014710387850841737479718752270059478070265333700426548969813843988905594153590492013658955369137134981603583684691844571449790837586373733889515151515259844302204308660341258839925421574923207155423150538303366721025325648055004241711204449425515788353970771590383948957929252513478611350013579775947733633446097259076802135782896371144877120817257965935000388300545405876504727181535429871459022633396829281218285349525161010247292051777257315374632355180517398805370737470669898929440551198101520353986881999603017290856328679304349009827725154850033384728504735540240295338262808684236963030909625103535480840092566921674544747985029792674872286019386499208290402845691074626816932563537877814526692273229285207185902631008535175 := by
  rw [powBits_B6000]
  rfl
private lemma pb6000_2 : pow2mod B6000 (powBits B6000 19 bits6000) 800 = 491305494003692333875576583035127502297358632610744114173801022789175662090942042268110027567125986323629412194761917807544893424688868363824136706714422851854354445696631698611644375296902333914452889915881122704927857723595583803022011656781077979224649833411222472690762447621022267875081853236448231192498090136558858205379870307985653040603423544126678350108015866118428520473391105029651245315134605888678337466123904089776495506898586309622846746581561381883309049032809465738797349586273591842191039691149132597785739013700091134128624511261920821909016813259017300314132363743165094316015372489044924590431385909339984569011872165341550073913892365046815017368685928795960575766670482419704336176772827652030863779718407425328231113338430292040147926331101851670116412623329546092286235248000590608108772932985922978044339718668942454436432125743605021910176731464683819745641336793314272848278375792322243779844179656220586040222708749801834970366736842340544078470665733231001781441423350557840562227307541824983171140436928605697668329451534074628923348029867539181069965031808049861305435569925091851996378316449889632749969763065140842782602676785454814254252261882522746824066256706601735774321943440608922546346352660514635103182353444115933399037794762754791064434678614155292384746080829628720395214655086102336534276031020379654933537229836700578222115327043090337392076824281281447399930322502361200286446886804894553694059069478960194832633192732027682729867718808030020039052619634952872270851548284268303123193035270573955984480360540304349620030189121927051811214742787310019833988666229721510890862240742247412712441837665914319588953181867561503587645202251834808269075811524845262549000305622747999442982716506348446623633525064942279036457491955626587634319493741240948128608621001557 := by
  have hadd := pow2mod_add B6000 (powBits B6000 19 bits6000) 400 400 (by decide)
  rw [hadd, pb6000_1]
  rfl
private lemma pb6000_3 : pow2mod B6000 (powBits B6000 19 bits6000) 1200 = 722001931027617434213093838787267201139171179084866938910266281770205341003939434453926704522153706204118044406903777283675763112995024941113060152871928582637812373284610293014501080799897784740932755074308450011685710677369558158649358742120859382041445844345785062453129115629590420205725245301374663374042212895756064719051531879799672603004509599843168284530948535837514023458364921551564613488654259306277302808966363201691271389789345704455796356479265530664982840819147907625716046574151803970838280911778897729796807757625241402395656517970718429351346728045937283605773917975147253435845094237453240487062229354125775745006127720037700961506739429078631488592876359631880580432853044890573785190651820870507958608372804238054211088162139377787528514371534007093296416542765186155900685939550017829101766349254026793517790537788752628192864103183531746207947879884479300692135176877335369494445702718304470209756350159131765373152350152323332828199832939615089458379264986433578867647705698092591861845855228670101079118782272934446668255765813435746126076535903467267898938001886557732905261423729347137517690051875719021439890728019613431636028308766772440919788590118200808601569339440430405691362434649859375848146011135643447624960566530594367129641273025373960226470528257824945030481430949058278205680597806148392831477480748218509476848137035453470913434875408405107017664243432938067025004005919272248408034987930712543935855852739848456594438162027708253161522389043199125400889255438649127600355582368616441320614036484864589809106047091782755307837415115830621789013393530414015643763505818359435102742274316772879035140382507249329769951397856323740884165614971024793182557755711415518254389358305808105384738958183587254284680521569087026106424069348037785603808711002350252222026918509857 := by
  have hadd := pow2mod_add B6000 (powBits B6000 19 bits6000) 800 400 (by decide)
  rw [hadd, pb6000_2]
  rfl
private lemma pb6000_4 : pow2mod B6000 (powBits B6000 19 bits6000) 1600 = 455357074678863975909826029650588354413864927780707183864305979367437810786934026301774353452124126421529304889626891611997899474342482501115700821842562178521709225892798322799681168446312273805997196961755753608626150191637588487313664514618249691544584692435474338647603015892195346510227107874392706890297293666430470140915192174717093355971832380077803991933947841230226998364589547219402793664773813072696833183754716701999468154671409226011802212232632147911468154342822219064410629299198167439878740006750020759269356968974546127006048595722647150443473644667644287388410529975806132665949884576942088961577579419263955583614770775397500643529520788113014363067778754228330699924250664474012864915092405199749795081194848458443935149330924391150254672649161988842709639532199976789053936289050592827922894483409799998599454385819736311447683627086890435863029500595870881126035332263872764881651755943215175740067005426343157883488732984358666849533351259180421292219182934268890548588318163301407456013219344698208467240165455930347109924430664525605654429559535612771972335616903307137295540279330281337227277147931501572612613433044979659034692125391291340608991913720587916329767098115531886573149048230281890864497004156432253735142476815811303130039895264242612343858358569799409734366641018269493331681940454697768998865930602673748394649327125022091539196118895576950863085798368653890002597191428103093854662922254511077917154206180595717939199435732485918751879320044953257675043820330375584429696819128961359094328200872469593860426904946286194223490636768111504503551622449914087161852998941826638679031459562077853432210160951069752993410987481870532781818584504265859791274466138234511126542331236577542612161595228521793262442466008333027852745239631435614134414370367178767291638658182107 := by
  have hadd := pow2mod_add B6000 (powBits B6000 19 bits6000) 1200 400 (by decide)
  rw [hadd, pb6000_3]
  rfl
private lemma pb6000_5 : pow2mod B6000 (powBits B6000 19 bits6000) 2000 = 78965447318435513495550398919053167993070299717925269277318200558247292187161912599775238827750895840345090121095711844112326940852997218032621517207532120585131377478301987864557759262239167762660460272021043811045186278321921739616298307444842763819260031878864970834038785430966710590454166505584953537267400529468307046449872138679383454206263941113178481382961032422082809251653044430717943393618094607395101185179636308533407928234399213551514620063002186648080908210399920768037707652647561269447903370295180930586468635887852783067970537959552620346463642527812624213807398072220271018649279894703686674840639216846412301704596664465294630904362033912514460409582836184590791520756174148859000674976069317729590991759911355183851382441884168401288467101951731626657344945658830783585265320239875598923404657246725238206102230068376728678090648627121435323424767503670098441404515630179904568792628035423366834805914250565697258162888869926637251751128603683953062692379520448137691169400688706695992389243623673817818984342725777399325575925795500721534922995302913726299637136041800848767034990143108202280920763212875423707083871218727958944818499168766939836430366031129556547529038098829938662122839673298687464783966044228062934801734012377264604567116944503786564878175650705944057038836402300508120499166531379802811138112287357546372117137510471515436424509240949878743305574518081867698210732859204829277703765269386770893595662179938940881505987696604345347327271749819508336297755926043120820934536850141779258294694856936431472773020271370093811503299899139075871992090510948200536211903810878090818471367701846371958910216289119114126981262035701867832686563481642462978475594322428648816656971293502135566706153525253380083413896299305849520165427256553940054331977353030874351182806353987 := by
  have hadd := pow2mod_add B6000 (powBits B6000 19 bits6000) 1600 400 (by decide)
  rw [hadd, pb6000_4]
  rfl
private lemma pb6000_6 : pow2mod B6000 (powBits B6000 19 bits6000) 2400 = 480084437270034206965379245584608954654204388389527783773680583082911006410990978864122180569745188585684832150115088866944038168409897462742468335266367438739211963046850529069000134654710086314654352839331228296587532316934845909921777022572556292641590990977338159700820534259471140624281881642438234708707329984585042419106515259609457819786634586983309985797212553413215958149620565937296248099301375452524091017216293612098863714465606386704915911105125411211641649820055949366064688643060257771976466781524551034950639476042055913286811309873888856854829832623819103674940493877187394248627652659966124864603742629649732802613814659514792292104963127928066281032614517523274489670328044433738343561799331278384687261071699845427592418458216992659623658415410294000329025808970476183833443224139793508845605498713510371816317424110547292784704696622045259524689725102552156937596269861517078973130408108185501702991964082343279014998448165801537113113378929095269320784879659676680781511039222590837562283635448283716257951446183090905948593419648110068609711259289044911684247172012886240172672979325757684816887904824743154959671920986017667595723623071070960255586999812456715385669339559412833244888890030514196415680451185481380934598167463897608768015576066947449730874491295491179013495890676846642031982266400082407989298536596334449178497201703136093696737297857065384397195984229631094423466323793503107869251702916756659846281410740694039014484873389836374258775973800072107712399295292463903096218498249218481617231374142878678829252950309069102202315246336971460181432729804219621440333271208017273585564957927921443421630514206414120421161152285237085580175572646177973863606479548380836808782489444936317432784170550544869165686247213988185782816440883184898441930725684617972701224834094043 := by
  have hadd := pow2mod_add B6000 (powBits B6000 19 bits6000) 2000 400 (by decide)
  rw [hadd, pb6000_5]
  rfl
private lemma pb6000_7 : pow2mod B6000 (powBits B6000 19 bits6000) 2800 = 717356311021326452129239650376919018138787576109108295273574850655170363250649643246850882235232035125837112838738706148529222527025405972248215841397329386519847447790471270651847958389966849952012085256944298682203917521181143344358849536262991885768193145744666193597264854861862062738805345518054761407548174480683477149856341992892984313989501577116782846744911731582323519907578446644840122225855344512662584253607803662697662685474191226892653855572329706940958931829353949029294651964598450681687574619562625643724205704753495251283706837706265595193260965247720589821102923192856112821019416401045654947031829236775926147086443863064623746628949892550190838973353881305008334701707209236940493342023876190798462360856445174944297799605835162272729961496781408290040518521820992906429466391224383394722000454590108304438746850453649714466671441303652870861571345989689736609889874527934503383712501207965116014043075246194004820407028205789240096749908048954365931723208395756003543555564168786942045597944433538534070667015913696788972920700757400802440860154776528317617133226641929748342810646559785983902849378296676605413513619893662863318440446074955746550953119198773938798837747824283932889431169481451066263312150591174254017952021088310700605564737800795609164093516749535046428445339960245329283289374146661544940980908395151406022507642525911509908168319862405732292771298591481548579166184754183790651124462741091035205862139577937340534890804215190192143147184173570985552259488486220468616931812765450353008291785454027364346066738432424164511058027719491636443988449138676532002685470614311150264424687823920415471903161353445102303464098957866824348387801644971962421122800812547008972003040578376776938880500714965381863208145944964242877574718138018328079148427667814988234317217771615 := by
  have hadd := pow2mod_add B6000 (powBits B6000 19 bits6000) 2400 400 (by decide)
  rw [hadd, pb6000_6]
  rfl
private lemma pb6000_8 : pow2mod B6000 (powBits B6000 19 bits6000) 3200 = 9168572794146622462476338404294457791929529250636445279321747378581638533225717996421582821819695517822421620699539615491474718511399971681152467607596710520618395950613971036196248455511811343741642265758268156817942126294793447975279525667563384612847713184292627811732339723478459428613460670812250994834105008020704044833549098095121819681551306922879981309902929382624916155456983198162097126626392898721034147759720008480026193677618760740655549627429367516623126117205403056717871646709567134844751372604706477811197718131588591004255780381757013876156126932173300748940191167335933736635298025147705578060791916322959727752769378353541156357869950379193989569497114289775093593898754284989027320300640746057656637162617123703769996830615784907924191877447771933966574415397511570923088802655862568456557382070941534040626934891312084676172061829339289391207606597187006007159077775162599445801049760481315890808057735934232564872957300875767247503703660554712145692626703094966805822086462093475877955347906707806671332309625014573748221166360600465340922919908733755425037230033632648620040820910178140530062728637386690992606618972160877113527062062639954685792786665181908717533417104921630853091307102220446264653629754066288507652227173682416282927956364400880054780689453241212165728495259866163245295603373807076692788317272917718005942015209595775562557799747986776322555014575366054088796378550352744847293194820824756209696613650023991543225971357522560511315575086337466899125212733847372045207037135019415102230123904368508233717504768180380392000540440963663748461577536042766825352638205639574889516395107688871502070329955932275042727196192025542428940767888971088823666565363498805866611944736749812874928840530911365201183174027695301652523639433229298150054938724229760681044539689884 := by
  have hadd := pow2mod_add B6000 (powBits B6000 19 bits6000) 2800 400 (by decide)
  rw [hadd, pb6000_7]
  rfl
private lemma pb6000_9 : pow2mod B6000 (powBits B6000 19 bits6000) 3600 = 334418583144653377874899302919251421466517583186043620094552355705461969872563768322911416857782595272931928521452261662780342225633215344523285255667176347462128530477494363749876509170604903927303986446093595752150482619929395601985769790293701879562680807628226029032662570870815259105202360540870648676444640463300824199019319932236497856463746447068467520596073725745405596597642082600828984375661284492301637599986326104586047818066852321181779600191019742906013164772862469232113634690215855419617685745775255215126575378274075887619135512592698566451942341399091964433159154373714375366635935750068765693314129186421847273231142656854581660027364563888326803049376265651511204800674984596971330427157063748925170679837944081577797202903513571123253770434310764733553222680126446055802975026635286638557101741610673846042798327431637422160953145836813246411956517839169575887268618377731805070527289214946811725327613425893369404545767223301639306382554243596473664949210378730271471386804976694254348202121200899414009706063839294780051989302615566813757851911653790385953809624704619810586760683914680620502303758528795364726397637289224487624776171131686541855363300626936028695411680515199768416364132859320459196311084276879389619583356629394914177250853638915134127413262987047986930595712781152582187808859355615865010523795104681859382978810022489561992344895371057910232553808077762164978323893587781576418680561145909668508899969203945938127712488726487325437719757733101425029752169459222908279888210543410601597727546344324138025844493896284071655308448960524651079437806573453222844069125835565916419752267641091586307508566031844680567597043734375909860171485858527280314273663427325784782992304660364549006227991480265360472497320670292354189722428319702197530243490129566460792482045545316 := by
  have hadd := pow2mod_add B6000 (powBits B6000 19 bits6000) 3200 400 (by decide)
  rw [hadd, pb6000_8]
  rfl
private lemma pb6000_10 : pow2mod B6000 (powBits B6000 19 bits6000) 4000 = 282127293145970295421558731925732667356957052189795156364660535877352771661053941629625253375879583310274114308090393458466897231447497472145322114170654006497977672804324401746284993844356060958499099322809200792042212923178113072880608804417488082458565693296255751132438758457307823692706606472131060237098304895055565969817195974677099570359794445028960088587676676469519446405903922869899915070237530414501990685286414443373208445020922122047968443412634198271454680710261016816792544555549502012186740857288171835673178502020076238574594708100395908276233274151632503161616186504160753085897889680381268424244840712366097584760836911311955569199264097691387509071873944043947069763210680192259885601641669505023806420754882561167913576920255229174175081069157622043045894803499312105308248267641068770011627045988015443072265783847063196789040098477023549291540171087966241638200019300334930809337678785891662825192666163729278219647891709426253290339681378661423315149611549735401448025788514003746342417329975882960083269565343692202271746655391407037204266690319469260777547086545819706673539376869679078472398481625802599934991635521537589955552158211626683221526484752496947902936078122740211034127850725008606885632873807402108027799890615509117811080255824522463656183037659135462592957393636690844477803483910568860295823446691990590047561686248406180728137157696127929101455210652955408066545590206999712928006469765009261914059205435871850747360136776719799731951700625115128611821572939927712542538668128987693220241185673703127444111218767453673737455853149814662841151809635136147622028156250072230134535464667435000162519957933256762276991467167443722366790171433588853109045737648366772415457723659723730362274468991330446329338605420879961965942559200630489315302988260687433005737553563906 := by
  have hadd := pow2mod_add B6000 (powBits B6000 19 bits6000) 3600 400 (by decide)
  rw [hadd, pb6000_9]
  rfl
private lemma pb6000_11 : pow2mod B6000 (powBits B6000 19 bits6000) 4400 = 390356665080623221756126877415662879674823863401825285082385696555790174566118397738625048624541725783571296698684247778375991376027411165104070228331970243322908545840835278054547772932171267071407417208151506548799980557671958283937984927849037459193010166804416244601143653615757998730015019990427810552539231184930369174135427077409761788845698120095637451290296426255001412267723006700627730331263115788132075046404717287577600328783204169961482016023082737107213888049051693066339668847746085695339987560919257139897427489174954975523253773933057120994560095934283627034544016177350654050425417170681329216053789868732551138691184324992881833676312380597116619919598942108645231242272039432159310575919367058470222430306806862949021514590896417926544345041027031157098799111357231041058156733011538183728137297817064067867595783879164721374525231926616942106598581899866926148224407577069277374870339141580608459921234832794383023294972912024963447890268842158579364178863037483015877763267643238439770211561148767532888029522623257008788323901896320856974833107266283819921007835789707632686221576306538230523466485664278002023801418970111498797496175291282045716808210670460332459515468217971189996910080974197753822187256853438941938176156257053149802424001510152190152854610846602531126013443486179677218920739579518657706963284050448353305312521689464373337410177151032724596953525845668749048443994777824335090226775653601230639975387784613379850017423712589646112706043758319028061173801813636054840141614660396630980377691405310947182169763982363902822791686375671160847364373428217261847932397070483813462771515427615107983015204916553440900579836611066524614114424422693376608658268524914019533000624558655957409267212012928757720295592613192893405948379712893953801309089298651868043157082515909 := by
  have hadd := pow2mod_add B6000 (powBits B6000 19 bits6000) 4000 400 (by decide)
  rw [hadd, pb6000_10]
  rfl
private lemma pb6000_12 : pow2mod B6000 (powBits B6000 19 bits6000) 4800 = 515721159241308323425059899415808295820882708909914336059011566135006403573375304195593499431697652634595465067483693441752986505689369067082964043979078026226939792250285524355735073623976327306898816350298660804374524801695044764487168895618642616710860419564437320734456967505934070671127367786734502322296984029120859448406524201110367632279211900732994140520268655150573756071301659659760123372788034973077827592681859065506619029711846419073709606416200955081808632182409626137796879232176462721117045594913702235020838304762796326833322155976817889258328260257011069451571656312847347883745213743948233434991536988726933563115272584780474843446053720336185741611794789146841319409962068109082000124604985784612193721309602072156773997173729499874573327761234388023032117965253537236772315284122167914661354897731472069773643805158923836802860360630097785840389936701654194610726073258219927023616895201925302041586836933554609094084891838967457723067549452800198681850703378420620890770841031823087651064907476874305429767662080042917062488119202969199134111209659430069831551470490509234126561233428626351318228969615413157101271719317268954824599066990189335010516923224911206230383135568428719055318119508094720750423834193070543397784786272450375165668299169142518896226246741691309862957282917625142398902165489143951489764279363055330113808567020547425936243864757947178600065305743650387054732610652013249353127572599616641895517822666279358537906993479356581539364151973175551156275575379248656304512129298583774088475180176203905073079508615135028825517279072407708146627811128913120838161234689998185447170729913226664770575148353708704391970321557340802875060835503835137505333867585281678954114834853310445197760339413280566391031427415179717139789658874199031471894962160640576819033069586602 := by
  have hadd := pow2mod_add B6000 (powBits B6000 19 bits6000) 4400 400 (by decide)
  rw [hadd, pb6000_11]
  rfl
private lemma pb6000_13 : pow2mod B6000 (powBits B6000 19 bits6000) 5200 = 307988561315876195901222119660559972720459744973543282098103768023071671222309261648492920774782140325671520669818133950078248480264791183121899066789605050075509405400911523890836761170431952162833187373663182236266733603688265076293394484546284226501387519164110997774961244160127997120794090331486824263609645091205447248346042500253016243921473378015818115232669131245849807923071672971592587895681972288428204086397281491393864968352446395700488855176207138693633506289559974918253376839920709242350302231845398357763819210687826351329340885217774066018372133381243845531706419131473350401748935688663840639203341063052812594690032883156924247643005003901670415736213127015793089200477854787566284409789320021067580875600238958929261187502700262311929463189477323131006778922694532875232165671754949095632060200415005196411920406176364878982953465423068677870084467299448552191190140364924719027157963735298076766249344330320385866816536899356246814405092643830747042937567675484641485427227929431075357644976647316880365551438244006588613281134022243865113828710655934361174341379330664570220215056109042040229012642859929172685754400236506985231133416679646232142425031582387955714145837831796813553492036663816305429063413822908967813083881897306293963810024923182874654861005378897022907718904168389859111535197804784919283708808644314785109073739881453568325279364233235097088974856622610865041067364530310072527612331553499307466169793257893480477746432745744014019085565190468908712326709625208215126007820064510306200128342880515357935580746410249124927378716273118739491915452913157527097055342233168576647147643576221166311769918839694461627834160220537812729478535409131199011682498333810683235221199933770182864022780481321261556963083268617338713907400253031698516846701545122201142620890126962 := by
  have hadd := pow2mod_add B6000 (powBits B6000 19 bits6000) 4800 400 (by decide)
  rw [hadd, pb6000_12]
  rfl
private lemma pb6000_14 : pow2mod B6000 (powBits B6000 19 bits6000) 5600 = 399279635221949244366621706730332757142254361923274260876044829334651561650449941927387053642878797737255461519542889014517637787908491100058540602595900340731832336793726751432124443999007191638795465659941636211029808201651958212260165350165108654481116120183375917086392331594757715900447204256749329617826809196263736254030890558396795100879017061511907238965440878047571050400412282052794702995055768394695918965609558038415361363595651189495775290728508664349662481269865396358289797072594402172669950888013333458995519323933308201054023553242895848158207407035976820280075914686323690342423427139974073640335434837281188061753704168059638945279465485819325560682041694723791980702282202464706968039298982761579185225909357523136640239885662674350577123366296675258946431086945003727845768488456519582898660492472111006015362643586086988295706321722773633615803142348417242755297571942334329973713392607361079961340916260228232035832993317271324787556713995996543567368959455638440558945973215195517399603780386294757137530347585338852478693764446223551338606722294725048700719988987596334566339641464738408472529328148358282625897281246505408623648872539900690601174099459107892675797214180085977641673826754468700621495035064272200530647557321102302695886231291419974662479081436996425543764862887047400025780990137769441637953211021486529558185462291034494236046529633001593878402323763072987053953096586921588845914180660936001973883562462578639878793457604598644906911649506240525144589954296107161632421750864632412426304541008152963802264570942777025662921791660702062173382027210366428764651972583812473513114498672604672901231990494855586681724066189796515476321468481551151089960160321406998042028749235962338162144646778960337441272318183606163560058982578301380905463181640107202013979971168932 := by
  have hadd := pow2mod_add B6000 (powBits B6000 19 bits6000) 5200 400 (by decide)
  rw [hadd, pb6000_13]
  rfl
private lemma pb6000_15 : pow2mod B6000 (powBits B6000 19 bits6000) 5999 = 788374393675188612257597871122216916539869076976223284740419429078447874459482733914477452081804557001085229621810881330730197628966279171399502678192266479777145399927086170870698819671085127899988261900953619912005589345156234057954252240991698025613470335829118576650384206277522915885254862180219963090366970296673411203883511587961740647185757226868989829866972761670218248402924352481694732353732323060440629735081628382273170502859833524097884052833887311612857717282773069277688417573497196985432896608178179576087042832650777557339542248894403241570084512873975632939126611987661897420035789453757060803912816125665417382082310748930236311500968710825896385160996966030855262050994024148340120772199094384730698662541808055363598423975435435816725170822071163805492339416331738407433485125186360619621784252031528931982082855307758088257238032987081907164443679609565187302601524342448825426596191680744594779466810509628950529182130868648897956685577309906913501486993770543049935616855825022522863392312492234841392476476939442310203202349013289946586384791684755344878083007733602499702566982935973024575301758649244194439526388880065643320573957820756079797566295670640698857830868442990366833232626873082367971861474299919429757089489288834707649316357735323157283917712935936509407198001652263129118384733743695825717273156614045349979238995565716577696678991622067846409120766347013443902509980672279523231542770734059023088203329114499983235959601175567302127706977974692749850727713018142643838221485924673477304500808812115843401248593849230246704338834252125258617628177010109167107102183048822897260394197161012514267280327091172797981509345060585636067597405791371196801935023189681566841494158048242587115306099199771442678270736573413829157161277851105188122222935199576862105303022305280 := by
  have hadd := pow2mod_add B6000 (powBits B6000 19 bits6000) 5600 399 (by decide)
  rw [hadd, pb6000_14]
  rfl

lemma pow_B6000 : pow2mod B6000 (powBits B6000 19 bits6000) 5999 = B6000 - 1 := by
  convert pb6000_15

lemma proth_B6000_pow : (19 : ZMod B6000) ^ ((B6000 - 1) / 2) = -1 := by
  haveI : NeZero B6000 := ⟨by decide⟩
  have hN1 : B6000 - 1 = 520905 * 2 ^ 6000 := by
    rw [B6000_eq, Nat.add_sub_cancel]
  have hhalf : (B6000 - 1) / 2 = 520905 * 2 ^ 5999 := by
    have : 520905 * 2 ^ 6000 = 520905 * 2 ^ 5999 * 2 := by
      calc
        520905 * 2 ^ 6000 = 520905 * 2 ^ (5999 + 1) := rfl
        _ = 520905 * (2 ^ 5999 * 2) := by rw [pow_succ]
        _ = 520905 * 2 ^ 5999 * 2 := by ring
    rw [hN1, this, Nat.mul_div_cancel _ two_pos]
  have hspec := pow2mod_spec (a := (19 : ZMod B6000) ^ 520905) B6000
      (powBits B6000 19 bits6000) 5999 acc_B6000
  have h1 : 1 ≤ B6000 := by
    rw [B6000_eq]
    exact Nat.le_add_left 1 _
  rw [hhalf, pow_mul, ← hspec, pow_B6000, cast_pred_neg_one B6000 h1]

lemma prime_B6000 : Nat.Prime B6000 :=
  proth_primality (k := 520905) (n := 6000) (a := 19) (N := B6000)
    (by decide) (by decide) (by decide) B6000_eq proth_B6000_pow

lemma pair_520905_6000 : Nat.Prime (520905 * 2 ^ 6000 - 1) ∧ Nat.Prime (520905 * 2 ^ 6000 + 1) := by
  rw [← A6000_eq, ← B6000_eq]
  exact ⟨prime_A6000, prime_B6000⟩

lemma base_520905_6000 : 520905 * 2 ^ (6000 - 2329) ≤ 3 ^ 2329 := by norm_num
