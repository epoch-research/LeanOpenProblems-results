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

def A726 : ℕ := 75189371650606290856270022923698216861729797903048251594695576409219223233366910059993893146497998669350155668891811408892532779054012158980556975980964940083719945935727316710246328930118231425645039696123969370987692031
def B726 : ℕ := 75189371650606290856270022923698216861729797903048251594695576409219223233366910059993893146497998669350155668891811408892532779054012158980556975980964940083719945935727316710246328930118231425645039696123969370987692033

lemma jac_5_A726 : jacobiSym (5 ^ 2 - 4) A726 = -1 := by
  unfold A726
  norm_num

lemma v_A726 : vpow2mod A726 (vPair 5 A726 213).1 724 = 0 := rfl

lemma lucasV_A726 : (lucasV 5 (213 * 2 ^ 724) : ZMod A726) = 0 := by
  haveI : NeZero A726 := ⟨by decide⟩
  have hacc : ((vPair 5 A726 213).1 : ZMod A726) = (lucasV (5 : ℤ) 213 : ZMod A726) :=
    (vPair_spec 5 A726 213).1
  exact vpow2mod_zero (5 : ℤ) 213 A726 724 (by decide) hacc v_A726

lemma A726_eq : A726 = 213 * 2 ^ 726 - 1 := by
  unfold A726
  norm_num

lemma prime_A726 : Nat.Prime A726 := by
  refine riesel_primality (k := 213) (n := 726) (P := 5) (N := A726)
    (by decide) (by decide) (by decide) (by decide) A726_eq jac_5_A726 ?_
  simpa using lucasV_A726

lemma pow_B726 : pow2mod B726 (powSmall B726 5 213) 725 = B726 - 1 := rfl

lemma B726_eq : B726 = 213 * 2 ^ 726 + 1 := by
  unfold B726
  norm_num

lemma proth_B726_pow : (5 : ZMod B726) ^ ((B726 - 1) / 2) = -1 := by
  haveI : NeZero B726 := ⟨by decide⟩
  exact proth_pow_neg_one 213 726 5 B726 B726_eq (by decide) pow_B726

lemma prime_B726 : Nat.Prime B726 :=
  proth_primality (k := 213) (n := 726) (a := 5) (N := B726)
    (by decide) (by decide) (by decide) B726_eq proth_B726_pow

lemma pair_213_726 : Nat.Prime (213 * 2 ^ 726 - 1) ∧ Nat.Prime (213 * 2 ^ 726 + 1) := by
  rw [← A726_eq, ← B726_eq]
  exact ⟨prime_A726, prime_B726⟩

lemma base_213_726 : 213 * 2 ^ (726 - 284) ≤ 3 ^ 284 := by norm_num

set_option exponentiation.threshold 1200

def A1032 : ℕ := 8145707132688125841103027680503228872969777286983379542373663837419183006098859641469286524432930272188994600124732575822235082004518845998395902777135851523805418786867504868839806174571663016740658094724875781397594283718301678085345950864825963770345738340139974345848489607964392905204699666007932844105531391
def B1032 : ℕ := 8145707132688125841103027680503228872969777286983379542373663837419183006098859641469286524432930272188994600124732575822235082004518845998395902777135851523805418786867504868839806174571663016740658094724875781397594283718301678085345950864825963770345738340139974345848489607964392905204699666007932844105531393

lemma jac_5_A1032 : jacobiSym (5 ^ 2 - 4) A1032 = -1 := by
  unfold A1032
  norm_num

lemma v_A1032 : vpow2mod A1032 (vPair 5 A1032 177).1 1030 = 0 := rfl

lemma lucasV_A1032 : (lucasV 5 (177 * 2 ^ 1030) : ZMod A1032) = 0 := by
  haveI : NeZero A1032 := ⟨by decide⟩
  have hacc : ((vPair 5 A1032 177).1 : ZMod A1032) = (lucasV (5 : ℤ) 177 : ZMod A1032) :=
    (vPair_spec 5 A1032 177).1
  exact vpow2mod_zero (5 : ℤ) 177 A1032 1030 (by decide) hacc v_A1032

lemma A1032_eq : A1032 = 177 * 2 ^ 1032 - 1 := by
  unfold A1032
  norm_num

lemma prime_A1032 : Nat.Prime A1032 := by
  refine riesel_primality (k := 177) (n := 1032) (P := 5) (N := A1032)
    (by decide) (by decide) (by decide) (by decide) A1032_eq jac_5_A1032 ?_
  simpa using lucasV_A1032

lemma pow_B1032 : pow2mod B1032 (powSmall B1032 5 177) 1031 = B1032 - 1 := rfl

lemma B1032_eq : B1032 = 177 * 2 ^ 1032 + 1 := by
  unfold B1032
  norm_num

lemma proth_B1032_pow : (5 : ZMod B1032) ^ ((B1032 - 1) / 2) = -1 := by
  haveI : NeZero B1032 := ⟨by decide⟩
  exact proth_pow_neg_one 177 1032 5 B1032 B1032_eq (by decide) pow_B1032

lemma prime_B1032 : Nat.Prime B1032 :=
  proth_primality (k := 177) (n := 1032) (a := 5) (N := B1032)
    (by decide) (by decide) (by decide) B1032_eq proth_B1032_pow

lemma pair_177_1032 : Nat.Prime (177 * 2 ^ 1032 - 1) ∧ Nat.Prime (177 * 2 ^ 1032 + 1) := by
  rw [← A1032_eq, ← B1032_eq]
  exact ⟨prime_A1032, prime_B1032⟩

lemma base_177_1032 : 177 * 2 ^ (1032 - 403) ≤ 3 ^ 403 := by norm_num


