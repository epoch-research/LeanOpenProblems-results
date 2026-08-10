import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000

structure GR (n : ℕ) where
  a : ZMod n
  b : ZMod n
deriving DecidableEq

namespace GR
variable {n : ℕ}

@[ext] theorem ext {x y : GR n} (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x; cases y; simp_all

instance : Add (GR n) := ⟨fun x y => ⟨x.a+y.a, x.b+y.b⟩⟩
instance : Mul (GR n) := ⟨fun x y => ⟨x.a*y.a + 3*x.b*y.b, x.a*y.b + x.b*y.a⟩⟩
instance : Neg (GR n) := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub (GR n) := ⟨fun x y => ⟨x.a-y.a, x.b-y.b⟩⟩
instance : Zero (GR n) := ⟨⟨0,0⟩⟩
instance : One (GR n) := ⟨⟨1,0⟩⟩

@[simp] theorem add_a (x y : GR n) : (x+y).a = x.a+y.a := rfl
@[simp] theorem add_b (x y : GR n) : (x+y).b = x.b+y.b := rfl
@[simp] theorem mul_a (x y : GR n) : (x*y).a = x.a*y.a + 3*x.b*y.b := rfl
@[simp] theorem mul_b (x y : GR n) : (x*y).b = x.a*y.b + x.b*y.a := rfl
@[simp] theorem neg_a (x : GR n) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : GR n) : (-x).b = -x.b := rfl
@[simp] theorem sub_a (x y : GR n) : (x-y).a = x.a-y.a := rfl
@[simp] theorem sub_b (x y : GR n) : (x-y).b = x.b-y.b := rfl
@[simp] theorem zero_a : (0 : GR n).a = 0 := rfl
@[simp] theorem zero_b : (0 : GR n).b = 0 := rfl
@[simp] theorem one_a : (1 : GR n).a = 1 := rfl
@[simp] theorem one_b : (1 : GR n).b = 0 := rfl

instance : CommRing (GR n) where
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  mul_comm a b := by ext <;> simp <;> ring
  neg_add_cancel a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec

@[simp] theorem natCast_a (m : ℕ) : ((m : GR n)).a = (m : ZMod n) := by
  induction m with
  | zero => simp
  | succ k ih => push_cast; simp [ih]
@[simp] theorem natCast_b (m : ℕ) : ((m : GR n)).b = 0 := by
  induction m with
  | zero => simp
  | succ k ih => push_cast; simp [ih]

end GR

namespace GR
variable {n : ℕ}

-- scalar embedding
def scal (a : ZMod n) : GR n := ⟨a, 0⟩
@[simp] theorem scal_a (a : ZMod n) : (scal a).a = a := rfl
@[simp] theorem scal_b (a : ZMod n) : (scal a).b = 0 := rfl
@[simp] theorem scal_mul (a c : ZMod n) : scal a * scal c = scal (a*c) := by
  ext <;> simp [scal]
@[simp] theorem scal_one : (scal 1 : GR n) = 1 := by ext <;> simp [scal]
theorem scal_pow (a : ZMod n) (k : ℕ) : (scal a)^k = scal (a^k) := by
  induction k with
  | zero => simp
  | succ j ih => rw [pow_succ, ih, scal_mul, pow_succ]

-- sqrt(3) element
def sq3 : GR n := ⟨0, 1⟩
@[simp] theorem sq3_sq : (sq3 : GR n)^2 = scal 3 := by
  rw [pow_two]; ext <;> simp [sq3, scal]

-- omega
def om : GR n := ⟨2, 1⟩
theorem om_eq : (om : GR n) = scal 2 + sq3 := by ext <;> simp [scal, sq3, om]
-- conjugate
def omc : GR n := ⟨2, -1⟩
theorem om_mul_omc : (om : GR n) * omc = 1 := by ext <;> simp [om, omc] <;> ring

end GR

namespace GR

-- ring hom induced by a ring hom on ZMod
def map {n m : ℕ} (f : ZMod n →+* ZMod m) : GR n →+* GR m where
  toFun x := ⟨f x.a, f x.b⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp [map_ofNat] <;> ring

@[simp] theorem map_a {n m : ℕ} (f : ZMod n →+* ZMod m) (x : GR n) : (map f x).a = f x.a := rfl
@[simp] theorem map_b {n m : ℕ} (f : ZMod n →+* ZMod m) (x : GR n) : (map f x).b = f x.b := rfl

-- CharP instance for GR p
instance charP (p : ℕ) [hp : Fact p.Prime] : CharP (GR p) p where
  cast_eq_zero_iff := by
    intro k
    constructor
    · intro h
      have : ((k : ZMod p)) = 0 := by
        have := congrArg GR.a h; simpa using this
      exact (ZMod.natCast_eq_zero_iff k p).1 this
    · intro h
      ext
      · simp [(ZMod.natCast_eq_zero_iff k p).2 h]
      · simp

end GR

namespace GR

-- (a,0)^k = (a^k,0)  already via scal_pow

-- key: om^p = ⟨2, χ⟩ where χ = 3^((p-1)/2)
theorem om_pow_card (p : ℕ) [hp : Fact p.Prime] (hodd : Odd p) :
    (om : GR p)^p = ⟨2, (3 : ZMod p)^((p-1)/2)⟩ := by
  rw [om_eq, add_pow_char]
  -- (scal 2)^p = scal 2
  have h2 : (scal (2 : ZMod p))^p = scal 2 := by rw [scal_pow, ZMod.pow_card]
  -- sq3^p = scal (3^((p-1)/2)) * sq3
  have hp2 : p = 2 * ((p-1)/2) + 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hpow : ((sq3:GR p)^2)^((p-1)/2) * sq3 = sq3^p := by
    rw [← pow_mul, ← pow_succ]
    congr 1
    omega
  have h3 : (sq3 : GR p)^p = scal ((3:ZMod p)^((p-1)/2)) * sq3 := by
    rw [← hpow, sq3_sq, scal_pow]
  rw [h2, h3]
  ext <;> simp [scal, sq3] <;> ring

end GR

namespace GR

theorem om_pm_one (p : ℕ) [hp : Fact p.Prime] (hodd : Odd p) (hp3 : (3:ZMod p) ≠ 0) :
    (om : GR p)^(p+1) = 1 ∨ (om : GR p)^(p-1) = 1 := by
  obtain ⟨k, hk⟩ := hodd
  have hompow : (om : GR p)^p = ⟨2, (3 : ZMod p)^((p-1)/2)⟩ := om_pow_card p ⟨k, hk⟩
  have hχsq : ((3 : ZMod p)^((p-1)/2))^2 = 1 := by
    rw [← pow_mul]
    have h : (p-1)/2*2 = p-1 := by omega
    rw [h, ZMod.pow_card_sub_one_eq_one hp3]
  have hcases : (3 : ZMod p)^((p-1)/2) = 1 ∨ (3 : ZMod p)^((p-1)/2) = -1 := by
    have := hχsq
    rw [pow_two] at this
    exact mul_self_eq_one_iff.1 this
  rcases hcases with h1 | h1
  · right
    have hp1 : (om:GR p)^p = om := by rw [hompow, h1]; ext <;> simp [om]
    have hstep : (om:GR p)^(p-1) * om = om^p := by rw [← pow_succ]; congr 1; omega
    have key : (om:GR p)^(p-1) = (om:GR p)^(p-1) * (om * omc) := by rw [om_mul_omc, mul_one]
    rw [key, ← mul_assoc, hstep, hp1]
    exact om_mul_omc
  · left
    have hp1 : (om:GR p)^p = omc := by rw [hompow, h1]; ext <;> simp [om, omc]
    rw [pow_succ, hp1, mul_comm]
    exact om_mul_omc

end GR

namespace GR
variable {n : ℕ}

theorem bitid (c w : ℕ) : c % 2^(w+1) = ((c >>> w) &&& 1) * 2^w + c % 2^w := by
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, pow_succ, Nat.mod_mul]; ring

end GR

def NN : ℕ := 201886 * 3^39101 - 1

namespace GR

def toGR (N : ℕ) (p : ℕ × ℕ) : GR N := ⟨(p.1 : ZMod N), (p.2 : ZMod N)⟩

def nmul (N : ℕ) (p q : ℕ × ℕ) : ℕ × ℕ :=
  ((p.1*q.1 + 3*(p.2*q.2)) % N, (p.1*q.2 + p.2*q.1) % N)

def nsub (N : ℕ) (p q : ℕ × ℕ) : ℕ × ℕ := ((p.1 + N - q.1) % N, (p.2 + N - q.2) % N)

theorem toGR_mul (N : ℕ) (p q : ℕ × ℕ) : toGR N (nmul N p q) = toGR N p * toGR N q := by
  apply GR.ext
  · show (((p.1*q.1 + 3*(p.2*q.2)) % N : ℕ) : ZMod N) = _
    rw [ZMod.natCast_mod]; push_cast; simp [toGR]; try ring
  · show (((p.1*q.2 + p.2*q.1) % N : ℕ) : ZMod N) = _
    rw [ZMod.natCast_mod]; push_cast; simp [toGR]; try ring

theorem toGR_one (N : ℕ) : toGR N ((1,0) : ℕ × ℕ) = 1 := by apply GR.ext <;> simp [toGR]

theorem toGR_om (N : ℕ) : toGR N ((2,1) : ℕ × ℕ) = (GR.om : GR N) := by
  apply GR.ext <;> simp [toGR, GR.om]

theorem toGR_sub (N : ℕ) (p q : ℕ × ℕ) (hq1 : q.1 ≤ N) (hq2 : q.2 ≤ N) :
    toGR N (nsub N p q) = toGR N p - toGR N q := by
  apply GR.ext
  · show (((p.1 + N - q.1) % N : ℕ) : ZMod N) = (p.1 : ZMod N) - (q.1 : ZMod N)
    rw [ZMod.natCast_mod, show p.1 + N - q.1 = p.1 + (N - q.1) from by omega]
    push_cast [Nat.cast_sub hq1]
    simp only [ZMod.natCast_self]; ring
  · show (((p.2 + N - q.2) % N : ℕ) : ZMod N) = (p.2 : ZMod N) - (q.2 : ZMod N)
    rw [ZMod.natCast_mod, show p.2 + N - q.2 = p.2 + (N - q.2) from by omega]
    push_cast [Nat.cast_sub hq2]
    simp only [ZMod.natCast_self]; ring

def nstep (N : ℕ) (om : ℕ × ℕ) : (ℕ × ℕ) → ℕ → ℕ → (ℕ × ℕ)
  | acc, _, 0 => acc
  | acc, c, (w+1) =>
      nstep N om (nmul N (nmul N acc acc) (if (c >>> w) &&& 1 == 1 then om else (1,0))) c w

theorem toGR_nstep (N : ℕ) (om : ℕ × ℕ) (c : ℕ) : ∀ (w : ℕ) (acc : ℕ × ℕ),
    toGR N (nstep N om acc c w) = (toGR N acc)^(2^w) * (toGR N om)^(c % 2^w) := by
  intro w
  induction w with
  | zero => intro acc; simp [nstep, Nat.mod_one, toGR_one]
  | succ k ih =>
    intro acc
    show toGR N (nstep N om (nmul N (nmul N acc acc)
      (if (c >>> k) &&& 1 == 1 then om else (1,0))) c k) = _
    rw [ih, toGR_mul, toGR_mul]
    have hbit : ((c >>> k) &&& 1 = 0) ∨ ((c >>> k) &&& 1 = 1) := by
      rw [Nat.and_one_is_mod]; omega
    have hb : (toGR N (if (c >>> k) &&& 1 == 1 then om else (1,0)))^(2^k)
        = (toGR N om) ^ (((c >>> k) &&& 1) * 2^k) := by
      rcases hbit with h | h <;> rw [h] <;> simp [toGR_one]
    rw [mul_pow, hb, ← pow_two (toGR N acc), ← pow_mul, mul_assoc, ← pow_add, ← bitid, pow_succ']

def nchainResult (acc : ℕ × ℕ) : List (ℕ × (ℕ × ℕ)) → (ℕ × ℕ)
  | [] => acc
  | (_, cp) :: rest => nchainResult cp rest

def ncheckChain (N : ℕ) (om : ℕ × ℕ) (W : ℕ) : (ℕ × ℕ) → List (ℕ × (ℕ × ℕ)) → Bool
  | _, [] => true
  | acc, (c, cp) :: rest => (nstep N om acc c W == cp) && ncheckChain N om W cp rest

def nfoldExp (W : ℕ) (E0 : ℕ) : List (ℕ × (ℕ × ℕ)) → ℕ
  | [] => E0
  | (c, _) :: rest => nfoldExp W (E0 * 2^W + c % 2^W) rest

theorem ncheckChain_sound (N : ℕ) (om : ℕ × ℕ) (W : ℕ) :
    ∀ (chunks : List (ℕ × (ℕ × ℕ))) (acc : ℕ × ℕ) (E0 : ℕ),
    toGR N acc = (toGR N om) ^ E0 → ncheckChain N om W acc chunks = true →
    toGR N (nchainResult acc chunks) = (toGR N om) ^ (nfoldExp W E0 chunks) := by
  intro chunks
  induction chunks with
  | nil => intro acc E0 hacc _; simpa [nchainResult, nfoldExp] using hacc
  | cons hd tl ih =>
    intro acc E0 hacc hcheck
    obtain ⟨c, cp⟩ := hd
    rw [ncheckChain, Bool.and_eq_true] at hcheck
    obtain ⟨h1, h2⟩ := hcheck
    have hcp : toGR N cp = (toGR N om) ^ (E0 * 2^W + c % 2^W) := by
      have hst : nstep N om acc c W = cp := eq_of_beq h1
      rw [← hst, toGR_nstep, hacc, ← pow_mul, ← pow_add]
    show toGR N (nchainResult cp tl) = (toGR N om) ^ (nfoldExp W (E0 * 2^W + c % 2^W) tl)
    exact ih cp (E0 * 2^W + c % 2^W) hcp h2

theorem ncheckChain_append (N : ℕ) (om : ℕ × ℕ) (W : ℕ) :
    ∀ (l1 : List (ℕ × (ℕ × ℕ))) (acc : ℕ × ℕ) (l2 : List (ℕ × (ℕ × ℕ))),
    ncheckChain N om W acc l1 = true →
    ncheckChain N om W (nchainResult acc l1) l2 = true →
    ncheckChain N om W acc (l1 ++ l2) = true := by
  intro l1
  induction l1 with
  | nil => intro acc l2 _ h2; simpa [nchainResult] using h2
  | cons hd tl ih =>
    intro acc l2 h1 h2
    obtain ⟨c, cp⟩ := hd
    rw [List.cons_append, ncheckChain, Bool.and_eq_true]
    rw [ncheckChain, Bool.and_eq_true] at h1
    exact ⟨h1.1, ih cp l2 h1.2 h2⟩

theorem cert_value (N W : ℕ) (fp : ℕ × ℕ) (chunks : List (ℕ × (ℕ × ℕ))) (E : ℕ)
    (h1 : ncheckChain N (2,1) W (1,0) chunks = true)
    (h2 : nfoldExp W 0 chunks = E)
    (h3 : nchainResult (1,0) chunks = fp) :
    toGR N fp = (GR.om : GR N)^E := by
  have hstart : toGR N (1,0) = (toGR N (2,1))^(0:ℕ) := by rw [pow_zero]; exact toGR_one N
  have hs := ncheckChain_sound N (2,1) W chunks (1,0) 0 hstart h1
  rw [h3, h2, toGR_om] at hs
  exact hs

theorem hH1_from_cert (N W : ℕ) (chunks : List (ℕ × (ℕ × ℕ)))
    (h1 : ncheckChain N (2,1) W (1,0) chunks = true)
    (h2 : nfoldExp W 0 chunks = N + 1)
    (h3 : nchainResult (1,0) chunks = (1,0)) :
    (GR.om : GR N)^(N+1) = 1 := by
  have hstart : toGR N (1,0) = (toGR N (2,1))^(0:ℕ) := by rw [pow_zero]; exact toGR_one N
  have hs := ncheckChain_sound N (2,1) W chunks (1,0) 0 hstart h1
  rw [h3, h2, toGR_om, toGR_one] at hs
  exact hs.symm

theorem hU_from_cert (N W : ℕ) (hN : 1 ≤ N) (chunks : List (ℕ × (ℕ × ℕ)))
    (invpair : ℕ × ℕ) (E : ℕ)
    (h1 : ncheckChain N (2,1) W (1,0) chunks = true)
    (h2 : nfoldExp W 0 chunks = E)
    (h3 : nmul N (nsub N (nchainResult (1,0) chunks) (1,0)) invpair = (1,0)) :
    IsUnit ((GR.om : GR N)^E - 1) := by
  have hstart : toGR N (1,0) = (toGR N (2,1))^(0:ℕ) := by rw [pow_zero]; exact toGR_one N
  have hs := ncheckChain_sound N (2,1) W chunks (1,0) 0 hstart h1
  rw [h2, toGR_om] at hs
  have hcg := congrArg (toGR N) h3
  rw [toGR_mul, toGR_sub N _ (1,0) hN (Nat.zero_le N), hs, toGR_one] at hcg
  exact IsUnit.of_mul_eq_one _ hcg

end GR

theorem hNN1 : NN + 1 = 2 * 100943 * 3^39101 := by
  have h1 : (1:ℕ) ≤ 201886 * 3^39101 := by
    have : 0 < 201886 * 3^39101 := by positivity
    omega
  unfold NN
  rw [Nat.sub_add_cancel h1, show (201886:ℕ) = 2 * 100943 from by norm_num]

theorem NN_odd : Odd NN := by
  have h : NN + 1 = 2 * (100943 * 3^39101) := by rw [hNN1]; ring
  rcases Nat.even_or_odd NN with he | ho
  · exfalso; obtain ⟨k, hk⟩ := he; omega
  · exact ho

theorem NN_not_dvd_3 : ¬ (3 ∣ NN) := by
  have h : NN + 1 = 3 * (2 * 100943 * 3^39100) := by
    rw [hNN1, show (39101:ℕ) = 39100 + 1 from by norm_num, pow_succ]
    generalize (3:ℕ)^39100 = Y
    ring
  intro hd
  obtain ⟨k, hk⟩ := hd
  omega

theorem primality_test (N : ℕ) (hN2 : 2 ≤ N)
    (h2 : ¬ (2 ∣ N)) (h3 : ¬ (3 ∣ N))
    (hH1 : (GR.om : GR N)^(N+1) = 1)
    (hd0 : ∀ q : ℕ, q.Prime → q ∣ (N+1) → IsUnit ((GR.om : GR N)^((N+1)/q) - 1))
    : Nat.Prime N := by
  by_contra hnp
  obtain ⟨p, hp_def⟩ : ∃ p, N.minFac = p := ⟨_, rfl⟩
  have hp_prime : p.Prime := hp_def ▸ Nat.minFac_prime (by omega)
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hp_dvd : p ∣ N := hp_def ▸ Nat.minFac_dvd N
  have hpsq : p * p ≤ N := by
    have := Nat.minFac_sq_le_self (show 0 < N by omega) hnp
    rw [pow_two, hp_def] at this; exact this
  have hp_ne2 : p ≠ 2 := fun h => h2 (h ▸ hp_dvd)
  have hp_ne3 : p ≠ 3 := fun h => h3 (h ▸ hp_dvd)
  have hodd : Odd p := hp_prime.odd_of_ne_two hp_ne2
  have hp3 : (3 : ZMod p) ≠ 0 := by
    intro hcon
    have h1 : ((3:ℕ) : ZMod p) = 0 := by exact_mod_cast hcon
    rw [ZMod.natCast_eq_zero_iff 3 p] at h1
    exact hp_ne3 ((Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_three).1 h1)
  set f := ZMod.castHom hp_dvd (ZMod p) with hf
  set π := GR.map f with hπ
  have hπom : π (GR.om : GR N) = (GR.om : GR p) := by
    apply GR.ext
    · show f (2 : ZMod N) = (2 : ZMod p); rw [hf]; exact map_ofNat _ 2
    · show f (1 : ZMod N) = (1 : ZMod p); rw [hf]; exact map_one _
  have hp1 : (GR.om : GR p)^(N+1) = 1 := by
    have hc := congrArg π hH1
    rw [map_pow, hπom, map_one] at hc
    exact hc
  haveI : Nontrivial (GR p) := ⟨0, 1, fun h => zero_ne_one (congrArg GR.a h)⟩
  have hd : ∀ q : ℕ, q.Prime → q ∣ (N+1) → (GR.om : GR p)^((N+1)/q) ≠ 1 := by
    intro q hq hqd hcon
    have hu := hd0 q hq hqd
    have hu2 : IsUnit ((GR.om : GR p)^((N+1)/q) - 1) := by
      have hmap := hu.map π
      simp only [map_sub, map_pow, map_one, hπom] at hmap
      exact hmap
    rw [hcon, sub_self] at hu2
    exact not_isUnit_zero hu2
  have horder : orderOf (GR.om : GR p) = N + 1 :=
    orderOf_eq_of_pow_and_pow_div_prime (Nat.succ_pos N) hp1 hd
  have hpm := GR.om_pm_one p hodd hp3
  have hp2le : p ≥ 2 := hp_prime.two_le
  rcases hpm with h | h
  · have hdvd : (N+1) ∣ (p+1) := horder ▸ orderOf_dvd_of_pow_eq_one h
    have : N + 1 ≤ p + 1 := Nat.le_of_dvd (by omega) hdvd
    nlinarith [hpsq, hp2le]
  · have hdvd : (N+1) ∣ (p-1) := horder ▸ orderOf_dvd_of_pow_eq_one h
    have hp1pos : 0 < p - 1 := by omega
    have hle : N + 1 ≤ p - 1 := Nat.le_of_dvd hp1pos hdvd
    have hNp : N + 2 ≤ p := by omega
    nlinarith [hpsq, hNp, hp2le]

