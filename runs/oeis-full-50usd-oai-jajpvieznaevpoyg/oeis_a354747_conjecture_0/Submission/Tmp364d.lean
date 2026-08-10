import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000
set_option maxHeartbeats 0


open Nat Set

noncomputable def a354747 (n : ℕ) : ℕ :=
  let prime_steps : Set ℕ :=
    { m : ℕ | m > 0 ∧ Nat.Prime (2 * n * 3 ^ m - 1) }
  sInf prime_steps

namespace Counter

def N : Nat := 201886 * 3 ^ 39101 - 1
def M : Nat := 2 * 100943 * 3 ^ 39101

theorem N_add_one : N + 1 = M := by
  unfold N M
  have hpos : 1 ≤ 201886 * 3 ^ 39101 := by native_decide
  rw [Nat.sub_add_cancel hpos]

theorem N_eq_orig : N = 2 * 100943 * 3 ^ 39101 - 1 := by
  unfold N
  norm_num [show 201886 = 2 * 100943 by norm_num]

def inv5 : Nat := (2*N + 1) / 5

theorem inv5_spec : 5 * inv5 = 2 * N + 1 := by native_decide

theorem N_pos : 0 < N := by native_decide
theorem N_ge_two : 2 ≤ N := by native_decide
theorem fuel_bound : N + 1 < 2 ^ 70000 := by native_decide

-- Algebra with alpha^2 = alpha + 5 over ZMod m, represented as u*alpha+v.
def X (m : Nat) := ZMod m × ZMod m

namespace X

instance (m) : One (X m) where one := (0,1)
instance (m) : Zero (X m) where zero := (0,0)
@[simp] theorem zero_fst {m} : (0 : X m).1 = 0 := rfl
@[simp] theorem zero_snd {m} : (0 : X m).2 = 0 := rfl

instance (m) : Mul (X m) where
  mul x y := (x.1*y.1 + x.1*y.2 + x.2*y.1, 5*x.1*y.1 + x.2*y.2)

@[ext] theorem ext {m} {x y : X m} (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y := Prod.ext h1 h2
@[simp] theorem one_fst {m} : (1 : X m).1 = 0 := rfl
@[simp] theorem one_snd {m} : (1 : X m).2 = 1 := rfl
@[simp] theorem mul_fst {m} (x y : X m) : (x*y).1 = x.1*y.1 + x.1*y.2 + x.2*y.1 := rfl
@[simp] theorem mul_snd {m} (x y : X m) : (x*y).2 = 5*x.1*y.1 + x.2*y.2 := rfl

instance (m) : Monoid (X m) :=
{ inferInstanceAs (Mul (X m)), inferInstanceAs (One (X m)) with
  mul_assoc := by intro a b c; ext <;> simp <;> ring
  one_mul := by intro a; ext <;> simp
  mul_one := by intro a; ext <;> simp }


instance (m) : MonoidWithZero (X m) :=
{ inferInstanceAs (Monoid (X m)), inferInstanceAs (Zero (X m)) with
  zero_mul := by intro a; ext <;> simp
  mul_zero := by intro a; ext <;> simp }

instance (m) : CommMonoid (X m) :=
{ inferInstanceAs (Monoid (X m)) with
  mul_comm := by intro a b; ext <;> simp <;> ring }

instance (m) : DecidableEq (X m) := by
  dsimp [X]
  infer_instance

instance (m) [NeZero m] : Fintype (X m) := by
  dsimp [X]
  infer_instance

theorem card_eq (m : Nat) [NeZero m] : Fintype.card (X m) = m ^ 2 := by
  change Fintype.card (ZMod m × ZMod m) = m ^ 2
  rw [Fintype.card_prod, ZMod.card, pow_two]

theorem card_units_lt {p : Nat} [NeZero p] (hp : 1 < p) : Fintype.card (X p)ˣ < p ^ 2 := by
  haveI : Fact (1 < (p : Nat)) := ⟨hp⟩
  haveI : Nontrivial (X p) := by
    refine ⟨⟨0, 1, ?_⟩⟩
    intro h
    have hs := congrArg Prod.snd h
    simpa using hs
  have hnot : (0 : X p) ∉ Set.range (Units.val : (X p)ˣ → X p) := by
    rintro ⟨u, hu⟩
    have h01 : (0 : X p) = 1 := by
      calc
        (0 : X p) = (↑u⁻¹ : X p) * (↑u : X p) := by rw [hu, mul_zero]
        _ = 1 := u.inv_val
    have hs := congrArg Prod.snd h01
    simpa using hs
  have h := Fintype.card_lt_of_injective_of_notMem (Units.val : (X p)ˣ → X p) Units.val_injective hnot
  rw [card_eq] at h
  exact h

def gammaUnit (p : Nat) (hpdvd : p ∣ N) : Units (X p) where
  val := (-(inv5 : ZMod p), -1)
  inv := ((inv5 : ZMod p), -(inv5 : ZMod p) - 1)
  val_inv := by
    have hN : (N : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff N p).2 hpdvd
    have h5 : (5 : ZMod p) * (inv5 : ZMod p) = 1 := by
      have hs := congrArg (fun n : Nat => (n : ZMod p)) inv5_spec
      change ((5 * inv5 : Nat) : ZMod p) = ((2 * N + 1 : Nat) : ZMod p) at hs
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_mul, hN] at hs
      norm_num at hs
      simpa using hs
    ext <;> simp [mul_assoc, mul_comm, mul_left_comm]
    · ring
    · ring_nf
      have haux : (inv5 : ZMod p) - (inv5 : ZMod p) ^ 2 * 5 = 0 := by
        calc
          (inv5 : ZMod p) - (inv5 : ZMod p) ^ 2 * 5 = (inv5 : ZMod p) - (inv5 : ZMod p) * (5 * (inv5 : ZMod p)) := by ring
          _ = 0 := by rw [h5]; ring
      rw [haux]
      ring
  inv_val := by
    have hN : (N : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff N p).2 hpdvd
    have h5 : (5 : ZMod p) * (inv5 : ZMod p) = 1 := by
      have hs := congrArg (fun n : Nat => (n : ZMod p)) inv5_spec
      change ((5 * inv5 : Nat) : ZMod p) = ((2 * N + 1 : Nat) : ZMod p) at hs
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_mul, hN] at hs
      norm_num at hs
      simpa using hs
    ext <;> simp [mul_assoc, mul_comm, mul_left_comm]
    · ring
    · ring_nf
      have haux : (inv5 : ZMod p) - (inv5 : ZMod p) ^ 2 * 5 = 0 := by
        calc
          (inv5 : ZMod p) - (inv5 : ZMod p) ^ 2 * 5 = (inv5 : ZMod p) - (inv5 : ZMod p) * (5 * (inv5 : ZMod p)) := by ring
          _ = 0 := by rw [h5]; ring
      rw [haux]
      ring


@[simp] theorem gammaUnit_coe (p : Nat) (hpdvd : p ∣ N) :
    ((gammaUnit p hpdvd : Units (X p)) : X p) = (-(inv5 : ZMod p), -1) := rfl

end X

structure Elt where
  u : Nat
  v : Nat
  deriving BEq, Repr, DecidableEq


lemma Elt.eq_of_beq {x y : Elt} (h : (x == y) = true) : x = y := by
  cases x with
  | mk xu xv =>
  cases y with
  | mk yu yv =>
  change ((xu == yu) && (xv == yv)) = true at h
  rw [Bool.and_eq_true] at h
  have hu : xu = yu := beq_iff_eq.mp h.1
  have hv : xv = yv := beq_iff_eq.mp h.2
  subst yu
  subst yv
  rfl

def emul (m : Nat) (x y : Elt) : Elt :=
  ⟨(x.u*y.u + x.u*y.v + x.v*y.u) % m,
   (5*x.u*y.u + x.v*y.v) % m⟩

def stepAcc (m : Nat) (base acc : Elt) (e : Nat) : Elt :=
  if e % 2 = 1 then emul m acc base else acc

def one (m : Nat) : Elt := ⟨0,1 % m⟩
def gamma (m : Nat) : Elt := ⟨(m - (inv5 % m)) % m, (m - (1 % m)) % m⟩

def epowFuelAux : Nat → Nat → Elt → Elt → Nat → Elt
| 0, m, base, acc, e => acc
| f+1, m, base, acc, e => epowFuelAux f m (emul m base base) (stepAcc m base acc e) (e/2)

def epow4Aux : Nat → Nat → Elt → Elt → Elt → Elt → Elt → Nat → Nat → Nat → Nat → Elt × Elt × Elt × Elt
| 0, m, base, a1, a2, a3, a4, e1, e2, e3, e4 => (a1,a2,a3,a4)
| f+1, m, base, a1, a2, a3, a4, e1, e2, e3, e4 =>
    let b := emul m base base
    epow4Aux f m b (stepAcc m base a1 e1) (stepAcc m base a2 e2)
      (stepAcc m base a3 e3) (stepAcc m base a4 e4) (e1/2) (e2/2) (e3/2) (e4/2)

def epow4 (m e1 e2 e3 e4 : Nat) : Elt × Elt × Elt × Elt :=
  epow4Aux 70000 m (gamma m) (one m) (one m) (one m) (one m) e1 e2 e3 e4

def certTuple : Elt × Elt × Elt × Elt := epow4 N (N+1) ((N+1)/2) ((N+1)/3) ((N+1)/100943)

def diffGcd (x : Elt) (m : Nat) : Nat :=
  Nat.gcd (Nat.gcd (x.u % m) ((x.v + m - 1) % m)) m

def good : Bool :=
  let t := certTuple
  t.1 == one N &&
  diffGcd t.2.1 N == 1 &&
  diffGcd t.2.2.1 N == 1 &&
  diffGcd t.2.2.2 N == 1

theorem certAll : good = true := by native_decide

def toX (m : Nat) (x : Elt) : X m := ((x.u : ZMod m), (x.v : ZMod m))

lemma cast_mod_of_dvd {p m a : Nat} (hpm : p ∣ m) : ((a % m : Nat) : ZMod p) = (a : ZMod p) := by
  conv_rhs => rw [← Nat.div_add_mod a m]
  rw [Nat.cast_add, Nat.cast_mul]
  have hm : (m : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff m p).2 hpm
  simp [hm]

lemma toX_emul_of_dvd {p m : Nat} (hpm : p ∣ m) (x y : Elt) :
    toX p (emul m x y) = toX p x * toX p y := by
  ext <;> simp [toX, emul, Nat.cast_add, Nat.cast_mul, cast_mod_of_dvd hpm]

lemma toX_stepAcc_of_dvd {p m : Nat} (hpm : p ∣ m) (base acc : Elt) (e : Nat) :
    toX p (stepAcc m base acc e) = if e % 2 = 1 then toX p acc * toX p base else toX p acc := by
  by_cases h : e % 2 = 1 <;> simp [stepAcc, h, toX_emul_of_dvd hpm]

lemma div2_bound {e f : Nat} (h : e < 2 ^ (f+1)) : e / 2 < 2 ^ f := by
  apply Nat.div_lt_of_lt_mul
  simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using h

lemma epowFuelAux_correct {p m : Nat} (hpm : p ∣ m) (fuel : Nat) (base acc : Elt) (e : Nat)
    (he : e < 2 ^ fuel) :
    toX p (epowFuelAux fuel m base acc e) = toX p acc * (toX p base) ^ e := by
  induction fuel generalizing base acc e with
  | zero =>
      have he0 : e = 0 := by omega
      simp [epowFuelAux, he0]
  | succ f ih =>
      rw [epowFuelAux]
      have hediv : e / 2 < 2 ^ f := div2_bound he
      rw [ih (emul m base base) (stepAcc m base acc e) (e/2) hediv]
      rw [toX_stepAcc_of_dvd hpm, toX_emul_of_dvd hpm]
      by_cases hodd : e % 2 = 1
      · have heq : e = 2 * (e/2) + 1 := by
          have := Nat.mod_add_div e 2
          omega
        have hdiv : (2 * (e / 2) + 1) / 2 = e / 2 := by omega
        rw [if_pos hodd, heq, hdiv]
        simp [pow_succ, pow_mul, pow_two, mul_assoc, mul_comm, mul_left_comm]
      · have hmod0 : e % 2 = 0 := by omega
        have heq : e = 2 * (e/2) := by
          have := Nat.mod_add_div e 2
          omega
        rw [if_neg hodd, heq]
        simp [pow_mul, pow_two, mul_assoc, mul_comm, mul_left_comm]

lemma epow4Aux_fst (fuel m : Nat) (base a1 a2 a3 a4 : Elt) (e1 e2 e3 e4 : Nat) :
    (epow4Aux fuel m base a1 a2 a3 a4 e1 e2 e3 e4).1 = epowFuelAux fuel m base a1 e1 := by
  induction fuel generalizing base a1 a2 a3 a4 e1 e2 e3 e4 with
  | zero => rfl
  | succ f ih => simp [epow4Aux, epowFuelAux, ih]

lemma epow4Aux_snd_fst (fuel m : Nat) (base a1 a2 a3 a4 : Elt) (e1 e2 e3 e4 : Nat) :
    (epow4Aux fuel m base a1 a2 a3 a4 e1 e2 e3 e4).2.1 = epowFuelAux fuel m base a2 e2 := by
  induction fuel generalizing base a1 a2 a3 a4 e1 e2 e3 e4 with
  | zero => rfl
  | succ f ih => simp [epow4Aux, epowFuelAux, ih]

lemma epow4Aux_snd_snd_fst (fuel m : Nat) (base a1 a2 a3 a4 : Elt) (e1 e2 e3 e4 : Nat) :
    (epow4Aux fuel m base a1 a2 a3 a4 e1 e2 e3 e4).2.2.1 = epowFuelAux fuel m base a3 e3 := by
  induction fuel generalizing base a1 a2 a3 a4 e1 e2 e3 e4 with
  | zero => rfl
  | succ f ih => simp [epow4Aux, epowFuelAux, ih]

lemma epow4Aux_snd_snd_snd (fuel m : Nat) (base a1 a2 a3 a4 : Elt) (e1 e2 e3 e4 : Nat) :
    (epow4Aux fuel m base a1 a2 a3 a4 e1 e2 e3 e4).2.2.2 = epowFuelAux fuel m base a4 e4 := by
  induction fuel generalizing base a1 a2 a3 a4 e1 e2 e3 e4 with
  | zero => rfl
  | succ f ih => simp [epow4Aux, epowFuelAux, ih]

lemma toX_one_of_dvd {p m : Nat} (hpm : p ∣ m) : toX p (one m) = (1 : X p) := by
  ext <;> simp [one, toX, cast_mod_of_dvd hpm]

lemma toX_gamma_of_dvd {p : Nat} (hpdvd : p ∣ N) : toX p (gamma N) = (X.gammaUnit p hpdvd : Units (X p)) := by
  rw [X.gammaUnit_coe]
  have hN0 : (N : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff N p).2 hpdvd
  ext
  · dsimp [toX, gamma]
    rw [cast_mod_of_dvd hpdvd]
    let k := inv5 % N
    have hk : (k : ZMod p) = (inv5 : ZMod p) := by
      dsimp [k]
      exact (cast_mod_of_dvd (p := p) (m := N) (a := inv5) hpdvd)
    have hle : k ≤ N := by
      dsimp [k]
      exact le_of_lt (Nat.mod_lt inv5 N_pos)
    have hsum : ((N - k : Nat) : ZMod p) + (k : ZMod p) = 0 := by
      rw [← Nat.cast_add, Nat.sub_add_cancel hle, hN0]
    calc
      ((N - k : Nat) : ZMod p) = ((N - k : Nat) : ZMod p) + (k : ZMod p) - (k : ZMod p) := by ring
      _ = -(k : ZMod p) := by rw [hsum]; ring
      _ = -(inv5 : ZMod p) := by rw [hk]
  · dsimp [toX, gamma]
    rw [cast_mod_of_dvd hpdvd]
    let k := 1 % N
    have hk : (k : ZMod p) = (1 : ZMod p) := by
      dsimp [k]
      simpa only [Nat.cast_one] using (cast_mod_of_dvd (p := p) (m := N) (a := 1) hpdvd)
    have hle : k ≤ N := by
      dsimp [k]
      exact le_of_lt (Nat.mod_lt 1 N_pos)
    have hsum : ((N - k : Nat) : ZMod p) + (k : ZMod p) = 0 := by
      rw [← Nat.cast_add, Nat.sub_add_cancel hle, hN0]
    calc
      ((N - k : Nat) : ZMod p) = ((N - k : Nat) : ZMod p) + (k : ZMod p) - (k : ZMod p) := by ring
      _ = -(k : ZMod p) := by rw [hsum]; ring
      _ = (-1 : ZMod p) := by rw [hk]

lemma cert_parts :
    certTuple.1 = one N ∧ diffGcd certTuple.2.1 N = 1 ∧
    diffGcd certTuple.2.2.1 N = 1 ∧ diffGcd certTuple.2.2.2 N = 1 := by
  have h := certAll
  unfold good at h
  repeat rw [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  exact ⟨Elt.eq_of_beq h1, beq_iff_eq.mp h2, beq_iff_eq.mp h3, beq_iff_eq.mp h4⟩

lemma gamma_pow_eq_one_of_cert {p : Nat} (hpdvd : p ∣ N) :
    (X.gammaUnit p hpdvd) ^ (N+1) = 1 := by
  have hcert := cert_parts.1
  apply Units.ext
  change ((X.gammaUnit p hpdvd : Units (X p)) ^ (N+1) : X p) = (1 : X p)
  rw [← toX_gamma_of_dvd hpdvd]
  have hbound := fuel_bound
  have hc := epowFuelAux_correct hpdvd 70000 (gamma N) (one N) (N+1) hbound
  rw [toX_one_of_dvd hpdvd, one_mul] at hc
  rw [← hc]
  rw [← epow4Aux_fst 70000 N (gamma N) (one N) (one N) (one N) (one N) (N+1) ((N+1)/2) ((N+1)/3) ((N+1)/100943)]
  change toX p certTuple.1 = (1 : X p)
  rw [hcert, toX_one_of_dvd hpdvd]

lemma gamma_pow_ne_one_of_gcd {p e : Nat} (hpprime : Nat.Prime p) (hpdvd : p ∣ N) (hgcd : diffGcd (epowFuelAux 70000 N (gamma N) (one N) e) N = 1)
    (he : e < 2 ^ 70000) : (X.gammaUnit p hpdvd) ^ e ≠ 1 := by
  intro hpow
  have hval := congrArg (fun u : Units (X p) => (u : X p)) hpow
  change ((X.gammaUnit p hpdvd : Units (X p)) ^ e : X p) = (1 : X p) at hval
  rw [← toX_gamma_of_dvd hpdvd] at hval
  have hc := epowFuelAux_correct hpdvd 70000 (gamma N) (one N) e he
  rw [toX_one_of_dvd hpdvd, one_mul] at hc
  rw [← hc] at hval
  have hu : (p : Nat) ∣ (epowFuelAux 70000 N (gamma N) (one N) e).u % N := by
    rw [← ZMod.natCast_eq_zero_iff]
    rw [cast_mod_of_dvd hpdvd]
    have hu0 := congrArg Prod.fst hval
    change (((epowFuelAux 70000 N (gamma N) (one N) e).u : Nat) : ZMod p) = 0 at hu0
    exact hu0
  have hv : (p : Nat) ∣ ((epowFuelAux 70000 N (gamma N) (one N) e).v + N - 1) % N := by
    rw [← ZMod.natCast_eq_zero_iff]
    rw [cast_mod_of_dvd hpdvd]
    have hv1 : (((epowFuelAux 70000 N (gamma N) (one N) e).v : Nat) : ZMod p) = 1 := by
      have hv1' := congrArg Prod.snd hval
      change (((epowFuelAux 70000 N (gamma N) (one N) e).v : Nat) : ZMod p) = 1 at hv1'
      exact hv1'
    have hN0 : (N : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff N p).2 hpdvd
    have hNpred : ((N - 1 : Nat) : ZMod p) = -1 := by
      have hleN : 1 ≤ N := Nat.succ_le_of_lt N_pos
      rw [Nat.cast_sub hleN, hN0]
      ring
    have hrewrite : (epowFuelAux 70000 N (gamma N) (one N) e).v + N - 1 =
        (epowFuelAux 70000 N (gamma N) (one N) e).v + (N - 1) := by
      exact Nat.add_sub_assoc (Nat.succ_le_of_lt N_pos) _
    rw [hrewrite, Nat.cast_add, hNpred, hv1]
    ring
