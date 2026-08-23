import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A268597: Smallest $x$ such that $x-1 \pmod{\phi(x)} = n$, or $0$ if no such $x$ exists.
-/
noncomputable def A268597 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

/-- The remainder map whose surjectivity is equivalent to the conjecture. -/
def totientRem (x : ℕ) : ℕ := (x - 1) % x.totient

lemma A268597_pos_of_exists {n x : ℕ} (hx0 : 0 < x) (hx : totientRem x = n) :
    A268597 n > 0 := by
  have hxmem : x ∈ { y : ℕ | y > 0 ∧ (y - 1) % y.totient = n } := ⟨hx0, hx⟩
  have hne : { y : ℕ | y > 0 ∧ (y - 1) % y.totient = n }.Nonempty := ⟨x, hxmem⟩
  exact (Nat.sInf_mem hne).1

lemma totientRem_one : totientRem 1 = 0 := by
  simp [totientRem]

/-- `p^{k+1} - 1 = p^k(p-1) + (p^k - 1)`. -/
lemma prime_pow_succ_pred_eq {p k : ℕ} (hp : 0 < p) :
    p ^ (k + 1) - 1 = p ^ k * (p - 1) + (p ^ k - 1) := by
  have hpk : 1 ≤ p ^ k := one_le_pow k p hp
  have hp1 : 1 ≤ p := hp
  have hpow : p ^ (k + 1) = p * p ^ k := pow_succ' p k
  have hsplit : p * p ^ k = p ^ k * (p - 1) + p ^ k := by
    nth_rw 1 [show p = (p - 1) + 1 from (Nat.sub_add_cancel hp1).symm]
    rw [add_mul, one_mul, mul_comm (p - 1)]
  omega

lemma totientRem_prime_pow_succ {p k : ℕ} (hp : p.Prime) :
    totientRem (p ^ (k + 1)) = p ^ k - 1 := by
  have hφ : (p ^ (k + 1)).totient = p ^ k * (p - 1) := totient_prime_pow_succ hp k
  have hcalc := prime_pow_succ_pred_eq (p := p) (k := k) hp.pos
  have hlt : p ^ k - 1 < p ^ k * (p - 1) := by
    have hpos : 0 < p - 1 := tsub_pos_iff_lt.mpr hp.one_lt
    have hpk : 0 < p ^ k := pow_pos hp.pos _
    have : p ^ k ≤ p ^ k * (p - 1) := Nat.le_mul_of_pos_right _ hpos
    omega
  unfold totientRem
  rw [hφ, hcalc, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]

lemma exists_of_succ_prime_pow {n p k : ℕ} (hp : p.Prime) (hn : n + 1 = p ^ k) :
    ∃ x > 0, totientRem x = n := by
  refine ⟨p ^ (k + 1), pow_pos hp.pos _, ?_⟩
  have h := totientRem_prime_pow_succ (p := p) (k := k) hp
  have hpk : 1 ≤ p ^ k := by
    rw [← hn]
    exact Nat.succ_le_succ (Nat.zero_le n)
  have : p ^ k - 1 = n := by omega
  rw [h, this]

/-- If `x` is even and at least `2`, then `totientRem (2x) = 2 * totientRem x + 1`. -/
lemma totientRem_two_mul_of_even {x : ℕ} (hx : Even x) (hx2 : 2 ≤ x) :
    totientRem (2 * x) = 2 * totientRem x + 1 := by
  have hφ : (2 * x).totient = 2 * x.totient := totient_two_mul_of_even hx
  have hid : 2 * x - 1 = 2 * (x - 1) + 1 := by omega
  have hφx : 0 < x.totient := totient_pos.mpr (by omega)
  set r := (x - 1) % x.totient
  set q := (x - 1) / x.totient
  have hsum : 2 * r + 1 < 2 * x.totient := by
    have := Nat.mod_lt (x - 1) hφx
    omega
  have hdecomp : x.totient * q + r = x - 1 := Nat.div_add_mod (x - 1) x.totient
  unfold totientRem
  rw [hφ, hid]
  have hrew : 2 * (x - 1) + 1 = q * (2 * x.totient) + (2 * r + 1) := by
    calc
      2 * (x - 1) + 1 = 2 * (x.totient * q + r) + 1 := by rw [hdecomp]
      _ = q * (2 * x.totient) + (2 * r + 1) := by ring
  rw [hrew, Nat.mul_add_mod_of_lt hsum]

/-- Product of two distinct odd primes, under the standard no-wrap bound. -/
lemma totientRem_mul_two_odd_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hwrap : 1 < (p - 2) * (q - 2)) :
    totientRem (p * q) = p + q - 2 := by
  have hcop : p.Coprime q :=
    hp.coprime_iff_not_dvd.2 fun hdvd => by
      have : p = q := (hq.dvd_iff_eq hp.ne_one).1 hdvd |>.symm
      exact hne this
  have hφ : (p * q).totient = (p - 1) * (q - 1) := by
    rw [totient_mul hcop, totient_prime hp, totient_prime hq]
  have hp1 : 1 ≤ p := hp.one_le
  have hq1 : 1 ≤ q := hq.one_le
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hid : p * q - 1 = (p - 1) * (q - 1) + (p + q - 2) := by
    have hp' : p = (p - 1) + 1 := (Nat.sub_add_cancel hp1).symm
    have hq' : q = (q - 1) + 1 := (Nat.sub_add_cancel hq1).symm
    have hmul : p * q = (p - 1) * (q - 1) + (p + q - 1) := by
      nth_rw 1 [hp', hq']
      have : p + q - 1 = (p - 1) + (q - 1) + 1 := by omega
      rw [this]
      ring
    have : 1 ≤ p * q := Nat.succ_le_of_lt (mul_pos hp.pos hq.pos)
    omega
  have hlt : p + q - 2 < (p - 1) * (q - 1) := by
    have hp' : p = (p - 2) + 2 := (Nat.sub_add_cancel hp2).symm
    have hq' : q = (q - 2) + 2 := (Nat.sub_add_cancel hq2).symm
    have : (p - 1) * (q - 1) + 1 = (p + q - 2) + (p - 2) * (q - 2) := by
      have hp'' : p - 1 = (p - 2) + 1 := by omega
      have hq'' : q - 1 = (q - 2) + 1 := by omega
      rw [hp'', hq'']
      have hsum : p + q - 2 = (p - 2) + (q - 2) + 2 := by omega
      rw [hsum]
      ring
    omega
  unfold totientRem
  rw [hφ, hid, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]

lemma exists_of_goldbach {n p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hsum : p + q = n + 2)
    (hwrap : 1 < (p - 2) * (q - 2)) :
    ∃ x > 0, totientRem x = n := by
  refine ⟨p * q, mul_pos hp.pos hq.pos, ?_⟩
  have h := totientRem_mul_two_odd_primes hp hq hne hwrap
  have : p + q - 2 = n := by omega
  rw [h, this]

/-- `2^a` and an odd prime power are coprime. -/
lemma coprime_two_pow_odd_prime_pow {p a b : ℕ} (hp : p.Prime) (hodd : Odd p) :
    (2 ^ a).Coprime (p ^ b) := by
  have h2p : Nat.Coprime 2 p := by
    rw [Nat.coprime_primes Nat.prime_two hp]
    intro h
    have : Even p := by rw [← h]; exact even_two
    exact Nat.not_odd_iff_even.2 this hodd
  exact h2p.pow a b

/-- The family `x = 2^a p^{b+1}` realizes `n = 2^a p^b - 1`. -/
lemma totientRem_two_pow_mul_odd_prime_pow {p a b : ℕ}
    (hp : p.Prime) (hodd : Odd p) (ha : 0 < a) :
    totientRem (2 ^ a * p ^ (b + 1)) = 2 ^ a * p ^ b - 1 := by
  have hcop := coprime_two_pow_odd_prime_pow (a := a) (b := b + 1) hp hodd
  have hφ2 : (2 ^ a).totient = 2 ^ (a - 1) := by
    rw [totient_prime_pow Nat.prime_two ha, Nat.mul_one]
  have hφp : (p ^ (b + 1)).totient = p ^ b * (p - 1) := totient_prime_pow_succ hp b
  have hφ : (2 ^ a * p ^ (b + 1)).totient = 2 ^ (a - 1) * (p ^ b * (p - 1)) := by
    rw [totient_mul hcop, hφ2, hφp]
  have hp1 : 1 ≤ p := hp.one_le
  have hpb : 1 ≤ p ^ b := one_le_pow b p hp.pos
  have ha' : a = (a - 1) + 1 := (Nat.sub_add_cancel ha).symm
  have h2a : 2 ^ a = 2 * 2 ^ (a - 1) := by
    nth_rw 1 [ha']
    exact pow_succ' 2 (a - 1)
  have hpow : p ^ (b + 1) = p * p ^ b := pow_succ' p b
  have hx : 2 ^ a * p ^ (b + 1) =
      2 * (2 ^ (a - 1) * (p ^ b * (p - 1))) + 2 ^ a * p ^ b := by
    rw [hpow, h2a]
    have hp' : p = (p - 1) + 1 := (Nat.sub_add_cancel hp1).symm
    nth_rw 1 [hp']
    ring
  have hpos : 1 ≤ 2 ^ a * p ^ (b + 1) :=
    one_le_mul (one_le_pow a 2 (by decide)) (one_le_pow (b + 1) p hp.pos)
  have hid : 2 ^ a * p ^ (b + 1) - 1 =
      2 * (2 ^ (a - 1) * (p ^ b * (p - 1))) + (2 ^ a * p ^ b - 1) := by
    have hB : 1 ≤ 2 ^ a * p ^ b :=
      one_le_mul (one_le_pow a 2 (by decide)) hpb
    calc
      2 ^ a * p ^ (b + 1) - 1
          = 2 * (2 ^ (a - 1) * (p ^ b * (p - 1))) + 2 ^ a * p ^ b - 1 := by
            rw [hx]
      _ = 2 * (2 ^ (a - 1) * (p ^ b * (p - 1))) + (2 ^ a * p ^ b - 1) := by
            omega
  have hp_ne_two : p ≠ 2 := fun h => by
    rw [h] at hodd
    exact Nat.not_odd_iff_even.2 even_two hodd
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hlt : 2 ^ a * p ^ b - 1 < 2 ^ (a - 1) * (p ^ b * (p - 1)) := by
    set K := 2 ^ (a - 1) * p ^ b
    have hK : 0 < K := mul_pos (pow_pos (by decide : 0 < 2) _) (pow_pos hp.pos _)
    have hleft : 2 ^ a * p ^ b = 2 * K := by
      rw [h2a]; ring
    have hright : 2 ^ (a - 1) * (p ^ b * (p - 1)) = K * (p - 1) := by
      simp [K, mul_assoc]
    rw [hleft, hright]
    have h2le : 2 ≤ p - 1 := by omega
    have : 2 * K ≤ K * (p - 1) := by
      rw [mul_comm K]
      exact Nat.mul_le_mul_right K h2le
    omega
  unfold totientRem
  rw [hφ, hid, Nat.mul_add_mod_of_lt hlt]

lemma exists_of_two_pow_mul_prime_pow {n p a b : ℕ}
    (hp : p.Prime) (hodd : Odd p) (ha : 0 < a)
    (hn : n + 1 = 2 ^ a * p ^ b) :
    ∃ x > 0, totientRem x = n := by
  refine ⟨2 ^ a * p ^ (b + 1), mul_pos (pow_pos (by decide) _) (pow_pos hp.pos _), ?_⟩
  have h := totientRem_two_pow_mul_odd_prime_pow (p := p) (a := a) (b := b) hp hodd ha
  have hpb : 1 ≤ 2 ^ a * p ^ b := by
    rw [← hn]
    exact Nat.succ_le_succ (Nat.zero_le n)
  have : 2 ^ a * p ^ b - 1 = n := by omega
  rw [h, this]

/-- If `x` is odd then `φ(2x) = φ(x)`, so doubling wraps unless `2 * totientRem x + 1 < φ(x)`. -/
lemma totientRem_two_mul_of_odd {x : ℕ} (hx : Odd x) (hwrap : 2 * totientRem x + 1 < x.totient) :
    totientRem (2 * x) = 2 * totientRem x + 1 := by
  have hφ : (2 * x).totient = x.totient := totient_two_mul_of_odd hx
  have hx0 : 1 ≤ x := by
    match x with
    | 0 => exact (Nat.not_odd_zero hx).elim
    | x + 1 => exact Nat.succ_le_succ (Nat.zero_le _)
  have hid : 2 * x - 1 = 2 * (x - 1) + 1 := by omega
  set r := (x - 1) % x.totient
  set q := (x - 1) / x.totient
  have hdecomp : x.totient * q + r = x - 1 := Nat.div_add_mod (x - 1) x.totient
  unfold totientRem at hwrap ⊢
  rw [hφ, hid]
  have hrew : 2 * (x - 1) + 1 = q * (2 * x.totient) + (2 * r + 1) := by
    calc
      2 * (x - 1) + 1 = 2 * (x.totient * q + r) + 1 := by rw [hdecomp]
      _ = q * (2 * x.totient) + (2 * r + 1) := by ring
  -- We need the remainder against `x.totient`, not `2 * x.totient`.
  have hsum : 2 * (x - 1) + 1 = (2 * q) * x.totient + (2 * r + 1) := by
    calc
      2 * (x - 1) + 1 = 2 * (x.totient * q + r) + 1 := by rw [hdecomp]
      _ = (2 * q) * x.totient + (2 * r + 1) := by ring
  rw [hsum, Nat.mul_add_mod_of_lt hwrap]

/-- If `p` divides `x`, then `totientRem (p * x) = p * totientRem x + (p - 1)`. -/
lemma totientRem_prime_mul_of_dvd {p x : ℕ} (hp : p.Prime) (hx0 : 0 < x) (hdiv : p ∣ x) :
    totientRem (p * x) = p * totientRem x + (p - 1) := by
  have hφ : (p * x).totient = p * x.totient := totient_mul_of_prime_of_dvd hp hdiv
  have hφx : 0 < x.totient := totient_pos.mpr hx0
  have hid : p * x - 1 = p * (x - 1) + (p - 1) := by
    have hx1 : 1 ≤ x := hx0
    have hp1 : 1 ≤ p := hp.one_le
    have hsplit : p * x = p * (x - 1) + p := by
      nth_rw 1 [show x = (x - 1) + 1 from (Nat.sub_add_cancel hx1).symm]
      ring
    calc
      p * x - 1 = p * (x - 1) + p - 1 := by rw [hsplit]
      _ = p * (x - 1) + (p - 1) := Nat.add_sub_assoc hp1 _
  set r := (x - 1) % x.totient
  set q := (x - 1) / x.totient
  have hdecomp : x.totient * q + r = x - 1 := Nat.div_add_mod (x - 1) x.totient
  have hrlt : r < x.totient := Nat.mod_lt (x - 1) hφx
  have hsum : p * r + (p - 1) < p * x.totient := by
    have hle : p * (r + 1) ≤ p * x.totient :=
      Nat.mul_le_mul_left p (Nat.succ_le_of_lt hrlt)
    have hp0 : 0 < p := hp.pos
    calc
      p * r + (p - 1) < p * r + p := Nat.add_lt_add_left (Nat.sub_lt hp0 (by decide)) _
      _ = p * (r + 1) := by ring
      _ ≤ p * x.totient := hle
  unfold totientRem
  rw [hφ, hid]
  have hrew : p * (x - 1) + (p - 1) = q * (p * x.totient) + (p * r + (p - 1)) := by
    calc
      p * (x - 1) + (p - 1) = p * (x.totient * q + r) + (p - 1) := by rw [hdecomp]
      _ = q * (p * x.totient) + (p * r + (p - 1)) := by ring
  rw [hrew, Nat.mul_add_mod_of_lt hsum]

lemma exists_of_prime_mul_dvd {n r p x : ℕ} (hp : p.Prime) (hx0 : 0 < x)
    (hdiv : p ∣ x) (hx : totientRem x = r) (hn : n = p * r + (p - 1)) :
    ∃ y > 0, totientRem y = n := by
  refine ⟨p * x, mul_pos hp.pos hx0, ?_⟩
  rw [totientRem_prime_mul_of_dvd hp hx0 hdiv, hx, hn]


/-- `n+1 = p(p + q - 1)` is realized by `x = p^2 q`. -/
lemma totientRem_p_sq_q {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hwrap : p * (p + q - 1) - 1 < p * (p - 1) * (q - 1)) :
    totientRem (p ^ 2 * q) = p * (p + q - 1) - 1 := by
  have hcop : (p ^ 2).Coprime q := by
    rw [Nat.coprime_pow_left_iff (by decide : 0 < 2)]
    exact hp.coprime_iff_not_dvd.2 fun hdvd =>
      hne ((hq.dvd_iff_eq hp.ne_one).1 hdvd).symm
  have hφ : (p ^ 2 * q).totient = p * (p - 1) * (q - 1) := by
    rw [totient_mul hcop, totient_prime_pow hp (by decide : 0 < 2), totient_prime hq]
    ring
  have hp1 : 1 ≤ p := hp.one_le
  have hq1 : 1 ≤ q := hq.one_le
  have hinner : (p - 1) * (q - 1) + (p + q - 1) = p * q := by
    have hsum : p + q - 1 = (p - 1) + (q - 1) + 1 := by omega
    have hmul : p * q = ((p - 1) + 1) * ((q - 1) + 1) := by
      rw [Nat.sub_add_cancel hp1, Nat.sub_add_cancel hq1]
    rw [hsum, hmul]
    ring
  have hx : p ^ 2 * q = p * (p - 1) * (q - 1) + p * (p + q - 1) := by
    have hpow : p ^ 2 * q = p * (p * q) := by
      rw [sq, mul_assoc]
    rw [hpow, ← hinner]
    ring
  have hB : 1 ≤ p * (p + q - 1) := by
    exact one_le_mul hp1 (by omega)
  have hid : p ^ 2 * q - 1 = p * (p - 1) * (q - 1) + (p * (p + q - 1) - 1) := by
    rw [hx]
    omega
  unfold totientRem
  rw [hφ, hid, Nat.add_mod_left, Nat.mod_eq_of_lt hwrap]

lemma exists_of_p_sq_q {n p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hn : n + 1 = p * (p + q - 1))
    (hwrap : p * (p + q - 1) - 1 < p * (p - 1) * (q - 1)) :
    ∃ x > 0, totientRem x = n := by
  refine ⟨p ^ 2 * q, mul_pos (pow_pos hp.pos _) hq.pos, ?_⟩
  have h := totientRem_p_sq_q hp hq hne hwrap
  have : p * (p + q - 1) - 1 = n := by omega
  rw [h, this]

/-- Goldbach partner `p` gives a witness, provided the wrap bound holds. -/
lemma exists_of_goldbach_prime {n p : ℕ} (hp : p.Prime) (hq : (n + 2 - p).Prime)
    (hplt : p < n + 2) (hne : p ≠ n + 2 - p)
    (hwrap : 1 < (p - 2) * (n + 2 - p - 2)) :
    ∃ x > 0, totientRem x = n :=
  exists_of_goldbach hp hq hne (by omega) hwrap

/-- If `n - 1` is an odd prime `≥ 5`, then `x = 3(n - 1)` is a witness. -/
lemma exists_of_three_goldbach {n : ℕ} (hn : 6 ≤ n) (hp : (n - 1).Prime) :
    ∃ x > 0, totientRem x = n := by
  have h3 : Nat.Prime 3 := by decide
  have hne : (3 : ℕ) ≠ n - 1 := by omega
  have hsum : (3 : ℕ) + (n - 1) = n + 2 := by omega
  have hwrap : 1 < (3 - 2) * (n - 1 - 2) := by
    simp
    omega
  exact exists_of_goldbach h3 hp hne hsum hwrap

/-- If `n - 3` is prime and `n ≥ 10`, then `x = 5(n - 3)` is a witness. -/
lemma exists_of_five_goldbach {n : ℕ} (hn : 10 ≤ n) (hp : (n - 3).Prime) :
    ∃ x > 0, totientRem x = n := by
  have h5 : Nat.Prime 5 := by decide
  have hne : (5 : ℕ) ≠ n - 3 := by omega
  have hsum : (5 : ℕ) + (n - 3) = n + 2 := by omega
  have hwrap : 1 < (5 - 2) * (n - 3 - 2) := by
    simp
    omega
  exact exists_of_goldbach h5 hp hne hsum hwrap

/-- If `n - 5` is prime and `n ≥ 14`, then `x = 7(n - 5)` is a witness. -/
lemma exists_of_seven_goldbach {n : ℕ} (hn : 14 ≤ n) (hp : (n - 5).Prime) :
    ∃ x > 0, totientRem x = n := by
  have h7 : Nat.Prime 7 := by decide
  have hne : (7 : ℕ) ≠ n - 5 := by omega
  have hsum : (7 : ℕ) + (n - 5) = n + 2 := by omega
  have hwrap : 1 < (7 - 2) * (n - 5 - 2) := by
    simp
    omega
  exact exists_of_goldbach h7 hp hne hsum hwrap

/-- A `p^2 q` witness coming from a prime factor of `n+1`. -/
lemma exists_of_p2q_of_factor {n p : ℕ} (hp : p.Prime) (hpd : p ∣ n + 1)
    (hq : ((n + 1) / p + 1 - p).Prime)
    (hne : p ≠ (n + 1) / p + 1 - p)
    (hwrap : p * ((n + 1) / p) - 1 < p * (p - 1) * ((n + 1) / p + 1 - p - 1)) :
    ∃ x > 0, totientRem x = n := by
  set s := (n + 1) / p
  set q := s + 1 - p
  have hs : n + 1 = p * s := (Nat.mul_div_cancel' hpd).symm
  have hq' : q.Prime := hq
  have hq2 : 2 ≤ q := hq'.two_le
  have hple : p ≤ s + 1 := by
    have : 2 ≤ s + 1 - p := hq2
    omega
  have hqs : p + q - 1 = s := by
    simp [q]
    omega
  have hn : n + 1 = p * (p + q - 1) := by
    rw [hs, hqs]
  refine exists_of_p_sq_q hp hq' hne hn ?_
  simpa [hqs] using hwrap

/-- `x = 9p` realizes `n = 3p + 5` for primes `p ≥ 5`. -/
lemma totientRem_nine_mul_prime {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    totientRem (9 * p) = 3 * p + 5 := by
  have hP3 : Nat.Prime 3 := by decide
  have h3 : p ≠ 3 := by omega
  have hcop : (9 : ℕ).Coprime p := by
    have h9eq : (9 : ℕ) = 3 ^ 2 := by decide
    rw [h9eq, Nat.coprime_pow_left_iff (by decide : 0 < 2)]
    exact hP3.coprime_iff_not_dvd.2 fun hdvd =>
      h3 ((hp.dvd_iff_eq hP3.ne_one).1 hdvd)
  have hφ : (9 * p).totient = 6 * (p - 1) := by
    rw [totient_mul hcop, show (9 : ℕ).totient = 6 from by decide, totient_prime hp]
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hp5
  have hid : 9 * (a + 5) - 1 = 6 * (a + 5 - 1) + (3 * (a + 5) + 5) := by
    simp; ring_nf; omega
  have hlt : 3 * (a + 5) + 5 < 6 * (a + 5 - 1) := by
    simp; omega
  unfold totientRem
  rw [hφ, hid, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]

lemma exists_of_nine_mul_prime {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : n = 3 * p + 5) :
    ∃ x > 0, totientRem x = n := by
  refine ⟨9 * p, mul_pos (by decide : 0 < 9) hp.pos, ?_⟩
  rw [totientRem_nine_mul_prime hp hp5, hn]

/-- `x = 15p` realizes `n = 7(p + 1)` for primes `p > 15`. -/
lemma totientRem_fifteen_mul_prime {p : ℕ} (hp : p.Prime) (hp17 : 17 ≤ p) :
    totientRem (15 * p) = 7 * (p + 1) := by
  have h3 : Nat.Prime 3 := by decide
  have h5 : Nat.Prime 5 := by decide
  have hcop : (15 : ℕ).Coprime p := by
    have h3p : (3 : ℕ).Coprime p :=
      h3.coprime_iff_not_dvd.2 fun hdvd => by
        have : p = 3 := (hp.dvd_iff_eq h3.ne_one).1 hdvd
        omega
    have h5p : (5 : ℕ).Coprime p :=
      h5.coprime_iff_not_dvd.2 fun hdvd => by
        have : p = 5 := (hp.dvd_iff_eq h5.ne_one).1 hdvd
        omega
    have : (15 : ℕ) = 3 * 5 := by decide
    rw [this]
    exact h3p.mul_left h5p
  have hφ : (15 * p).totient = 8 * (p - 1) := by
    have h15 : (15 : ℕ).totient = 8 := by decide
    rw [totient_mul hcop, h15, totient_prime hp]
  have hid : 15 * p - 1 = 8 * (p - 1) + 7 * (p + 1) := by
    have : 15 * p = 8 * (p - 1) + 7 * (p + 1) + 1 := by
      cases p with
      | zero => cases hp.pos
      | succ p =>
        simp
        ring
    omega
  have hlt : 7 * (p + 1) < 8 * (p - 1) := by omega
  unfold totientRem
  rw [hφ, hid, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]

lemma exists_of_fifteen_mul_prime {n p : ℕ} (hp : p.Prime) (hp17 : 17 ≤ p)
    (hn : n = 7 * (p + 1)) :
    ∃ x > 0, totientRem x = n := by
  refine ⟨15 * p, mul_pos (by decide : 0 < 15) hp.pos, ?_⟩
  rw [totientRem_fifteen_mul_prime hp hp17, hn]

/-- `x = 3pq` realizes `n = (p + 2)(q + 2) - 7` for distinct primes `p, q ≥ 7`. -/
lemma totientRem_three_mul_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp7 : 7 ≤ p) (hq7 : 7 ≤ q) (hne : p ≠ q) :
    totientRem (3 * p * q) = (p + 2) * (q + 2) - 7 := by
  have h3 : Nat.Prime 3 := by decide
  have hp3 : p ≠ 3 := by omega
  have hq3 : q ≠ 3 := by omega
  have hcop3p : (3 : ℕ).Coprime p :=
    h3.coprime_iff_not_dvd.2 fun hdvd => hp3 ((hp.dvd_iff_eq h3.ne_one).1 hdvd)
  have hcop3q : (3 : ℕ).Coprime q :=
    h3.coprime_iff_not_dvd.2 fun hdvd => hq3 ((hq.dvd_iff_eq h3.ne_one).1 hdvd)
  have hcoppq : p.Coprime q :=
    hp.coprime_iff_not_dvd.2 fun hdvd => hne ((hq.dvd_iff_eq hp.ne_one).1 hdvd).symm
  have hcop : (3 * p).Coprime q := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨hcop3q, hcoppq⟩
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hp7
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' hq7
  have hφ : (3 * (a + 7) * (b + 7)).totient = 2 * (a + 6) * (b + 6) := by
    have h3p : (3 * (a + 7)).totient = 2 * (a + 6) := by
      rw [totient_mul hcop3p, totient_prime h3, totient_prime hp]
      simp
    rw [totient_mul hcop, h3p, totient_prime hq]
    simp
  have hid : 3 * (a + 7) * (b + 7) - 1 =
      2 * (a + 6) * (b + 6) + ((a + 9) * (b + 9) - 7) := by
    have : 3 * (a + 7) * (b + 7) =
        2 * (a + 6) * (b + 6) + ((a + 9) * (b + 9) - 7) + 1 := by
      ring_nf; omega
    omega
  have hlt : (a + 9) * (b + 9) - 7 < 2 * (a + 6) * (b + 6) := by
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (by omega)
    have hL : (a + 9) * (b + 9) - 7 = a * b + 9 * a + 9 * b + 74 := by ring_nf; omega
    have hR : 2 * (a + 6) * (b + 6) = 2 * a * b + 12 * a + 12 * b + 72 := by ring
    rw [hL, hR]
    rcases hab with ha | hb
    · have : 1 ≤ a := Nat.pos_of_ne_zero ha
      nlinarith
    · have : 1 ≤ b := Nat.pos_of_ne_zero hb
      nlinarith
  unfold totientRem
  -- `(a+7+2)(b+7+2)-7 = (a+9)(b+9)-7`
  have hrew : (a + 7 + 2) * (b + 7 + 2) - 7 = (a + 9) * (b + 9) - 7 := by ring_nf
  rw [hφ, hrew, hid, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]

lemma exists_of_three_mul_two_primes {n p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp7 : 7 ≤ p) (hq7 : 7 ≤ q) (hne : p ≠ q)
    (hfac : (p + 2) * (q + 2) = n + 7) :
    ∃ x > 0, totientRem x = n := by
  refine ⟨3 * p * q, by positivity, ?_⟩
  have h := totientRem_three_mul_two_primes hp hq hp7 hq7 hne
  have : (p + 2) * (q + 2) - 7 = n := by omega
  rw [h, this]

/-- `x = 5pq` realizes `n = (p + 4)(q + 4) - 21` for distinct primes `p, q ≥ 7`. -/
lemma totientRem_five_mul_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp7 : 7 ≤ p) (hq7 : 7 ≤ q) (hne : p ≠ q) :
    totientRem (5 * p * q) = (p + 4) * (q + 4) - 21 := by
  have h5 : Nat.Prime 5 := by decide
  have hp5 : p ≠ 5 := by omega
  have hq5 : q ≠ 5 := by omega
  have hcop5p : (5 : ℕ).Coprime p :=
    h5.coprime_iff_not_dvd.2 fun hdvd => hp5 ((hp.dvd_iff_eq h5.ne_one).1 hdvd)
  have hcop5q : (5 : ℕ).Coprime q :=
    h5.coprime_iff_not_dvd.2 fun hdvd => hq5 ((hq.dvd_iff_eq h5.ne_one).1 hdvd)
  have hcoppq : p.Coprime q :=
    hp.coprime_iff_not_dvd.2 fun hdvd => hne ((hq.dvd_iff_eq hp.ne_one).1 hdvd).symm
  have hcop : (5 * p).Coprime q := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨hcop5q, hcoppq⟩
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hp7
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' hq7
  have hφ : (5 * (a + 7) * (b + 7)).totient = 4 * (a + 6) * (b + 6) := by
    have h5p : (5 * (a + 7)).totient = 4 * (a + 6) := by
      rw [totient_mul hcop5p, totient_prime h5, totient_prime hp]
      simp
    rw [totient_mul hcop, h5p, totient_prime hq]
    simp
  have hid : 5 * (a + 7) * (b + 7) - 1 =
      4 * (a + 6) * (b + 6) + ((a + 11) * (b + 11) - 21) := by
    have : 5 * (a + 7) * (b + 7) =
        4 * (a + 6) * (b + 6) + ((a + 11) * (b + 11) - 21) + 1 := by
      ring_nf; omega
    omega
  have hlt : (a + 11) * (b + 11) - 21 < 4 * (a + 6) * (b + 6) := by
    have hL : (a + 11) * (b + 11) - 21 = a * b + 11 * a + 11 * b + 100 := by ring_nf; omega
    have hR : 4 * (a + 6) * (b + 6) = 4 * a * b + 24 * a + 24 * b + 144 := by ring
    rw [hL, hR]
    nlinarith
  unfold totientRem
  have hrew : (a + 7 + 4) * (b + 7 + 4) - 21 = (a + 11) * (b + 11) - 21 := by ring_nf
  rw [hφ, hrew, hid, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]

lemma exists_of_five_mul_two_primes {n p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp7 : 7 ≤ p) (hq7 : 7 ≤ q) (hne : p ≠ q)
    (hfac : (p + 4) * (q + 4) = n + 21) :
    ∃ x > 0, totientRem x = n := by
  refine ⟨5 * p * q, by positivity, ?_⟩
  have h := totientRem_five_mul_two_primes hp hq hp7 hq7 hne
  have : (p + 4) * (q + 4) - 21 = n := by omega
  rw [h, this]

set_option maxHeartbeats 40000000

/-- `x = r p q` realizes
`n = (p + r - 1)(q + r - 1) - (r(r - 1) + 1)`
for distinct primes `r, p, q` with `r ≥ 3` and `p, q ≥ 7`. -/
lemma totientRem_prime_mul_two_primes {r p q : ℕ}
    (hr : r.Prime) (hp : p.Prime) (hq : q.Prime)
    (hr3 : 3 ≤ r) (hp7 : 7 ≤ p) (hq7 : 7 ≤ q)
    (hrp : r ≠ p) (hrq : r ≠ q) (hpq : p ≠ q) :
    totientRem (r * p * q) =
      (p + r - 1) * (q + r - 1) - (r * (r - 1) + 1) := by
  have hcoprp : r.Coprime p :=
    hr.coprime_iff_not_dvd.2 fun hdvd => hrp ((hp.dvd_iff_eq hr.ne_one).1 hdvd).symm
  have hcoprq : r.Coprime q :=
    hr.coprime_iff_not_dvd.2 fun hdvd => hrq ((hq.dvd_iff_eq hr.ne_one).1 hdvd).symm
  have hcoppq : p.Coprime q :=
    hp.coprime_iff_not_dvd.2 fun hdvd => hpq ((hq.dvd_iff_eq hp.ne_one).1 hdvd).symm
  have hcop : (r * p).Coprime q := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨hcoprq, hcoppq⟩
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hp7
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' hq7
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hr3
  have hφ : ((c + 3) * (a + 7) * (b + 7)).totient =
      (c + 2) * (a + 6) * (b + 6) := by
    have hrpφ : ((c + 3) * (a + 7)).totient = (c + 2) * (a + 6) := by
      rw [totient_mul hcoprp, totient_prime hr, totient_prime hp]
      simp
    rw [totient_mul hcop, hrpφ, totient_prime hq]
    simp
  have hrem :
      (a + 7 + (c + 3) - 1) * (b + 7 + (c + 3) - 1) - ((c + 3) * (c + 3 - 1) + 1) =
        (a + c + 9) * (b + c + 9) - (c * c + 5 * c + 7) := by
    simp; ring_nf
  have hid :
      (c + 3) * (a + 7) * (b + 7) - 1 =
        (c + 2) * (a + 6) * (b + 6) +
          ((a + c + 9) * (b + c + 9) - (c * c + 5 * c + 7)) := by
    have : (c + 3) * (a + 7) * (b + 7) =
        (c + 2) * (a + 6) * (b + 6) +
          ((a + c + 9) * (b + c + 9) - (c * c + 5 * c + 7)) + 1 := by
      have hge : c * c + 5 * c + 7 ≤ (a + c + 9) * (b + c + 9) := by
        nlinarith
      ring_nf; omega
    omega
  have hlt :
      (a + c + 9) * (b + c + 9) - (c * c + 5 * c + 7) <
        (c + 2) * (a + 6) * (b + 6) := by
    have hge : c * c + 5 * c + 7 ≤ (a + c + 9) * (b + c + 9) := by
      nlinarith
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push_neg at h
      exact hpq (by omega)
    have hL :
        (a + c + 9) * (b + c + 9) - (c * c + 5 * c + 7) =
          a * b + a * c + b * c + 9 * a + 9 * b + 13 * c + 74 := by
      ring_nf; omega
    have hR :
        (c + 2) * (a + 6) * (b + 6) =
          c * a * b + 2 * a * b + 6 * a * c + 6 * b * c +
            12 * a + 12 * b + 36 * c + 72 := by
      ring
    rw [hL, hR]
    -- Enough to show the difference is positive:
    -- `(c a b + a b + 5 a c + 5 b c + 3 a + 3 b + 23 c) ≥ 3`.
    have hdiff :
        3 ≤ c * a * b + a * b + 5 * a * c + 5 * b * c + 3 * a + 3 * b + 23 * c := by
      rcases hab with ha | hb
      · have ha1 : 1 ≤ a := Nat.pos_of_ne_zero ha
        have h3 : 3 ≤ 3 * a := by omega
        refine le_trans h3 ?_
        have hrest :
            3 * a ≤
              (c * a * b + a * b + 5 * a * c + 5 * b * c + 3 * b + 23 * c) + 3 * a :=
          Nat.le_add_left _ _
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrest
      · have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hb
        have h3 : 3 ≤ 3 * b := by omega
        refine le_trans h3 ?_
        have hrest :
            3 * b ≤
              (c * a * b + a * b + 5 * a * c + 5 * b * c + 3 * a + 23 * c) + 3 * b :=
          Nat.le_add_left _ _
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrest
    -- `RHS - LHS = (c a b + a b + 5 a c + 5 b c + 3 a + 3 b + 23 c) - 2 ≥ 1`.
    have hcmp :
        a * b + a * c + b * c + 9 * a + 9 * b + 13 * c + 74 + 1 ≤
          c * a * b + 2 * a * b + 6 * a * c + 6 * b * c +
            12 * a + 12 * b + 36 * c + 72 := by
      have hLHS :
          a * b + a * c + b * c + 9 * a + 9 * b + 13 * c + 74 + 1 =
            (a * b + a * c + b * c + 9 * a + 9 * b + 13 * c + 72) + 3 := by
        omega
      have hRHS :
          c * a * b + 2 * a * b + 6 * a * c + 6 * b * c +
              12 * a + 12 * b + 36 * c + 72 =
            (a * b + a * c + b * c + 9 * a + 9 * b + 13 * c + 72) +
              (c * a * b + a * b + 5 * a * c + 5 * b * c + 3 * a + 3 * b + 23 * c) := by
        ring
      rw [hLHS, hRHS]
      exact Nat.add_le_add_left hdiff _
    omega
  unfold totientRem
  rw [hφ, hrem, hid, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]

lemma exists_of_prime_mul_two_primes {n r p q : ℕ}
    (hr : r.Prime) (hp : p.Prime) (hq : q.Prime)
    (hr3 : 3 ≤ r) (hp7 : 7 ≤ p) (hq7 : 7 ≤ q)
    (hrp : r ≠ p) (hrq : r ≠ q) (hpq : p ≠ q)
    (hfac : (p + r - 1) * (q + r - 1) = n + r * (r - 1) + 1) :
    ∃ x > 0, totientRem x = n := by
  refine ⟨r * p * q, mul_pos (mul_pos hr.pos hp.pos) hq.pos, ?_⟩
  have h := totientRem_prime_mul_two_primes hr hp hq hr3 hp7 hq7 hrp hrq hpq
  have : (p + r - 1) * (q + r - 1) - (r * (r - 1) + 1) = n := by omega
  rw [h, this]


/-- `x = 21p` realizes `n = 9p + 11` for primes `p > 7`. -/
lemma totientRem_twentyone_mul_prime {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) :
    totientRem (21 * p) = 9 * p + 11 := by
  have h3 : Nat.Prime 3 := by decide
  have h7 : Nat.Prime 7 := by decide
  have hcop21 : (21 : ℕ).Coprime p := by
    have h3p : (3 : ℕ).Coprime p :=
      h3.coprime_iff_not_dvd.2 fun hdvd => by
        have : p = 3 := (hp.dvd_iff_eq h3.ne_one).1 hdvd
        omega
    have h7p : (7 : ℕ).Coprime p :=
      h7.coprime_iff_not_dvd.2 fun hdvd => by
        have : p = 7 := (hp.dvd_iff_eq h7.ne_one).1 hdvd
        omega
    have : (21 : ℕ) = 3 * 7 := by decide
    rw [this]
    exact h3p.mul_left h7p
  have hφ : (21 * p).totient = 12 * (p - 1) := by
    have h21 : (21 : ℕ).totient = 12 := by decide
    rw [totient_mul hcop21, h21, totient_prime hp]
  have hp1 : 1 ≤ p := hp.one_le
  have hid : 21 * p - 1 = 12 * (p - 1) + (9 * p + 11) := by
    have : 21 * p = 12 * (p - 1) + (9 * p + 12) := by
      cases p with
      | zero => cases hp1
      | succ p =>
        simp
        ring
    omega
  have hlt : 9 * p + 11 < 12 * (p - 1) := by omega
  unfold totientRem
  rw [hφ, hid, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]

lemma exists_of_twentyone_mul_prime {n p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hn : n = 9 * p + 11) :
    ∃ x > 0, totientRem x = n := by
  refine ⟨21 * p, mul_pos (by decide : 0 < 21) hp.pos, ?_⟩
  rw [totientRem_twentyone_mul_prime hp hp7, hn]

/-- If `n - 9` is prime and `n ≥ 22`, then `x = 11(n - 9)` is a witness. -/
lemma exists_of_eleven_goldbach {n : ℕ} (hn : 22 ≤ n) (hp : (n - 9).Prime) :
    ∃ x > 0, totientRem x = n := by
  have h11 : Nat.Prime 11 := by decide
  have hne : (11 : ℕ) ≠ n - 9 := by omega
  have hsum : (11 : ℕ) + (n - 9) = n + 2 := by omega
  have hwrap : 1 < (11 - 2) * (n - 9 - 2) := by
    simp
    omega
  exact exists_of_goldbach h11 hp hne hsum hwrap

/-- If `n - 11` is prime and `n ≥ 26`, then `x = 13(n - 11)` is a witness. -/
lemma exists_of_thirteen_goldbach {n : ℕ} (hn : 26 ≤ n) (hp : (n - 11).Prime) :
    ∃ x > 0, totientRem x = n := by
  have h13 : Nat.Prime 13 := by decide
  have hne : (13 : ℕ) ≠ n - 11 := by omega
  have hsum : (13 : ℕ) + (n - 11) = n + 2 := by omega
  have hwrap : 1 < (13 - 2) * (n - 11 - 2) := by
    simp
    omega
  exact exists_of_goldbach h13 hp hne hsum hwrap

/-- If `n - 15` is prime and `n ≥ 34`, then `x = 17(n - 15)` is a witness. -/
lemma exists_of_seventeen_goldbach {n : ℕ} (hn : 34 ≤ n) (hp : (n - 15).Prime) :
    ∃ x > 0, totientRem x = n := by
  have h17 : Nat.Prime 17 := by decide
  have hne : (17 : ℕ) ≠ n - 15 := by omega
  have hsum : (17 : ℕ) + (n - 15) = n + 2 := by omega
  have hwrap : 1 < (17 - 2) * (n - 15 - 2) := by
    simp
    omega
  exact exists_of_goldbach h17 hp hne hsum hwrap

/-- If `n - 17` is prime and `n ≥ 38`, then `x = 19(n - 17)` is a witness. -/
lemma exists_of_nineteen_goldbach {n : ℕ} (hn : 38 ≤ n) (hp : (n - 17).Prime) :
    ∃ x > 0, totientRem x = n := by
  have h19 : Nat.Prime 19 := by decide
  have hne : (19 : ℕ) ≠ n - 17 := by omega
  have hsum : (19 : ℕ) + (n - 17) = n + 2 := by omega
  have hwrap : 1 < (19 - 2) * (n - 17 - 2) := by
    simp
    omega
  exact exists_of_goldbach h19 hp hne hsum hwrap

/-- Product `x = 2pq` of two odd primes `≥ 5` realizes `n = 2p + 2q - 3`. -/
lemma totientRem_two_mul_odd_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hne : p ≠ q) :
    totientRem (2 * (p * q)) = 2 * p + 2 * q - 3 := by
  have hpodd : Odd p := Nat.Prime.odd_of_ne_two hp (by omega)
  have hqodd : Odd q := Nat.Prime.odd_of_ne_two hq (by omega)
  have hpq : p.Coprime q :=
    hp.coprime_iff_not_dvd.2 fun hdvd =>
      hne ((hq.dvd_iff_eq hp.ne_one).1 hdvd).symm
  have h2pq : (2 : ℕ).Coprime (p * q) := by
    rw [Nat.coprime_mul_iff_right]
    constructor
    · rw [Nat.coprime_primes Nat.prime_two hp]
      intro h; exact Nat.not_even_iff_odd.2 hpodd (h ▸ even_two)
    · rw [Nat.coprime_primes Nat.prime_two hq]
      intro h; exact Nat.not_even_iff_odd.2 hqodd (h ▸ even_two)
  have hφ : (2 * (p * q)).totient = (p - 1) * (q - 1) := by
    rw [totient_mul h2pq, totient_two, totient_mul hpq, totient_prime hp, totient_prime hq,
      one_mul]
  have hp1 : 1 ≤ p := hp.one_le
  have hq1 : 1 ≤ q := hq.one_le
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hp5
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' hq5
  -- Now `p = a + 5`, `q = b + 5`.
  have hid : 2 * ((a + 5) * (b + 5)) - 1 =
      2 * ((a + 5 - 1) * (b + 5 - 1)) + (2 * (a + 5) + 2 * (b + 5) - 3) := by
    have h1 : 2 * ((a + 5) * (b + 5)) - 1 = 2 * a * b + 10 * a + 10 * b + 49 := by
      ring_nf; omega
    have h2 : 2 * ((a + 5 - 1) * (b + 5 - 1)) + (2 * (a + 5) + 2 * (b + 5) - 3) =
        2 * a * b + 10 * a + 10 * b + 49 := by
      simp
      ring_nf
      omega
    omega
  have hlt : 2 * (a + 5) + 2 * (b + 5) - 3 < (a + 5 - 1) * (b + 5 - 1) := by
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push_neg at h
      apply hne
      omega
    have hL : 2 * (a + 5) + 2 * (b + 5) - 3 = 2 * a + 2 * b + 17 := by omega
    have hR : (a + 5 - 1) * (b + 5 - 1) = (a + 4) * (b + 4) := by simp
    rw [hL, hR]
    have : 2 * a + 2 * b + 17 < (a + 4) * (b + 4) := by
      have hexp : (a + 4) * (b + 4) = a * b + 4 * a + 4 * b + 16 := by ring
      rw [hexp]
      rcases hab with ha | hb
      · have : 1 ≤ a := Nat.pos_of_ne_zero ha
        nlinarith
      · have : 1 ≤ b := Nat.pos_of_ne_zero hb
        nlinarith
    exact this
  unfold totientRem
  rw [hφ, hid, Nat.mul_add_mod_of_lt hlt]

lemma exists_of_two_mul_goldbach {n p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hne : p ≠ q)
    (hsum : p + q = (n + 3) / 2) (hdiv : 2 ∣ n + 3) :
    ∃ x > 0, totientRem x = n := by
  refine ⟨2 * (p * q), mul_pos (by decide : 0 < 2) (mul_pos hp.pos hq.pos), ?_⟩
  have h := totientRem_two_mul_odd_primes hp hq hp5 hq5 hne
  have : 2 * p + 2 * q - 3 = n := by
    have h2 : n + 3 = 2 * ((n + 3) / 2) := (Nat.mul_div_cancel' hdiv).symm
    have h2' : n + 3 = 2 * (p + q) := by
      rw [h2, hsum]
    omega
  rw [h, this]

/-- Even modulo even is even. -/
lemma even_mod_even {a b : ℕ} (ha : Even a) (hb : Even b) (hb0 : 0 < b) : Even (a % b) := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨m, hm⟩ := hb
  have ha2 : a = 2 * k := by omega
  have hb2 : b = 2 * m := by omega
  have hm0 : 0 < m := by omega
  refine ⟨k % m, ?_⟩
  rw [ha2, hb2, Nat.mul_mod_mul_left]
  ring

/-- Odd modulo even is odd. -/
lemma odd_mod_even {a b : ℕ} (ha : Odd a) (hb : Even b) (hb0 : 0 < b) : Odd (a % b) := by
  obtain ⟨k, rfl⟩ := ha
  obtain ⟨m, hm⟩ := hb
  have hb2 : b = 2 * m := by omega
  have hm0 : 0 < m := by omega
  have hdecomp : 2 * k + 1 = (k / m) * (2 * m) + (2 * (k % m) + 1) := by
    have hkm := Nat.div_add_mod k m
    conv_lhs => rw [← hkm]
    ring
  have hlt : 2 * (k % m) + 1 < 2 * m := by
    have := Nat.mod_lt k hm0
    omega
  have hmod : (2 * k + 1) % (2 * m) = 2 * (k % m) + 1 := by
    rw [hdecomp, Nat.mul_add_mod_of_lt hlt]
  rw [hb2, hmod]
  exact ⟨k % m, rfl⟩

/-- `totientRem` of an odd integer `> 1` is even. -/
lemma totientRem_even_of_odd {x : ℕ} (hx : Odd x) (hx1 : 1 < x) : Even (totientRem x) := by
  have hx2 : 2 < x := by
    have : x ≠ 2 := fun h => by
      rw [h] at hx
      exact Nat.not_odd_iff_even.2 even_two hx
    omega
  have hφ : Even x.totient := totient_even hx2
  have hφ0 : 0 < x.totient := totient_pos.mpr (by omega)
  have hx1e : Even (x - 1) := by
    obtain ⟨k, hk⟩ := hx
    have : x = 2 * k + 1 := hk
    have : 1 ≤ x := by omega
    exact ⟨k, by omega⟩
  unfold totientRem
  exact even_mod_even hx1e hφ hφ0

/-- `totientRem` of an even integer `> 2` is odd. -/
lemma totientRem_odd_of_even {x : ℕ} (hx : Even x) (hx2 : 2 < x) : Odd (totientRem x) := by
  have hφ : Even x.totient := totient_even hx2
  have hφ0 : 0 < x.totient := totient_pos.mpr (by omega)
  have hx1o : Odd (x - 1) := by
    obtain ⟨k, hk⟩ := hx
    have : 1 ≤ x := by omega
    refine ⟨k - 1, ?_⟩
    omega
  unfold totientRem
  exact odd_mod_even hx1o hφ hφ0

/-- An odd value of `totientRem` can only arise from even `x`. -/
lemma even_of_totientRem_odd {x : ℕ} (hx0 : 0 < x) (h : Odd (totientRem x)) : Even x := by
  by_contra hxodd
  have hxodd' : Odd x := not_even_iff_odd.1 hxodd
  have : x = 1 ∨ 1 < x := by omega
  rcases this with rfl | hx1
  · have : totientRem 1 = 0 := totientRem_one
    rw [this] at h
    exact Nat.not_odd_zero h
  · have he : Even (totientRem x) := totientRem_even_of_odd hxodd' hx1
    exact Nat.not_odd_iff_even.2 he h

/-- `x = 27p` realizes `n = 9p + 17` for primes `p ≥ 5`. -/
lemma totientRem_twentyseven_mul_prime {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    totientRem (27 * p) = 9 * p + 17 := by
  have hP3 : Nat.Prime 3 := by decide
  have h3 : p ≠ 3 := by omega
  have hcop : (27 : ℕ).Coprime p := by
    have h27 : (27 : ℕ) = 3 ^ 3 := by decide
    rw [h27, Nat.coprime_pow_left_iff (by decide : 0 < 3)]
    exact hP3.coprime_iff_not_dvd.2 fun hdvd =>
      h3 ((hp.dvd_iff_eq hP3.ne_one).1 hdvd)
  have hφ : (27 * p).totient = 18 * (p - 1) := by
    rw [totient_mul hcop, show (27 : ℕ).totient = 18 from by decide, totient_prime hp]
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hp5
  have hid : 27 * (a + 5) - 1 = 18 * (a + 5 - 1) + (9 * (a + 5) + 17) := by
    simp; ring_nf; omega
  have hlt : 9 * (a + 5) + 17 < 18 * (a + 5 - 1) := by
    simp; omega
  unfold totientRem
  rw [hφ, hid, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]

lemma exists_of_twentyseven_mul_prime {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : n = 9 * p + 17) :
    ∃ x > 0, totientRem x = n := by
  refine ⟨27 * p, mul_pos (by decide : 0 < 27) hp.pos, ?_⟩
  rw [totientRem_twentyseven_mul_prime hp hp5, hn]

/-- Try a 2-Goldbach partner `r` for odd `n`. -/
lemma exists_of_two_mul_goldbach_prime {n r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hdiv : 2 ∣ n + 3)
    (hq5 : 5 ≤ (n + 3) / 2 - r) (hq : ((n + 3) / 2 - r).Prime)
    (hne : r ≠ (n + 3) / 2 - r) :
    ∃ x > 0, totientRem x = n := by
  have hsum : r + ((n + 3) / 2 - r) = (n + 3) / 2 := by omega
  exact exists_of_two_mul_goldbach hr hq hr5 hq5 hne hsum hdiv


/-- Distinct-odd-prime Goldbach data for an even integer. -/
def IsGoldbach (N : ℕ) : Prop :=
  ∃ p < N, p.Prime ∧ (N - p).Prime ∧ p ≠ N - p

instance (N : ℕ) : Decidable (IsGoldbach N) := by
  unfold IsGoldbach
  infer_instance

lemma odd_prime_ne_two {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : 3 ≤ p := by
  have := hp.two_le
  omega

lemma not_prime_four : ¬ Nat.Prime 4 := by decide

lemma goldbach_wrap {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hne : p ≠ q) :
    1 < (p - 2) * (q - 2) := by
  have hp3 : 3 ≤ p := odd_prime_ne_two hp hp2
  have hq3 : 3 ≤ q := odd_prime_ne_two hq hq2
  have hp1 : 1 ≤ p - 2 := by omega
  have hq1 : 1 ≤ q - 2 := by omega
  have h2 : 3 ≤ p - 2 ∨ 3 ≤ q - 2 := by
    by_contra h
    push_neg at h
    have hp34 : p = 3 ∨ p = 4 := by omega
    have hq34 : q = 3 ∨ q = 4 := by omega
    have hp_eq : p = 3 := by
      rcases hp34 with rfl | rfl
      · rfl
      · cases not_prime_four hp
    have hq_eq : q = 3 := by
      rcases hq34 with rfl | rfl
      · rfl
      · cases not_prime_four hq
    exact hne (hp_eq.trans hq_eq.symm)
  rcases h2 with hp5 | hq5
  · have : 3 * 1 ≤ (p - 2) * (q - 2) := Nat.mul_le_mul hp5 hq1
    omega
  · have : 1 * 3 ≤ (p - 2) * (q - 2) := Nat.mul_le_mul hp1 hq5
    omega

lemma exists_of_IsGoldbach {n : ℕ} (hn6 : 6 ≤ n) (hen : Even n)
    (hG : IsGoldbach (n + 2)) :
    ∃ x > 0, totientRem x = n := by
  obtain ⟨p, hpN, hp, hq, hne⟩ := hG
  have hp2 : p ≠ 2 := by
    intro h
    subst h
    have hnP : n.Prime := by simpa using hq
    have : n = 2 := hnP.even_iff.mp hen
    omega
  have hq2 : n + 2 - p ≠ 2 := by
    intro h
    have hpn : p = n := by omega
    have hnP : n.Prime := by simpa [hpn] using hp
    have : n = 2 := hnP.even_iff.mp hen
    omega
  have hwrap := goldbach_wrap hp hq hp2 hq2 hne
  exact exists_of_goldbach_prime hp hq (by omega) hne (by simpa using hwrap)

set_option maxRecDepth 10000000
set_option maxHeartbeats 40000000

lemma IsGoldbach_of_le_four_hundred {N : ℕ} (hE : Even N) (h8 : 8 ≤ N) (hN : N ≤ 400) :
    IsGoldbach N := by
  revert hE h8
  interval_cases N <;> first | omega | decide

/-- A Goldbach partner `p` with `2 * p < N` is automatically distinct from `N - p`. -/
lemma IsGoldbach.of_partner {N p : ℕ} (hpN : p < N) (hp : p.Prime) (hq : (N - p).Prime)
    (h2p : 2 * p < N) : IsGoldbach N :=
  ⟨p, hpN, hp, hq, by omega⟩

def IsGoldbachGeFive (N : ℕ) : Prop :=
  ∃ p < N, p.Prime ∧ 5 ≤ p ∧ (N - p).Prime ∧ 5 ≤ N - p ∧ p ≠ N - p

instance (N : ℕ) : Decidable (IsGoldbachGeFive N) := by
  unfold IsGoldbachGeFive
  infer_instance

lemma IsGoldbachGeFive_of_le_four_hundred {N : ℕ} (hE : Even N) (h16 : 16 ≤ N)
    (hN : N ≤ 400) : IsGoldbachGeFive N := by
  revert hE h16
  interval_cases N <;> first | omega | decide

/-- Even Goldbach with both primes at least `5`. This is the only remaining
input to `exists_totientRem`: every even `n ≥ 6` is `totientRem (p * q)` for a
Goldbach pair of `n + 2`, and every odd `n ≡ 1 (mod 4)` is `totientRem (2 * p * q)`
for a Goldbach pair of `(n + 3) / 2`. -/
lemma exists_goldbach_sum_ge_five {N : ℕ} (hE : Even N) (h16 : 16 ≤ N) :
    IsGoldbachGeFive N := by
  by_cases h400 : N ≤ 400
  · exact IsGoldbachGeFive_of_le_four_hundred hE h16 h400
  have h401 : 401 ≤ N := by omega
  by_cases h5 : (N - 5).Prime
  · have : 5 ≠ N - 5 := by omega
    exact ⟨5, by omega, by decide, by omega, h5, by omega, this⟩
  by_cases h7 : (N - 7).Prime
  · exact ⟨7, by omega, by decide, by omega, h7, by omega, by omega⟩
  by_cases h11 : (N - 11).Prime
  · exact ⟨11, by omega, by decide, by omega, h11, by omega, by omega⟩
  by_cases h13 : (N - 13).Prime
  · exact ⟨13, by omega, by decide, by omega, h13, by omega, by omega⟩
  by_cases h17 : (N - 17).Prime
  · exact ⟨17, by omega, by decide, by omega, h17, by omega, by omega⟩
  by_cases h19 : (N - 19).Prime
  · exact ⟨19, by omega, by decide, by omega, h19, by omega, by omega⟩
  by_cases h23 : (N - 23).Prime
  · exact ⟨23, by omega, by decide, by omega, h23, by omega, by omega⟩
  by_cases h29 : (N - 29).Prime
  · exact ⟨29, by omega, by decide, by omega, h29, by omega, by omega⟩
  by_cases h31 : (N - 31).Prime
  · exact ⟨31, by omega, by decide, by omega, h31, by omega, by omega⟩
  by_cases h37 : (N - 37).Prime
  · exact ⟨37, by omega, by decide, by omega, h37, by omega, by omega⟩
  by_cases h41 : (N - 41).Prime
  · exact ⟨41, by omega, by decide, by omega, h41, by omega, by omega⟩
  by_cases h43 : (N - 43).Prime
  · exact ⟨43, by omega, by decide, by omega, h43, by omega, by omega⟩
  by_cases h47 : (N - 47).Prime
  · exact ⟨47, by omega, by decide, by omega, h47, by omega, by omega⟩
  by_cases h53 : (N - 53).Prime
  · exact ⟨53, by omega, by decide, by omega, h53, by omega, by omega⟩
  by_cases h59 : (N - 59).Prime
  · exact ⟨59, by omega, by decide, by omega, h59, by omega, by omega⟩
  by_cases h61 : (N - 61).Prime
  · exact ⟨61, by omega, by decide, by omega, h61, by omega, by omega⟩
  by_cases h67 : (N - 67).Prime
  · exact ⟨67, by omega, by decide, by omega, h67, by omega, by omega⟩
  by_cases h71 : (N - 71).Prime
  · exact ⟨71, by omega, by decide, by omega, h71, by omega, by omega⟩
  by_cases h73 : (N - 73).Prime
  · exact ⟨73, by omega, by decide, by omega, h73, by omega, by omega⟩
  by_cases h79 : (N - 79).Prime
  · exact ⟨79, by omega, by decide, by omega, h79, by omega, by omega⟩
  by_cases h83 : (N - 83).Prime
  · exact ⟨83, by omega, by decide, by omega, h83, by omega, by omega⟩
  by_cases h89 : (N - 89).Prime
  · exact ⟨89, by omega, by decide, by omega, h89, by omega, by omega⟩
  by_cases h97 : (N - 97).Prime
  · exact ⟨97, by omega, by decide, by omega, h97, by omega, by omega⟩
  by_cases h101 : (N - 101).Prime
  · exact ⟨101, by omega, by decide, by omega, h101, by omega, by omega⟩
  by_cases h103 : (N - 103).Prime
  · exact ⟨103, by omega, by decide, by omega, h103, by omega, by omega⟩
  by_cases h107 : (N - 107).Prime
  · exact ⟨107, by omega, by decide, by omega, h107, by omega, by omega⟩
  by_cases h109 : (N - 109).Prime
  · exact ⟨109, by omega, by decide, by omega, h109, by omega, by omega⟩
  by_cases h113 : (N - 113).Prime
  · exact ⟨113, by omega, by decide, by omega, h113, by omega, by omega⟩
  by_cases h127 : (N - 127).Prime
  · exact ⟨127, by omega, by decide, by omega, h127, by omega, by omega⟩
  by_cases h131 : (N - 131).Prime
  · exact ⟨131, by omega, by decide, by omega, h131, by omega, by omega⟩
  by_cases h137 : (N - 137).Prime
  · exact ⟨137, by omega, by decide, by omega, h137, by omega, by omega⟩
  by_cases h139 : (N - 139).Prime
  · exact ⟨139, by omega, by decide, by omega, h139, by omega, by omega⟩
  by_cases h149 : (N - 149).Prime
  · exact ⟨149, by omega, by decide, by omega, h149, by omega, by omega⟩
  by_cases h151 : (N - 151).Prime
  · exact ⟨151, by omega, by decide, by omega, h151, by omega, by omega⟩
  by_cases h157 : (N - 157).Prime
  · exact ⟨157, by omega, by decide, by omega, h157, by omega, by omega⟩
  by_cases h163 : (N - 163).Prime
  · exact ⟨163, by omega, by decide, by omega, h163, by omega, by omega⟩
  by_cases h167 : (N - 167).Prime
  · exact ⟨167, by omega, by decide, by omega, h167, by omega, by omega⟩
  by_cases h173 : (N - 173).Prime
  · exact ⟨173, by omega, by decide, by omega, h173, by omega, by omega⟩
  by_cases h179 : (N - 179).Prime
  · exact ⟨179, by omega, by decide, by omega, h179, by omega, by omega⟩
  by_cases h181 : (N - 181).Prime
  · exact ⟨181, by omega, by decide, by omega, h181, by omega, by omega⟩
  by_cases h191 : (N - 191).Prime
  · exact ⟨191, by omega, by decide, by omega, h191, by omega, by omega⟩
  by_cases h193 : (N - 193).Prime
  · exact ⟨193, by omega, by decide, by omega, h193, by omega, by omega⟩
  by_cases h197 : (N - 197).Prime
  · exact ⟨197, by omega, by decide, by omega, h197, by omega, by omega⟩
  by_cases h199 : (N - 199).Prime
  · exact ⟨199, by omega, by decide, by omega, h199, by omega, by omega⟩
  -- Remaining even `N` have `N-p` composite for every prime `5 ≤ p ≤ 199`.
  --
  -- This tail is the binary Goldbach conjecture (every even integer `≥ 16`
  -- is a sum of two distinct primes `≥ 5`). Known-factorization families
  -- cannot replace it:
  -- * 0-free (`rad(x) ⊆ primes(n+1)`): finitely many `x` per `n`, empty
  --   for leftovers such as `n = 1272` (`x = 19^a 67^b`).
  -- * 1-free (`x = m p`): `p` is determined except when `m = 2^a 3^b`,
  --   which gives constant rem `m-1` (and requires even `x`, hence odd `n`).
  --   Dirichlet cannot free a determined prime.
  -- * 2-free factorization (`(p+c)(q+c) = n+d`): fails when `n+d` is prime
  --   (Dirichlet produces infinitely many such `n` in every AP).
  -- * Chen `N = p+qr` does not invert: no monomial identity equals `p+qr-2`.
  -- Even `n` forces odd `x`, so the constant-rem family is unavailable.
  -- Thus every even leftover of a finite union of thin families still
  -- requires a Goldbach product (or an equally hard 2-prime condition).
  sorry

lemma isGoldbach_of_ge_five {N : ℕ} (h : IsGoldbachGeFive N) : IsGoldbach N := by
  obtain ⟨p, hpN, hp, _, hq, _, hne⟩ := h
  exact ⟨p, hpN, hp, hq, hne⟩

lemma exists_goldbach_sum {N : ℕ} (hE : Even N) (h8 : 8 ≤ N) :
    IsGoldbach N := by
  by_cases h400 : N ≤ 400
  · exact IsGoldbach_of_le_four_hundred hE h8 h400
  have h16 : 16 ≤ N := by omega
  exact isGoldbach_of_ge_five (exists_goldbach_sum_ge_five hE h16)

lemma exists_totientRem_of_lt_twenty {n : ℕ} (hn : n < 20) :
    ∃ x > 0, totientRem x = n := by
  interval_cases n
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨4, by decide, by decide⟩
  · exact ⟨9, by decide, by decide⟩
  · exact ⟨8, by decide, by decide⟩
  · exact ⟨25, by decide, by decide⟩
  · exact ⟨18, by decide, by decide⟩
  · exact ⟨15, by decide, by decide⟩
  · exact ⟨16, by decide, by decide⟩
  · exact ⟨21, by decide, by decide⟩
  · exact ⟨50, by decide, by decide⟩
  · exact ⟨35, by decide, by decide⟩
  · exact ⟨36, by decide, by decide⟩
  · exact ⟨33, by decide, by decide⟩
  · exact ⟨98, by decide, by decide⟩
  · exact ⟨39, by decide, by decide⟩
  · exact ⟨32, by decide, by decide⟩
  · exact ⟨65, by decide, by decide⟩
  · exact ⟨54, by decide, by decide⟩
  · exact ⟨51, by decide, by decide⟩
  · exact ⟨100, by decide, by decide⟩

/-- Existence form of the conjecture, proved by strong induction. -/
lemma exists_totientRem : ∀ n, ∃ x > 0, totientRem x = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h20 : n < 20
    · exact exists_totientRem_of_lt_twenty h20
    have hn20 : 20 ≤ n := Nat.le_of_not_lt h20
    by_cases h0 : n = 0
    · subst h0; exact ⟨1, one_pos, totientRem_one⟩
    by_cases hpp : IsPrimePow (n + 1)
    · obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff (n + 1)).1 hpp
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      exact exists_of_succ_prime_pow (hp := hp) (hn := hpk.symm)
    by_cases hn1 : n = 1
    · subst hn1
      refine ⟨4, by decide, ?_⟩
      unfold totientRem
      decide
    by_cases hodd : Odd n
    · obtain ⟨m, hm⟩ := hodd
      have hm_lt : m < n := by omega
      obtain ⟨x, hx0, hx⟩ := ih m hm_lt
      by_cases hxeven : Even x
      · have hx2 : 2 ≤ x := by
          match x with
          | 0 => exact (Nat.lt_irrefl 0 hx0).elim
          | 1 => cases Nat.not_even_one hxeven
          | x + 2 => omega
        refine ⟨2 * x, mul_pos (by decide : 0 < 2) hx0, ?_⟩
        rw [totientRem_two_mul_of_even hxeven hx2, hx, hm]
      · have hxodd : Odd x := not_even_iff_odd.1 hxeven
        -- Odd witness of `m` forces `m` even, hence `n ≡ 1 (mod 4)`.
        have hm_even : Even m := by
          by_contra hmo
          have : Odd m := not_even_iff_odd.1 hmo
          have : Even x := even_of_totientRem_odd hx0 (by rw [hx]; exact this)
          exact hxeven this
        by_cases hφ : 2 * totientRem x + 1 < x.totient
        · refine ⟨2 * x, mul_pos (by decide : 0 < 2) hx0, ?_⟩
          rw [totientRem_two_mul_of_odd hxodd hφ, hx, hm]
        · let a := (n + 1).factorization 2
          let M := ordCompl[2] (n + 1)
          have hdecomp : 2 ^ a * M = n + 1 := ordProj_mul_ordCompl_eq_self (n + 1) 2
          have ha : 0 < a := by
            have heven : Even (n + 1) := ⟨m + 1, by omega⟩
            have h2 : 2 ∣ n + 1 := even_iff_two_dvd.mp heven
            have hn1 : n + 1 ≠ 0 := Nat.succ_ne_zero n
            exact Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hn1 |>.mp h2
          have hModd : Odd M := by
            have hn1 : n + 1 ≠ 0 := Nat.succ_ne_zero n
            have hnd : ¬ 2 ∣ M := not_dvd_ordCompl Nat.prime_two hn1
            exact not_even_iff_odd.1 (mt even_iff_two_dvd.mp hnd)
          by_cases hMpp : IsPrimePow M
          · obtain ⟨p, b, hp, hb, hpb⟩ := (isPrimePow_nat_iff M).1 hMpp
            have hodd_p : Odd p := by
              have : p ∣ M := by
                rw [← hpb]
                exact dvd_pow_self p hb.ne'
              exact Odd.of_dvd_nat hModd this
            have hn' : n + 1 = 2 ^ a * p ^ b := by
              rw [← hdecomp, hpb]
            exact exists_of_two_pow_mul_prime_pow hp hodd_p ha hn'
          · -- `n ≡ 1 (mod 4)` leftover: try `x = 2pq` from Goldbach of `(n+3)/2`.
            have hdiv : 2 ∣ n + 3 := by
              refine ⟨m + 2, ?_⟩
              rw [hm]; ring
            by_cases h5 : 5 ≤ (n + 3) / 2 - 5 ∧ ((n + 3) / 2 - 5).Prime ∧
                (5 : ℕ) ≠ (n + 3) / 2 - 5
            · obtain ⟨hp5, hq, hne⟩ := h5
              have h5p : Nat.Prime 5 := by decide
              have hsum : (5 : ℕ) + ((n + 3) / 2 - 5) = (n + 3) / 2 := by
                have : 5 ≤ (n + 3) / 2 := by omega
                omega
              exact exists_of_two_mul_goldbach h5p hq (le_rfl) hp5 hne hsum hdiv
            by_cases h7 : 5 ≤ (n + 3) / 2 - 7 ∧ ((n + 3) / 2 - 7).Prime ∧
                (7 : ℕ) ≠ (n + 3) / 2 - 7
            · obtain ⟨hq5, hq, hne⟩ := h7
              exact exists_of_two_mul_goldbach_prime (by decide : Nat.Prime 7) (by decide)
                hdiv hq5 hq hne
            by_cases h11 : 5 ≤ (n + 3) / 2 - 11 ∧ ((n + 3) / 2 - 11).Prime ∧
                (11 : ℕ) ≠ (n + 3) / 2 - 11
            · obtain ⟨hq5, hq, hne⟩ := h11
              exact exists_of_two_mul_goldbach_prime (by decide : Nat.Prime 11) (by decide)
                hdiv hq5 hq hne
            by_cases h13 : 5 ≤ (n + 3) / 2 - 13 ∧ ((n + 3) / 2 - 13).Prime ∧
                (13 : ℕ) ≠ (n + 3) / 2 - 13
            · obtain ⟨hq5, hq, hne⟩ := h13
              exact exists_of_two_mul_goldbach_prime (by decide : Nat.Prime 13) (by decide)
                hdiv hq5 hq hne
            by_cases h17 : 5 ≤ (n + 3) / 2 - 17 ∧ ((n + 3) / 2 - 17).Prime ∧
                (17 : ℕ) ≠ (n + 3) / 2 - 17
            · obtain ⟨hq5, hq, hne⟩ := h17
              exact exists_of_two_mul_goldbach_prime (by decide : Nat.Prime 17) (by decide)
                hdiv hq5 hq hne
            by_cases h19 : 5 ≤ (n + 3) / 2 - 19 ∧ ((n + 3) / 2 - 19).Prime ∧
                (19 : ℕ) ≠ (n + 3) / 2 - 19
            · obtain ⟨hq5, hq, hne⟩ := h19
              exact exists_of_two_mul_goldbach_prime (by decide : Nat.Prime 19) (by decide)
                hdiv hq5 hq hne
            · -- Remaining `n ≡ 1 (mod 4)`: Goldbach of `(n+3)/2` with both primes ≥ 5.
              have hm2 : n + 3 = 2 * (m + 2) := by
                rw [hm]; ring
              have hNeq : (n + 3) / 2 = m + 2 := by omega
              have hN : Even ((n + 3) / 2) := by
                rw [hNeq]
                obtain ⟨k, hk⟩ := hm_even
                refine ⟨k + 1, ?_⟩
                rw [hk]
                ring
              have h16 : 16 ≤ (n + 3) / 2 := by
                by_contra hlt
                have hNlt : (n + 3) / 2 < 16 := Nat.not_le.mp hlt
                -- Then `n < 29`. Combined with `n ≥ 20`, `n` odd and `n ≡ 1 (mod 4)`,
                -- we get `n = 21` or `n = 25`, both of which have `M` a prime power.
                have hn29 : n < 29 := by omega
                have hcases : n = 21 ∨ n = 25 := by
                  obtain ⟨k, hk⟩ := hm_even
                  omega
                have hMpp' : IsPrimePow M := by
                  rcases hcases with rfl | rfl
                  · -- n=21, n+1=22=2*11
                    have hM : M = 11 := by
                      have hdecomp' : 2 ^ a * M = 22 := by simpa using hdecomp
                      have ha1 : a = 1 := by
                        have h12 : a = 1 ∨ 2 ≤ a := by omega
                        rcases h12 with h | h
                        · exact h
                        · have : 4 ∣ 2 ^ a := Nat.pow_dvd_pow 2 h
                          have : 4 ∣ 22 := by
                            rw [← hdecomp']
                            exact dvd_mul_of_dvd_left this M
                          exact absurd this (by decide)
                      rw [ha1, pow_one] at hdecomp'
                      omega
                    rw [hM]
                    exact (isPrimePow_nat_iff 11).2 ⟨11, 1, by decide, by decide, by decide⟩
                  · -- n=25, n+1=26=2*13
                    have hM : M = 13 := by
                      have hdecomp' : 2 ^ a * M = 26 := by simpa using hdecomp
                      have ha1 : a = 1 := by
                        have h12 : a = 1 ∨ 2 ≤ a := by omega
                        rcases h12 with h | h
                        · exact h
                        · have : 4 ∣ 2 ^ a := Nat.pow_dvd_pow 2 h
                          have : 4 ∣ 26 := by
                            rw [← hdecomp']
                            exact dvd_mul_of_dvd_left this M
                          exact absurd this (by decide)
                      rw [ha1, pow_one] at hdecomp'
                      omega
                    rw [hM]
                    exact (isPrimePow_nat_iff 13).2 ⟨13, 1, by decide, by decide, by decide⟩
                exact hMpp hMpp'
              have hG := exists_goldbach_sum_ge_five hN h16
              obtain ⟨p, hpN, hp, hp5, hq, hq5, hne⟩ := hG
              exact exists_of_two_mul_goldbach_prime hp hp5 hdiv hq5 hq hne
    · -- Even `n > 0`, `n+1` not a prime power.
      have heven : Even n := not_odd_iff_even.1 hodd
      have hn6 : 6 ≤ n := by
        by_contra hlt
        obtain ⟨k, hk⟩ := heven
        have : n = 2 ∨ n = 4 := by omega
        rcases this with rfl | rfl
        · exact hpp ((isPrimePow_nat_iff _).2 ⟨3, 1, by decide, by decide, rfl⟩)
        · exact hpp ((isPrimePow_nat_iff _).2 ⟨5, 1, by decide, by decide, rfl⟩)
      by_cases h3 : (n - 1).Prime
      · exact exists_of_three_goldbach hn6 h3
      by_cases h5 : (n - 3).Prime
      · have hn10 : 10 ≤ n := by
          by_contra hlt
          obtain ⟨k, hk⟩ := heven
          have : n = 6 ∨ n = 8 := by omega
          rcases this with rfl | rfl
          · exact hpp ((isPrimePow_nat_iff _).2 ⟨7, 1, by decide, by decide, rfl⟩)
          · exact hpp ((isPrimePow_nat_iff _).2 ⟨3, 2, by decide, by decide, rfl⟩)
        exact exists_of_five_goldbach hn10 h5
      by_cases h7 : (n - 5).Prime
      · have hn14 : 14 ≤ n := by
          by_contra hlt
          obtain ⟨k, hk⟩ := heven
          have : n = 6 ∨ n = 8 ∨ n = 10 ∨ n = 12 := by omega
          rcases this with rfl | rfl | rfl | rfl
          · exact hpp ((isPrimePow_nat_iff _).2 ⟨7, 1, by decide, by decide, rfl⟩)
          · exact hpp ((isPrimePow_nat_iff _).2 ⟨3, 2, by decide, by decide, rfl⟩)
          · exact hpp ((isPrimePow_nat_iff _).2 ⟨11, 1, by decide, by decide, rfl⟩)
          · exact hpp ((isPrimePow_nat_iff _).2 ⟨13, 1, by decide, by decide, rfl⟩)
        exact exists_of_seven_goldbach hn14 h7
      · have hn22 : 22 ≤ n := by
          by_contra hlt
          obtain ⟨k, hk⟩ := heven
          have : n = 6 ∨ n = 8 ∨ n = 10 ∨ n = 12 ∨ n = 14 ∨ n = 16 ∨ n = 18 ∨ n = 20 :=
            by omega
          rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hpp ((isPrimePow_nat_iff _).2 ⟨7, 1, by decide, by decide, rfl⟩)
          · exact hpp ((isPrimePow_nat_iff _).2 ⟨3, 2, by decide, by decide, rfl⟩)
          · exact hpp ((isPrimePow_nat_iff _).2 ⟨11, 1, by decide, by decide, rfl⟩)
          · exact hpp ((isPrimePow_nat_iff _).2 ⟨13, 1, by decide, by decide, rfl⟩)
          · exact h5 (by decide)
          · exact h5 (by decide)
          · exact h3 (by decide)
          · exact h3 (by decide)
        by_cases h11 : (n - 9).Prime
        · exact exists_of_eleven_goldbach hn22 h11
        by_cases h13 : (n - 11).Prime
        · have hn26 : 26 ≤ n := by
            by_contra hlt
            obtain ⟨k, hk⟩ := heven
            have : n = 22 ∨ n = 24 := by omega
            rcases this with rfl | rfl
            · exact h5 (by decide)
            · exact h3 (by decide)
          exact exists_of_thirteen_goldbach hn26 h13
        by_cases h17 : (n - 15).Prime
        · have hn34 : 34 ≤ n := by
            by_contra hlt
            obtain ⟨k, hk⟩ := heven
            have : n = 22 ∨ n = 24 ∨ n = 26 ∨ n = 28 ∨ n = 30 ∨ n = 32 := by omega
            rcases this with rfl | rfl | rfl | rfl | rfl | rfl
            · exact h5 (by decide)
            · exact h3 (by decide)
            · exact h5 (by decide)
            · exact h7 (by decide)
            · exact h3 (by decide)
            · exact h3 (by decide)
          exact exists_of_seventeen_goldbach hn34 h17
        by_cases h19 : (n - 17).Prime
        · have hn38 : 38 ≤ n := by
            by_contra hlt
            obtain ⟨k, hk⟩ := heven
            have : n = 22 ∨ n = 24 ∨ n = 26 ∨ n = 28 ∨ n = 30 ∨ n = 32 ∨
                   n = 34 ∨ n = 36 := by omega
            rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact h5 (by decide)
            · exact h3 (by decide)
            · exact h5 (by decide)
            · exact h7 (by decide)
            · exact h3 (by decide)
            · exact h3 (by decide)
            · exact h5 (by decide)
            · exact h7 (by decide)
          exact exists_of_nineteen_goldbach hn38 h19
        -- If a prime factor of `n+1` is a Goldbach partner of `n+2`, we are done.
        by_cases hfacGB : ∃ p : ℕ, p.Prime ∧ p ∣ n + 1 ∧ p < n + 2 ∧
            (n + 2 - p).Prime ∧ p ≠ n + 2 - p
        · obtain ⟨p, hp, hpdvd, hpN, hq, hne⟩ := hfacGB
          have hp2 : p ≠ 2 := by
            intro h
            subst h
            have hEven : Even (n + 1) := even_iff_two_dvd.mpr hpdvd
            have hOdd : Odd (n + 1) := heven.add_one
            exact Nat.not_odd_iff_even.2 hEven hOdd
          have hq2 : n + 2 - p ≠ 2 := by
            intro h
            have : p = n := by omega
            have hnP : n.Prime := by simpa [this] using hp
            have : n = 2 := hnP.even_iff.mp heven
            omega
          have hwrap := goldbach_wrap hp hq hp2 hq2 hne
          exact exists_of_goldbach_prime hp hq (by omega) hne (by simpa using hwrap)
        by_cases h9p : 3 ∣ (n - 5) ∧ 5 ≤ (n - 5) / 3 ∧ ((n - 5) / 3).Prime
        · obtain ⟨hdvd, hp5, hp⟩ := h9p
          have hn5 : n = 3 * ((n - 5) / 3) + 5 := by
            have : n - 5 = 3 * ((n - 5) / 3) := (Nat.mul_div_cancel' hdvd).symm
            omega
          exact exists_of_nine_mul_prime hp hp5 hn5
        by_cases h21p : 9 ∣ (n - 11) ∧ 7 < (n - 11) / 9 ∧ ((n - 11) / 9).Prime
        · obtain ⟨hdvd, hp7, hp⟩ := h21p
          have hn11 : n = 9 * ((n - 11) / 9) + 11 := by
            have : n - 11 = 9 * ((n - 11) / 9) := (Nat.mul_div_cancel' hdvd).symm
            omega
          exact exists_of_twentyone_mul_prime hp hp7 hn11
        by_cases h27p : 9 ∣ (n - 17) ∧ 5 ≤ (n - 17) / 9 ∧ ((n - 17) / 9).Prime
        · obtain ⟨hdvd, hp5, hp⟩ := h27p
          have hn17 : n = 9 * ((n - 17) / 9) + 17 := by
            have : n - 17 = 9 * ((n - 17) / 9) := (Nat.mul_div_cancel' hdvd).symm
            omega
          exact exists_of_twentyseven_mul_prime hp hp5 hn17
        by_cases h15p : 7 ∣ n ∧ 17 ≤ n / 7 - 1 ∧ (n / 7 - 1).Prime
        · obtain ⟨hdvd, hp17, hp⟩ := h15p
          have hn7 : n = 7 * ((n / 7 - 1) + 1) := by
            have : n = 7 * (n / 7) := (Nat.mul_div_cancel' hdvd).symm
            omega
          exact exists_of_fifteen_mul_prime hp hp17 hn7
        by_cases hp2q : ∃ p : ℕ, p.Prime ∧ p ∣ n + 1 ∧
            ((n + 1) / p + 1 - p).Prime ∧ p ≠ (n + 1) / p + 1 - p ∧
            p * ((n + 1) / p) - 1 < p * (p - 1) * ((n + 1) / p + 1 - p - 1)
        · obtain ⟨p, hp, hpd, hq, hne, hwrap⟩ := hp2q
          exact exists_of_p2q_of_factor hp hpd hq hne hwrap
        by_cases h3pq : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 7 ≤ p ∧ 7 ≤ q ∧ p ≠ q ∧
            (p + 2) * (q + 2) = n + 7
        · obtain ⟨p, q, hp, hq, hp7, hq7, hne, hfac⟩ := h3pq
          exact exists_of_three_mul_two_primes hp hq hp7 hq7 hne hfac
        by_cases h5pq : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 7 ≤ p ∧ 7 ≤ q ∧ p ≠ q ∧
            (p + 4) * (q + 4) = n + 21
        · obtain ⟨p, q, hp, hq, hp7, hq7, hne, hfac⟩ := h5pq
          exact exists_of_five_mul_two_primes hp hq hp7 hq7 hne hfac
        by_cases hrpq : ∃ r p q : ℕ, r.Prime ∧ p.Prime ∧ q.Prime ∧
            3 ≤ r ∧ 7 ≤ p ∧ 7 ≤ q ∧ r ≠ p ∧ r ≠ q ∧ p ≠ q ∧
            (p + r - 1) * (q + r - 1) = n + r * (r - 1) + 1
        · obtain ⟨r, p, q, hr, hp, hq, hr3, hp7, hq7, hrp, hrq, hpq, hfac⟩ := hrpq
          exact exists_of_prime_mul_two_primes hr hp hq hr3 hp7 hq7 hrp hrq hpq hfac
        · -- Remaining even `n`: invoke Goldbach of `n+2`.
          have hG : IsGoldbach (n + 2) :=
            exists_goldbach_sum (heven.add even_two) (by omega)
          exact exists_of_IsGoldbach hn6 heven hG

/--
A268597 Conjecture: a(n) > 0 for all n.
-/
theorem oeis_268597_conjecture_0 (n : ℕ) : A268597 n > 0 := by
  obtain ⟨x, hx0, hx⟩ := exists_totientRem n
  exact A268597_pos_of_exists hx0 hx
