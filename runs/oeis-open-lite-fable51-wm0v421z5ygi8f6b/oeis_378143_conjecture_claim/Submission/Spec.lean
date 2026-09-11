import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A378143: $a(n)$ is the smallest prime of the form $(2p)^{2^n} + 1$ for some prime $p$.
-/
noncomputable def A378143 (n : ℕ) : ℕ :=
  sInf { k : ℕ | Nat.Prime k ∧ ∃ p : ℕ, Nat.Prime p ∧ k = (2 * p) ^ (2 ^ n) + 1 }

/-! ### Verified partial results

The conjecture below is not settled here; it is equivalent to an open problem on
generalized Fermat numbers in base 10.  The following auxiliary development proves the
provable fragments: the cases `n = 0, 1`, compositeness of `10^(2^n)+1` for
`2 ≤ n ≤ 20` and `n ∈ {22, 26, 28, 29, 30, 35}` (kernel-checked certificates), the
resulting reduction of the conjecture to `n ≥ 21`, and the impossibility of a covering set.
-/

set_option exponentiation.threshold 2000000
set_option maxRecDepth 100000

open Nat

namespace FermatWitness

/-- `force n f = f n`, but evaluating it makes the kernel reduce `n` to a literal first
(via `Nat.casesOn`), so that `f` receives a literal rather than an unevaluated thunk. -/
def force (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  match n with
  | 0 => f 0
  | k + 1 => f (k + 1)

theorem force_eq (n : ℕ) (f : ℕ → ℕ) : force n f = f n := by
  cases n <;> rfl

/-- One step of binary exponentiation, with forced evaluation of the new state. -/
def step (m : ℕ) (ih : ℕ → ℕ → ℕ → ℕ) (a e acc : ℕ) : ℕ :=
  force (a * a % m) fun a' =>
  force (if e % 2 = 1 then acc * a % m else acc % m) fun acc' =>
  force (e / 2) fun e' =>
  ih a' e' acc'

/-- Tail-recursive binary modular exponentiation via `Nat.rec`:
`loop m fuel a e acc = acc * a^e % m`. -/
def loop (m fuel : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc % m)
    (fun _ ih => step m ih) fuel

theorem loop_zero (m a e acc : ℕ) : loop m 0 a e acc = acc % m := rfl

theorem loop_succ (m k a e acc : ℕ) : loop m (k + 1) a e acc = step m (loop m k) a e acc := rfl

theorem loop_spec (m : ℕ) :
    ∀ fuel a e acc, e < 2 ^ fuel → loop m fuel a e acc = acc * a ^ e % m := by
  intro fuel
  induction fuel with
  | zero =>
    intro a e acc he
    simp at he; subst he; simp [loop_zero]
  | succ k ih =>
    intro a e acc he
    rw [loop_succ]
    simp only [step, force_eq]
    have he2 : e / 2 < 2 ^ k := by rw [pow_succ] at he; omega
    rw [ih _ _ _ he2]
    split_ifs with h1
    · obtain ⟨d, rfl⟩ : ∃ d, e = 2 * d + 1 := ⟨e / 2, by omega⟩
      have hd : (2 * d + 1) / 2 = d := by omega
      rw [hd, Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod, Nat.mod_mul_mod, pow_succ, pow_mul, sq]
      ring_nf
    · obtain ⟨d, rfl⟩ : ∃ d, e = 2 * d := ⟨e / 2, by omega⟩
      have hd : (2 * d) / 2 = d := by omega
      rw [hd, Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod, Nat.mod_mul_mod, pow_mul, sq]

def powMod (m fuel a e : ℕ) : ℕ := loop m fuel a e 1

theorem powMod_spec (m fuel a e : ℕ) (he : e < 2 ^ fuel) : powMod m fuel a e = a ^ e % m := by
  rw [powMod, loop_spec m fuel a e 1 he, one_mul]

/-- Repeated squaring: `sqLoop m k x = x^(2^k) % m`. -/
def sqLoop (m k : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun x => x % m) (fun _ ih x => force (x * x % m) ih) k

theorem sqLoop_zero (m x : ℕ) : sqLoop m 0 x = x % m := rfl

theorem sqLoop_succ (m k x : ℕ) : sqLoop m (k + 1) x = sqLoop m k (x * x % m) := by
  show force (x * x % m) (sqLoop m k) = _
  rw [force_eq]

theorem sqLoop_spec (m : ℕ) : ∀ k x, sqLoop m k x = x ^ (2 ^ k) % m := by
  intro k
  induction k with
  | zero => intro x; simp [sqLoop_zero]
  | succ k ih =>
    intro x
    rw [sqLoop_succ, ih, ← Nat.pow_mod, pow_succ, pow_mul, ← pow_mul, mul_comm (2 ^ k) 2, pow_mul, sq]

/-- Fermat's little theorem, contrapositive: a witness of compositeness. -/
theorem not_prime_of_pow_mod {q a : ℕ} (hq : 2 ≤ q) (ha : ¬ q ∣ a)
    (hw : a ^ (q - 1) % q ≠ 1) : ¬ Nat.Prime q := by
  intro hp
  apply hw
  haveI := Fact.mk hp
  have h := ZMod.pow_card_sub_one_eq_one (p := q) (a := (a : ZMod q))
    (by rwa [Ne, ZMod.natCast_eq_zero_iff])
  have h2 : ((a ^ (q - 1) % q : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
    rw [ZMod.natCast_mod]; push_cast; exact h
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h2
  rwa [Nat.mod_mod, Nat.one_mod_eq_one.mpr (by omega)] at this

theorem five_pow_lt (n : ℕ) : 5 ^ (2 ^ n) < 2 ^ (3 * 2 ^ n) := by
  calc 5 ^ (2 ^ n) < 8 ^ (2 ^ n) := Nat.pow_lt_pow_left (by norm_num) (by positivity)
    _ = 2 ^ (3 * 2 ^ n) := by rw [show (8:ℕ) = 2 ^ 3 by norm_num, ← pow_mul]

theorem four_le_ten_pow (n : ℕ) : 4 ≤ 10 ^ (2 ^ n) :=
  le_trans (by norm_num : 4 ≤ 10 ^ 1) (Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow)

/-- The kernel-checkable Fermat witness for `q = 10^(2^n)+1`:
`3^(q-1) = (3^(5^(2^n)))^(2^(2^n))`, computed as a binary exponentiation followed by
`2^n` squarings. -/
theorem not_prime_ten_pow (n : ℕ)
    (hw : sqLoop (10 ^ (2 ^ n) + 1) (2 ^ n)
      (powMod (10 ^ (2 ^ n) + 1) (3 * 2 ^ n) 3 (5 ^ (2 ^ n))) ≠ 1) :
    ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  have h4 := four_le_ten_pow n
  refine not_prime_of_pow_mod (a := 3) (by omega) ?_ ?_
  · intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  · rw [Nat.add_sub_cancel]
    rw [sqLoop_spec, powMod_spec _ _ _ _ (five_pow_lt n), ← Nat.pow_mod, ← pow_mul,
      ← mul_pow] at hw
    simpa using hw


/-- Compositeness of `10^(2^n)+1` from a divisor `r` certified by `2^n` modular squarings.
No large numbers are ever constructed: `sqLoop r n 10 = 10^(2^n) % r`. -/
theorem not_prime_ten_pow_of_factor (n r : ℕ) (hr : 2 ≤ r) (hlt : r < 10 ^ (2 ^ n) + 1)
    (h : sqLoop r n 10 = r - 1) : ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  intro hp
  rw [sqLoop_spec] at h
  have hdvd : r ∣ 10 ^ (2 ^ n) + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, h, Nat.one_mod_eq_one.mpr (by omega), Nat.sub_add_cancel (by omega), Nat.mod_self]
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1 <;> omega

/-- `r < 10^(2^n)+1` whenever `r < 10^k` and `k ≤ 2^n`. -/
theorem lt_ten_pow_of {n r k : ℕ} (hk : k ≤ 2 ^ n) (hr : r < 10 ^ k) : r < 10 ^ (2 ^ n) + 1 :=
  lt_of_lt_of_le hr (le_trans (Nat.pow_le_pow_right (by norm_num) hk) (Nat.le_succ _))

end FermatWitness

namespace A378143Partial

open FermatWitness

/-- The statement of the conjecture for a single `n`. -/
def Claim (n : ℕ) : Prop :=
  Nat.Prime (10 ^ (2 ^ n) + 1) → Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1)

theorem claim_zero : Claim 0 := fun _ => Or.inl (by norm_num)

theorem claim_one : Claim 1 := fun _ => Or.inl (by norm_num)

theorem not_prime_2 : ¬ Nat.Prime (10 ^ (2 ^ 2) + 1) :=
  not_prime_ten_pow_of_factor 2 73 (by norm_num)
    (lt_ten_pow_of (k := 2) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_3 : ¬ Nat.Prime (10 ^ (2 ^ 3) + 1) :=
  not_prime_ten_pow_of_factor 3 17 (by norm_num)
    (lt_ten_pow_of (k := 2) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_4 : ¬ Nat.Prime (10 ^ (2 ^ 4) + 1) :=
  not_prime_ten_pow_of_factor 4 353 (by norm_num)
    (lt_ten_pow_of (k := 3) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_5 : ¬ Nat.Prime (10 ^ (2 ^ 5) + 1) :=
  not_prime_ten_pow_of_factor 5 19841 (by norm_num)
    (lt_ten_pow_of (k := 5) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_6 : ¬ Nat.Prime (10 ^ (2 ^ 6) + 1) :=
  not_prime_ten_pow_of_factor 6 1265011073 (by norm_num)
    (lt_ten_pow_of (k := 10) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_7 : ¬ Nat.Prime (10 ^ (2 ^ 7) + 1) :=
  not_prime_ten_pow_of_factor 7 257 (by norm_num)
    (lt_ten_pow_of (k := 3) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_8 : ¬ Nat.Prime (10 ^ (2 ^ 8) + 1) :=
  not_prime_ten_pow_of_factor 8 10753 (by norm_num)
    (lt_ten_pow_of (k := 5) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_9 : ¬ Nat.Prime (10 ^ (2 ^ 9) + 1) :=
  not_prime_ten_pow_of_factor 9 1514497 (by norm_num)
    (lt_ten_pow_of (k := 7) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_10 : ¬ Nat.Prime (10 ^ (2 ^ 10) + 1) :=
  not_prime_ten_pow 10 (by decide +kernel)

theorem not_prime_11 : ¬ Nat.Prime (10 ^ (2 ^ 11) + 1) :=
  not_prime_ten_pow_of_factor 11 106907803649 (by norm_num)
    (lt_ten_pow_of (k := 12) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_12 : ¬ Nat.Prime (10 ^ (2 ^ 12) + 1) :=
  not_prime_ten_pow_of_factor 12 458924033 (by norm_num)
    (lt_ten_pow_of (k := 9) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_13 : ¬ Nat.Prime (10 ^ (2 ^ 13) + 1) :=
  not_prime_ten_pow 13 (by decide +kernel)

theorem not_prime_14 : ¬ Nat.Prime (10 ^ (2 ^ 14) + 1) :=
  not_prime_ten_pow 14 (by decide +kernel)

theorem not_prime_15 : ¬ Nat.Prime (10 ^ (2 ^ 15) + 1) :=
  not_prime_ten_pow_of_factor 15 65537 (by norm_num)
    (lt_ten_pow_of (k := 5) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_16 : ¬ Nat.Prime (10 ^ (2 ^ 16) + 1) :=
  not_prime_ten_pow_of_factor 16 8257537 (by norm_num)
    (lt_ten_pow_of (k := 7) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_17 : ¬ Nat.Prime (10 ^ (2 ^ 17) + 1) :=
  not_prime_ten_pow_of_factor 17 175636481 (by norm_num)
    (lt_ten_pow_of (k := 9) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_18 : ¬ Nat.Prime (10 ^ (2 ^ 18) + 1) :=
  not_prime_ten_pow_of_factor 18 639631361 (by norm_num)
    (lt_ten_pow_of (k := 9) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_19 : ¬ Nat.Prime (10 ^ (2 ^ 19) + 1) :=
  not_prime_ten_pow_of_factor 19 70254593 (by norm_num)
    (lt_ten_pow_of (k := 8) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_20 : ¬ Nat.Prime (10 ^ (2 ^ 20) + 1) :=
  not_prime_ten_pow_of_factor 20 167772161 (by norm_num)
    (lt_ten_pow_of (k := 9) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_22 : ¬ Nat.Prime (10 ^ (2 ^ 22) + 1) :=
  not_prime_ten_pow_of_factor 22 101702694862849 (by norm_num)
    (lt_ten_pow_of (k := 15) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_26 : ¬ Nat.Prime (10 ^ (2 ^ 26) + 1) :=
  not_prime_ten_pow_of_factor 26 2281701377 (by norm_num)
    (lt_ten_pow_of (k := 10) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_28 : ¬ Nat.Prime (10 ^ (2 ^ 28) + 1) :=
  not_prime_ten_pow_of_factor 28 165422073617842177 (by norm_num)
    (lt_ten_pow_of (k := 18) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_29 : ¬ Nat.Prime (10 ^ (2 ^ 29) + 1) :=
  not_prime_ten_pow_of_factor 29 52613349377 (by norm_num)
    (lt_ten_pow_of (k := 11) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_30 : ¬ Nat.Prime (10 ^ (2 ^ 30) + 1) :=
  not_prime_ten_pow_of_factor 30 572183787362844673 (by norm_num)
    (lt_ten_pow_of (k := 18) (by norm_num) (by norm_num)) (by decide +kernel)

theorem not_prime_35 : ¬ Nat.Prime (10 ^ (2 ^ 35) + 1) :=
  not_prime_ten_pow_of_factor 35 2748779069441 (by norm_num)
    (lt_ten_pow_of (k := 13) (by norm_num) (by norm_num)) (by decide +kernel)

/-- The conjecture holds for all `n ≤ 20`: for `n = 0, 1` directly, otherwise vacuously. -/
theorem claim_of_le (n : ℕ) (hn : n ≤ 20) : Claim n := by
  interval_cases n
  · exact claim_zero
  · exact claim_one
  · exact fun h => absurd h not_prime_2
  · exact fun h => absurd h not_prime_3
  · exact fun h => absurd h not_prime_4
  · exact fun h => absurd h not_prime_5
  · exact fun h => absurd h not_prime_6
  · exact fun h => absurd h not_prime_7
  · exact fun h => absurd h not_prime_8
  · exact fun h => absurd h not_prime_9
  · exact fun h => absurd h not_prime_10
  · exact fun h => absurd h not_prime_11
  · exact fun h => absurd h not_prime_12
  · exact fun h => absurd h not_prime_13
  · exact fun h => absurd h not_prime_14
  · exact fun h => absurd h not_prime_15
  · exact fun h => absurd h not_prime_16
  · exact fun h => absurd h not_prime_17
  · exact fun h => absurd h not_prime_18
  · exact fun h => absurd h not_prime_19
  · exact fun h => absurd h not_prime_20

/-- Reduction: the conjecture is equivalent to its restriction to `n ≥ 21`. -/
theorem claim_iff : (∀ n, Claim n) ↔ ∀ n, 21 ≤ n → Claim n := by
  constructor
  · exact fun h n _ => h n
  · intro h n
    by_cases hn : n ≤ 20
    · exact claim_of_le n hn
    · exact h n (by omega)

/-- Any prime factor `r` of `b^(2^n)+1` with `b` even satisfies `2^(n+1) ∣ r - 1`.
Consequently each prime divides at most one number of the form `b^(2^n)+1`, so there can be
no finite covering set proving compositeness of all `10^(2^n)+1`. -/
theorem prime_dvd_pow_two_pow_add_one {b n r : ℕ} (hb : Even b) (hr : r.Prime)
    (hdvd : r ∣ b ^ (2 ^ n) + 1) : 2 ^ (n + 1) ∣ r - 1 := by
  haveI := Fact.mk hr
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h1 : Even (b ^ (2 ^ n) + 1) := even_iff_two_dvd.mpr hdvd
    have h2 : Odd (b ^ (2 ^ n) + 1) := (hb.pow_of_ne_zero (by positivity)).add_one
    exact Nat.not_even_iff_odd.mpr h2 h1
  haveI : Fact (2 < r) := ⟨lt_of_le_of_ne hr.two_le (Ne.symm hr2)⟩
  have hcast : ((b : ZMod r) ^ (2 ^ n)) = -1 := by
    have h := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at h
    exact eq_neg_of_add_eq_zero_left h
  have hb0 : (b : ZMod r) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by positivity)] at hcast
    exact zero_ne_one (α := ZMod r) (by simpa using congrArg Neg.neg hcast)
  have hord : orderOf (b : ZMod r) = 2 ^ (n + 1) := by
    apply orderOf_eq_prime_pow
    · rw [hcast]; exact ZMod.neg_one_ne_one
    · rw [pow_succ, pow_mul, hcast]; simp
  rw [← hord]
  exact ZMod.orderOf_dvd_card_sub_one hb0

end A378143Partial


/-- The conjecture is equivalent to its restriction to `n ≥ 21`. -/
theorem oeis_378143_conjecture_claim_iff :
    (∀ (n : ℕ), Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1)) ↔
    (∀ (n : ℕ), 21 ≤ n → Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1)) :=
  A378143Partial.claim_iff

/--
The conjecture is equivalent to the claim that a(n) is not 10^(2^n) + 1 for any n,
which in turn is equivalent to the claim that, if 10^(2^n) + 1 is prime,
then either 4^(2^n) + 1 or 6^(2^n) + 1 is prime. - Charles R Greathouse IV, Nov 17 2024
-/
theorem oeis_378143_conjecture_claim :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) :=
  by sorry

theorem oeis_378143_conjecture_claim.disproof : ¬ (type_of% @oeis_378143_conjecture_claim) := sorry
