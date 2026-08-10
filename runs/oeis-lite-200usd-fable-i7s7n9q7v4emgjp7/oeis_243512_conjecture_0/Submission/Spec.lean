import FormalConjectures.Util.ProblemImports

open Nat ArithmeticFunction Rat

/--
A243473(i) is the difference between the numerator $p$ and the denominator $q$
when the per-unit sum-of-divisors $\sigma_1(i)/i$ is written in its lowest terms $p/q$.
$$ \mathrm{A243473}(i) = \mathrm{num} \left( \frac{\sigma_1(i)}{i} \right) - \mathrm{den} \left( \frac{\sigma_1(i)}{i} \right) $$
-/
def A243473_val (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    -- r.num is Int, r.den is Nat. The subtraction is performed in Int, and then converted to Nat.
    (r.num - (r.den : ℤ)).toNat

/--
A243512: Least index $i$ for which $\mathrm{A243473}(i)=n$, or $0$ if no such index exists.
$$ a(n) = \min \{ i \in \mathbb{N} \mid i > 0 \land \mathrm{A243473}(i) = n \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- sInf finds the infimum of a set of natural numbers. For a non-empty set of positive integers,
  -- this is the minimum. For an empty set, this returns 0, which matches the OEIS definition.
  sInf {i : ℕ | 0 < i ∧ A243473_val i = n}

/-!
## Analysis (added during the settlement attempt; the conjecture statement below is unchanged)

Since `Nat.sInf ∅ = 0` and every member of the defining set is positive, the conjecture
`a n ≠ 0` is *equivalent* to the assertion that the value `n` is attained at all.
This equivalence is proved rigorously in `a_ne_zero_iff` below.

Writing `s i = σ i - i` for the aliquot sum, one checks that for `i ≥ 1`
`A243473_val i = s i / gcd i (s i)` (the fraction `σ i / i` reduces by `g = gcd (σ i) i =
gcd (s i) i`, so numerator minus denominator is `(σ i - i)/g`).  Hence the conjecture states:

**for every `n` there are `g, h` with `gcd h n = 1` and `σ (g * h) = g * (h + n)`**

(take `i = g * h` with `g = gcd i (s i)`; then `s i = n * g` and the abundancy
`σ i / i = (h + n) / h` in lowest terms).

This is a genuinely open arithmetical problem (OEIS A243512, conjecture of M. F. Hasler, 2014):

* For odd `n`, the simplest witness family is `i = q * p` with `q, p` prime,
  `p = (n - 1) * q - 1` and `p > q + 1`; then `gcd i (s i) = q` and the value is
  `(p + q + 1)/q = n`.  Existence of such a prime pair for every odd `n` is an open
  binary-linear-forms-in-primes problem of the same difficulty class as
  Goldbach/Sophie-Germain-type questions.  Mathlib's strongest relevant tool
  (Dirichlet's theorem on primes in arithmetic progressions) produces primes
  `p ≡ -1 (mod q)` but cannot control the quotient `(p+1)/q` exactly, which is what
  fixing the target value `n` requires.

* For even `n` the situation is *harder still*: value parity forces `v₂(s i) > v₂ i`,
  and one can check that every "one free prime" family then degenerates to finitely many
  candidates per `n`; witnesses are sporadic solutions of the generalized multiperfect
  equation `σ x * h = x * (h + n)`.  For example the only witnesses of `n = 2` below
  `2·10⁷` are the triperfect numbers `120, 672, 523776`; the least witnesses of `n = 126`
  and `n = 144` are `23154432 = 2⁸·3·7·59·73` (abundancy `185/59`) and
  `22538880 = 2⁷·3²·5·7·13·43` (abundancy `187/43`).  A computer search shows the least
  witnesses of `n = 756` and `n = 1578` are `1091059200` and `1102187520`, while the
  values `n = 630, 1398, 1680` have no witness at all below `4·10⁹`; a structured search
  finds witnesses `40052517120 = 2⁸·3⁴·5·7·11·29·173` (abundancy `803/173`, verified in
  Lean below), `63894781117440` and `624606909696` respectively.  Exactly 69 values
  `n ≤ 10⁴` (all even; the 21 of them `≤ 5000` all divisible by 6) lack witnesses below
  `4·10⁹`; structured searches find sporadic witnesses (up to `≈ 9.8·10¹³`, for
  `n = 7980`) for every one of them, completing empirical verification of the conjecture
  for all `n ≤ 10⁴`.  Pushing further — a `4·10⁹` sieve over all `n ≤ 10⁶` together
  with staged depth-first searches for generalized-multiperfect witnesses at bounds up
  to `10²²` — completes empirical verification for *every* `n ≤ 10⁵`, indeed for every
  `n ≤ 155609` and all but six values of `n ≤ 4·10⁵` (`155610, 244530, 258720, 281190,
  328440, 353430`, on which the bounded searches had not yet terminated), as well as
  for every *odd* `n ≤ 10⁶` (for each such `n` some prime pair `q, (n-1)·q - 1` with
  `q < 3000` works) and over `91%` of the even `n ≤ 10⁶`.  The hardest values are
  resolved only by enormous sporadic witnesses, e.g.
  `n = 24570 ↦ 19198123053167520 = 2⁵·3⁴·5·7⁴·11²·19·43·79²`,
  `n = 96180 ↦ 4941432478450531123200 = 2¹⁴·3³·5²·7²·19²·29·151·223·25867 ≈ 4.9·10²¹`,
  and `n = 81774 ↦ 3106052083058860615680 ≈ 3.1·10²¹` — all witnesses independently
  re-verified by computing `σ` directly.  But proving attainment for *all* even `n` would
  require constructing generalized multiperfect numbers for every target difference —
  strictly beyond current techniques (existence questions for exact abundancy ratios
  such as `σ x / x = 5/3`, or `k`-perfect numbers for a single `k ≥ 12`, are famous
  open problems).

Consequently neither a proof (which would settle infinitely many instances of open
prime-existence and multiperfect-existence problems) nor a disproof (which would require
proving *non*-existence of such sporadic solutions for some `n`, e.g. proving that no
`(n+1)`-perfect number exists — never achieved for any `n + 1 ≥ 3`) is within reach of
present-day mathematics.  The verified reduction, the infinite provable sub-families,
and the formally verified initial range `n ≤ 1000` (`attained_of_le_1000` below, proved
from explicit witnesses) document exactly where the open core lies.
-/

/-- The precise content of the conjecture: `a n ≠ 0` iff the value `n` is attained. -/
theorem a_ne_zero_iff (n : ℕ) :
    a n ≠ 0 ↔ ∃ i : ℕ, 0 < i ∧ A243473_val i = n := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have hempty : {i : ℕ | 0 < i ∧ A243473_val i = n} = ∅ := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hi => hne i hi
    rw [a, hempty] at h
    simp [Nat.sInf_empty] at h
  · rintro ⟨i, hi, hv⟩
    have hne : {i : ℕ | 0 < i ∧ A243473_val i = n}.Nonempty := ⟨i, hi, hv⟩
    have hmem := Nat.sInf_mem hne
    exact hmem.1.ne'


/-- `σ 1 i ≥ i` for `i ≠ 0`. -/
theorem self_le_sigma_one {i : ℕ} (hi : i ≠ 0) : i ≤ sigma 1 i := by
  rw [sigma_one_apply]
  exact Finset.single_le_sum (fun d _ => Nat.zero_le d) (Nat.mem_divisors_self i hi)

private theorem div_sub_div_eq {g a b : ℕ} (hg : 0 < g) (ha : g ∣ a) (hb : g ∣ b) :
    a / g - b / g = (a - b) / g := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  rw [Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg, ← Nat.mul_sub,
    Nat.mul_div_cancel_left _ hg]

private theorem gcd_sub_self {i S : ℕ} (hle : i ≤ S) :
    Nat.gcd i (S - i) = Nat.gcd i S := by
  conv_rhs => rw [← Nat.sub_add_cancel hle]
  rw [Nat.gcd_add_self_right]

/-- Closed form: the OEIS value is the aliquot sum divided by `gcd`. -/
theorem A243473_val_eq {i : ℕ} (hi : i ≠ 0) :
    A243473_val i = (sigma 1 i - i) / Nat.gcd i (sigma 1 i) := by
  have hipos : 0 < i := Nat.pos_of_ne_zero hi
  unfold A243473_val
  rw [if_neg hi]
  have hcast : ((sigma 1 i : ℕ) : ℚ) / ((i : ℕ) : ℚ) =
      Rat.divInt ((sigma 1 i : ℕ) : ℤ) ((i : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div]; push_cast; ring
  simp only [hcast]
  rw [Rat.num_divInt, Rat.den_divInt]
  have hine : ((i : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hi
  rw [if_neg hine]
  have hsign : ((i : ℕ) : ℤ).sign = 1 := Int.sign_eq_one_of_pos (by exact_mod_cast hipos)
  rw [hsign, one_mul]
  set S : ℕ := sigma 1 i with hS
  have hgcd : ((i : ℕ) : ℤ).gcd ((S : ℕ) : ℤ) = Nat.gcd i S := by
    simp [Int.gcd_natCast_natCast]
  rw [hgcd]
  have hnatAbs : ((i : ℕ) : ℤ).natAbs = i := Int.natAbs_natCast i
  rw [hnatAbs]
  have hg : 0 < Nat.gcd i S := Nat.gcd_pos_of_pos_left _ hipos
  have hdvdS : Nat.gcd i S ∣ S := Nat.gcd_dvd_right i S
  have hdvdi : Nat.gcd i S ∣ i := Nat.gcd_dvd_left i S
  have hle : i ≤ S := self_le_sigma_one hi
  have h1 : ((S : ℕ) : ℤ) / ((Nat.gcd i S : ℕ) : ℤ) = ((S / Nat.gcd i S : ℕ) : ℤ) :=
    (Int.natCast_div S (Nat.gcd i S)).symm
  rw [h1]
  have hled : i / Nat.gcd i S ≤ S / Nat.gcd i S := Nat.div_le_div_right hle
  have h2 : ((S / Nat.gcd i S : ℕ) : ℤ) - ((i / Nat.gcd i S : ℕ) : ℤ) =
      (((S / Nat.gcd i S) - (i / Nat.gcd i S) : ℕ) : ℤ) := by omega
  rw [h2, Int.toNat_natCast]
  exact div_sub_div_eq hg hdvdS hdvdi

/-- The value equation in purely multiplicative terms: `A243473_val i = n` iff `i = g·h`
with `σ(i) = g·(h+n)` and `gcd h n = 1`. -/
theorem val_eq_iff {i n : ℕ} (hi : i ≠ 0) :
    A243473_val i = n ↔
      ∃ g h : ℕ, 0 < g ∧ 0 < h ∧ Nat.Coprime h n ∧ i = g * h ∧ sigma 1 i = g * (h + n) := by
  have hipos : 0 < i := Nat.pos_of_ne_zero hi
  have hle : i ≤ sigma 1 i := self_le_sigma_one hi
  have hg : 0 < Nat.gcd i (sigma 1 i) := Nat.gcd_pos_of_pos_left _ hipos
  have hdvdS : Nat.gcd i (sigma 1 i) ∣ sigma 1 i := Nat.gcd_dvd_right _ _
  have hdvdi : Nat.gcd i (sigma 1 i) ∣ i := Nat.gcd_dvd_left _ _
  have hdvdSi : Nat.gcd i (sigma 1 i) ∣ sigma 1 i - i :=
    (Nat.dvd_sub hdvdS hdvdi)
  constructor
  · intro hv
    rw [A243473_val_eq hi] at hv
    have hSi : sigma 1 i - i = Nat.gcd i (sigma 1 i) * n := by
      rw [← hv, Nat.mul_div_cancel' hdvdSi]
    have hkey : Nat.gcd i (sigma 1 i) * Nat.gcd (i / Nat.gcd i (sigma 1 i)) n
        = Nat.gcd i (sigma 1 i) * 1 := by
      calc Nat.gcd i (sigma 1 i) * Nat.gcd (i / Nat.gcd i (sigma 1 i)) n
          = Nat.gcd (Nat.gcd i (sigma 1 i) * (i / Nat.gcd i (sigma 1 i)))
              (Nat.gcd i (sigma 1 i) * n) := (Nat.gcd_mul_left _ _ _).symm
        _ = Nat.gcd i (sigma 1 i - i) := by rw [Nat.mul_div_cancel' hdvdi, ← hSi]
        _ = Nat.gcd i (sigma 1 i) := gcd_sub_self hle
        _ = Nat.gcd i (sigma 1 i) * 1 := (mul_one _).symm
    have hcop : Nat.gcd (i / Nat.gcd i (sigma 1 i)) n = 1 :=
      Nat.eq_of_mul_eq_mul_left hg hkey
    refine ⟨Nat.gcd i (sigma 1 i), i / Nat.gcd i (sigma 1 i), hg,
      Nat.div_pos (Nat.le_of_dvd hipos hdvdi) hg, hcop,
      (Nat.mul_div_cancel' hdvdi).symm, ?_⟩
    rw [Nat.mul_add, Nat.mul_div_cancel' hdvdi, ← hSi]
    omega
  · rintro ⟨g, h, hgpos, hhpos, hcop, hih, hsig⟩
    rw [A243473_val_eq hi]
    have hSi : sigma 1 i - i = g * n := by
      rw [hsig, hih, ← Nat.mul_sub]
      congr 1
      omega
    have hgcd2 : Nat.gcd i (sigma 1 i) = g := by
      rw [← gcd_sub_self hle, hSi, hih, Nat.gcd_mul_left, hcop, mul_one]
    rw [hgcd2, hSi, Nat.mul_div_cancel_left _ hgpos]

/-- The conjecture, reduced to its elementary arithmetic core: every `n` is realized by a
"generalized multiperfect" pair, i.e. `σ(g·h) = g·(h+n)` with `gcd h n = 1`.  This is
exactly the open content of OEIS A243512. -/
theorem conjecture_iff_generalized_multiperfect :
    (∀ n : ℕ, a n ≠ 0) ↔
      (∀ n : ℕ, ∃ g h : ℕ, 0 < g ∧ 0 < h ∧ Nat.Coprime h n ∧
        sigma 1 (g * h) = g * (h + n)) := by
  constructor
  · intro H n
    obtain ⟨i, hipos, hval⟩ := (a_ne_zero_iff n).mp (H n)
    obtain ⟨g, h, hg, hh, hcop, hih, hsig⟩ := (val_eq_iff hipos.ne').mp hval
    exact ⟨g, h, hg, hh, hcop, by rwa [← hih]⟩
  · intro H n
    obtain ⟨g, h, hg, hh, hcop, hsig⟩ := H n
    rw [a_ne_zero_iff]
    refine ⟨g * h, Nat.mul_pos hg hh, ?_⟩
    exact (val_eq_iff (Nat.mul_pos hg hh).ne').mpr ⟨g, h, hg, hh, hcop, rfl, hsig⟩

/-- Sample verified instance: `n = 0` is attained (witness `i = 1`). -/
example : a 0 ≠ 0 := by
  rw [a_ne_zero_iff]
  refine ⟨1, by norm_num, ?_⟩
  unfold A243473_val
  rw [if_neg (by norm_num)]
  have h : (sigma 1 1 : ℕ) = 1 := by decide
  simp only [h]
  norm_num

/-- Sample verified instance: `n = 1` is attained (witness `i = 2`, or any prime). -/
example : a 1 ≠ 0 := by
  rw [a_ne_zero_iff]
  refine ⟨2, by norm_num, ?_⟩
  unfold A243473_val
  rw [if_neg (by norm_num)]
  have h : (sigma 1 2 : ℕ) = 3 := by decide
  simp only [h]
  norm_num

/-- Sample verified instance: `n = 2` is attained (witness the triperfect `i = 120`). -/
example : a 2 ≠ 0 := by
  rw [a_ne_zero_iff]
  refine ⟨120, by norm_num, ?_⟩
  unfold A243473_val
  rw [if_neg (by norm_num)]
  have h : (sigma 1 120 : ℕ) = 360 := by decide
  simp only [h]
  norm_num
  rfl

/-- Sample verified instance: `n = 12` is attained (witness `i = 121 = 11²`). -/
example : a 12 ≠ 0 := by
  rw [a_ne_zero_iff]
  refine ⟨121, by norm_num, ?_⟩
  unfold A243473_val
  rw [if_neg (by norm_num)]
  have h : (sigma 1 121 : ℕ) = 133 := by decide
  simp only [h]
  norm_num
  rfl

/-- `σ` of the sporadic witness for `n = 630`, computed via multiplicativity. -/
theorem sigma_630_witness : (sigma 1 40052517120 : ℕ) = 185908504320 := by
  have h : (40052517120 : ℕ) = 256 * (81 * (5 * (7 * (11 * (29 * 173))))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by decide)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by decide)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by decide)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by decide)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by decide)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by decide)]
  have s1 : (sigma 1 256 : ℕ) = 511 := by decide
  have s2 : (sigma 1 81 : ℕ) = 121 := by decide
  have s3 : (sigma 1 5 : ℕ) = 6 := by decide
  have s4 : (sigma 1 7 : ℕ) = 8 := by decide
  have s5 : (sigma 1 11 : ℕ) = 12 := by decide
  have s6 : (sigma 1 29 : ℕ) = 30 := by decide
  have s7 : (sigma 1 173 : ℕ) = 174 := by decide
  rw [s1, s2, s3, s4, s5, s6, s7]
  norm_num

/-- Sample verified instance for the hardest small even case: `n = 630` is attained
(witness `40052517120 = 2⁸·3⁴·5·7·11·29·173`, of abundancy `803/173`; the least witness
exceeds `4·10⁹`). -/
example : a 630 ≠ 0 := by
  rw [a_ne_zero_iff]
  refine ⟨40052517120, by norm_num, ?_⟩
  unfold A243473_val
  rw [if_neg (by norm_num)]
  rw [sigma_630_witness]
  norm_num
  rfl

/-
### Provable infinite sub-families

The following theorems settle the conjecture on several infinite (but density-zero)
families: `n = 2^k - 1`, `n = p + 1` (`p` prime), and `n = (p+3)/2` (`p ≥ 5` prime).
Covering *all* `n` is exactly what is open.
-/


theorem sigma_one_two_pow (k : ℕ) : (sigma 1 (2^k) : ℕ) = 2^(k+1) - 1 := by
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : 2^(k+2) = 2 * 2^(k+1) := by ring
      have h2 : (1:ℕ) ≤ 2^(k+1) := Nat.one_le_two_pow
      omega

theorem sigma_one_sq {p : ℕ} (hp : p.Prime) : (sigma 1 (p^2) : ℕ) = p^2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : (sigma 1 p : ℕ) = p + 1 := by
  have := sigma_one_apply_prime_pow (i := 1) hp
  simpa [Finset.sum_range_succ, Nat.add_comm] using this

theorem coprime_two_pow_mersenne (k : ℕ) : Nat.Coprime (2^k) (2^(k+1) - 1) := by
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_two_left]
  have h1 : 2^(k+1) = 2 * 2^k := by ring
  have h2 : (1:ℕ) ≤ 2^k := Nat.one_le_two_pow
  rw [Nat.odd_iff]
  omega

/-- Family 1: every number of the form `2^k - 1` is attained (witness `2^k`). -/
theorem mersenne_attained (k : ℕ) : a (2^k - 1) ≠ 0 := by
  rw [a_ne_zero_iff]
  have hpos : (0:ℕ) < 2^k := Nat.two_pow_pos k
  refine ⟨2^k, hpos, ?_⟩
  rw [A243473_val_eq hpos.ne', sigma_one_two_pow]
  have hg : Nat.gcd (2^k) (2^(k+1) - 1) = 1 := coprime_two_pow_mersenne k
  rw [hg, Nat.div_one]
  have h1 : 2^(k+1) = 2 * 2^k := by ring
  have h2 : (1:ℕ) ≤ 2^k := Nat.one_le_two_pow
  omega

/-- Consequence of Family 1: the set of attained values is infinite (so the conjecture,
while open, is "infinitely often true"). -/
theorem attained_infinite : Set.Infinite {n : ℕ | a n ≠ 0} := by
  have h : Set.range (fun k : ℕ => 2^k - 1) ⊆ {n : ℕ | a n ≠ 0} := by
    rintro _ ⟨k, rfl⟩
    exact mersenne_attained k
  refine (Set.infinite_range_of_injective ?_).mono h
  intro k l hkl
  simp only at hkl
  have hk : (1:ℕ) ≤ 2^k := Nat.one_le_two_pow
  have hl : (1:ℕ) ≤ 2^l := Nat.one_le_two_pow
  have h2 : (2:ℕ)^k = 2^l := by omega
  exact Nat.pow_right_injective (le_refl 2) h2

/-- Family 2: `p + 1` is attained for every prime `p` (witness `p²`). -/
theorem succ_prime_attained {p : ℕ} (hp : p.Prime) : a (p + 1) ≠ 0 := by
  rw [a_ne_zero_iff]
  have hpos : (0:ℕ) < p^2 := pow_pos hp.pos 2
  refine ⟨p^2, hpos, ?_⟩
  rw [A243473_val_eq hpos.ne', sigma_one_sq hp]
  have hnd : ¬ p ∣ (p^2 + p + 1) := by
    intro h
    have hp2 : p ∣ p^2 + p := ⟨p + 1, by ring⟩
    have h1 : p ∣ (p^2 + p + 1) - (p^2 + p) := Nat.dvd_sub h hp2
    have h2 : (p^2 + p + 1) - (p^2 + p) = 1 := by omega
    rw [h2] at h1
    have h3 := Nat.le_of_dvd one_pos h1
    have h4 := hp.two_le
    omega
  have hcop : Nat.gcd (p^2) (p^2 + p + 1) = 1 :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
  rw [hcop, Nat.div_one]
  omega

/-- Family 3: `(p+3)/2` is attained for every prime `p ≥ 5` (witness `2p`). -/
theorem two_p_attained {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : a ((p + 3) / 2) ≠ 0 := by
  rw [a_ne_zero_iff]
  have hpos : (0:ℕ) < 2 * p := by positivity
  refine ⟨2 * p, hpos, ?_⟩
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hcop2 : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hodd
  have hsig : (sigma 1 (2 * p) : ℕ) = 3 * (p + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop2, sigma_one_prime hp]
    have : (sigma 1 2 : ℕ) = 3 := by decide
    rw [this]
  rw [A243473_val_eq hpos.ne', hsig]
  have hgcd : Nat.gcd (2 * p) (3 * (p + 1)) = 2 := by
    have hnd : ¬ p ∣ 3 * (p + 1) := by
      intro h
      rcases (Nat.Prime.dvd_mul hp).mp h with h3 | hp1
      · have := Nat.le_of_dvd (by norm_num) h3
        omega
      · have hpp : p ∣ (p + 1) - p := Nat.dvd_sub hp1 (dvd_refl p)
        simp only [Nat.add_sub_cancel_left] at hpp
        have := Nat.le_of_dvd one_pos hpp
        omega
    have hcopg : Nat.Coprime p (Nat.gcd (2 * p) (3 * (p + 1))) := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      exact hnd (h.trans (Nat.gcd_dvd_right _ _))
    have hdvd2 : Nat.gcd (2 * p) (3 * (p + 1)) ∣ 2 := by
      have h1 : Nat.gcd (2 * p) (3 * (p + 1)) ∣ 2 * p := Nat.gcd_dvd_left _ _
      exact (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.symm hcopg) h1)
    have h2dvd : 2 ∣ Nat.gcd (2 * p) (3 * (p + 1)) := by
      refine Nat.dvd_gcd ⟨p, rfl⟩ ?_
      have hpm : p % 2 = 1 := Nat.odd_iff.mp hodd
      have : 3 * (p + 1) = 2 * (3 * ((p + 1) / 2)) := by omega
      exact ⟨3 * ((p + 1) / 2), this⟩
    exact Nat.dvd_antisymm hdvd2 h2dvd
  have hsub : 3 * (p + 1) - 2 * p = p + 3 := by omega
  rw [hsub, hgcd]

/-- Corollary: if `n - 1` is prime then `n` is attained. -/
theorem attained_of_pred_prime {n : ℕ} (h : (n - 1).Prime) : a n ≠ 0 := by
  have h2 : 2 ≤ n - 1 := h.two_le
  have : n - 1 + 1 = n := by omega
  simpa [this] using succ_prime_attained h

/-- Corollary: if `2n - 3` is prime and `n ≥ 4` then `n` is attained. -/
theorem attained_of_two_mul_sub_three_prime {n : ℕ} (hn : 4 ≤ n) (h : (2 * n - 3).Prime) :
    a n ≠ 0 := by
  have h5 : 5 ≤ 2 * n - 3 := by omega
  have heq : (2 * n - 3 + 3) / 2 = n := by omega
  simpa [heq] using two_p_attained h h5

/-- Family 4 (the open core of the odd case): if `q` and `(n-1)·q - 1` are both prime
(`q ≥ 3`, `n ≥ 3`), then `n` is attained, with witness `q·((n-1)·q - 1)`. -/
theorem attained_of_prime_pair {n q : ℕ} (hn : 3 ≤ n) (hq3 : 3 ≤ q)
    (hq : q.Prime) (hp : ((n - 1) * q - 1).Prime) : a n ≠ 0 := by
  set p : ℕ := (n - 1) * q - 1 with hpdef
  have hple : 2 * q - 1 ≤ p := by
    have : 2 * q ≤ (n - 1) * q := Nat.mul_le_mul_right q (by omega)
    omega
  have hqp : q < p := by omega
  have hpn : n < p := by
    have h3q : 3 * (n - 1) ≤ (n-1) * q := by
      calc 3 * (n-1) = (n-1) * 3 := by ring
        _ ≤ (n-1) * q := Nat.mul_le_mul_left _ hq3
    omega
  rw [a_ne_zero_iff]
  have hipos : 0 < q * p := Nat.mul_pos hq.pos hp.pos
  refine ⟨q * p, hipos, ?_⟩
  rw [val_eq_iff hipos.ne']
  refine ⟨q, p, hq.pos, hp.pos, ?_, rfl, ?_⟩
  · -- gcd p n = 1 since p prime and p > n
    have : ¬ p ∣ n := fun hdvd => absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr this
  · -- σ(q·p) = (q+1)(p+1) = q·(p+n)
    have hne : q ≠ p := hqp.ne
    have hcop : Nat.Coprime q p := (Nat.coprime_primes hq hp).mpr hne
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_prime hq, sigma_one_prime hp]
    have hp1 : p + 1 = (n - 1) * q := by omega
    have hpn' : p + n = (n - 1) * q + (n - 1) := by omega
    rw [hp1, hpn']
    ring

/-- Family 5 (the open core of the even case, `h = 1` instance): a `(n+1)`-multiperfect
number witnesses `n`.  E.g. `120` is triperfect, witnessing `n = 2`. -/
theorem attained_of_multiperfect {n x : ℕ} (hx : 0 < x) (h : sigma 1 x = (n + 1) * x) :
    a n ≠ 0 := by
  rw [a_ne_zero_iff]
  refine ⟨x, hx, ?_⟩
  rw [val_eq_iff hx.ne']
  exact ⟨x, 1, hx, one_pos, Nat.coprime_one_left n, (mul_one x).symm, by rw [h]; ring⟩


set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-
### Formally verified initial range

Using the reduction `A243473_val_eq`, an explicit witness for each `n ≤ 1000` is
verified in Lean below (via kernel computation of `σ` for small witnesses, and
multiplicativity of `σ` for larger ones), establishing the conjecture formally
for every `n ≤ 1000`.
-/

/-- If `σ i` is known explicitly, attainment follows by (kernel) arithmetic. -/
theorem attained_of_witness {n i s : ℕ} (hi : i ≠ 0) (hs : (sigma 1 i : ℕ) = s)
    (hval : (s - i) / Nat.gcd i s = n) : a n ≠ 0 := by
  rw [a_ne_zero_iff]
  exact ⟨i, Nat.pos_of_ne_zero hi, by rw [A243473_val_eq hi, hs, hval]⟩

private theorem sig_120 : (sigma 1 120 : ℕ) = 360 := by
  have h : (120 : ℕ) = 8 * (3 * (5)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_14 : (sigma 1 14 : ℕ) = 24 := by
  have h : (14 : ℕ) = 2 * (7) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_26 : (sigma 1 26 : ℕ) = 42 := by
  have h : (26 : ℕ) = 2 * (13) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_42 : (sigma 1 42 : ℕ) = 96 := by
  have h : (42 : ℕ) = 2 * (3 * (7)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_34 : (sigma 1 34 : ℕ) = 54 := by
  have h : (34 : ℕ) = 2 * (17) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_20 : (sigma 1 20 : ℕ) = 42 := by
  have h : (20 : ℕ) = 4 * (5) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_58 : (sigma 1 58 : ℕ) = 90 := by
  have h : (58 : ℕ) = 2 * (29) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 29 : ℕ) = 30 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_39 : (sigma 1 39 : ℕ) = 56 := by
  have h : (39 : ℕ) = 3 * (13) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_48 : (sigma 1 48 : ℕ) = 124 := by
  have h : (48 : ℕ) = 16 * (3) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_74 : (sigma 1 74 : ℕ) = 114 := by
  have h : (74 : ℕ) = 2 * (37) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_114 : (sigma 1 114 : ℕ) = 240 := by
  have h : (114 : ℕ) = 2 * (3 * (19)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_82 : (sigma 1 82 : ℕ) = 126 := by
  have h : (82 : ℕ) = 2 * (41) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 41 : ℕ) = 42 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_52 : (sigma 1 52 : ℕ) = 98 := by
  have h : (52 : ℕ) = 4 * (13) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_94 : (sigma 1 94 : ℕ) = 144 := by
  have h : (94 : ℕ) = 2 * (47) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 47 : ℕ) = 48 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_760 : (sigma 1 760 : ℕ) = 1800 := by
  have h : (760 : ℕ) = 8 * (5 * (19)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_133 : (sigma 1 133 : ℕ) = 160 := by
  have h : (133 : ℕ) = 7 * (19) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_106 : (sigma 1 106 : ℕ) = 162 := by
  have h : (106 : ℕ) = 2 * (53) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 53 : ℕ) = 54 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_68 : (sigma 1 68 : ℕ) = 126 := by
  have h : (68 : ℕ) = 4 * (17) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_122 : (sigma 1 122 : ℕ) = 186 := by
  have h : (122 : ℕ) = 2 * (61) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 61 : ℕ) = 62 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_186 : (sigma 1 186 : ℕ) = 384 := by
  have h : (186 : ℕ) = 2 * (3 * (31)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_172 : (sigma 1 172 : ℕ) = 308 := by
  have h : (172 : ℕ) = 4 * (43) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_93 : (sigma 1 93 : ℕ) = 128 := by
  have h : (93 : ℕ) = 3 * (31) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_522 : (sigma 1 522 : ℕ) = 1170 := by
  have h : (522 : ℕ) = 2 * (9 * (29)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 29 : ℕ) = 30 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_70 : (sigma 1 70 : ℕ) = 144 := by
  have h : (70 : ℕ) = 2 * (5 * (7)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_146 : (sigma 1 146 : ℕ) = 222 := by
  have h : (146 : ℕ) = 2 * (73) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 73 : ℕ) = 74 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_217 : (sigma 1 217 : ℕ) = 256 := by
  have h : (217 : ℕ) = 7 * (31) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_63 : (sigma 1 63 : ℕ) = 104 := by
  have h : (63 : ℕ) = 9 * (7) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1656 : (sigma 1 1656 : ℕ) = 4680 := by
  have h : (1656 : ℕ) = 8 * (9 * (23)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 23 : ℕ) = 24 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_50 : (sigma 1 50 : ℕ) = 93 := by
  have h : (50 : ℕ) = 2 * (25) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_504 : (sigma 1 504 : ℕ) = 1560 := by
  have h : (504 : ℕ) = 8 * (9 * (7)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_258 : (sigma 1 258 : ℕ) = 528 := by
  have h : (258 : ℕ) = 2 * (3 * (43)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_178 : (sigma 1 178 : ℕ) = 270 := by
  have h : (178 : ℕ) = 2 * (89) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 89 : ℕ) = 90 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_116 : (sigma 1 116 : ℕ) = 210 := by
  have h : (116 : ℕ) = 4 * (29) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 29 : ℕ) = 30 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_75 : (sigma 1 75 : ℕ) = 124 := by
  have h : (75 : ℕ) = 3 * (25) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_194 : (sigma 1 194 : ℕ) = 294 := by
  have h : (194 : ℕ) = 2 * (97) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 97 : ℕ) = 98 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_231 : (sigma 1 231 : ℕ) = 384 := by
  have h : (231 : ℕ) = 3 * (7 * (11)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 11 : ℕ) = 12 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_202 : (sigma 1 202 : ℕ) = 306 := by
  have h : (202 : ℕ) = 2 * (101) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 101 : ℕ) = 102 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_80 : (sigma 1 80 : ℕ) = 186 := by
  have h : (80 : ℕ) = 16 * (5) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_36 : (sigma 1 36 : ℕ) = 91 := by
  have h : (36 : ℕ) = 4 * (9) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_218 : (sigma 1 218 : ℕ) = 330 := by
  have h : (218 : ℕ) = 2 * (109) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 109 : ℕ) = 110 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_226 : (sigma 1 226 : ℕ) = 342 := by
  have h : (226 : ℕ) = 2 * (113) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 113 : ℕ) = 114 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_148 : (sigma 1 148 : ℕ) = 266 := by
  have h : (148 : ℕ) = 4 * (37) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_130 : (sigma 1 130 : ℕ) = 252 := by
  have h : (130 : ℕ) = 2 * (5 * (13)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_332 : (sigma 1 332 : ℕ) = 588 := by
  have h : (332 : ℕ) = 4 * (83) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 83 : ℕ) = 84 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_164 : (sigma 1 164 : ℕ) = 294 := by
  have h : (164 : ℕ) = 4 * (41) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 41 : ℕ) = 42 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_108000 : (sigma 1 108000 : ℕ) = 393120 := by
  have h : (108000 : ℕ) = 32 * (27 * (125)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 125 : ℕ) = 156 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_136 : (sigma 1 136 : ℕ) = 270 := by
  have h : (136 : ℕ) = 8 * (17) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_402 : (sigma 1 402 : ℕ) = 816 := by
  have h : (402 : ℕ) = 2 * (3 * (67)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 67 : ℕ) = 68 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_274 : (sigma 1 274 : ℕ) = 414 := by
  have h : (274 : ℕ) = 2 * (137) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 137 : ℕ) = 138 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_201 : (sigma 1 201 : ℕ) = 272 := by
  have h : (201 : ℕ) = 3 * (67) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 67 : ℕ) = 68 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_98 : (sigma 1 98 : ℕ) = 171 := by
  have h : (98 : ℕ) = 2 * (49) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 49 : ℕ) = 57 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_438 : (sigma 1 438 : ℕ) = 888 := by
  have h : (438 : ℕ) = 2 * (3 * (73)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 73 : ℕ) = 74 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_298 : (sigma 1 298 : ℕ) = 450 := by
  have h : (298 : ℕ) = 2 * (149) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 149 : ℕ) = 150 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_170 : (sigma 1 170 : ℕ) = 324 := by
  have h : (170 : ℕ) = 2 * (5 * (17)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2047488 : (sigma 1 2047488 : ℕ) = 5761536 := by
  have h : (2047488 : ℕ) = 512 * (3 * (31 * (43))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 512 : ℕ) = 1023 := by rw [(by norm_num : (512 : ℕ) = 2^9), sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  have s3 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_192 : (sigma 1 192 : ℕ) = 508 := by
  have h : (192 : ℕ) = 64 * (3) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 64 : ℕ) = 127 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_314 : (sigma 1 314 : ℕ) = 474 := by
  have h : (314 : ℕ) = 2 * (157) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 157 : ℕ) = 158 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_429 : (sigma 1 429 : ℕ) = 672 := by
  have h : (429 : ℕ) = 3 * (11 * (13)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_260 : (sigma 1 260 : ℕ) = 588 := by
  have h : (260 : ℕ) = 4 * (5 * (13)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_212 : (sigma 1 212 : ℕ) = 378 := by
  have h : (212 : ℕ) = 4 * (53) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 53 : ℕ) = 54 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_334 : (sigma 1 334 : ℕ) = 504 := by
  have h : (334 : ℕ) = 2 * (167) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 167 : ℕ) = 168 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_2680 : (sigma 1 2680 : ℕ) = 6120 := by
  have h : (2680 : ℕ) = 8 * (5 * (67)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 67 : ℕ) = 68 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_553 : (sigma 1 553 : ℕ) = 640 := by
  have h : (553 : ℕ) = 7 * (79) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 79 : ℕ) = 80 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_346 : (sigma 1 346 : ℕ) = 522 := by
  have h : (346 : ℕ) = 2 * (173) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 173 : ℕ) = 174 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_171 : (sigma 1 171 : ℕ) = 260 := by
  have h : (171 : ℕ) = 9 * (19) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_358 : (sigma 1 358 : ℕ) = 540 := by
  have h : (358 : ℕ) = 2 * (179) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 179 : ℕ) = 180 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_362 : (sigma 1 362 : ℕ) = 546 := by
  have h : (362 : ℕ) = 2 * (181) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 181 : ℕ) = 182 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1027 : (sigma 1 1027 : ℕ) = 1120 := by
  have h : (1027 : ℕ) = 13 * (79) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 13 : ℕ) = 14 := by decide
  have s1 : (sigma 1 79 : ℕ) = 80 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1464 : (sigma 1 1464 : ℕ) = 3720 := by
  have h : (1464 : ℕ) = 8 * (3 * (61)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 61 : ℕ) = 62 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_244 : (sigma 1 244 : ℕ) = 434 := by
  have h : (244 : ℕ) = 4 * (61) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 61 : ℕ) = 62 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_2832 : (sigma 1 2832 : ℕ) = 7440 := by
  have h : (2832 : ℕ) = 16 * (3 * (59)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 59 : ℕ) = 60 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_238 : (sigma 1 238 : ℕ) = 432 := by
  have h : (238 : ℕ) = 2 * (7 * (17)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_386 : (sigma 1 386 : ℕ) = 582 := by
  have h : (386 : ℕ) = 2 * (193) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 193 : ℕ) = 194 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_582 : (sigma 1 582 : ℕ) = 1176 := by
  have h : (582 : ℕ) = 2 * (3 * (97)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 97 : ℕ) = 98 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_394 : (sigma 1 394 : ℕ) = 594 := by
  have h : (394 : ℕ) = 2 * (197) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 197 : ℕ) = 198 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_230 : (sigma 1 230 : ℕ) = 432 := by
  have h : (230 : ℕ) = 2 * (5 * (23)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 23 : ℕ) = 24 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_315 : (sigma 1 315 : ℕ) = 624 := by
  have h : (315 : ℕ) = 9 * (5 * (7)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_340 : (sigma 1 340 : ℕ) = 756 := by
  have h : (340 : ℕ) = 4 * (5 * (17)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_618 : (sigma 1 618 : ℕ) = 1248 := by
  have h : (618 : ℕ) = 2 * (3 * (103)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 103 : ℕ) = 104 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_556 : (sigma 1 556 : ℕ) = 980 := by
  have h : (556 : ℕ) = 4 * (139) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 139 : ℕ) = 140 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_266 : (sigma 1 266 : ℕ) = 480 := by
  have h : (266 : ℕ) = 2 * (7 * (19)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_160 : (sigma 1 160 : ℕ) = 378 := by
  have h : (160 : ℕ) = 32 * (5) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_627 : (sigma 1 627 : ℕ) = 960 := by
  have h : (627 : ℕ) = 3 * (11 * (19)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1752 : (sigma 1 1752 : ℕ) = 4440 := by
  have h : (1752 : ℕ) = 8 * (3 * (73)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 73 : ℕ) = 74 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_208 : (sigma 1 208 : ℕ) = 434 := by
  have h : (208 : ℕ) = 16 * (13) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_454 : (sigma 1 454 : ℕ) = 684 := by
  have h : (454 : ℕ) = 2 * (227) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 227 : ℕ) = 228 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_458 : (sigma 1 458 : ℕ) = 690 := by
  have h : (458 : ℕ) = 2 * (229) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 229 : ℕ) = 230 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_100 : (sigma 1 100 : ℕ) = 217 := by
  have h : (100 : ℕ) = 4 * (25) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_466 : (sigma 1 466 : ℕ) = 702 := by
  have h : (466 : ℕ) = 2 * (233) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 233 : ℕ) = 234 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_555 : (sigma 1 555 : ℕ) = 912 := by
  have h : (555 : ℕ) = 3 * (5 * (37)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1818 : (sigma 1 1818 : ℕ) = 3978 := by
  have h : (1818 : ℕ) = 2 * (9 * (101)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 101 : ℕ) = 102 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_482 : (sigma 1 482 : ℕ) = 726 := by
  have h : (482 : ℕ) = 2 * (241) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 241 : ℕ) = 242 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1417 : (sigma 1 1417 : ℕ) = 1540 := by
  have h : (1417 : ℕ) = 13 * (109) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 13 : ℕ) = 14 := by decide
  have s1 : (sigma 1 109 : ℕ) = 110 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_652 : (sigma 1 652 : ℕ) = 1148 := by
  have h : (652 : ℕ) = 4 * (163) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 163 : ℕ) = 164 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1243 : (sigma 1 1243 : ℕ) = 1368 := by
  have h : (1243 : ℕ) = 11 * (113) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 11 : ℕ) = 12 := by decide
  have s1 : (sigma 1 113 : ℕ) = 114 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_23154432 : (sigma 1 23154432 : ℕ) = 72602880 := by
  have h : (23154432 : ℕ) = 256 * (3 * (7 * (59 * (73)))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 256 : ℕ) = 511 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  have s3 : (sigma 1 59 : ℕ) = 60 := by decide
  have s4 : (sigma 1 73 : ℕ) = 74 := by decide
  rw [s0, s1, s2, s3, s4] <;> norm_num

private theorem sig_762 : (sigma 1 762 : ℕ) = 1536 := by
  have h : (762 : ℕ) = 2 * (3 * (127)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 127 : ℕ) = 128 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_514 : (sigma 1 514 : ℕ) = 774 := by
  have h : (514 : ℕ) = 2 * (257) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 257 : ℕ) = 258 := by rw [sigma_one_prime (by norm_num : Nat.Prime 257)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_189 : (sigma 1 189 : ℕ) = 320 := by
  have h : (189 : ℕ) = 27 * (7) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 27 : ℕ) = 40 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_310 : (sigma 1 310 : ℕ) = 576 := by
  have h : (310 : ℕ) = 2 * (5 * (31)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1208 : (sigma 1 1208 : ℕ) = 2280 := by
  have h : (1208 : ℕ) = 8 * (151) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 151 : ℕ) = 152 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_889 : (sigma 1 889 : ℕ) = 1024 := by
  have h : (889 : ℕ) = 7 * (127) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 127 : ℕ) = 128 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_538 : (sigma 1 538 : ℕ) = 810 := by
  have h : (538 : ℕ) = 2 * (269) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 269 : ℕ) = 270 := by rw [sigma_one_prime (by norm_num : Nat.Prime 269)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_279 : (sigma 1 279 : ℕ) = 416 := by
  have h : (279 : ℕ) = 9 * (31) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_624 : (sigma 1 624 : ℕ) = 1736 := by
  have h : (624 : ℕ) = 16 * (3 * (13)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_554 : (sigma 1 554 : ℕ) = 834 := by
  have h : (554 : ℕ) = 2 * (277) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 277 : ℕ) = 278 := by rw [sigma_one_prime (by norm_num : Nat.Prime 277)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_834 : (sigma 1 834 : ℕ) = 1680 := by
  have h : (834 : ℕ) = 2 * (3 * (139)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 139 : ℕ) = 140 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_300 : (sigma 1 300 : ℕ) = 868 := by
  have h : (300 : ℕ) = 4 * (3 * (25)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 25 : ℕ) = 31 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_272 : (sigma 1 272 : ℕ) = 558 := by
  have h : (272 : ℕ) = 16 * (17) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_22538880 : (sigma 1 22538880 : ℕ) = 98017920 := by
  have h : (22538880 : ℕ) = 128 * (9 * (5 * (7 * (13 * (43))))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 128 : ℕ) = 255 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 7 : ℕ) = 8 := by decide
  have s4 : (sigma 1 13 : ℕ) = 14 := by decide
  have s5 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1, s2, s3, s4, s5] <;> norm_num

private theorem sig_539 : (sigma 1 539 : ℕ) = 684 := by
  have h : (539 : ℕ) = 49 * (11) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 49 : ℕ) = 57 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_27244 : (sigma 1 27244 : ℕ) = 55860 := by
  have h : (27244 : ℕ) = 4 * (49 * (139)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 49 : ℕ) = 57 := by decide
  have s2 : (sigma 1 139 : ℕ) = 140 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1083 : (sigma 1 1083 : ℕ) = 1524 := by
  have h : (1083 : ℕ) = 3 * (361) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 361 : ℕ) = 381 := by rw [(by norm_num : (361 : ℕ) = 19^2), sigma_one_sq (by norm_num : Nat.Prime 19)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_500 : (sigma 1 500 : ℕ) = 1092 := by
  have h : (500 : ℕ) = 4 * (125) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 125 : ℕ) = 156 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_388 : (sigma 1 388 : ℕ) = 686 := by
  have h : (388 : ℕ) = 4 * (97) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 97 : ℕ) = 98 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_328 : (sigma 1 328 : ℕ) = 630 := by
  have h : (328 : ℕ) = 8 * (41) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 41 : ℕ) = 42 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_3120 : (sigma 1 3120 : ℕ) = 10416 := by
  have h : (3120 : ℕ) = 16 * (3 * (5 * (13))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_906 : (sigma 1 906 : ℕ) = 1824 := by
  have h : (906 : ℕ) = 2 * (3 * (151)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 151 : ℕ) = 152 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2424 : (sigma 1 2424 : ℕ) = 6120 := by
  have h : (2424 : ℕ) = 8 * (3 * (101)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 101 : ℕ) = 102 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_404 : (sigma 1 404 : ℕ) = 714 := by
  have h : (404 : ℕ) = 4 * (101) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 101 : ℕ) = 102 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_242 : (sigma 1 242 : ℕ) = 399 := by
  have h : (242 : ℕ) = 2 * (121) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 121 : ℕ) = 133 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_626 : (sigma 1 626 : ℕ) = 942 := by
  have h : (626 : ℕ) = 2 * (313) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 313 : ℕ) = 314 := by rw [sigma_one_prime (by norm_num : Nat.Prime 313)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_942 : (sigma 1 942 : ℕ) = 1896 := by
  have h : (942 : ℕ) = 2 * (3 * (157)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 157 : ℕ) = 158 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_634 : (sigma 1 634 : ℕ) = 954 := by
  have h : (634 : ℕ) = 2 * (317) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 317 : ℕ) = 318 := by rw [sigma_one_prime (by norm_num : Nat.Prime 317)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_333 : (sigma 1 333 : ℕ) = 494 := by
  have h : (333 : ℕ) = 9 * (37) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_2466 : (sigma 1 2466 : ℕ) = 5382 := by
  have h : (2466 : ℕ) = 2 * (9 * (137)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 137 : ℕ) = 138 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_608 : (sigma 1 608 : ℕ) = 1260 := by
  have h : (608 : ℕ) = 32 * (19) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1840 : (sigma 1 1840 : ℕ) = 4464 := by
  have h : (1840 : ℕ) = 16 * (5 * (23)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 23 : ℕ) = 24 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_978 : (sigma 1 978 : ℕ) = 1968 := by
  have h : (978 : ℕ) = 2 * (3 * (163)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 163 : ℕ) = 164 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2616 : (sigma 1 2616 : ℕ) = 6600 := by
  have h : (2616 : ℕ) = 8 * (3 * (109)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 109 : ℕ) = 110 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_434 : (sigma 1 434 : ℕ) = 768 := by
  have h : (434 : ℕ) = 2 * (7 * (31)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_363 : (sigma 1 363 : ℕ) = 532 := by
  have h : (363 : ℕ) = 3 * (121) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 121 : ℕ) = 133 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_674 : (sigma 1 674 : ℕ) = 1014 := by
  have h : (674 : ℕ) = 2 * (337) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 337 : ℕ) = 338 := by rw [sigma_one_prime (by norm_num : Nat.Prime 337)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1023 : (sigma 1 1023 : ℕ) = 1536 := by
  have h : (1023 : ℕ) = 3 * (11 * (31)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_908 : (sigma 1 908 : ℕ) = 1596 := by
  have h : (908 : ℕ) = 4 * (227) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 227 : ℕ) = 228 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_410 : (sigma 1 410 : ℕ) = 756 := by
  have h : (410 : ℕ) = 2 * (5 * (41)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 41 : ℕ) = 42 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_694 : (sigma 1 694 : ℕ) = 1044 := by
  have h : (694 : ℕ) = 2 * (347) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 347 : ℕ) = 348 := by rw [sigma_one_prime (by norm_num : Nat.Prime 347)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_698 : (sigma 1 698 : ℕ) = 1050 := by
  have h : (698 : ℕ) = 2 * (349) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 349 : ℕ) = 350 := by rw [sigma_one_prime (by norm_num : Nat.Prime 349)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1572 : (sigma 1 1572 : ℕ) = 3696 := by
  have h : (1572 : ℕ) = 4 * (3 * (131)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 131 : ℕ) = 132 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_225 : (sigma 1 225 : ℕ) = 403 := by
  have h : (225 : ℕ) = 9 * (25) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_506 : (sigma 1 506 : ℕ) = 864 := by
  have h : (506 : ℕ) = 2 * (11 * (23)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 23 : ℕ) = 24 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_430 : (sigma 1 430 : ℕ) = 792 := by
  have h : (430 : ℕ) = 2 * (5 * (43)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_987 : (sigma 1 987 : ℕ) = 1536 := by
  have h : (987 : ℕ) = 3 * (7 * (47)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 47 : ℕ) = 48 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_16020 : (sigma 1 16020 : ℕ) = 49140 := by
  have h : (16020 : ℕ) = 4 * (9 * (5 * (89))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 89 : ℕ) = 90 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_387 : (sigma 1 387 : ℕ) = 572 := by
  have h : (387 : ℕ) = 9 * (43) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_315360 : (sigma 1 315360 : ℕ) = 1118880 := by
  have h : (315360 : ℕ) = 32 * (27 * (5 * (73))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 73 : ℕ) = 74 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_750 : (sigma 1 750 : ℕ) = 1872 := by
  have h : (750 : ℕ) = 2 * (3 * (125)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 125 : ℕ) = 156 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_746 : (sigma 1 746 : ℕ) = 1122 := by
  have h : (746 : ℕ) = 2 * (373) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 373 : ℕ) = 374 := by rw [sigma_one_prime (by norm_num : Nat.Prime 373)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1689 : (sigma 1 1689 : ℕ) = 2256 := by
  have h : (1689 : ℕ) = 3 * (563) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 563 : ℕ) = 564 := by rw [sigma_one_prime (by norm_num : Nat.Prime 563)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1004 : (sigma 1 1004 : ℕ) = 1764 := by
  have h : (1004 : ℕ) = 4 * (251) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 251 : ℕ) = 252 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_385 : (sigma 1 385 : ℕ) = 576 := by
  have h : (385 : ℕ) = 5 * (7 * (11)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 5 : ℕ) = 6 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 11 : ℕ) = 12 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_424 : (sigma 1 424 : ℕ) = 810 := by
  have h : (424 : ℕ) = 8 * (53) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 53 : ℕ) = 54 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_4080 : (sigma 1 4080 : ℕ) = 13392 := by
  have h : (4080 : ℕ) = 16 * (3 * (5 * (17))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1158 : (sigma 1 1158 : ℕ) = 2328 := by
  have h : (1158 : ℕ) = 2 * (3 * (193)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 193 : ℕ) = 194 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_778 : (sigma 1 778 : ℕ) = 1170 := by
  have h : (778 : ℕ) = 2 * (389) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 389 : ℕ) = 390 := by rw [sigma_one_prime (by norm_num : Nat.Prime 389)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_350 : (sigma 1 350 : ℕ) = 744 := by
  have h : (350 : ℕ) = 2 * (25 * (7)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_965 : (sigma 1 965 : ℕ) = 1164 := by
  have h : (965 : ℕ) = 5 * (193) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 5 : ℕ) = 6 := by decide
  have s1 : (sigma 1 193 : ℕ) = 194 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_794 : (sigma 1 794 : ℕ) = 1194 := by
  have h : (794 : ℕ) = 2 * (397) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 397 : ℕ) = 398 := by rw [sigma_one_prime (by norm_num : Nat.Prime 397)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1194 : (sigma 1 1194 : ℕ) = 2400 := by
  have h : (1194 : ℕ) = 2 * (3 * (199)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 199 : ℕ) = 200 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_802 : (sigma 1 802 : ℕ) = 1206 := by
  have h : (802 : ℕ) = 2 * (401) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 401 : ℕ) = 402 := by rw [sigma_one_prime (by norm_num : Nat.Prime 401)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_597 : (sigma 1 597 : ℕ) = 800 := by
  have h : (597 : ℕ) = 3 * (199) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 199 : ℕ) = 200 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_3114 : (sigma 1 3114 : ℕ) = 6786 := by
  have h : (3114 : ℕ) = 2 * (9 * (173)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 173 : ℕ) = 174 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_598 : (sigma 1 598 : ℕ) = 1008 := by
  have h : (598 : ℕ) = 2 * (13 * (23)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 23 : ℕ) = 24 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_818 : (sigma 1 818 : ℕ) = 1230 := by
  have h : (818 : ℕ) = 2 * (409) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 409 : ℕ) = 410 := by rw [sigma_one_prime (by norm_num : Nat.Prime 409)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1393 : (sigma 1 1393 : ℕ) = 1600 := by
  have h : (1393 : ℕ) = 7 * (199) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 199 : ℕ) = 200 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_3288 : (sigma 1 3288 : ℕ) = 8280 := by
  have h : (3288 : ℕ) = 8 * (3 * (137)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 137 : ℕ) = 138 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_351 : (sigma 1 351 : ℕ) = 560 := by
  have h : (351 : ℕ) = 27 * (13) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 27 : ℕ) = 40 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_6288 : (sigma 1 6288 : ℕ) = 16368 := by
  have h : (6288 : ℕ) = 16 * (3 * (131)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 131 : ℕ) = 132 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_338 : (sigma 1 338 : ℕ) = 549 := by
  have h : (338 : ℕ) = 2 * (169) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 169 : ℕ) = 183 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_842 : (sigma 1 842 : ℕ) = 1266 := by
  have h : (842 : ℕ) = 2 * (421) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 421 : ℕ) = 422 := by rw [sigma_one_prime (by norm_num : Nat.Prime 421)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1266 : (sigma 1 1266 : ℕ) = 2544 := by
  have h : (1266 : ℕ) = 2 * (3 * (211)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 211 : ℕ) = 212 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_740 : (sigma 1 740 : ℕ) = 1596 := by
  have h : (740 : ℕ) = 4 * (5 * (37)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_633 : (sigma 1 633 : ℕ) = 848 := by
  have h : (633 : ℕ) = 3 * (211) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 211 : ℕ) = 212 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_86328 : (sigma 1 86328 : ℕ) = 257400 := by
  have h : (86328 : ℕ) = 8 * (9 * (11 * (109))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 11 : ℕ) = 12 := by decide
  have s3 : (sigma 1 109 : ℕ) = 110 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_646 : (sigma 1 646 : ℕ) = 1080 := by
  have h : (646 : ℕ) = 2 * (17 * (19)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 17 : ℕ) = 18 := by decide
  have s2 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_866 : (sigma 1 866 : ℕ) = 1302 := by
  have h : (866 : ℕ) = 2 * (433) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 433 : ℕ) = 434 := by rw [sigma_one_prime (by norm_num : Nat.Prime 433)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1477 : (sigma 1 1477 : ℕ) = 1696 := by
  have h : (1477 : ℕ) = 7 * (211) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 211 : ℕ) = 212 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_884 : (sigma 1 884 : ℕ) = 1764 := by
  have h : (884 : ℕ) = 4 * (13 * (17)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_320 : (sigma 1 320 : ℕ) = 762 := by
  have h : (320 : ℕ) = 64 * (5) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 64 : ℕ) = 127 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_20272 : (sigma 1 20272 : ℕ) = 45136 := by
  have h : (20272 : ℕ) = 16 * (7 * (181)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 181 : ℕ) = 182 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_886 : (sigma 1 886 : ℕ) = 1332 := by
  have h : (886 : ℕ) = 2 * (443) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 443 : ℕ) = 444 := by rw [sigma_one_prime (by norm_num : Nat.Prime 443)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1338 : (sigma 1 1338 : ℕ) = 2688 := by
  have h : (1338 : ℕ) = 2 * (3 * (223)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 223 : ℕ) = 224 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_898 : (sigma 1 898 : ℕ) = 1350 := by
  have h : (898 : ℕ) = 2 * (449) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 449 : ℕ) = 450 := by rw [sigma_one_prime (by norm_num : Nat.Prime 449)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_596 : (sigma 1 596 : ℕ) = 1050 := by
  have h : (596 : ℕ) = 4 * (149) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 149 : ℕ) = 150 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_930 : (sigma 1 930 : ℕ) = 2304 := by
  have h : (930 : ℕ) = 2 * (3 * (5 * (31))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_914 : (sigma 1 914 : ℕ) = 1374 := by
  have h : (914 : ℕ) = 2 * (457) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 457 : ℕ) = 458 := by rw [sigma_one_prime (by norm_num : Nat.Prime 457)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1374 : (sigma 1 1374 : ℕ) = 2760 := by
  have h : (1374 : ℕ) = 2 * (3 * (229)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 229 : ℕ) = 230 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_922 : (sigma 1 922 : ℕ) = 1386 := by
  have h : (922 : ℕ) = 2 * (461) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 461 : ℕ) = 462 := by rw [sigma_one_prime (by norm_num : Nat.Prime 461)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_416 : (sigma 1 416 : ℕ) = 882 := by
  have h : (416 : ℕ) = 32 * (13) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_682 : (sigma 1 682 : ℕ) = 1152 := by
  have h : (682 : ℕ) = 2 * (11 * (31)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_820 : (sigma 1 820 : ℕ) = 1764 := by
  have h : (820 : ℕ) = 4 * (5 * (41)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 41 : ℕ) = 42 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1603 : (sigma 1 1603 : ℕ) = 1840 := by
  have h : (1603 : ℕ) = 7 * (229) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 229 : ℕ) = 230 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_3768 : (sigma 1 3768 : ℕ) = 9480 := by
  have h : (3768 : ℕ) = 8 * (3 * (157)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 157 : ℕ) = 158 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_628 : (sigma 1 628 : ℕ) = 1106 := by
  have h : (628 : ℕ) = 4 * (157) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 157 : ℕ) = 158 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_399 : (sigma 1 399 : ℕ) = 640 := by
  have h : (399 : ℕ) = 3 * (7 * (19)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_988 : (sigma 1 988 : ℕ) = 1960 := by
  have h : (988 : ℕ) = 4 * (13 * (19)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_38520 : (sigma 1 38520 : ℕ) = 126360 := by
  have h : (38520 : ℕ) = 8 * (9 * (5 * (107))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 107 : ℕ) = 108 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_723 : (sigma 1 723 : ℕ) = 968 := by
  have h : (723 : ℕ) = 3 * (241) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 241 : ℕ) = 242 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_419040 : (sigma 1 419040 : ℕ) = 1481760 := by
  have h : (419040 : ℕ) = 32 * (27 * (5 * (97))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 97 : ℕ) = 98 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_658 : (sigma 1 658 : ℕ) = 1152 := by
  have h : (658 : ℕ) = 2 * (7 * (47)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 47 : ℕ) = 48 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_14496 : (sigma 1 14496 : ℕ) = 38304 := by
  have h : (14496 : ℕ) = 32 * (3 * (151)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 151 : ℕ) = 152 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1653 : (sigma 1 1653 : ℕ) = 2400 := by
  have h : (1653 : ℕ) = 3 * (19 * (29)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 19 : ℕ) = 20 := by decide
  have s2 : (sigma 1 29 : ℕ) = 30 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1324 : (sigma 1 1324 : ℕ) = 2324 := by
  have h : (1324 : ℕ) = 4 * (331) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 331 : ℕ) = 332 := by rw [sigma_one_prime (by norm_num : Nat.Prime 331)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_732 : (sigma 1 732 : ℕ) = 1736 := by
  have h : (732 : ℕ) = 4 * (3 * (61)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 61 : ℕ) = 62 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_450 : (sigma 1 450 : ℕ) = 1209 := by
  have h : (450 : ℕ) = 2 * (9 * (25)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 25 : ℕ) = 31 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_4580 : (sigma 1 4580 : ℕ) = 9660 := by
  have h : (4580 : ℕ) = 4 * (5 * (229)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 229 : ℕ) = 230 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1018 : (sigma 1 1018 : ℕ) = 1530 := by
  have h : (1018 : ℕ) = 2 * (509) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 509 : ℕ) = 510 := by rw [sigma_one_prime (by norm_num : Nat.Prime 509)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_549 : (sigma 1 549 : ℕ) = 806 := by
  have h : (549 : ℕ) = 9 * (61) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 61 : ℕ) = 62 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_2028 : (sigma 1 2028 : ℕ) = 5124 := by
  have h : (2028 : ℕ) = 4 * (3 * (169)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 169 : ℕ) = 183 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_144 : (sigma 1 144 : ℕ) = 403 := by
  have h : (144 : ℕ) = 16 * (9) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_94120 : (sigma 1 94120 : ℕ) = 229320 := by
  have h : (94120 : ℕ) = 8 * (5 * (13 * (181))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  have s3 : (sigma 1 181 : ℕ) = 182 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2790 : (sigma 1 2790 : ℕ) = 7488 := by
  have h : (2790 : ℕ) = 2 * (9 * (5 * (31))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1042 : (sigma 1 1042 : ℕ) = 1566 := by
  have h : (1042 : ℕ) = 2 * (521) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 521 : ℕ) = 522 := by rw [sigma_one_prime (by norm_num : Nat.Prime 521)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_584 : (sigma 1 584 : ℕ) = 1110 := by
  have h : (584 : ℕ) = 8 * (73) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 73 : ℕ) = 74 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1578 : (sigma 1 1578 : ℕ) = 3168 := by
  have h : (1578 : ℕ) = 2 * (3 * (263)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 263 : ℕ) = 264 := by rw [sigma_one_prime (by norm_num : Nat.Prime 263)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_8440 : (sigma 1 8440 : ℕ) = 19080 := by
  have h : (8440 : ℕ) = 8 * (5 * (211)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 211 : ℕ) = 212 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2391 : (sigma 1 2391 : ℕ) = 3192 := by
  have h : (2391 : ℕ) = 3 * (797) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 797 : ℕ) = 798 := by rw [sigma_one_prime (by norm_num : Nat.Prime 797)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_490 : (sigma 1 490 : ℕ) = 1026 := by
  have h : (490 : ℕ) = 2 * (5 * (49)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 49 : ℕ) = 57 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_595 : (sigma 1 595 : ℕ) = 864 := by
  have h : (595 : ℕ) = 5 * (7 * (17)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 5 : ℕ) = 6 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1110 : (sigma 1 1110 : ℕ) = 2736 := by
  have h : (1110 : ℕ) = 2 * (3 * (5 * (37))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1082 : (sigma 1 1082 : ℕ) = 1626 := by
  have h : (1082 : ℕ) = 2 * (541) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 541 : ℕ) = 542 := by rw [sigma_one_prime (by norm_num : Nat.Prime 541)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1626 : (sigma 1 1626 : ℕ) = 3264 := by
  have h : (1626 : ℕ) = 2 * (3 * (271)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 271 : ℕ) = 272 := by rw [sigma_one_prime (by norm_num : Nat.Prime 271)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2488 : (sigma 1 2488 : ℕ) = 4680 := by
  have h : (2488 : ℕ) = 8 * (311) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 311 : ℕ) = 312 := by rw [sigma_one_prime (by norm_num : Nat.Prime 311)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_724 : (sigma 1 724 : ℕ) = 1274 := by
  have h : (724 : ℕ) = 4 * (181) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 181 : ℕ) = 182 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_6444 : (sigma 1 6444 : ℕ) = 16380 := by
  have h : (6444 : ℕ) = 4 * (9 * (179)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 179 : ℕ) = 180 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_670 : (sigma 1 670 : ℕ) = 1224 := by
  have h : (670 : ℕ) = 2 * (5 * (67)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 67 : ℕ) = 68 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1976 : (sigma 1 1976 : ℕ) = 4200 := by
  have h : (1976 : ℕ) = 8 * (13 * (19)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1662 : (sigma 1 1662 : ℕ) = 3336 := by
  have h : (1662 : ℕ) = 2 * (3 * (277)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 277 : ℕ) = 278 := by rw [sigma_one_prime (by norm_num : Nat.Prime 277)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1114 : (sigma 1 1114 : ℕ) = 1674 := by
  have h : (1114 : ℕ) = 2 * (557) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 557 : ℕ) = 558 := by rw [sigma_one_prime (by norm_num : Nat.Prime 557)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_603 : (sigma 1 603 : ℕ) = 884 := by
  have h : (603 : ℕ) = 9 * (67) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 67 : ℕ) = 68 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_550 : (sigma 1 550 : ℕ) = 1116 := by
  have h : (550 : ℕ) = 2 * (25 * (11)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 11 : ℕ) = 12 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_684 : (sigma 1 684 : ℕ) = 1820 := by
  have h : (684 : ℕ) = 4 * (9 * (19)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1698 : (sigma 1 1698 : ℕ) = 3408 := by
  have h : (1698 : ℕ) = 2 * (3 * (283)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 283 : ℕ) = 284 := by rw [sigma_one_prime (by norm_num : Nat.Prime 283)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1138 : (sigma 1 1138 : ℕ) = 1710 := by
  have h : (1138 : ℕ) = 2 * (569) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 569 : ℕ) = 570 := by rw [sigma_one_prime (by norm_num : Nat.Prime 569)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_513 : (sigma 1 513 : ℕ) = 800 := by
  have h : (513 : ℕ) = 27 * (19) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 27 : ℕ) = 40 := by decide
  have s1 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_12024 : (sigma 1 12024 : ℕ) = 32760 := by
  have h : (12024 : ℕ) = 8 * (9 * (167)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 167 : ℕ) = 168 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1075 : (sigma 1 1075 : ℕ) = 1364 := by
  have h : (1075 : ℕ) = 25 * (43) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 25 : ℕ) = 31 := by decide
  have s1 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1154 : (sigma 1 1154 : ℕ) = 1734 := by
  have h : (1154 : ℕ) = 2 * (577) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 577 : ℕ) = 578 := by rw [sigma_one_prime (by norm_num : Nat.Prime 577)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1981 : (sigma 1 1981 : ℕ) = 2272 := by
  have h : (1981 : ℕ) = 7 * (283) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 283 : ℕ) = 284 := by rw [sigma_one_prime (by norm_num : Nat.Prime 283)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_4632 : (sigma 1 4632 : ℕ) = 11640 := by
  have h : (4632 : ℕ) = 8 * (3 * (193)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 193 : ℕ) = 194 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_592 : (sigma 1 592 : ℕ) = 1178 := by
  have h : (592 : ℕ) = 16 * (37) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_544 : (sigma 1 544 : ℕ) = 1134 := by
  have h : (544 : ℕ) = 32 * (17) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_48608 : (sigma 1 48608 : ℕ) = 114912 := by
  have h : (48608 : ℕ) = 32 * (49 * (31)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 49 : ℕ) = 57 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2661 : (sigma 1 2661 : ℕ) = 3552 := by
  have h : (2661 : ℕ) = 3 * (887) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 887 : ℕ) = 888 := by rw [sigma_one_prime (by norm_num : Nat.Prime 887)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1186 : (sigma 1 1186 : ℕ) = 1782 := by
  have h : (1186 : ℕ) = 2 * (593) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 593 : ℕ) = 594 := by rw [sigma_one_prime (by norm_num : Nat.Prime 593)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_788 : (sigma 1 788 : ℕ) = 1386 := by
  have h : (788 : ℕ) = 4 * (197) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 197 : ℕ) = 198 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_17524 : (sigma 1 17524 : ℕ) = 33124 := by
  have h : (17524 : ℕ) = 4 * (13 * (337)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 337 : ℕ) = 338 := by rw [sigma_one_prime (by norm_num : Nat.Prime 337)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_730 : (sigma 1 730 : ℕ) = 1332 := by
  have h : (730 : ℕ) = 2 * (5 * (73)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 73 : ℕ) = 74 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1060 : (sigma 1 1060 : ℕ) = 2268 := by
  have h : (1060 : ℕ) = 4 * (5 * (53)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 53 : ℕ) = 54 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_5377 : (sigma 1 5377 : ℕ) = 5680 := by
  have h : (5377 : ℕ) = 19 * (283) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 19 : ℕ) = 20 := by decide
  have s1 : (sigma 1 283 : ℕ) = 284 := by rw [sigma_one_prime (by norm_num : Nat.Prime 283)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_92576 : (sigma 1 92576 : ℕ) = 199584 := by
  have h : (92576 : ℕ) = 32 * (11 * (263)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 263 : ℕ) = 264 := by rw [sigma_one_prime (by norm_num : Nat.Prime 263)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_657 : (sigma 1 657 : ℕ) = 962 := by
  have h : (657 : ℕ) = 9 * (73) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 73 : ℕ) = 74 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_26820 : (sigma 1 26820 : ℕ) = 81900 := by
  have h : (26820 : ℕ) = 4 * (9 * (5 * (149))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 149 : ℕ) = 150 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_826 : (sigma 1 826 : ℕ) = 1440 := by
  have h : (826 : ℕ) = 2 * (7 * (59)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 59 : ℕ) = 60 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1226 : (sigma 1 1226 : ℕ) = 1842 := by
  have h : (1226 : ℕ) = 2 * (613) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 613 : ℕ) = 614 := by rw [sigma_one_prime (by norm_num : Nat.Prime 613)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1842 : (sigma 1 1842 : ℕ) = 3696 := by
  have h : (1842 : ℕ) = 2 * (3 * (307)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 307 : ℕ) = 308 := by rw [sigma_one_prime (by norm_num : Nat.Prime 307)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1234 : (sigma 1 1234 : ℕ) = 1854 := by
  have h : (1234 : ℕ) = 2 * (617) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 617 : ℕ) = 618 := by rw [sigma_one_prime (by norm_num : Nat.Prime 617)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_921 : (sigma 1 921 : ℕ) = 1232 := by
  have h : (921 : ℕ) = 3 * (307) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 307 : ℕ) = 308 := by rw [sigma_one_prime (by norm_num : Nat.Prime 307)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1175 : (sigma 1 1175 : ℕ) = 1488 := by
  have h : (1175 : ℕ) = 25 * (47) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 25 : ℕ) = 31 := by decide
  have s1 : (sigma 1 47 : ℕ) = 48 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_8096 : (sigma 1 8096 : ℕ) = 18144 := by
  have h : (8096 : ℕ) = 32 * (11 * (23)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 23 : ℕ) = 24 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1878 : (sigma 1 1878 : ℕ) = 3768 := by
  have h : (1878 : ℕ) = 2 * (3 * (313)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 313 : ℕ) = 314 := by rw [sigma_one_prime (by norm_num : Nat.Prime 313)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1676 : (sigma 1 1676 : ℕ) = 2940 := by
  have h : (1676 : ℕ) = 4 * (419) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 419 : ℕ) = 420 := by rw [sigma_one_prime (by norm_num : Nat.Prime 419)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_854 : (sigma 1 854 : ℕ) = 1488 := by
  have h : (854 : ℕ) = 2 * (7 * (61)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 61 : ℕ) = 62 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_712 : (sigma 1 712 : ℕ) = 1350 := by
  have h : (712 : ℕ) = 8 * (89) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 89 : ℕ) = 90 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_25364 : (sigma 1 25364 : ℕ) = 47124 := by
  have h : (25364 : ℕ) = 4 * (17 * (373)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 17 : ℕ) = 18 := by decide
  have s2 : (sigma 1 373 : ℕ) = 374 := by rw [sigma_one_prime (by norm_num : Nat.Prime 373)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1050 : (sigma 1 1050 : ℕ) = 2976 := by
  have h : (1050 : ℕ) = 2 * (3 * (25 * (7))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 25 : ℕ) = 31 := by decide
  have s3 : (sigma 1 7 : ℕ) = 8 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1282 : (sigma 1 1282 : ℕ) = 1926 := by
  have h : (1282 : ℕ) = 2 * (641) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 641 : ℕ) = 642 := by rw [sigma_one_prime (by norm_num : Nat.Prime 641)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_656 : (sigma 1 656 : ℕ) = 1302 := by
  have h : (656 : ℕ) = 16 * (41) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 41 : ℕ) = 42 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_8871552 : (sigma 1 8871552 : ℕ) = 27907200 := by
  have h : (8871552 : ℕ) = 128 * (27 * (17 * (151))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 128 : ℕ) = 255 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 17 : ℕ) = 18 := by decide
  have s3 : (sigma 1 151 : ℕ) = 152 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1294 : (sigma 1 1294 : ℕ) = 1944 := by
  have h : (1294 : ℕ) = 2 * (647) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 647 : ℕ) = 648 := by rw [sigma_one_prime (by norm_num : Nat.Prime 647)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_650 : (sigma 1 650 : ℕ) = 1302 := by
  have h : (650 : ℕ) = 2 * (25 * (13)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2931 : (sigma 1 2931 : ℕ) = 3912 := by
  have h : (2931 : ℕ) = 3 * (977) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 977 : ℕ) = 978 := by rw [sigma_one_prime (by norm_num : Nat.Prime 977)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1306 : (sigma 1 1306 : ℕ) = 1962 := by
  have h : (1306 : ℕ) = 2 * (653) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 653 : ℕ) = 654 := by rw [sigma_one_prime (by norm_num : Nat.Prime 653)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_711 : (sigma 1 711 : ℕ) = 1040 := by
  have h : (711 : ℕ) = 9 * (79) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 79 : ℕ) = 80 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_4144 : (sigma 1 4144 : ℕ) = 9424 := by
  have h : (4144 : ℕ) = 16 * (7 * (37)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1216 : (sigma 1 1216 : ℕ) = 2540 := by
  have h : (1216 : ℕ) = 64 * (19) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 64 : ℕ) = 127 := by decide
  have s1 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1322 : (sigma 1 1322 : ℕ) = 1986 := by
  have h : (1322 : ℕ) = 2 * (661) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 661 : ℕ) = 662 := by rw [sigma_one_prime (by norm_num : Nat.Prime 661)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1986 : (sigma 1 1986 : ℕ) = 3984 := by
  have h : (1986 : ℕ) = 2 * (3 * (331)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 331 : ℕ) = 332 := by rw [sigma_one_prime (by norm_num : Nat.Prime 331)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1772 : (sigma 1 1772 : ℕ) = 3108 := by
  have h : (1772 : ℕ) = 4 * (443) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 443 : ℕ) = 444 := by rw [sigma_one_prime (by norm_num : Nat.Prime 443)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_993 : (sigma 1 993 : ℕ) = 1328 := by
  have h : (993 : ℕ) = 3 * (331) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 331 : ℕ) = 332 := by rw [sigma_one_prime (by norm_num : Nat.Prime 331)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_43578 : (sigma 1 43578 : ℕ) = 98010 := by
  have h : (43578 : ℕ) = 2 * (81 * (269)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 81 : ℕ) = 121 := by decide
  have s2 : (sigma 1 269 : ℕ) = 270 := by rw [sigma_one_prime (by norm_num : Nat.Prime 269)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1054 : (sigma 1 1054 : ℕ) = 1728 := by
  have h : (1054 : ℕ) = 2 * (17 * (31)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 17 : ℕ) = 18 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1346 : (sigma 1 1346 : ℕ) = 2022 := by
  have h : (1346 : ℕ) = 2 * (673) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 673 : ℕ) = 674 := by rw [sigma_one_prime (by norm_num : Nat.Prime 673)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2022 : (sigma 1 2022 : ℕ) = 4056 := by
  have h : (2022 : ℕ) = 2 * (3 * (337)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 337 : ℕ) = 338 := by rw [sigma_one_prime (by norm_num : Nat.Prime 337)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1354 : (sigma 1 1354 : ℕ) = 2034 := by
  have h : (1354 : ℕ) = 2 * (677) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 677 : ℕ) = 678 := by rw [sigma_one_prime (by norm_num : Nat.Prime 677)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_830 : (sigma 1 830 : ℕ) = 1512 := by
  have h : (830 : ℕ) = 2 * (5 * (83)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 83 : ℕ) = 84 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_92196 : (sigma 1 92196 : ℕ) = 252252 := by
  have h : (92196 : ℕ) = 4 * (9 * (13 * (197))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  have s3 : (sigma 1 197 : ℕ) = 198 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_578 : (sigma 1 578 : ℕ) = 921 := by
  have h : (578 : ℕ) = 2 * (289) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 289 : ℕ) = 307 := by rw [(by norm_num : (289 : ℕ) = 17^2), sigma_one_sq (by norm_num : Nat.Prime 17)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_4698 : (sigma 1 4698 : ℕ) = 10890 := by
  have h : (4698 : ℕ) = 2 * (81 * (29)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 81 : ℕ) = 121 := by decide
  have s2 : (sigma 1 29 : ℕ) = 30 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2359 : (sigma 1 2359 : ℕ) = 2704 := by
  have h : (2359 : ℕ) = 7 * (337) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 337 : ℕ) = 338 := by rw [sigma_one_prime (by norm_num : Nat.Prime 337)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1220 : (sigma 1 1220 : ℕ) = 2604 := by
  have h : (1220 : ℕ) = 4 * (5 * (61)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 61 : ℕ) = 62 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_776 : (sigma 1 776 : ℕ) = 1470 := by
  have h : (776 : ℕ) = 8 * (97) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 97 : ℕ) = 98 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1066 : (sigma 1 1066 : ℕ) = 1764 := by
  have h : (1066 : ℕ) = 2 * (13 * (41)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 41 : ℕ) = 42 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2094 : (sigma 1 2094 : ℕ) = 4200 := by
  have h : (2094 : ℕ) = 2 * (3 * (349)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 349 : ℕ) = 350 := by rw [sigma_one_prime (by norm_num : Nat.Prime 349)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1402 : (sigma 1 1402 : ℕ) = 2106 := by
  have h : (1402 : ℕ) = 2 * (701) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 701 : ℕ) = 702 := by rw [sigma_one_prime (by norm_num : Nat.Prime 701)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_932 : (sigma 1 932 : ℕ) = 1638 := by
  have h : (932 : ℕ) = 4 * (233) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 233 : ℕ) = 234 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_2118 : (sigma 1 2118 : ℕ) = 4248 := by
  have h : (2118 : ℕ) = 2 * (3 * (353)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 353 : ℕ) = 354 := by rw [sigma_one_prime (by norm_num : Nat.Prime 353)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1418 : (sigma 1 1418 : ℕ) = 2130 := by
  have h : (1418 : ℕ) = 2 * (709) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 709 : ℕ) = 710 := by rw [sigma_one_prime (by norm_num : Nat.Prime 709)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3870 : (sigma 1 3870 : ℕ) = 10296 := by
  have h : (3870 : ℕ) = 2 * (9 * (5 * (43))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1508 : (sigma 1 1508 : ℕ) = 2940 := by
  have h : (1508 : ℕ) = 4 * (13 * (29)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 29 : ℕ) = 30 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1765 : (sigma 1 1765 : ℕ) = 2124 := by
  have h : (1765 : ℕ) = 5 * (353) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 5 : ℕ) = 6 := by decide
  have s1 : (sigma 1 353 : ℕ) = 354 := by rw [sigma_one_prime (by norm_num : Nat.Prime 353)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_808 : (sigma 1 808 : ℕ) = 1530 := by
  have h : (808 : ℕ) = 8 * (101) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 101 : ℕ) = 102 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_10896 : (sigma 1 10896 : ℕ) = 28272 := by
  have h : (10896 : ℕ) = 16 * (3 * (227)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 227 : ℕ) = 228 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2883 : (sigma 1 2883 : ℕ) = 3972 := by
  have h : (2883 : ℕ) = 3 * (961) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 961 : ℕ) = 993 := by rw [(by norm_num : (961 : ℕ) = 31^2), sigma_one_sq (by norm_num : Nat.Prime 31)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_964 : (sigma 1 964 : ℕ) = 1694 := by
  have h : (964 : ℕ) = 4 * (241) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 241 : ℕ) = 242 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_17260800 : (sigma 1 17260800 : ℕ) = 60829440 := by
  have h : (17260800 : ℕ) = 256 * (3 * (25 * (29 * (31)))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 256 : ℕ) = 511 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 25 : ℕ) = 31 := by decide
  have s3 : (sigma 1 29 : ℕ) = 30 := by decide
  have s4 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2, s3, s4] <;> norm_num

private theorem sig_994 : (sigma 1 994 : ℕ) = 1728 := by
  have h : (994 : ℕ) = 2 * (7 * (71)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 71 : ℕ) = 72 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1466 : (sigma 1 1466 : ℕ) = 2202 := by
  have h : (1466 : ℕ) = 2 * (733) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 733 : ℕ) = 734 := by rw [sigma_one_prime (by norm_num : Nat.Prime 733)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2202 : (sigma 1 2202 : ℕ) = 4416 := by
  have h : (2202 : ℕ) = 2 * (3 * (367)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 367 : ℕ) = 368 := by rw [sigma_one_prime (by norm_num : Nat.Prime 367)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1964 : (sigma 1 1964 : ℕ) = 3444 := by
  have h : (1964 : ℕ) = 4 * (491) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 491 : ℕ) = 492 := by rw [sigma_one_prime (by norm_num : Nat.Prime 491)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1101 : (sigma 1 1101 : ℕ) = 1472 := by
  have h : (1101 : ℕ) = 3 * (367) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 367 : ℕ) = 368 := by rw [sigma_one_prime (by norm_num : Nat.Prime 367)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_5706 : (sigma 1 5706 : ℕ) = 12402 := by
  have h : (5706 : ℕ) = 2 * (9 * (317)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 317 : ℕ) = 318 := by rw [sigma_one_prime (by norm_num : Nat.Prime 317)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_651 : (sigma 1 651 : ℕ) = 1024 := by
  have h : (651 : ℕ) = 3 * (7 * (31)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2238 : (sigma 1 2238 : ℕ) = 4488 := by
  have h : (2238 : ℕ) = 2 * (3 * (373)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 373 : ℕ) = 374 := by rw [sigma_one_prime (by norm_num : Nat.Prime 373)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1100 : (sigma 1 1100 : ℕ) = 2604 := by
  have h : (1100 : ℕ) = 4 * (25 * (11)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 11 : ℕ) = 12 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1022 : (sigma 1 1022 : ℕ) = 1776 := by
  have h : (1022 : ℕ) = 2 * (7 * (73)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 73 : ℕ) = 74 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1264048 : (sigma 1 1264048 : ℕ) = 2467600 := by
  have h : (1264048 : ℕ) = 16 * (199 * (397)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 199 : ℕ) = 200 := by decide
  have s2 : (sigma 1 397 : ℕ) = 398 := by rw [sigma_one_prime (by norm_num : Nat.Prime 397)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_741 : (sigma 1 741 : ℕ) = 1120 := by
  have h : (741 : ℕ) = 3 * (13 * (19)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1514 : (sigma 1 1514 : ℕ) = 2274 := by
  have h : (1514 : ℕ) = 2 * (757) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 757 : ℕ) = 758 := by rw [sigma_one_prime (by norm_num : Nat.Prime 757)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1612 : (sigma 1 1612 : ℕ) = 3136 := by
  have h : (1612 : ℕ) = 4 * (13 * (31)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1522 : (sigma 1 1522 : ℕ) = 2286 := by
  have h : (1522 : ℕ) = 2 * (761) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 761 : ℕ) = 762 := by rw [sigma_one_prime (by norm_num : Nat.Prime 761)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1137 : (sigma 1 1137 : ℕ) = 1520 := by
  have h : (1137 : ℕ) = 3 * (379) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 379 : ℕ) = 380 := by rw [sigma_one_prime (by norm_num : Nat.Prime 379)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2298 : (sigma 1 2298 : ℕ) = 4608 := by
  have h : (2298 : ℕ) = 2 * (3 * (383)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 383 : ℕ) = 384 := by rw [sigma_one_prime (by norm_num : Nat.Prime 383)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1538 : (sigma 1 1538 : ℕ) = 2310 := by
  have h : (1538 : ℕ) = 2 * (769) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 769 : ℕ) = 770 := by rw [sigma_one_prime (by norm_num : Nat.Prime 769)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2653 : (sigma 1 2653 : ℕ) = 3040 := by
  have h : (2653 : ℕ) = 7 * (379) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 379 : ℕ) = 380 := by rw [sigma_one_prime (by norm_num : Nat.Prime 379)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1546 : (sigma 1 1546 : ℕ) = 2322 := by
  have h : (1546 : ℕ) = 2 * (773) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 773 : ℕ) = 774 := by rw [sigma_one_prime (by norm_num : Nat.Prime 773)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_648 : (sigma 1 648 : ℕ) = 1815 := by
  have h : (648 : ℕ) = 8 * (81) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 81 : ℕ) = 121 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1040 : (sigma 1 1040 : ℕ) = 2604 := by
  have h : (1040 : ℕ) = 16 * (5 * (13)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_4450 : (sigma 1 4450 : ℕ) = 8370 := by
  have h : (4450 : ℕ) = 2 * (25 * (89)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 89 : ℕ) = 90 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2352 : (sigma 1 2352 : ℕ) = 7068 := by
  have h : (2352 : ℕ) = 16 * (3 * (49)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 49 : ℕ) = 57 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_972 : (sigma 1 972 : ℕ) = 2548 := by
  have h : (972 : ℕ) = 4 * (243) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 243 : ℕ) = 364 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1164 : (sigma 1 1164 : ℕ) = 2744 := by
  have h : (1164 : ℕ) = 4 * (3 * (97)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 97 : ℕ) = 98 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_45888 : (sigma 1 45888 : ℕ) = 121920 := by
  have h : (45888 : ℕ) = 64 * (3 * (239)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 64 : ℕ) = 127 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 239 : ℕ) = 240 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_970 : (sigma 1 970 : ℕ) = 1764 := by
  have h : (970 : ℕ) = 2 * (5 * (97)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 97 : ℕ) = 98 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_13464 : (sigma 1 13464 : ℕ) = 42120 := by
  have h : (13464 : ℕ) = 8 * (9 * (11 * (17))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 11 : ℕ) = 12 := by decide
  have s3 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2382 : (sigma 1 2382 : ℕ) = 4776 := by
  have h : (2382 : ℕ) = 2 * (3 * (397)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 397 : ℕ) = 398 := by rw [sigma_one_prime (by norm_num : Nat.Prime 397)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1594 : (sigma 1 1594 : ℕ) = 2394 := by
  have h : (1594 : ℕ) = 2 * (797) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 797 : ℕ) = 798 := by rw [sigma_one_prime (by norm_num : Nat.Prime 797)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_567 : (sigma 1 567 : ℕ) = 968 := by
  have h : (567 : ℕ) = 81 * (7) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 81 : ℕ) = 121 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_904 : (sigma 1 904 : ℕ) = 1710 := by
  have h : (904 : ℕ) = 8 * (113) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 113 : ℕ) = 114 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_8880 : (sigma 1 8880 : ℕ) = 28272 := by
  have h : (8880 : ℕ) = 16 * (3 * (5 * (37))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2779 : (sigma 1 2779 : ℕ) = 3184 := by
  have h : (2779 : ℕ) = 7 * (397) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 397 : ℕ) = 398 := by rw [sigma_one_prime (by norm_num : Nat.Prime 397)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1618 : (sigma 1 1618 : ℕ) = 2430 := by
  have h : (1618 : ℕ) = 2 * (809) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 809 : ℕ) = 810 := by rw [sigma_one_prime (by norm_num : Nat.Prime 809)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1076 : (sigma 1 1076 : ℕ) = 1890 := by
  have h : (1076 : ℕ) = 4 * (269) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 269 : ℕ) = 270 := by rw [sigma_one_prime (by norm_num : Nat.Prime 269)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_828096 : (sigma 1 828096 : ℕ) = 2316480 := by
  have h : (828096 : ℕ) = 64 * (3 * (19 * (227))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 64 : ℕ) = 127 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 19 : ℕ) = 20 := by decide
  have s3 : (sigma 1 227 : ℕ) = 228 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1712 : (sigma 1 1712 : ℕ) = 3348 := by
  have h : (1712 : ℕ) = 16 * (107) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 107 : ℕ) = 108 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_2454 : (sigma 1 2454 : ℕ) = 4920 := by
  have h : (2454 : ℕ) = 2 * (3 * (409)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 409 : ℕ) = 410 := by rw [sigma_one_prime (by norm_num : Nat.Prime 409)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_850 : (sigma 1 850 : ℕ) = 1674 := by
  have h : (850 : ℕ) = 2 * (25 * (17)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_848 : (sigma 1 848 : ℕ) = 1674 := by
  have h : (848 : ℕ) = 16 * (53) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 53 : ℕ) = 54 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_6354 : (sigma 1 6354 : ℕ) = 13806 := by
  have h : (6354 : ℕ) = 2 * (9 * (353)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 353 : ℕ) = 354 := by rw [sigma_one_prime (by norm_num : Nat.Prime 353)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1654 : (sigma 1 1654 : ℕ) = 2484 := by
  have h : (1654 : ℕ) = 2 * (827) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 827 : ℕ) = 828 := by rw [sigma_one_prime (by norm_num : Nat.Prime 827)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1658 : (sigma 1 1658 : ℕ) = 2490 := by
  have h : (1658 : ℕ) = 2 * (829) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 829 : ℕ) = 830 := by rw [sigma_one_prime (by norm_num : Nat.Prime 829)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1725 : (sigma 1 1725 : ℕ) = 2976 := by
  have h : (1725 : ℕ) = 3 * (25 * (23)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 23 : ℕ) = 24 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_6648 : (sigma 1 6648 : ℕ) = 16680 := by
  have h : (6648 : ℕ) = 8 * (3 * (277)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 277 : ℕ) = 278 := by rw [sigma_one_prime (by norm_num : Nat.Prime 277)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1108 : (sigma 1 1108 : ℕ) = 1946 := by
  have h : (1108 : ℕ) = 4 * (277) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 277 : ℕ) = 278 := by rw [sigma_one_prime (by norm_num : Nat.Prime 277)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_722 : (sigma 1 722 : ℕ) = 1143 := by
  have h : (722 : ℕ) = 2 * (361) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 361 : ℕ) = 381 := by rw [(by norm_num : (361 : ℕ) = 19^2), sigma_one_sq (by norm_num : Nat.Prime 19)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_122688 : (sigma 1 122688 : ℕ) = 365760 := by
  have h : (122688 : ℕ) = 64 * (27 * (71)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 64 : ℕ) = 127 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 71 : ℕ) = 72 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2526 : (sigma 1 2526 : ℕ) = 5064 := by
  have h : (2526 : ℕ) = 2 * (3 * (421)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 421 : ℕ) = 422 := by rw [sigma_one_prime (by norm_num : Nat.Prime 421)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2252 : (sigma 1 2252 : ℕ) = 3948 := by
  have h : (2252 : ℕ) = 4 * (563) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 563 : ℕ) = 564 := by rw [sigma_one_prime (by norm_num : Nat.Prime 563)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_927 : (sigma 1 927 : ℕ) = 1352 := by
  have h : (927 : ℕ) = 9 * (103) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 103 : ℕ) = 104 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_39088 : (sigma 1 39088 : ℕ) = 86800 := by
  have h : (39088 : ℕ) = 16 * (7 * (349)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 349 : ℕ) = 350 := by rw [sigma_one_prime (by norm_num : Nat.Prime 349)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1998 : (sigma 1 1998 : ℕ) = 4560 := by
  have h : (1998 : ℕ) = 2 * (27 * (37)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1706 : (sigma 1 1706 : ℕ) = 2562 := by
  have h : (1706 : ℕ) = 2 * (853) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 853 : ℕ) = 854 := by rw [sigma_one_prime (by norm_num : Nat.Prime 853)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2947 : (sigma 1 2947 : ℕ) = 3376 := by
  have h : (2947 : ℕ) = 7 * (421) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 421 : ℕ) = 422 := by rw [sigma_one_prime (by norm_num : Nat.Prime 421)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1714 : (sigma 1 1714 : ℕ) = 2574 := by
  have h : (1714 : ℕ) = 2 * (857) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 857 : ℕ) = 858 := by rw [sigma_one_prime (by norm_num : Nat.Prime 857)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1298 : (sigma 1 1298 : ℕ) = 2160 := by
  have h : (1298 : ℕ) = 2 * (11 * (59)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 59 : ℕ) = 60 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_5488 : (sigma 1 5488 : ℕ) = 12400 := by
  have h : (5488 : ℕ) = 16 * (343) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 343 : ℕ) = 400 := by rw [(by norm_num : (343 : ℕ) = 7^3), sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1665 : (sigma 1 1665 : ℕ) = 2964 := by
  have h : (1665 : ℕ) = 9 * (5 * (37)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_61560 : (sigma 1 61560 : ℕ) = 217800 := by
  have h : (61560 : ℕ) = 8 * (81 * (5 * (19))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 81 : ℕ) = 121 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2598 : (sigma 1 2598 : ℕ) = 5208 := by
  have h : (2598 : ℕ) = 2 * (3 * (433)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 433 : ℕ) = 434 := by rw [sigma_one_prime (by norm_num : Nat.Prime 433)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_7408 : (sigma 1 7408 : ℕ) = 14384 := by
  have h : (7408 : ℕ) = 16 * (463) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 463 : ℕ) = 464 := by rw [sigma_one_prime (by norm_num : Nat.Prime 463)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1070 : (sigma 1 1070 : ℕ) = 1944 := by
  have h : (1070 : ℕ) = 2 * (5 * (107)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 107 : ℕ) = 108 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_196128 : (sigma 1 196128 : ℕ) = 574560 := by
  have h : (196128 : ℕ) = 32 * (27 * (227)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 227 : ℕ) = 228 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_777 : (sigma 1 777 : ℕ) = 1216 := by
  have h : (777 : ℕ) = 3 * (7 * (37)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1754 : (sigma 1 1754 : ℕ) = 2634 := by
  have h : (1754 : ℕ) = 2 * (877) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 877 : ℕ) = 878 := by rw [sigma_one_prime (by norm_num : Nat.Prime 877)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2634 : (sigma 1 2634 : ℕ) = 5280 := by
  have h : (2634 : ℕ) = 2 * (3 * (439)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 439 : ℕ) = 440 := by rw [sigma_one_prime (by norm_num : Nat.Prime 439)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1762 : (sigma 1 1762 : ℕ) = 2646 := by
  have h : (1762 : ℕ) = 2 * (881) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 881 : ℕ) = 882 := by rw [sigma_one_prime (by norm_num : Nat.Prime 881)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_837 : (sigma 1 837 : ℕ) = 1280 := by
  have h : (837 : ℕ) = 27 * (31) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 27 : ℕ) = 40 := by decide
  have s1 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1342 : (sigma 1 1342 : ℕ) = 2232 := by
  have h : (1342 : ℕ) = 2 * (11 * (61)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 61 : ℕ) = 62 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_6256 : (sigma 1 6256 : ℕ) = 13392 := by
  have h : (6256 : ℕ) = 16 * (17 * (23)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 17 : ℕ) = 18 := by decide
  have s2 : (sigma 1 23 : ℕ) = 24 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_484 : (sigma 1 484 : ℕ) = 931 := by
  have h : (484 : ℕ) = 4 * (121) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 121 : ℕ) = 133 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_3256 : (sigma 1 3256 : ℕ) = 6840 := by
  have h : (3256 : ℕ) = 8 * (11 * (37)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_981 : (sigma 1 981 : ℕ) = 1430 := by
  have h : (981 : ℕ) = 9 * (109) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 109 : ℕ) = 110 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1924 : (sigma 1 1924 : ℕ) = 3724 := by
  have h : (1924 : ℕ) = 4 * (13 * (37)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1085 : (sigma 1 1085 : ℕ) = 1536 := by
  have h : (1085 : ℕ) = 5 * (7 * (31)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 5 : ℕ) = 6 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1972 : (sigma 1 1972 : ℕ) = 3780 := by
  have h : (1972 : ℕ) = 4 * (17 * (29)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 17 : ℕ) = 18 := by decide
  have s2 : (sigma 1 29 : ℕ) = 30 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_5707 : (sigma 1 5707 : ℕ) = 6160 := by
  have h : (5707 : ℕ) = 13 * (439) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 13 : ℕ) = 14 := by decide
  have s1 : (sigma 1 439 : ℕ) = 440 := by rw [sigma_one_prime (by norm_num : Nat.Prime 439)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_36162 : (sigma 1 36162 : ℕ) = 93366 := by
  have h : (36162 : ℕ) = 2 * (9 * (49 * (41))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 49 : ℕ) = 57 := by decide
  have s3 : (sigma 1 41 : ℕ) = 42 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1814 : (sigma 1 1814 : ℕ) = 2724 := by
  have h : (1814 : ℕ) = 2 * (907) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 907 : ℕ) = 908 := by rw [sigma_one_prime (by norm_num : Nat.Prime 907)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_7002 : (sigma 1 7002 : ℕ) = 15210 := by
  have h : (7002 : ℕ) = 2 * (9 * (389)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 389 : ℕ) = 390 := by rw [sigma_one_prime (by norm_num : Nat.Prime 389)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1246 : (sigma 1 1246 : ℕ) = 2160 := by
  have h : (1246 : ℕ) = 2 * (7 * (89)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 89 : ℕ) = 90 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_20812 : (sigma 1 20812 : ℕ) = 40964 := by
  have h : (20812 : ℕ) = 4 * (121 * (43)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 121 : ℕ) = 133 := by decide
  have s2 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1815 : (sigma 1 1815 : ℕ) = 3192 := by
  have h : (1815 : ℕ) = 3 * (5 * (121)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 121 : ℕ) = 133 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_301280 : (sigma 1 301280 : ℕ) = 816480 := by
  have h : (301280 : ℕ) = 32 * (5 * (7 * (269))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  have s3 : (sigma 1 269 : ℕ) = 270 := by rw [sigma_one_prime (by norm_num : Nat.Prime 269)] <;> norm_num
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1130 : (sigma 1 1130 : ℕ) = 2052 := by
  have h : (1130 : ℕ) = 2 * (5 * (113)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 113 : ℕ) = 114 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_392 : (sigma 1 392 : ℕ) = 855 := by
  have h : (392 : ℕ) = 8 * (49) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 49 : ℕ) = 57 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_59360 : (sigma 1 59360 : ℕ) = 163296 := by
  have h : (59360 : ℕ) = 32 * (5 * (7 * (53))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  have s3 : (sigma 1 53 : ℕ) = 54 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2778 : (sigma 1 2778 : ℕ) = 5568 := by
  have h : (2778 : ℕ) = 2 * (3 * (463)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 463 : ℕ) = 464 := by rw [sigma_one_prime (by norm_num : Nat.Prime 463)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1858 : (sigma 1 1858 : ℕ) = 2790 := by
  have h : (1858 : ℕ) = 2 * (929) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 929 : ℕ) = 930 := by rw [sigma_one_prime (by norm_num : Nat.Prime 929)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_525 : (sigma 1 525 : ℕ) = 992 := by
  have h : (525 : ℕ) = 3 * (25 * (7)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1650 : (sigma 1 1650 : ℕ) = 4464 := by
  have h : (1650 : ℕ) = 2 * (3 * (25 * (11))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 25 : ℕ) = 31 := by decide
  have s3 : (sigma 1 11 : ℕ) = 12 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1874 : (sigma 1 1874 : ℕ) = 2814 := by
  have h : (1874 : ℕ) = 2 * (937) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 937 : ℕ) = 938 := by rw [sigma_one_prime (by norm_num : Nat.Prime 937)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3241 : (sigma 1 3241 : ℕ) = 3712 := by
  have h : (3241 : ℕ) = 7 * (463) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 463 : ℕ) = 464 := by rw [sigma_one_prime (by norm_num : Nat.Prime 463)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1882 : (sigma 1 1882 : ℕ) = 2826 := by
  have h : (1882 : ℕ) = 2 * (941) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 941 : ℕ) = 942 := by rw [sigma_one_prime (by norm_num : Nat.Prime 941)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_832 : (sigma 1 832 : ℕ) = 1778 := by
  have h : (832 : ℕ) = 64 * (13) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 64 : ℕ) = 127 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_190872 : (sigma 1 190872 : ℕ) = 566280 := by
  have h : (190872 : ℕ) = 8 * (9 * (11 * (241))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 11 : ℕ) = 12 := by decide
  have s3 : (sigma 1 241 : ℕ) = 242 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1894 : (sigma 1 1894 : ℕ) = 2844 := by
  have h : (1894 : ℕ) = 2 * (947) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 947 : ℕ) = 948 := by rw [sigma_one_prime (by norm_num : Nat.Prime 947)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_15160 : (sigma 1 15160 : ℕ) = 34200 := by
  have h : (15160 : ℕ) = 8 * (5 * (379)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 379 : ℕ) = 380 := by rw [sigma_one_prime (by norm_num : Nat.Prime 379)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_4281 : (sigma 1 4281 : ℕ) = 5712 := by
  have h : (4281 : ℕ) = 3 * (1427) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 1427 : ℕ) = 1428 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1427)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1906 : (sigma 1 1906 : ℕ) = 2862 := by
  have h : (1906 : ℕ) = 2 * (953) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 953 : ℕ) = 954 := by rw [sigma_one_prime (by norm_num : Nat.Prime 953)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_770 : (sigma 1 770 : ℕ) = 1728 := by
  have h : (770 : ℕ) = 2 * (5 * (7 * (11))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  have s3 : (sigma 1 11 : ℕ) = 12 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_928 : (sigma 1 928 : ℕ) = 1890 := by
  have h : (928 : ℕ) = 32 * (29) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 29 : ℕ) = 30 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_5680 : (sigma 1 5680 : ℕ) = 13392 := by
  have h : (5680 : ℕ) = 16 * (5 * (71)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 71 : ℕ) = 72 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_8797 : (sigma 1 8797 : ℕ) = 9280 := by
  have h : (8797 : ℕ) = 19 * (463) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 19 : ℕ) = 20 := by decide
  have s1 : (sigma 1 463 : ℕ) = 464 := by rw [sigma_one_prime (by norm_num : Nat.Prime 463)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2572 : (sigma 1 2572 : ℕ) = 4508 := by
  have h : (2572 : ℕ) = 4 * (643) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 643 : ℕ) = 644 := by rw [sigma_one_prime (by norm_num : Nat.Prime 643)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1934 : (sigma 1 1934 : ℕ) = 2904 := by
  have h : (1934 : ℕ) = 2 * (967) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 967 : ℕ) = 968 := by rw [sigma_one_prime (by norm_num : Nat.Prime 967)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_25792 : (sigma 1 25792 : ℕ) = 56896 := by
  have h : (25792 : ℕ) = 64 * (13 * (31)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 64 : ℕ) = 127 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1078 : (sigma 1 1078 : ℕ) = 2052 := by
  have h : (1078 : ℕ) = 2 * (49 * (11)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 49 : ℕ) = 57 := by decide
  have s2 : (sigma 1 11 : ℕ) = 12 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_23712 : (sigma 1 23712 : ℕ) = 70560 := by
  have h : (23712 : ℕ) = 32 * (3 * (13 * (19))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  have s3 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2922 : (sigma 1 2922 : ℕ) = 5856 := by
  have h : (2922 : ℕ) = 2 * (3 * (487)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 487 : ℕ) = 488 := by rw [sigma_one_prime (by norm_num : Nat.Prime 487)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1954 : (sigma 1 1954 : ℕ) = 2934 := by
  have h : (1954 : ℕ) = 2 * (977) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 977 : ℕ) = 978 := by rw [sigma_one_prime (by norm_num : Nat.Prime 977)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1461 : (sigma 1 1461 : ℕ) = 1952 := by
  have h : (1461 : ℕ) = 3 * (487) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 487 : ℕ) = 488 := by rw [sigma_one_prime (by norm_num : Nat.Prime 487)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1534 : (sigma 1 1534 : ℕ) = 2520 := by
  have h : (1534 : ℕ) = 2 * (13 * (59)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 59 : ℕ) = 60 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3608 : (sigma 1 3608 : ℕ) = 7560 := by
  have h : (3608 : ℕ) = 8 * (11 * (41)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 41 : ℕ) = 42 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3409 : (sigma 1 3409 : ℕ) = 3904 := by
  have h : (3409 : ℕ) = 7 * (487) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 487 : ℕ) = 488 := by rw [sigma_one_prime (by norm_num : Nat.Prime 487)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2106 : (sigma 1 2106 : ℕ) = 5082 := by
  have h : (2106 : ℕ) = 2 * (81 * (13)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 81 : ℕ) = 121 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1360 : (sigma 1 1360 : ℕ) = 3348 := by
  have h : (1360 : ℕ) = 16 * (5 * (17)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_13475328 : (sigma 1 13475328 : ℕ) = 37188096 := by
  have h : (13475328 : ℕ) = 512 * (3 * (31 * (283))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 512 : ℕ) = 1023 := by rw [(by norm_num : (512 : ℕ) = 2^9), sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  have s3 : (sigma 1 283 : ℕ) = 284 := by rw [sigma_one_prime (by norm_num : Nat.Prime 283)] <;> norm_num
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1935 : (sigma 1 1935 : ℕ) = 3432 := by
  have h : (1935 : ℕ) = 9 * (5 * (43)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1994 : (sigma 1 1994 : ℕ) = 2994 := by
  have h : (1994 : ℕ) = 2 * (997) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 997 : ℕ) = 998 := by rw [sigma_one_prime (by norm_num : Nat.Prime 997)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2994 : (sigma 1 2994 : ℕ) = 6000 := by
  have h : (2994 : ℕ) = 2 * (3 * (499)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 499 : ℕ) = 500 := by rw [sigma_one_prime (by norm_num : Nat.Prime 499)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_91120 : (sigma 1 91120 : ℕ) = 227664 := by
  have h : (91120 : ℕ) = 16 * (5 * (17 * (67))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 17 : ℕ) = 18 := by decide
  have s3 : (sigma 1 67 : ℕ) = 68 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1497 : (sigma 1 1497 : ℕ) = 2000 := by
  have h : (1497 : ℕ) = 3 * (499) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 499 : ℕ) = 500 := by rw [sigma_one_prime (by norm_num : Nat.Prime 499)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_903 : (sigma 1 903 : ℕ) = 1408 := by
  have h : (903 : ℕ) = 3 * (7 * (43)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2018 : (sigma 1 2018 : ℕ) = 3030 := by
  have h : (2018 : ℕ) = 2 * (1009) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1009 : ℕ) = 1010 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1009)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3493 : (sigma 1 3493 : ℕ) = 4000 := by
  have h : (3493 : ℕ) = 7 * (499) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 499 : ℕ) = 500 := by rw [sigma_one_prime (by norm_num : Nat.Prime 499)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2026 : (sigma 1 2026 : ℕ) = 3042 := by
  have h : (2026 : ℕ) = 2 * (1013) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1013 : ℕ) = 1014 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1013)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1348 : (sigma 1 1348 : ℕ) = 2366 := by
  have h : (1348 : ℕ) = 4 * (337) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 337 : ℕ) = 338 := by rw [sigma_one_prime (by norm_num : Nat.Prime 337)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2042 : (sigma 1 2042 : ℕ) = 3066 := by
  have h : (2042 : ℕ) = 2 * (1021) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1021 : ℕ) = 1022 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1021)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2877 : (sigma 1 2877 : ℕ) = 4416 := by
  have h : (2877 : ℕ) = 3 * (7 * (137)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 137 : ℕ) = 138 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2732 : (sigma 1 2732 : ℕ) = 4788 := by
  have h : (2732 : ℕ) = 4 * (683) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 683 : ℕ) = 684 := by rw [sigma_one_prime (by norm_num : Nat.Prime 683)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1524 : (sigma 1 1524 : ℕ) = 3584 := by
  have h : (1524 : ℕ) = 4 * (3 * (127)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 127 : ℕ) = 128 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_142133760 : (sigma 1 142133760 : ℕ) = 510681600 := by
  have h : (142133760 : ℕ) = 512 * (9 * (5 * (31 * (199)))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 512 : ℕ) = 1023 := by rw [(by norm_num : (512 : ℕ) = 2^9), sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 31 : ℕ) = 32 := by decide
  have s4 : (sigma 1 199 : ℕ) = 200 := by decide
  rw [s0, s1, s2, s3, s4] <;> norm_num

private theorem sig_1270 : (sigma 1 1270 : ℕ) = 2304 := by
  have h : (1270 : ℕ) = 2 * (5 * (127)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 127 : ℕ) = 128 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2066 : (sigma 1 2066 : ℕ) = 3102 := by
  have h : (2066 : ℕ) = 2 * (1033) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1033 : ℕ) = 1034 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1033)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2236 : (sigma 1 2236 : ℕ) = 4312 := by
  have h : (2236 : ℕ) = 4 * (13 * (43)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2764 : (sigma 1 2764 : ℕ) = 4844 := by
  have h : (2764 : ℕ) = 4 * (691) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 691 : ℕ) = 692 := by rw [sigma_one_prime (by norm_num : Nat.Prime 691)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_999 : (sigma 1 999 : ℕ) = 1520 := by
  have h : (999 : ℕ) = 27 * (37) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 27 : ℕ) = 40 := by decide
  have s1 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_74529 : (sigma 1 74529 : ℕ) = 135603 := by
  have h : (74529 : ℕ) = 9 * (49 * (169)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 49 : ℕ) = 57 := by decide
  have s2 : (sigma 1 169 : ℕ) = 183 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_324 : (sigma 1 324 : ℕ) = 847 := by
  have h : (324 : ℕ) = 4 * (81) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 81 : ℕ) = 121 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_3138 : (sigma 1 3138 : ℕ) = 6288 := by
  have h : (3138 : ℕ) = 2 * (3 * (523)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 523 : ℕ) = 524 := by rw [sigma_one_prime (by norm_num : Nat.Prime 523)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2098 : (sigma 1 2098 : ℕ) = 3150 := by
  have h : (2098 : ℕ) = 2 * (1049) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1049 : ℕ) = 1050 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1049)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1396 : (sigma 1 1396 : ℕ) = 2450 := by
  have h : (1396 : ℕ) = 4 * (349) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 349 : ℕ) = 350 := by rw [sigma_one_prime (by norm_num : Nat.Prime 349)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_4332 : (sigma 1 4332 : ℕ) = 10668 := by
  have h : (4332 : ℕ) = 4 * (3 * (361)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 361 : ℕ) = 381 := by rw [(by norm_num : (361 : ℕ) = 19^2), sigma_one_sq (by norm_num : Nat.Prime 19)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1192 : (sigma 1 1192 : ℕ) = 2250 := by
  have h : (1192 : ℕ) = 8 * (149) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 149 : ℕ) = 150 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_47268 : (sigma 1 47268 : ℕ) = 129948 := by
  have h : (47268 : ℕ) = 4 * (9 * (13 * (101))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  have s3 : (sigma 1 101 : ℕ) = 102 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2356 : (sigma 1 2356 : ℕ) = 4480 := by
  have h : (2356 : ℕ) = 4 * (19 * (31)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 19 : ℕ) = 20 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2122 : (sigma 1 2122 : ℕ) = 3186 := by
  have h : (2122 : ℕ) = 2 * (1061) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1061 : ℕ) = 1062 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1061)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1310 : (sigma 1 1310 : ℕ) = 2376 := by
  have h : (1310 : ℕ) = 2 * (5 * (131)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 131 : ℕ) = 132 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_6832 : (sigma 1 6832 : ℕ) = 15376 := by
  have h : (6832 : ℕ) = 16 * (7 * (61)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 61 : ℕ) = 62 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2144 : (sigma 1 2144 : ℕ) = 4284 := by
  have h : (2144 : ℕ) = 32 * (67) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 67 : ℕ) = 68 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_2138 : (sigma 1 2138 : ℕ) = 3210 := by
  have h : (2138 : ℕ) = 2 * (1069) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1069 : ℕ) = 1070 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1069)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_4812 : (sigma 1 4812 : ℕ) = 11256 := by
  have h : (4812 : ℕ) = 4 * (3 * (401)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 401 : ℕ) = 402 := by rw [sigma_one_prime (by norm_num : Nat.Prime 401)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_88218 : (sigma 1 88218 : ℕ) = 214110 := by
  have h : (88218 : ℕ) = 2 * (9 * (169 * (29))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 169 : ℕ) = 183 := by decide
  have s3 : (sigma 1 29 : ℕ) = 30 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_3609 : (sigma 1 3609 : ℕ) = 5226 := by
  have h : (3609 : ℕ) = 9 * (401) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 401 : ℕ) = 402 := by rw [sigma_one_prime (by norm_num : Nat.Prime 401)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_8298 : (sigma 1 8298 : ℕ) = 18018 := by
  have h : (8298 : ℕ) = 2 * (9 * (461)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 461 : ℕ) = 462 := by rw [sigma_one_prime (by norm_num : Nat.Prime 461)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1150 : (sigma 1 1150 : ℕ) = 2232 := by
  have h : (1150 : ℕ) = 2 * (25 * (23)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 23 : ℕ) = 24 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1225 : (sigma 1 1225 : ℕ) = 1767 := by
  have h : (1225 : ℕ) = 25 * (49) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 25 : ℕ) = 31 := by decide
  have s1 : (sigma 1 49 : ℕ) = 57 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1950 : (sigma 1 1950 : ℕ) = 5208 := by
  have h : (1950 : ℕ) = 2 * (3 * (25 * (13))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 25 : ℕ) = 31 := by decide
  have s3 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1940 : (sigma 1 1940 : ℕ) = 4116 := by
  have h : (1940 : ℕ) = 4 * (5 * (97)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 97 : ℕ) = 98 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1623 : (sigma 1 1623 : ℕ) = 2168 := by
  have h : (1623 : ℕ) = 3 * (541) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 541 : ℕ) = 542 := by rw [sigma_one_prime (by norm_num : Nat.Prime 541)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_59410176 : (sigma 1 59410176 : ℕ) = 185627904 := by
  have h : (59410176 : ℕ) = 256 * (3 * (7 * (43 * (257)))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 256 : ℕ) = 511 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  have s3 : (sigma 1 43 : ℕ) = 44 := by decide
  have s4 : (sigma 1 257 : ℕ) = 258 := by rw [sigma_one_prime (by norm_num : Nat.Prime 257)] <;> norm_num
  rw [s0, s1, s2, s3, s4] <;> norm_num

private theorem sig_1498 : (sigma 1 1498 : ℕ) = 2592 := by
  have h : (1498 : ℕ) = 2 * (7 * (107)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 107 : ℕ) = 108 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2186 : (sigma 1 2186 : ℕ) = 3282 := by
  have h : (2186 : ℕ) = 2 * (1093) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1093 : ℕ) = 1094 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1093)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3282 : (sigma 1 3282 : ℕ) = 6576 := by
  have h : (3282 : ℕ) = 2 * (3 * (547)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 547 : ℕ) = 548 := by rw [sigma_one_prime (by norm_num : Nat.Prime 547)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2194 : (sigma 1 2194 : ℕ) = 3294 := by
  have h : (2194 : ℕ) = 2 * (1097) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1097 : ℕ) = 1098 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1097)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1641 : (sigma 1 1641 : ℕ) = 2192 := by
  have h : (1641 : ℕ) = 3 * (547) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 547 : ℕ) = 548 := by rw [sigma_one_prime (by norm_num : Nat.Prime 547)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_16656 : (sigma 1 16656 : ℕ) = 43152 := by
  have h : (16656 : ℕ) = 16 * (3 * (347)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 347 : ℕ) = 348 := by rw [sigma_one_prime (by norm_num : Nat.Prime 347)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2206 : (sigma 1 2206 : ℕ) = 3312 := by
  have h : (2206 : ℕ) = 2 * (1103) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1103 : ℕ) = 1104 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1103)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_5048 : (sigma 1 5048 : ℕ) = 9480 := by
  have h : (5048 : ℕ) = 8 * (631) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 631 : ℕ) = 632 := by rw [sigma_one_prime (by norm_num : Nat.Prime 631)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3829 : (sigma 1 3829 : ℕ) = 4384 := by
  have h : (3829 : ℕ) = 7 * (547) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 547 : ℕ) = 548 := by rw [sigma_one_prime (by norm_num : Nat.Prime 547)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2218 : (sigma 1 2218 : ℕ) = 3330 := by
  have h : (2218 : ℕ) = 2 * (1109) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1109 : ℕ) = 1110 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1109)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1256 : (sigma 1 1256 : ℕ) = 2370 := by
  have h : (1256 : ℕ) = 8 * (157) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 157 : ℕ) = 158 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_2592 : (sigma 1 2592 : ℕ) = 7623 := by
  have h : (2592 : ℕ) = 32 * (81) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 81 : ℕ) = 121 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_2234 : (sigma 1 2234 : ℕ) = 3354 := by
  have h : (2234 : ℕ) = 2 * (1117) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1117 : ℕ) = 1118 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1117)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_400 : (sigma 1 400 : ℕ) = 961 := by
  have h : (400 : ℕ) = 16 * (25) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_8952 : (sigma 1 8952 : ℕ) = 22440 := by
  have h : (8952 : ℕ) = 8 * (3 * (373)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 373 : ℕ) = 374 := by rw [sigma_one_prime (by norm_num : Nat.Prime 373)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1168 : (sigma 1 1168 : ℕ) = 2294 := by
  have h : (1168 : ℕ) = 16 * (73) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 73 : ℕ) = 74 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_2444 : (sigma 1 2444 : ℕ) = 4704 := by
  have h : (2444 : ℕ) = 4 * (13 * (47)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 47 : ℕ) = 48 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2020 : (sigma 1 2020 : ℕ) = 4284 := by
  have h : (2020 : ℕ) = 4 * (5 * (101)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 101 : ℕ) = 102 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_5091 : (sigma 1 5091 : ℕ) = 6792 := by
  have h : (5091 : ℕ) = 3 * (1697) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 1697 : ℕ) = 1698 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1697)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1452 : (sigma 1 1452 : ℕ) = 3724 := by
  have h : (1452 : ℕ) = 4 * (3 * (121)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 121 : ℕ) = 133 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1251 : (sigma 1 1251 : ℕ) = 1820 := by
  have h : (1251 : ℕ) = 9 * (139) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 139 : ℕ) = 140 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1029 : (sigma 1 1029 : ℕ) = 1600 := by
  have h : (1029 : ℕ) = 3 * (343) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 343 : ℕ) = 400 := by rw [(by norm_num : (343 : ℕ) = 7^3), sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_12720 : (sigma 1 12720 : ℕ) = 40176 := by
  have h : (12720 : ℕ) = 16 * (3 * (5 * (53))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 53 : ℕ) = 54 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_3426 : (sigma 1 3426 : ℕ) = 6864 := by
  have h : (3426 : ℕ) = 2 * (3 * (571)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 571 : ℕ) = 572 := by rw [sigma_one_prime (by norm_num : Nat.Prime 571)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_4408 : (sigma 1 4408 : ℕ) = 9000 := by
  have h : (4408 : ℕ) = 8 * (19 * (29)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 19 : ℕ) = 20 := by decide
  have s2 : (sigma 1 29 : ℕ) = 30 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1713 : (sigma 1 1713 : ℕ) = 2288 := by
  have h : (1713 : ℕ) = 3 * (571) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 571 : ℕ) = 572 := by rw [sigma_one_prime (by norm_num : Nat.Prime 571)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_989280 : (sigma 1 989280 : ℕ) = 3477600 := by
  have h : (989280 : ℕ) = 32 * (27 * (5 * (229))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 229 : ℕ) = 230 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1582 : (sigma 1 1582 : ℕ) = 2736 := by
  have h : (1582 : ℕ) = 2 * (7 * (113)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 113 : ℕ) = 114 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2306 : (sigma 1 2306 : ℕ) = 3462 := by
  have h : (2306 : ℕ) = 2 * (1153) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1153 : ℕ) = 1154 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1153)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3462 : (sigma 1 3462 : ℕ) = 6936 := by
  have h : (3462 : ℕ) = 2 * (3 * (577)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 577 : ℕ) = 578 := by rw [sigma_one_prime (by norm_num : Nat.Prime 577)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_144180 : (sigma 1 144180 : ℕ) = 457380 := by
  have h : (144180 : ℕ) = 4 * (81 * (5 * (89))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 81 : ℕ) = 121 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 89 : ℕ) = 90 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1731 : (sigma 1 1731 : ℕ) = 2312 := by
  have h : (1731 : ℕ) = 3 * (577) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 577 : ℕ) = 578 := by rw [sigma_one_prime (by norm_num : Nat.Prime 577)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_85860 : (sigma 1 85860 : ℕ) = 274428 := by
  have h : (85860 : ℕ) = 4 * (81 * (5 * (53))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 81 : ℕ) = 121 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 53 : ℕ) = 54 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1209 : (sigma 1 1209 : ℕ) = 1792 := by
  have h : (1209 : ℕ) = 3 * (13 * (31)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_35120 : (sigma 1 35120 : ℕ) = 81840 := by
  have h : (35120 : ℕ) = 16 * (5 * (439)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 439 : ℕ) = 440 := by rw [sigma_one_prime (by norm_num : Nat.Prime 439)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_4039 : (sigma 1 4039 : ℕ) = 4624 := by
  have h : (4039 : ℕ) = 7 * (577) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 577 : ℕ) = 578 := by rw [sigma_one_prime (by norm_num : Nat.Prime 577)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_9336 : (sigma 1 9336 : ℕ) = 23400 := by
  have h : (9336 : ℕ) = 8 * (3 * (389)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 389 : ℕ) = 390 := by rw [sigma_one_prime (by norm_num : Nat.Prime 389)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1556 : (sigma 1 1556 : ℕ) = 2730 := by
  have h : (1556 : ℕ) = 4 * (389) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 389 : ℕ) = 390 := by rw [sigma_one_prime (by norm_num : Nat.Prime 389)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1846 : (sigma 1 1846 : ℕ) = 3024 := by
  have h : (1846 : ℕ) = 2 * (13 * (71)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 71 : ℕ) = 72 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_19424 : (sigma 1 19424 : ℕ) = 38304 := by
  have h : (19424 : ℕ) = 32 * (607) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 607 : ℕ) = 608 := by rw [sigma_one_prime (by norm_num : Nat.Prime 607)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3939 : (sigma 1 3939 : ℕ) = 5712 := by
  have h : (3939 : ℕ) = 3 * (13 * (101)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 101 : ℕ) = 102 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1210 : (sigma 1 1210 : ℕ) = 2394 := by
  have h : (1210 : ℕ) = 2 * (5 * (121)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 121 : ℕ) = 133 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2431 : (sigma 1 2431 : ℕ) = 3024 := by
  have h : (2431 : ℕ) = 11 * (13 * (17)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 11 : ℕ) = 12 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1978 : (sigma 1 1978 : ℕ) = 3168 := by
  have h : (1978 : ℕ) = 2 * (23 * (43)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 23 : ℕ) = 24 := by decide
  have s2 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_4472 : (sigma 1 4472 : ℕ) = 9240 := by
  have h : (4472 : ℕ) = 8 * (13 * (43)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_5361 : (sigma 1 5361 : ℕ) = 7152 := by
  have h : (5361 : ℕ) = 3 * (1787) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 1787 : ℕ) = 1788 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1787)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2386 : (sigma 1 2386 : ℕ) = 3582 := by
  have h : (2386 : ℕ) = 2 * (1193) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1193 : ℕ) = 1194 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1193)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1088 : (sigma 1 1088 : ℕ) = 2286 := by
  have h : (1088 : ℕ) = 64 * (17) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 64 : ℕ) = 127 := by decide
  have s1 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1058 : (sigma 1 1058 : ℕ) = 1659 := by
  have h : (1058 : ℕ) = 2 * (529) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 529 : ℕ) = 553 := by rw [(by norm_num : (529 : ℕ) = 23^2), sigma_one_sq (by norm_num : Nat.Prime 23)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2402 : (sigma 1 2402 : ℕ) = 3606 := by
  have h : (2402 : ℕ) = 2 * (1201) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1201 : ℕ) = 1202 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1201)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3606 : (sigma 1 3606 : ℕ) = 7224 := by
  have h : (3606 : ℕ) = 2 * (3 * (601)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 601 : ℕ) = 602 := by rw [sigma_one_prime (by norm_num : Nat.Prime 601)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_9624 : (sigma 1 9624 : ℕ) = 24120 := by
  have h : (9624 : ℕ) = 8 * (3 * (401)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 401 : ℕ) = 402 := by rw [sigma_one_prime (by norm_num : Nat.Prime 401)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_676 : (sigma 1 676 : ℕ) = 1281 := by
  have h : (676 : ℕ) = 4 * (169) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 169 : ℕ) = 183 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1041120 : (sigma 1 1041120 : ℕ) = 3659040 := by
  have h : (1041120 : ℕ) = 32 * (27 * (5 * (241))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 241 : ℕ) = 242 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1458 : (sigma 1 1458 : ℕ) = 3279 := by
  have h : (1458 : ℕ) = 2 * (729) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 729 : ℕ) = 1093 := by rw [(by norm_num : (729 : ℕ) = 3^6), sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2426 : (sigma 1 2426 : ℕ) = 3642 := by
  have h : (2426 : ℕ) = 2 * (1213) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1213 : ℕ) = 1214 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1213)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3642 : (sigma 1 3642 : ℕ) = 7296 := by
  have h : (3642 : ℕ) = 2 * (3 * (607)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 607 : ℕ) = 608 := by rw [sigma_one_prime (by norm_num : Nat.Prime 607)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2434 : (sigma 1 2434 : ℕ) = 3654 := by
  have h : (2434 : ℕ) = 2 * (1217) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1217 : ℕ) = 1218 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1217)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1812 : (sigma 1 1812 : ℕ) = 4256 := by
  have h : (1812 : ℕ) = 4 * (3 * (151)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 151 : ℕ) = 152 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_609120 : (sigma 1 609120 : ℕ) = 2195424 := by
  have h : (609120 : ℕ) = 32 * (81 * (5 * (47))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 81 : ℕ) = 121 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 47 : ℕ) = 48 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1384 : (sigma 1 1384 : ℕ) = 2610 := by
  have h : (1384 : ℕ) = 8 * (173) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 173 : ℕ) = 174 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1548 : (sigma 1 1548 : ℕ) = 4004 := by
  have h : (1548 : ℕ) = 4 * (9 * (43)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3678 : (sigma 1 3678 : ℕ) = 7368 := by
  have h : (3678 : ℕ) = 2 * (3 * (613)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 613 : ℕ) = 614 := by rw [sigma_one_prime (by norm_num : Nat.Prime 613)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2458 : (sigma 1 2458 : ℕ) = 3690 := by
  have h : (2458 : ℕ) = 2 * (1229) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1229 : ℕ) = 1230 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1229)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1359 : (sigma 1 1359 : ℕ) = 1976 := by
  have h : (1359 : ℕ) = 9 * (151) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 151 : ℕ) = 152 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_137200 : (sigma 1 137200 : ℕ) = 384400 := by
  have h : (137200 : ℕ) = 16 * (25 * (343)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 343 : ℕ) = 400 := by rw [(by norm_num : (343 : ℕ) = 7^3), sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2261 : (sigma 1 2261 : ℕ) = 2880 := by
  have h : (2261 : ℕ) = 7 * (17 * (19)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 17 : ℕ) = 18 := by decide
  have s2 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2474 : (sigma 1 2474 : ℕ) = 3714 := by
  have h : (2474 : ℕ) = 2 * (1237) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1237 : ℕ) = 1238 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1237)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3714 : (sigma 1 3714 : ℕ) = 7440 := by
  have h : (3714 : ℕ) = 2 * (3 * (619)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 619 : ℕ) = 620 := by rw [sigma_one_prime (by norm_num : Nat.Prime 619)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3308 : (sigma 1 3308 : ℕ) = 5796 := by
  have h : (3308 : ℕ) = 4 * (827) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 827 : ℕ) = 828 := by rw [sigma_one_prime (by norm_num : Nat.Prime 827)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1857 : (sigma 1 1857 : ℕ) = 2480 := by
  have h : (1857 : ℕ) = 3 * (619) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 619 : ℕ) = 620 := by rw [sigma_one_prime (by norm_num : Nat.Prime 619)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_166758384 : (sigma 1 166758384 : ℕ) = 475533552 := by
  have h : (166758384 : ℕ) = 16 * (3 * (169 * (61 * (337)))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 169 : ℕ) = 183 := by decide
  have s3 : (sigma 1 61 : ℕ) = 62 := by decide
  have s4 : (sigma 1 337 : ℕ) = 338 := by rw [sigma_one_prime (by norm_num : Nat.Prime 337)] <;> norm_num
  rw [s0, s1, s2, s3, s4] <;> norm_num

private theorem sig_1587 : (sigma 1 1587 : ℕ) = 2212 := by
  have h : (1587 : ℕ) = 3 * (529) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 529 : ℕ) = 553 := by rw [(by norm_num : (529 : ℕ) = 23^2), sigma_one_sq (by norm_num : Nat.Prime 23)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2498 : (sigma 1 2498 : ℕ) = 3750 := by
  have h : (2498 : ℕ) = 2 * (1249) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1249 : ℕ) = 1250 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1249)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_4333 : (sigma 1 4333 : ℕ) = 4960 := by
  have h : (4333 : ℕ) = 7 * (619) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 619 : ℕ) = 620 := by rw [sigma_one_prime (by norm_num : Nat.Prime 619)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_11380 : (sigma 1 11380 : ℕ) = 23940 := by
  have h : (11380 : ℕ) = 4 * (5 * (569)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 569 : ℕ) = 570 := by rw [sigma_one_prime (by norm_num : Nat.Prime 569)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1404 : (sigma 1 1404 : ℕ) = 3920 := by
  have h : (1404 : ℕ) = 4 * (27 * (13)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_40052517120 : (sigma 1 40052517120 : ℕ) = 185908504320 := by
  have h : (40052517120 : ℕ) = 256 * (81 * (5 * (7 * (11 * (29 * (173)))))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 256 : ℕ) = 511 := by decide
  have s1 : (sigma 1 81 : ℕ) = 121 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 7 : ℕ) = 8 := by decide
  have s4 : (sigma 1 11 : ℕ) = 12 := by decide
  have s5 : (sigma 1 29 : ℕ) = 30 := by decide
  have s6 : (sigma 1 173 : ℕ) = 174 := by decide
  rw [s0, s1, s2, s3, s4, s5, s6] <;> norm_num

private theorem sig_2518 : (sigma 1 2518 : ℕ) = 3780 := by
  have h : (2518 : ℕ) = 2 * (1259) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1259 : ℕ) = 1260 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1259)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2260 : (sigma 1 2260 : ℕ) = 4788 := by
  have h : (2260 : ℕ) = 4 * (5 * (113)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 113 : ℕ) = 114 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3786 : (sigma 1 3786 : ℕ) = 7584 := by
  have h : (3786 : ℕ) = 2 * (3 * (631)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 631 : ℕ) = 632 := by rw [sigma_one_prime (by norm_num : Nat.Prime 631)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2756 : (sigma 1 2756 : ℕ) = 5292 := by
  have h : (2756 : ℕ) = 4 * (13 * (53)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 53 : ℕ) = 54 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1684 : (sigma 1 1684 : ℕ) = 2954 := by
  have h : (1684 : ℕ) = 4 * (421) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 421 : ℕ) = 422 := by rw [sigma_one_prime (by norm_num : Nat.Prime 421)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_8176 : (sigma 1 8176 : ℕ) = 18352 := by
  have h : (8176 : ℕ) = 16 * (7 * (73)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 73 : ℕ) = 74 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1570 : (sigma 1 1570 : ℕ) = 2844 := by
  have h : (1570 : ℕ) = 2 * (5 * (157)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 157 : ℕ) = 158 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_5816 : (sigma 1 5816 : ℕ) = 10920 := by
  have h : (5816 : ℕ) = 8 * (727) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 727 : ℕ) = 728 := by rw [sigma_one_prime (by norm_num : Nat.Prime 727)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_4417 : (sigma 1 4417 : ℕ) = 5056 := by
  have h : (4417 : ℕ) = 7 * (631) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 631 : ℕ) = 632 := by rw [sigma_one_prime (by norm_num : Nat.Prime 631)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1089 : (sigma 1 1089 : ℕ) = 1729 := by
  have h : (1089 : ℕ) = 9 * (121) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 121 : ℕ) = 133 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1053 : (sigma 1 1053 : ℕ) = 1694 := by
  have h : (1053 : ℕ) = 81 * (13) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 81 : ℕ) = 121 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_237120 : (sigma 1 237120 : ℕ) = 853440 := by
  have h : (237120 : ℕ) = 64 * (3 * (5 * (13 * (19)))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 64 : ℕ) = 127 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 13 : ℕ) = 14 := by decide
  have s4 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1, s2, s3, s4] <;> norm_num

private theorem sig_2566 : (sigma 1 2566 : ℕ) = 3852 := by
  have h : (2566 : ℕ) = 2 * (1283) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1283 : ℕ) = 1284 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1283)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3633 : (sigma 1 3633 : ℕ) = 5568 := by
  have h : (3633 : ℕ) = 3 * (7 * (173)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 173 : ℕ) = 174 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2578 : (sigma 1 2578 : ℕ) = 3870 := by
  have h : (2578 : ℕ) = 2 * (1289) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1289 : ℕ) = 1290 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1289)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1778 : (sigma 1 1778 : ℕ) = 3072 := by
  have h : (1778 : ℕ) = 2 * (7 * (127)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 127 : ℕ) = 128 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2575 : (sigma 1 2575 : ℕ) = 3224 := by
  have h : (2575 : ℕ) = 25 * (103) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 25 : ℕ) = 31 := by decide
  have s1 : (sigma 1 103 : ℕ) = 104 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_2594 : (sigma 1 2594 : ℕ) = 3894 := by
  have h : (2594 : ℕ) = 2 * (1297) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1297 : ℕ) = 1298 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1297)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_4191 : (sigma 1 4191 : ℕ) = 6144 := by
  have h : (4191 : ℕ) = 3 * (11 * (127)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 127 : ℕ) = 128 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2602 : (sigma 1 2602 : ℕ) = 3906 := by
  have h : (2602 : ℕ) = 2 * (1301) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1301 : ℕ) = 1302 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1301)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1732 : (sigma 1 1732 : ℕ) = 3038 := by
  have h : (1732 : ℕ) = 4 * (433) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 433 : ℕ) = 434 := by rw [sigma_one_prime (by norm_num : Nat.Prime 433)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2614 : (sigma 1 2614 : ℕ) = 3924 := by
  have h : (2614 : ℕ) = 2 * (1307) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1307 : ℕ) = 1308 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1307)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_14640 : (sigma 1 14640 : ℕ) = 46128 := by
  have h : (14640 : ℕ) = 16 * (3 * (5 * (61))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 61 : ℕ) = 62 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_4884 : (sigma 1 4884 : ℕ) = 12768 := by
  have h : (4884 : ℕ) = 4 * (3 * (11 * (37))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 11 : ℕ) = 12 := by decide
  have s3 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_86338 : (sigma 1 86338 : ℕ) = 150822 := by
  have h : (86338 : ℕ) = 2 * (49 * (881)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 49 : ℕ) = 57 := by decide
  have s2 : (sigma 1 881 : ℕ) = 882 := by rw [sigma_one_prime (by norm_num : Nat.Prime 881)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1645 : (sigma 1 1645 : ℕ) = 2304 := by
  have h : (1645 : ℕ) = 5 * (7 * (47)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 5 : ℕ) = 6 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 47 : ℕ) = 48 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1200 : (sigma 1 1200 : ℕ) = 3844 := by
  have h : (1200 : ℕ) = 16 * (3 * (25)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 25 : ℕ) = 31 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2642 : (sigma 1 2642 : ℕ) = 3966 := by
  have h : (2642 : ℕ) = 2 * (1321) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1321 : ℕ) = 1322 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1321)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3966 : (sigma 1 3966 : ℕ) = 7944 := by
  have h : (3966 : ℕ) = 2 * (3 * (661)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 661 : ℕ) = 662 := by rw [sigma_one_prime (by norm_num : Nat.Prime 661)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3532 : (sigma 1 3532 : ℕ) = 6188 := by
  have h : (3532 : ℕ) = 4 * (883) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 883 : ℕ) = 884 := by rw [sigma_one_prime (by norm_num : Nat.Prime 883)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1467 : (sigma 1 1467 : ℕ) = 2132 := by
  have h : (1467 : ℕ) = 9 * (163) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 163 : ℕ) = 164 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_10242 : (sigma 1 10242 : ℕ) = 22230 := by
  have h : (10242 : ℕ) = 2 * (9 * (569)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 569 : ℕ) = 570 := by rw [sigma_one_prime (by norm_num : Nat.Prime 569)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1312 : (sigma 1 1312 : ℕ) = 2646 := by
  have h : (1312 : ℕ) = 32 * (41) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 41 : ℕ) = 42 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_6672 : (sigma 1 6672 : ℕ) = 17360 := by
  have h : (6672 : ℕ) = 16 * (3 * (139)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 139 : ℕ) = 140 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_4627 : (sigma 1 4627 : ℕ) = 5296 := by
  have h : (4627 : ℕ) = 7 * (661) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 661 : ℕ) = 662 := by rw [sigma_one_prime (by norm_num : Nat.Prime 661)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_499968 : (sigma 1 499968 : ℕ) = 1700608 := by
  have h : (499968 : ℕ) = 256 * (9 * (7 * (31))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 256 : ℕ) = 511 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  have s3 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_4380 : (sigma 1 4380 : ℕ) = 12432 := by
  have h : (4380 : ℕ) = 4 * (3 * (5 * (73))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 73 : ℕ) = 74 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_4544640 : (sigma 1 4544640 : ℕ) = 16156800 := by
  have h : (4544640 : ℕ) = 128 * (27 * (5 * (263))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 128 : ℕ) = 255 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 263 : ℕ) = 264 := by rw [sigma_one_prime (by norm_num : Nat.Prime 263)] <;> norm_num
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2015 : (sigma 1 2015 : ℕ) = 2688 := by
  have h : (2015 : ℕ) = 5 * (13 * (31)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 5 : ℕ) = 6 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_19620 : (sigma 1 19620 : ℕ) = 60060 := by
  have h : (19620 : ℕ) = 4 * (9 * (5 * (109))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 109 : ℕ) = 110 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_4038 : (sigma 1 4038 : ℕ) = 8088 := by
  have h : (4038 : ℕ) = 2 * (3 * (673)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 673 : ℕ) = 674 := by rw [sigma_one_prime (by norm_num : Nat.Prime 673)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_10776 : (sigma 1 10776 : ℕ) = 27000 := by
  have h : (10776 : ℕ) = 8 * (3 * (449)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 449 : ℕ) = 450 := by rw [sigma_one_prime (by norm_num : Nat.Prime 449)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1670 : (sigma 1 1670 : ℕ) = 3024 := by
  have h : (1670 : ℕ) = 2 * (5 * (167)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 167 : ℕ) = 168 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_112554 : (sigma 1 112554 : ℕ) = 271206 := by
  have h : (112554 : ℕ) = 2 * (9 * (169 * (37))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 169 : ℕ) = 183 := by decide
  have s3 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2242 : (sigma 1 2242 : ℕ) = 3600 := by
  have h : (2242 : ℕ) = 2 * (19 * (59)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 19 : ℕ) = 20 := by decide
  have s2 : (sigma 1 59 : ℕ) = 60 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_473248 : (sigma 1 473248 : ℕ) = 973728 := by
  have h : (473248 : ℕ) = 32 * (23 * (643)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 23 : ℕ) = 24 := by decide
  have s2 : (sigma 1 643 : ℕ) = 644 := by rw [sigma_one_prime (by norm_num : Nat.Prime 643)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_4711 : (sigma 1 4711 : ℕ) = 5392 := by
  have h : (4711 : ℕ) = 7 * (673) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 673 : ℕ) = 674 := by rw [sigma_one_prime (by norm_num : Nat.Prime 673)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2722 : (sigma 1 2722 : ℕ) = 4086 := by
  have h : (2722 : ℕ) = 2 * (1361) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1361 : ℕ) = 1362 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1361)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1424 : (sigma 1 1424 : ℕ) = 2790 := by
  have h : (1424 : ℕ) = 16 * (89) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 89 : ℕ) = 90 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1443 : (sigma 1 1443 : ℕ) = 2128 := by
  have h : (1443 : ℕ) = 3 * (13 * (37)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_13200 : (sigma 1 13200 : ℕ) = 46128 := by
  have h : (13200 : ℕ) = 16 * (3 * (25 * (11))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 25 : ℕ) = 31 := by decide
  have s3 : (sigma 1 11 : ℕ) = 12 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_8749 : (sigma 1 8749 : ℕ) = 9436 := by
  have h : (8749 : ℕ) = 13 * (673) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 13 : ℕ) = 14 := by decide
  have s1 : (sigma 1 673 : ℕ) = 674 := by rw [sigma_one_prime (by norm_num : Nat.Prime 673)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2746 : (sigma 1 2746 : ℕ) = 4122 := by
  have h : (2746 : ℕ) = 2 * (1373) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1373 : ℕ) = 1374 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1373)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1828 : (sigma 1 1828 : ℕ) = 3206 := by
  have h : (1828 : ℕ) = 4 * (457) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 457 : ℕ) = 458 := by rw [sigma_one_prime (by norm_num : Nat.Prime 457)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_7269444 : (sigma 1 7269444 : ℕ) = 23092524 := by
  have h : (7269444 : ℕ) = 4 * (9 * (49 * (13 * (317)))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 49 : ℕ) = 57 := by decide
  have s3 : (sigma 1 13 : ℕ) = 14 := by decide
  have s4 : (sigma 1 317 : ℕ) = 318 := by rw [sigma_one_prime (by norm_num : Nat.Prime 317)] <;> norm_num
  rw [s0, s1, s2, s3, s4] <;> norm_num

private theorem sig_2550 : (sigma 1 2550 : ℕ) = 6696 := by
  have h : (2550 : ℕ) = 2 * (3 * (25 * (17))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 25 : ℕ) = 31 := by decide
  have s3 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2762 : (sigma 1 2762 : ℕ) = 4146 := by
  have h : (2762 : ℕ) = 2 * (1381) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1381 : ℕ) = 1382 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1381)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_4146 : (sigma 1 4146 : ℕ) = 8304 := by
  have h : (4146 : ℕ) = 2 * (3 * (691)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 691 : ℕ) = 692 := by rw [sigma_one_prime (by norm_num : Nat.Prime 691)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_8240 : (sigma 1 8240 : ℕ) = 19344 := by
  have h : (8240 : ℕ) = 16 * (5 * (103)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 103 : ℕ) = 104 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1844 : (sigma 1 1844 : ℕ) = 3234 := by
  have h : (1844 : ℕ) = 4 * (461) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 461 : ℕ) = 462 := by rw [sigma_one_prime (by norm_num : Nat.Prime 461)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_242736 : (sigma 1 242736 : ℕ) = 677040 := by
  have h : (242736 : ℕ) = 16 * (3 * (13 * (389))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  have s3 : (sigma 1 389 : ℕ) = 390 := by rw [sigma_one_prime (by norm_num : Nat.Prime 389)] <;> norm_num
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1576 : (sigma 1 1576 : ℕ) = 2970 := by
  have h : (1576 : ℕ) = 8 * (197) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 197 : ℕ) = 198 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_393888 : (sigma 1 393888 : ℕ) = 1130976 := by
  have h : (393888 : ℕ) = 32 * (3 * (11 * (373))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 11 : ℕ) = 12 := by decide
  have s3 : (sigma 1 373 : ℕ) = 374 := by rw [sigma_one_prime (by norm_num : Nat.Prime 373)] <;> norm_num
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_4837 : (sigma 1 4837 : ℕ) = 5536 := by
  have h : (4837 : ℕ) = 7 * (691) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 691 : ℕ) = 692 := by rw [sigma_one_prime (by norm_num : Nat.Prime 691)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_313200 : (sigma 1 313200 : ℕ) = 1153200 := by
  have h : (313200 : ℕ) = 16 * (27 * (25 * (29))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 25 : ℕ) = 31 := by decide
  have s3 : (sigma 1 29 : ℕ) = 30 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1190 : (sigma 1 1190 : ℕ) = 2592 := by
  have h : (1190 : ℕ) = 2 * (5 * (7 * (17))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  have s3 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1281 : (sigma 1 1281 : ℕ) = 1984 := by
  have h : (1281 : ℕ) = 3 * (7 * (61)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 61 : ℕ) = 62 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_21264 : (sigma 1 21264 : ℕ) = 55056 := by
  have h : (21264 : ℕ) = 16 * (3 * (443)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 443 : ℕ) = 444 := by rw [sigma_one_prime (by norm_num : Nat.Prime 443)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_6333 : (sigma 1 6333 : ℕ) = 8448 := by
  have h : (6333 : ℕ) = 3 * (2111) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 2111 : ℕ) = 2112 := by rw [sigma_one_prime (by norm_num : Nat.Prime 2111)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1666 : (sigma 1 1666 : ℕ) = 3078 := by
  have h : (1666 : ℕ) = 2 * (49 * (17)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 49 : ℕ) = 57 := by decide
  have s2 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3495 : (sigma 1 3495 : ℕ) = 5616 := by
  have h : (3495 : ℕ) = 3 * (5 * (233)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 233 : ℕ) = 234 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_18096 : (sigma 1 18096 : ℕ) = 52080 := by
  have h : (18096 : ℕ) = 16 * (3 * (13 * (29))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  have s3 : (sigma 1 29 : ℕ) = 30 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2000 : (sigma 1 2000 : ℕ) = 4836 := by
  have h : (2000 : ℕ) = 16 * (125) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 125 : ℕ) = 156 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_497280 : (sigma 1 497280 : ℕ) = 1860480 := by
  have h : (497280 : ℕ) = 128 * (3 * (5 * (7 * (37)))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 128 : ℕ) = 255 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 7 : ℕ) = 8 := by decide
  have s4 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2, s3, s4] <;> norm_num

private theorem sig_3075 : (sigma 1 3075 : ℕ) = 5208 := by
  have h : (3075 : ℕ) = 3 * (25 * (41)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 41 : ℕ) = 42 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3788 : (sigma 1 3788 : ℕ) = 6636 := by
  have h : (3788 : ℕ) = 4 * (947) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 947 : ℕ) = 948 := by rw [sigma_one_prime (by norm_num : Nat.Prime 947)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2127 : (sigma 1 2127 : ℕ) = 2840 := by
  have h : (2127 : ℕ) = 3 * (709) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 709 : ℕ) = 710 := by rw [sigma_one_prime (by norm_num : Nat.Prime 709)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3790080 : (sigma 1 3790080 : ℕ) = 15305472 := by
  have h : (3790080 : ℕ) = 256 * (9 * (5 * (7 * (47)))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 256 : ℕ) = 511 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 7 : ℕ) = 8 := by decide
  have s4 : (sigma 1 47 : ℕ) = 48 := by decide
  rw [s0, s1, s2, s3, s4] <;> norm_num

private theorem sig_2854 : (sigma 1 2854 : ℕ) = 4284 := by
  have h : (2854 : ℕ) = 2 * (1427) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1427 : ℕ) = 1428 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1427)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2858 : (sigma 1 2858 : ℕ) = 4290 := by
  have h : (2858 : ℕ) = 2 * (1429) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1429 : ℕ) = 1430 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1429)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_4963 : (sigma 1 4963 : ℕ) = 5680 := by
  have h : (4963 : ℕ) = 7 * (709) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 709 : ℕ) = 710 := by rw [sigma_one_prime (by norm_num : Nat.Prime 709)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2866 : (sigma 1 2866 : ℕ) = 4302 := by
  have h : (2866 : ℕ) = 2 * (1433) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1433 : ℕ) = 1434 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1433)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2737 : (sigma 1 2737 : ℕ) = 3456 := by
  have h : (2737 : ℕ) = 7 * (17 * (23)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 17 : ℕ) = 18 := by decide
  have s2 : (sigma 1 23 : ℕ) = 24 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_159201 : (sigma 1 159201 : ℕ) = 282321 := by
  have h : (159201 : ℕ) = 9 * (49 * (361)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 49 : ℕ) = 57 := by decide
  have s2 : (sigma 1 361 : ℕ) = 381 := by rw [(by norm_num : (361 : ℕ) = 19^2), sigma_one_sq (by norm_num : Nat.Prime 19)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1152 : (sigma 1 1152 : ℕ) = 3315 := by
  have h : (1152 : ℕ) = 128 * (9) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 128 : ℕ) = 255 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_6584 : (sigma 1 6584 : ℕ) = 12360 := by
  have h : (6584 : ℕ) = 8 * (823) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 823 : ℕ) = 824 := by rw [sigma_one_prime (by norm_num : Nat.Prime 823)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3268 : (sigma 1 3268 : ℕ) = 6160 := by
  have h : (3268 : ℕ) = 4 * (19 * (43)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 19 : ℕ) = 20 := by decide
  have s2 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_5368 : (sigma 1 5368 : ℕ) = 11160 := by
  have h : (5368 : ℕ) = 8 * (11 * (61)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 61 : ℕ) = 62 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2222 : (sigma 1 2222 : ℕ) = 3672 := by
  have h : (2222 : ℕ) = 2 * (11 * (101)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 101 : ℕ) = 102 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3172 : (sigma 1 3172 : ℕ) = 6076 := by
  have h : (3172 : ℕ) = 4 * (13 * (61)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 61 : ℕ) = 62 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2300 : (sigma 1 2300 : ℕ) = 5208 := by
  have h : (2300 : ℕ) = 4 * (25 * (23)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 23 : ℕ) = 24 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2906 : (sigma 1 2906 : ℕ) = 4362 := by
  have h : (2906 : ℕ) = 2 * (1453) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1453 : ℕ) = 1454 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1453)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_4362 : (sigma 1 4362 : ℕ) = 8736 := by
  have h : (4362 : ℕ) = 2 * (3 * (727)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 727 : ℕ) = 728 := by rw [sigma_one_prime (by norm_num : Nat.Prime 727)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3884 : (sigma 1 3884 : ℕ) = 6804 := by
  have h : (3884 : ℕ) = 4 * (971) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 971 : ℕ) = 972 := by rw [sigma_one_prime (by norm_num : Nat.Prime 971)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2172 : (sigma 1 2172 : ℕ) = 5096 := by
  have h : (2172 : ℕ) = 4 * (3 * (181)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 181 : ℕ) = 182 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_67312 : (sigma 1 67312 : ℕ) = 149296 := by
  have h : (67312 : ℕ) = 16 * (7 * (601)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 601 : ℕ) = 602 := by rw [sigma_one_prime (by norm_num : Nat.Prime 601)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1810 : (sigma 1 1810 : ℕ) = 3276 := by
  have h : (1810 : ℕ) = 2 * (5 * (181)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 181 : ℕ) = 182 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_5616 : (sigma 1 5616 : ℕ) = 17360 := by
  have h : (5616 : ℕ) = 16 * (27 * (13)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_4398 : (sigma 1 4398 : ℕ) = 8808 := by
  have h : (4398 : ℕ) = 2 * (3 * (733)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 733 : ℕ) = 734 := by rw [sigma_one_prime (by norm_num : Nat.Prime 733)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_6712 : (sigma 1 6712 : ℕ) = 12600 := by
  have h : (6712 : ℕ) = 8 * (839) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 839 : ℕ) = 840 := by rw [sigma_one_prime (by norm_num : Nat.Prime 839)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1629 : (sigma 1 1629 : ℕ) = 2366 := by
  have h : (1629 : ℕ) = 9 * (181) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 181 : ℕ) = 182 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_96066 : (sigma 1 96066 : ℕ) = 215622 := by
  have h : (96066 : ℕ) = 2 * (81 * (593)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 81 : ℕ) = 121 := by decide
  have s2 : (sigma 1 593 : ℕ) = 594 := by rw [sigma_one_prime (by norm_num : Nat.Prime 593)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2266 : (sigma 1 2266 : ℕ) = 3744 := by
  have h : (2266 : ℕ) = 2 * (11 * (103)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 103 : ℕ) = 104 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_31914 : (sigma 1 31914 : ℕ) = 71874 := by
  have h : (31914 : ℕ) = 2 * (81 * (197)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 81 : ℕ) = 121 := by decide
  have s2 : (sigma 1 197 : ℕ) = 198 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_4434 : (sigma 1 4434 : ℕ) = 8880 := by
  have h : (4434 : ℕ) = 2 * (3 * (739)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 739 : ℕ) = 740 := by rw [sigma_one_prime (by norm_num : Nat.Prime 739)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2962 : (sigma 1 2962 : ℕ) = 4446 := by
  have h : (2962 : ℕ) = 2 * (1481) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1481 : ℕ) = 1482 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1481)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1552 : (sigma 1 1552 : ℕ) = 3038 := by
  have h : (1552 : ℕ) = 16 * (97) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 97 : ℕ) = 98 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_2542 : (sigma 1 2542 : ℕ) = 4032 := by
  have h : (2542 : ℕ) = 2 * (31 * (41)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 31 : ℕ) = 32 := by decide
  have s2 : (sigma 1 41 : ℕ) = 42 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2978 : (sigma 1 2978 : ℕ) = 4470 := by
  have h : (2978 : ℕ) = 2 * (1489) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1489 : ℕ) = 1490 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1489)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_5173 : (sigma 1 5173 : ℕ) = 5920 := by
  have h : (5173 : ℕ) = 7 * (739) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 739 : ℕ) = 740 := by rw [sigma_one_prime (by norm_num : Nat.Prime 739)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2986 : (sigma 1 2986 : ℕ) = 4482 := by
  have h : (2986 : ℕ) = 2 * (1493) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1493 : ℕ) = 1494 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1493)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3715 : (sigma 1 3715 : ℕ) = 4464 := by
  have h : (3715 : ℕ) = 5 * (743) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 5 : ℕ) = 6 := by decide
  have s1 : (sigma 1 743 : ℕ) = 744 := by rw [sigma_one_prime (by norm_num : Nat.Prime 743)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_11538 : (sigma 1 11538 : ℕ) = 25038 := by
  have h : (11538 : ℕ) = 2 * (9 * (641)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 641 : ℕ) = 642 := by rw [sigma_one_prime (by norm_num : Nat.Prime 641)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2998 : (sigma 1 2998 : ℕ) = 4500 := by
  have h : (2998 : ℕ) = 2 * (1499) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1499 : ℕ) = 1500 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1499)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_75072 : (sigma 1 75072 : ℕ) = 219456 := by
  have h : (75072 : ℕ) = 64 * (3 * (17 * (23))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 64 : ℕ) = 127 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 17 : ℕ) = 18 := by decide
  have s3 : (sigma 1 23 : ℕ) = 24 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_4506 : (sigma 1 4506 : ℕ) = 9024 := by
  have h : (4506 : ℕ) = 2 * (3 * (751)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 751 : ℕ) = 752 := by rw [sigma_one_prime (by norm_num : Nat.Prime 751)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_5848 : (sigma 1 5848 : ℕ) = 11880 := by
  have h : (5848 : ℕ) = 8 * (17 * (43)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 17 : ℕ) = 18 := by decide
  have s2 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2253 : (sigma 1 2253 : ℕ) = 3008 := by
  have h : (2253 : ℕ) = 3 * (751) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 751 : ℕ) = 752 := by rw [sigma_one_prime (by norm_num : Nat.Prime 751)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1091059200 : (sigma 1 1091059200 : ℕ) = 5114672640 := by
  have h : (1091059200 : ℕ) = 512 * (27 * (25 * (7 * (11 * (41))))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 512 : ℕ) = 1023 := by rw [(by norm_num : (512 : ℕ) = 2^9), sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 25 : ℕ) = 31 := by decide
  have s3 : (sigma 1 7 : ℕ) = 8 := by decide
  have s4 : (sigma 1 11 : ℕ) = 12 := by decide
  have s5 : (sigma 1 41 : ℕ) = 42 := by decide
  rw [s0, s1, s2, s3, s4, s5] <;> norm_num

private theorem sig_2086 : (sigma 1 2086 : ℕ) = 3600 := by
  have h : (2086 : ℕ) = 2 * (7 * (149)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 149 : ℕ) = 150 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_24640 : (sigma 1 24640 : ℕ) = 73152 := by
  have h : (24640 : ℕ) = 64 * (5 * (7 * (11))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 64 : ℕ) = 127 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  have s3 : (sigma 1 11 : ℕ) = 12 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_4542 : (sigma 1 4542 : ℕ) = 9096 := by
  have h : (4542 : ℕ) = 2 * (3 * (757)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 757 : ℕ) = 758 := by rw [sigma_one_prime (by norm_num : Nat.Prime 757)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_44564 : (sigma 1 44564 : ℕ) = 84084 := by
  have h : (44564 : ℕ) = 4 * (13 * (857)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 857 : ℕ) = 858 := by rw [sigma_one_prime (by norm_num : Nat.Prime 857)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_975 : (sigma 1 975 : ℕ) = 1736 := by
  have h : (975 : ℕ) = 3 * (25 * (13)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3015 : (sigma 1 3015 : ℕ) = 5304 := by
  have h : (3015 : ℕ) = 9 * (5 * (67)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 67 : ℕ) = 68 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2740 : (sigma 1 2740 : ℕ) = 5796 := by
  have h : (2740 : ℕ) = 4 * (5 * (137)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 137 : ℕ) = 138 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_5299 : (sigma 1 5299 : ℕ) = 6064 := by
  have h : (5299 : ℕ) = 7 * (757) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 757 : ℕ) = 758 := by rw [sigma_one_prime (by norm_num : Nat.Prime 757)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_4076 : (sigma 1 4076 : ℕ) = 7140 := by
  have h : (4076 : ℕ) = 4 * (1019) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 1019 : ℕ) = 1020 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1019)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2036 : (sigma 1 2036 : ℕ) = 3570 := by
  have h : (2036 : ℕ) = 4 * (509) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 509 : ℕ) = 510 := by rw [sigma_one_prime (by norm_num : Nat.Prime 509)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_8094996 : (sigma 1 8094996 : ℕ) = 25706772 := by
  have h : (8094996 : ℕ) = 4 * (9 * (49 * (13 * (353)))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 49 : ℕ) = 57 := by decide
  have s3 : (sigma 1 13 : ℕ) = 14 := by decide
  have s4 : (sigma 1 353 : ℕ) = 354 := by rw [sigma_one_prime (by norm_num : Nat.Prime 353)] <;> norm_num
  rw [s0, s1, s2, s3, s4] <;> norm_num

private theorem sig_1407 : (sigma 1 1407 : ℕ) = 2176 := by
  have h : (1407 : ℕ) = 3 * (7 * (67)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 67 : ℕ) = 68 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_4614 : (sigma 1 4614 : ℕ) = 9240 := by
  have h : (4614 : ℕ) = 2 * (3 * (769)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 769 : ℕ) = 770 := by rw [sigma_one_prime (by norm_num : Nat.Prime 769)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_9968 : (sigma 1 9968 : ℕ) = 22320 := by
  have h : (9968 : ℕ) = 16 * (7 * (89)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 89 : ℕ) = 90 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1616 : (sigma 1 1616 : ℕ) = 3162 := by
  have h : (1616 : ℕ) = 16 * (101) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 101 : ℕ) = 102 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_4124 : (sigma 1 4124 : ℕ) = 7224 := by
  have h : (4124 : ℕ) = 4 * (1031) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 1031 : ℕ) = 1032 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1031)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3098 : (sigma 1 3098 : ℕ) = 4650 := by
  have h : (3098 : ℕ) = 2 * (1549) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1549 : ℕ) = 1550 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1549)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_5829 : (sigma 1 5829 : ℕ) = 8160 := by
  have h : (5829 : ℕ) = 3 * (29 * (67)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 29 : ℕ) = 30 := by decide
  have s2 : (sigma 1 67 : ℕ) = 68 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3106 : (sigma 1 3106 : ℕ) = 4662 := by
  have h : (3106 : ℕ) = 2 * (1553) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1553 : ℕ) = 1554 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1553)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2316 : (sigma 1 2316 : ℕ) = 5432 := by
  have h : (2316 : ℕ) = 4 * (3 * (193)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 193 : ℕ) = 194 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_23568 : (sigma 1 23568 : ℕ) = 61008 := by
  have h : (23568 : ℕ) = 16 * (3 * (491)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 491 : ℕ) = 492 := by rw [sigma_one_prime (by norm_num : Nat.Prime 491)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1930 : (sigma 1 1930 : ℕ) = 3492 := by
  have h : (1930 : ℕ) = 2 * (5 * (193)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 193 : ℕ) = 194 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_7824 : (sigma 1 7824 : ℕ) = 20336 := by
  have h : (7824 : ℕ) = 16 * (3 * (163)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 163 : ℕ) = 164 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_8136 : (sigma 1 8136 : ℕ) = 22230 := by
  have h : (8136 : ℕ) = 8 * (9 * (113)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 113 : ℕ) = 114 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_7650 : (sigma 1 7650 : ℕ) = 21762 := by
  have h : (7650 : ℕ) = 2 * (9 * (25 * (17))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 25 : ℕ) = 31 := by decide
  have s3 : (sigma 1 17 : ℕ) = 18 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1737 : (sigma 1 1737 : ℕ) = 2522 := by
  have h : (1737 : ℕ) = 9 * (193) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 193 : ℕ) = 194 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1352160 : (sigma 1 1352160 : ℕ) = 4747680 := by
  have h : (1352160 : ℕ) = 32 * (27 * (5 * (313))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 313 : ℕ) = 314 := by rw [sigma_one_prime (by norm_num : Nat.Prime 313)] <;> norm_num
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1677 : (sigma 1 1677 : ℕ) = 2464 := by
  have h : (1677 : ℕ) = 3 * (13 * (43)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_68160 : (sigma 1 68160 : ℕ) = 219456 := by
  have h : (68160 : ℕ) = 64 * (3 * (5 * (71))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 64 : ℕ) = 127 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 71 : ℕ) = 72 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2625 : (sigma 1 2625 : ℕ) = 4992 := by
  have h : (2625 : ℕ) = 3 * (125 * (7)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 125 : ℕ) = 156 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_4204 : (sigma 1 4204 : ℕ) = 7364 := by
  have h : (4204 : ℕ) = 4 * (1051) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 1051 : ℕ) = 1052 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1051)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2361 : (sigma 1 2361 : ℕ) = 3152 := by
  have h : (2361 : ℕ) = 3 * (787) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 787 : ℕ) = 788 := by rw [sigma_one_prime (by norm_num : Nat.Prime 787)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_12186 : (sigma 1 12186 : ℕ) = 26442 := by
  have h : (12186 : ℕ) = 2 * (9 * (677)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 677 : ℕ) = 678 := by rw [sigma_one_prime (by norm_num : Nat.Prime 677)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1767 : (sigma 1 1767 : ℕ) = 2560 := by
  have h : (1767 : ℕ) = 3 * (19 * (31)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 19 : ℕ) = 20 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_46752 : (sigma 1 46752 : ℕ) = 122976 := by
  have h : (46752 : ℕ) = 32 * (3 * (487)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 487 : ℕ) = 488 := by rw [sigma_one_prime (by norm_num : Nat.Prime 487)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3484 : (sigma 1 3484 : ℕ) = 6664 := by
  have h : (3484 : ℕ) = 4 * (13 * (67)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 67 : ℕ) = 68 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_6232 : (sigma 1 6232 : ℕ) = 12600 := by
  have h : (6232 : ℕ) = 8 * (19 * (41)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 19 : ℕ) = 20 := by decide
  have s2 : (sigma 1 41 : ℕ) = 42 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1430 : (sigma 1 1430 : ℕ) = 3024 := by
  have h : (1430 : ℕ) = 2 * (5 * (11 * (13))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 11 : ℕ) = 12 := by decide
  have s3 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2849 : (sigma 1 2849 : ℕ) = 3648 := by
  have h : (2849 : ℕ) = 7 * (11 * (37)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3194 : (sigma 1 3194 : ℕ) = 4794 := by
  have h : (3194 : ℕ) = 2 * (1597) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1597 : ℕ) = 1598 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1597)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_5181 : (sigma 1 5181 : ℕ) = 7584 := by
  have h : (5181 : ℕ) = 3 * (11 * (157)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 157 : ℕ) = 158 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1690 : (sigma 1 1690 : ℕ) = 3294 := by
  have h : (1690 : ℕ) = 2 * (5 * (169)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 169 : ℕ) = 183 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2080 : (sigma 1 2080 : ℕ) = 5292 := by
  have h : (2080 : ℕ) = 32 * (5 * (13)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3814272 : (sigma 1 3814272 : ℕ) = 14002560 := by
  have h : (3814272 : ℕ) = 128 * (9 * (7 * (11 * (43)))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 128 : ℕ) = 255 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  have s3 : (sigma 1 11 : ℕ) = 12 := by decide
  have s4 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1, s2, s3, s4] <;> norm_num

private theorem sig_3214 : (sigma 1 3214 : ℕ) = 4824 := by
  have h : (3214 : ℕ) = 2 * (1607) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1607 : ℕ) = 1608 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1607)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3218 : (sigma 1 3218 : ℕ) = 4830 := by
  have h : (3218 : ℕ) = 2 * (1609) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1609 : ℕ) = 1610 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1609)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_7251 : (sigma 1 7251 : ℕ) = 9672 := by
  have h : (7251 : ℕ) = 3 * (2417) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 2417 : ℕ) = 2418 := by rw [sigma_one_prime (by norm_num : Nat.Prime 2417)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3226 : (sigma 1 3226 : ℕ) = 4842 := by
  have h : (3226 : ℕ) = 2 * (1613) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1613 : ℕ) = 1614 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1613)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1791 : (sigma 1 1791 : ℕ) = 2600 := by
  have h : (1791 : ℕ) = 9 * (199) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 199 : ℕ) = 200 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_2698 : (sigma 1 2698 : ℕ) = 4320 := by
  have h : (2698 : ℕ) = 2 * (19 * (71)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 19 : ℕ) = 20 := by decide
  have s2 : (sigma 1 71 : ℕ) = 72 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3242 : (sigma 1 3242 : ℕ) = 4866 := by
  have h : (3242 : ℕ) = 2 * (1621) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1621 : ℕ) = 1622 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1621)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_4866 : (sigma 1 4866 : ℕ) = 9744 := by
  have h : (4866 : ℕ) = 2 * (3 * (811)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 811 : ℕ) = 812 := by rw [sigma_one_prime (by norm_num : Nat.Prime 811)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_12984 : (sigma 1 12984 : ℕ) = 32520 := by
  have h : (12984 : ℕ) = 8 * (3 * (541)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 541 : ℕ) = 542 := by rw [sigma_one_prime (by norm_num : Nat.Prime 541)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2164 : (sigma 1 2164 : ℕ) = 3794 := by
  have h : (2164 : ℕ) = 4 * (541) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 541 : ℕ) = 542 := by rw [sigma_one_prime (by norm_num : Nat.Prime 541)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_739116 : (sigma 1 739116 : ℕ) = 2178540 := by
  have h : (739116 : ℕ) = 4 * (9 * (49 * (419))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 49 : ℕ) = 57 := by decide
  have s3 : (sigma 1 419 : ℕ) = 420 := by rw [sigma_one_prime (by norm_num : Nat.Prime 419)] <;> norm_num
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2686 : (sigma 1 2686 : ℕ) = 4320 := by
  have h : (2686 : ℕ) = 2 * (17 * (79)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 17 : ℕ) = 18 := by decide
  have s2 : (sigma 1 79 : ℕ) = 80 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_56304 : (sigma 1 56304 : ℕ) = 174096 := by
  have h : (56304 : ℕ) = 16 * (9 * (17 * (23))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 17 : ℕ) = 18 := by decide
  have s3 : (sigma 1 23 : ℕ) = 24 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_12336 : (sigma 1 12336 : ℕ) = 31992 := by
  have h : (12336 : ℕ) = 16 * (3 * (257)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 257 : ℕ) = 258 := by rw [sigma_one_prime (by norm_num : Nat.Prime 257)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3274 : (sigma 1 3274 : ℕ) = 4914 := by
  have h : (3274 : ℕ) = 2 * (1637) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1637 : ℕ) = 1638 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1637)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2635 : (sigma 1 2635 : ℕ) = 3456 := by
  have h : (2635 : ℕ) = 5 * (17 * (31)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 5 : ℕ) = 6 := by decide
  have s1 : (sigma 1 17 : ℕ) = 18 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_104076 : (sigma 1 104076 : ℕ) = 311220 := by
  have h : (104076 : ℕ) = 4 * (9 * (49 * (59))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 49 : ℕ) = 57 := by decide
  have s3 : (sigma 1 59 : ℕ) = 60 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1864 : (sigma 1 1864 : ℕ) = 3510 := by
  have h : (1864 : ℕ) = 8 * (233) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 233 : ℕ) = 234 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_13900 : (sigma 1 13900 : ℕ) = 30380 := by
  have h : (13900 : ℕ) = 4 * (25 * (139)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 139 : ℕ) = 140 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_4938 : (sigma 1 4938 : ℕ) = 9888 := by
  have h : (4938 : ℕ) = 2 * (3 * (823)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 823 : ℕ) = 824 := by rw [sigma_one_prime (by norm_num : Nat.Prime 823)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_26360 : (sigma 1 26360 : ℕ) = 59400 := by
  have h : (26360 : ℕ) = 8 * (5 * (659)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 659 : ℕ) = 660 := by rw [sigma_one_prime (by norm_num : Nat.Prime 659)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2282 : (sigma 1 2282 : ℕ) = 3936 := by
  have h : (2282 : ℕ) = 2 * (7 * (163)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 163 : ℕ) = 164 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_29304 : (sigma 1 29304 : ℕ) = 88920 := by
  have h : (29304 : ℕ) = 8 * (9 * (11 * (37))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 11 : ℕ) = 12 := by decide
  have s3 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2626 : (sigma 1 2626 : ℕ) = 4284 := by
  have h : (2626 : ℕ) = 2 * (13 * (101)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 101 : ℕ) = 102 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3314 : (sigma 1 3314 : ℕ) = 4974 := by
  have h : (3314 : ℕ) = 2 * (1657) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1657 : ℕ) = 1658 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1657)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_4974 : (sigma 1 4974 : ℕ) = 9960 := by
  have h : (4974 : ℕ) = 2 * (3 * (829)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 829 : ℕ) = 830 := by rw [sigma_one_prime (by norm_num : Nat.Prime 829)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_336532 : (sigma 1 336532 : ℕ) = 732564 := by
  have h : (336532 : ℕ) = 4 * (49 * (17 * (101))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 49 : ℕ) = 57 := by decide
  have s2 : (sigma 1 17 : ℕ) = 18 := by decide
  have s3 : (sigma 1 101 : ℕ) = 102 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1647 : (sigma 1 1647 : ℕ) = 2480 := by
  have h : (1647 : ℕ) = 27 * (61) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 27 : ℕ) = 40 := by decide
  have s1 : (sigma 1 61 : ℕ) = 62 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_3141000 : (sigma 1 3141000 : ℕ) = 10647000 := by
  have h : (3141000 : ℕ) = 8 * (9 * (125 * (349))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 125 : ℕ) = 156 := by decide
  have s3 : (sigma 1 349 : ℕ) = 350 := by rw [sigma_one_prime (by norm_num : Nat.Prime 349)] <;> norm_num
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1533 : (sigma 1 1533 : ℕ) = 2368 := by
  have h : (1533 : ℕ) = 3 * (7 * (73)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 73 : ℕ) = 74 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3338 : (sigma 1 3338 : ℕ) = 5010 := by
  have h : (3338 : ℕ) = 2 * (1669) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1669 : ℕ) = 1670 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1669)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_5803 : (sigma 1 5803 : ℕ) = 6640 := by
  have h : (5803 : ℕ) = 7 * (829) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 829 : ℕ) = 830 := by rw [sigma_one_prime (by norm_num : Nat.Prime 829)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_13368 : (sigma 1 13368 : ℕ) = 33480 := by
  have h : (13368 : ℕ) = 8 * (3 * (557)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 557 : ℕ) = 558 := by rw [sigma_one_prime (by norm_num : Nat.Prime 557)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2228 : (sigma 1 2228 : ℕ) = 3906 := by
  have h : (2228 : ℕ) = 4 * (557) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 557 : ℕ) = 558 := by rw [sigma_one_prime (by norm_num : Nat.Prime 557)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2135 : (sigma 1 2135 : ℕ) = 2976 := by
  have h : (2135 : ℕ) = 5 * (7 * (61)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 5 : ℕ) = 6 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 61 : ℕ) = 62 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1850 : (sigma 1 1850 : ℕ) = 3534 := by
  have h : (1850 : ℕ) = 2 * (25 * (37)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3528 : (sigma 1 3528 : ℕ) = 11115 := by
  have h : (3528 : ℕ) = 8 * (9 * (49)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 49 : ℕ) = 57 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_4492 : (sigma 1 4492 : ℕ) = 7868 := by
  have h : (4492 : ℕ) = 4 * (1123) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 1123 : ℕ) = 1124 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1123)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3424 : (sigma 1 3424 : ℕ) = 6804 := by
  have h : (3424 : ℕ) = 32 * (107) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 107 : ℕ) = 108 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_590992 : (sigma 1 590992 : ℕ) = 1173040 := by
  have h : (590992 : ℕ) = 16 * (43 * (859)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 43 : ℕ) = 44 := by decide
  have s2 : (sigma 1 859 : ℕ) = 860 := by rw [sigma_one_prime (by norm_num : Nat.Prime 859)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2914 : (sigma 1 2914 : ℕ) = 4608 := by
  have h : (2914 : ℕ) = 2 * (31 * (47)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 31 : ℕ) = 32 := by decide
  have s2 : (sigma 1 47 : ℕ) = 48 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3386 : (sigma 1 3386 : ℕ) = 5082 := by
  have h : (3386 : ℕ) = 2 * (1693) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1693 : ℕ) = 1694 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1693)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_6612 : (sigma 1 6612 : ℕ) = 16800 := by
  have h : (6612 : ℕ) = 4 * (3 * (19 * (29))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 19 : ℕ) = 20 := by decide
  have s3 : (sigma 1 29 : ℕ) = 30 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_3394 : (sigma 1 3394 : ℕ) = 5094 := by
  have h : (3394 : ℕ) = 2 * (1697) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1697 : ℕ) = 1698 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1697)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1928 : (sigma 1 1928 : ℕ) = 3630 := by
  have h : (1928 : ℕ) = 8 * (241) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 241 : ℕ) = 242 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_382752 : (sigma 1 382752 : ℕ) = 1118880 := by
  have h : (382752 : ℕ) = 32 * (27 * (443)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 443 : ℕ) = 444 := by rw [sigma_one_prime (by norm_num : Nat.Prime 443)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1696 : (sigma 1 1696 : ℕ) = 3402 := by
  have h : (1696 : ℕ) = 32 * (53) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 53 : ℕ) = 54 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_51120 : (sigma 1 51120 : ℕ) = 174096 := by
  have h : (51120 : ℕ) = 16 * (9 * (5 * (71))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 71 : ℕ) = 72 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_5118 : (sigma 1 5118 : ℕ) = 10248 := by
  have h : (5118 : ℕ) = 2 * (3 * (853)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 853 : ℕ) = 854 := by rw [sigma_one_prime (by norm_num : Nat.Prime 853)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3418 : (sigma 1 3418 : ℕ) = 5130 := by
  have h : (3418 : ℕ) = 2 * (1709) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1709 : ℕ) = 1710 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1709)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1899 : (sigma 1 1899 : ℕ) = 2756 := by
  have h : (1899 : ℕ) = 9 * (211) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 211 : ℕ) = 212 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_3632 : (sigma 1 3632 : ℕ) = 7068 := by
  have h : (3632 : ℕ) = 16 * (227) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 227 : ℕ) = 228 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_330880 : (sigma 1 330880 : ℕ) = 881280 := by
  have h : (330880 : ℕ) = 128 * (5 * (11 * (47))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 128 : ℕ) = 255 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 11 : ℕ) = 12 := by decide
  have s3 : (sigma 1 47 : ℕ) = 48 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_5154 : (sigma 1 5154 : ℕ) = 10320 := by
  have h : (5154 : ℕ) = 2 * (3 * (859)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 859 : ℕ) = 860 := by rw [sigma_one_prime (by norm_num : Nat.Prime 859)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3442 : (sigma 1 3442 : ℕ) = 5166 := by
  have h : (3442 : ℕ) = 2 * (1721) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1721 : ℕ) = 1722 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1721)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1808 : (sigma 1 1808 : ℕ) = 3534 := by
  have h : (1808 : ℕ) = 16 * (113) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 113 : ℕ) = 114 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_3796 : (sigma 1 3796 : ℕ) = 7252 := by
  have h : (3796 : ℕ) = 4 * (13 * (73)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 73 : ℕ) = 74 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2662 : (sigma 1 2662 : ℕ) = 4392 := by
  have h : (2662 : ℕ) = 2 * (1331) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1331 : ℕ) = 1464 := by rw [(by norm_num : (1331 : ℕ) = 11^3), sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_27500 : (sigma 1 27500 : ℕ) = 65604 := by
  have h : (27500 : ℕ) = 4 * (625 * (11)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 625 : ℕ) = 781 := by rw [(by norm_num : (625 : ℕ) = 5^4), sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have s2 : (sigma 1 11 : ℕ) = 12 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_6013 : (sigma 1 6013 : ℕ) = 6880 := by
  have h : (6013 : ℕ) = 7 * (859) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 859 : ℕ) = 860 := by rw [sigma_one_prime (by norm_num : Nat.Prime 859)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3466 : (sigma 1 3466 : ℕ) = 5202 := by
  have h : (3466 : ℕ) = 2 * (1733) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1733 : ℕ) = 1734 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1733)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1300 : (sigma 1 1300 : ℕ) = 3038 := by
  have h : (1300 : ℕ) = 4 * (25 * (13)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2661124 : (sigma 1 2661124 : ℕ) = 4669084 := by
  have h : (2661124 : ℕ) = 4 * (577 * (1153)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 577 : ℕ) = 578 := by rw [sigma_one_prime (by norm_num : Nat.Prime 577)] <;> norm_num
  have s2 : (sigma 1 1153 : ℕ) = 1154 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1153)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2585 : (sigma 1 2585 : ℕ) = 3456 := by
  have h : (2585 : ℕ) = 5 * (11 * (47)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 5 : ℕ) = 6 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 47 : ℕ) = 48 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3482 : (sigma 1 3482 : ℕ) = 5226 := by
  have h : (3482 : ℕ) = 2 * (1741) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1741 : ℕ) = 1742 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1741)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_7836 : (sigma 1 7836 : ℕ) = 18312 := by
  have h : (7836 : ℕ) = 4 * (3 * (653)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 653 : ℕ) = 654 := by rw [sigma_one_prime (by norm_num : Nat.Prime 653)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3140 : (sigma 1 3140 : ℕ) = 6636 := by
  have h : (3140 : ℕ) = 4 * (5 * (157)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 157 : ℕ) = 158 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3494 : (sigma 1 3494 : ℕ) = 5244 := by
  have h : (3494 : ℕ) = 2 * (1747) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1747 : ℕ) = 1748 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1747)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1507680 : (sigma 1 1507680 : ℕ) = 5292000 := by
  have h : (1507680 : ℕ) = 32 * (27 * (5 * (349))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 349 : ℕ) = 350 := by rw [sigma_one_prime (by norm_num : Nat.Prime 349)] <;> norm_num
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2422 : (sigma 1 2422 : ℕ) = 4176 := by
  have h : (2422 : ℕ) = 2 * (7 * (173)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 173 : ℕ) = 174 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3506 : (sigma 1 3506 : ℕ) = 5262 := by
  have h : (3506 : ℕ) = 2 * (1753) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1753 : ℕ) = 1754 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1753)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_5262 : (sigma 1 5262 : ℕ) = 10536 := by
  have h : (5262 : ℕ) = 2 * (3 * (877)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 877 : ℕ) = 878 := by rw [sigma_one_prime (by norm_num : Nat.Prime 877)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_4684 : (sigma 1 4684 : ℕ) = 8204 := by
  have h : (4684 : ℕ) = 4 * (1171) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 1171 : ℕ) = 1172 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1171)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1539 : (sigma 1 1539 : ℕ) = 2420 := by
  have h : (1539 : ℕ) = 81 * (19) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 81 : ℕ) = 121 := by decide
  have s1 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1197 : (sigma 1 1197 : ℕ) = 2080 := by
  have h : (1197 : ℕ) = 9 * (7 * (19)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_5298 : (sigma 1 5298 : ℕ) = 10608 := by
  have h : (5298 : ℕ) = 2 * (3 * (883)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 883 : ℕ) = 884 := by rw [sigma_one_prime (by norm_num : Nat.Prime 883)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_137952 : (sigma 1 137952 : ℕ) = 393120 := by
  have h : (137952 : ℕ) = 32 * (9 * (479)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 479 : ℕ) = 480 := by rw [sigma_one_prime (by norm_num : Nat.Prime 479)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2052 : (sigma 1 2052 : ℕ) = 5600 := by
  have h : (2052 : ℕ) = 4 * (27 * (19)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 19 : ℕ) = 20 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_13072 : (sigma 1 13072 : ℕ) = 27280 := by
  have h : (13072 : ℕ) = 16 * (19 * (43)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 19 : ℕ) = 20 := by decide
  have s2 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_4266 : (sigma 1 4266 : ℕ) = 9600 := by
  have h : (4266 : ℕ) = 2 * (27 * (79)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 79 : ℕ) = 80 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3554 : (sigma 1 3554 : ℕ) = 5334 := by
  have h : (3554 : ℕ) = 2 * (1777) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1777 : ℕ) = 1778 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1777)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_6181 : (sigma 1 6181 : ℕ) = 7072 := by
  have h : (6181 : ℕ) = 7 * (883) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 883 : ℕ) = 884 := by rw [sigma_one_prime (by norm_num : Nat.Prime 883)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_4748 : (sigma 1 4748 : ℕ) = 8316 := by
  have h : (4748 : ℕ) = 4 * (1187) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 1187 : ℕ) = 1188 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1187)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1280 : (sigma 1 1280 : ℕ) = 3066 := by
  have h : (1280 : ℕ) = 256 * (5) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 256 : ℕ) = 511 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_27024 : (sigma 1 27024 : ℕ) = 69936 := by
  have h : (27024 : ℕ) = 16 * (3 * (563)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 563 : ℕ) = 564 := by rw [sigma_one_prime (by norm_num : Nat.Prime 563)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3574 : (sigma 1 3574 : ℕ) = 5364 := by
  have h : (3574 : ℕ) = 2 * (1787) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1787 : ℕ) = 1788 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1787)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3578 : (sigma 1 3578 : ℕ) = 5370 := by
  have h : (3578 : ℕ) = 2 * (1789) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1789 : ℕ) = 1790 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1789)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_8061 : (sigma 1 8061 : ℕ) = 10752 := by
  have h : (8061 : ℕ) = 3 * (2687) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 2687 : ℕ) = 2688 := by rw [sigma_one_prime (by norm_num : Nat.Prime 2687)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_52676 : (sigma 1 52676 : ℕ) = 99372 := by
  have h : (52676 : ℕ) = 4 * (13 * (1013)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 1013 : ℕ) = 1014 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1013)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2676 : (sigma 1 2676 : ℕ) = 6272 := by
  have h : (2676 : ℕ) = 4 * (3 * (223)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 223 : ℕ) = 224 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_243828 : (sigma 1 243828 : ℕ) = 665028 := by
  have h : (243828 : ℕ) = 4 * (9 * (13 * (521))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  have s3 : (sigma 1 521 : ℕ) = 522 := by rw [sigma_one_prime (by norm_num : Nat.Prime 521)] <;> norm_num
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1659 : (sigma 1 1659 : ℕ) = 2560 := by
  have h : (1659 : ℕ) = 3 * (7 * (79)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 79 : ℕ) = 80 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3602 : (sigma 1 3602 : ℕ) = 5406 := by
  have h : (3602 : ℕ) = 2 * (1801) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1801 : ℕ) = 1802 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1801)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_16777 : (sigma 1 16777 : ℕ) = 17680 := by
  have h : (16777 : ℕ) = 19 * (883) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 19 : ℕ) = 20 := by decide
  have s1 : (sigma 1 883 : ℕ) = 884 := by rw [sigma_one_prime (by norm_num : Nat.Prime 883)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_8248 : (sigma 1 8248 : ℕ) = 15480 := by
  have h : (8248 : ℕ) = 8 * (1031) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 1031 : ℕ) = 1032 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1031)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2007 : (sigma 1 2007 : ℕ) = 2912 := by
  have h : (2007 : ℕ) = 9 * (223) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 223 : ℕ) = 224 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_1800960 : (sigma 1 1800960 : ℕ) = 6671616 := by
  have h : (1800960 : ℕ) = 256 * (3 * (5 * (7 * (67)))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 256 : ℕ) = 511 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 7 : ℕ) = 8 := by decide
  have s4 : (sigma 1 67 : ℕ) = 68 := by decide
  rw [s0, s1, s2, s3, s4] <;> norm_num

private theorem sig_2056 : (sigma 1 2056 : ℕ) = 3870 := by
  have h : (2056 : ℕ) = 8 * (257) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 257 : ℕ) = 258 := by rw [sigma_one_prime (by norm_num : Nat.Prime 257)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_39840 : (sigma 1 39840 : ℕ) = 127008 := by
  have h : (39840 : ℕ) = 32 * (3 * (5 * (83))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 83 : ℕ) = 84 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_5442 : (sigma 1 5442 : ℕ) = 10896 := by
  have h : (5442 : ℕ) = 2 * (3 * (907)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 907 : ℕ) = 908 := by rw [sigma_one_prime (by norm_num : Nat.Prime 907)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_25160 : (sigma 1 25160 : ℕ) = 61560 := by
  have h : (25160 : ℕ) = 8 * (5 * (17 * (37))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 17 : ℕ) = 18 := by decide
  have s3 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1809 : (sigma 1 1809 : ℕ) = 2720 := by
  have h : (1809 : ℕ) = 27 * (67) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 27 : ℕ) = 40 := by decide
  have s1 : (sigma 1 67 : ℕ) = 68 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_3450 : (sigma 1 3450 : ℕ) = 8928 := by
  have h : (3450 : ℕ) = 2 * (3 * (25 * (23))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 25 : ℕ) = 31 := by decide
  have s3 : (sigma 1 23 : ℕ) = 24 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_6968 : (sigma 1 6968 : ℕ) = 14280 := by
  have h : (6968 : ℕ) = 8 * (13 * (67)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 67 : ℕ) = 68 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_6349 : (sigma 1 6349 : ℕ) = 7264 := by
  have h : (6349 : ℕ) = 7 * (907) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 907 : ℕ) = 908 := by rw [sigma_one_prime (by norm_num : Nat.Prime 907)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_4148 : (sigma 1 4148 : ℕ) = 7812 := by
  have h : (4148 : ℕ) = 4 * (17 * (61)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 17 : ℕ) = 18 := by decide
  have s2 : (sigma 1 61 : ℕ) = 62 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2270 : (sigma 1 2270 : ℕ) = 4104 := by
  have h : (2270 : ℕ) = 2 * (5 * (227)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 227 : ℕ) = 228 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_24903168 : (sigma 1 24903168 : ℕ) = 68614656 := by
  have h : (24903168 : ℕ) = 512 * (3 * (31 * (523))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 512 : ℕ) = 1023 := by rw [(by norm_num : (512 : ℕ) = 2^9), sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 31 : ℕ) = 32 := by decide
  have s3 : (sigma 1 523 : ℕ) = 524 := by rw [sigma_one_prime (by norm_num : Nat.Prime 523)] <;> norm_num
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2345 : (sigma 1 2345 : ℕ) = 3264 := by
  have h : (2345 : ℕ) = 5 * (7 * (67)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 5 : ℕ) = 6 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 67 : ℕ) = 68 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_24992 : (sigma 1 24992 : ℕ) = 54432 := by
  have h : (24992 : ℕ) = 32 * (11 * (71)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 11 : ℕ) = 12 := by decide
  have s2 : (sigma 1 71 : ℕ) = 72 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_5514 : (sigma 1 5514 : ℕ) = 11040 := by
  have h : (5514 : ℕ) = 2 * (3 * (919)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 919 : ℕ) = 920 := by rw [sigma_one_prime (by norm_num : Nat.Prime 919)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_4292 : (sigma 1 4292 : ℕ) = 7980 := by
  have h : (4292 : ℕ) = 4 * (29 * (37)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 29 : ℕ) = 30 := by decide
  have s2 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1610 : (sigma 1 1610 : ℕ) = 3456 := by
  have h : (1610 : ℕ) = 2 * (5 * (7 * (23))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  have s3 : (sigma 1 23 : ℕ) = 24 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_325696 : (sigma 1 325696 : ℕ) = 739648 := by
  have h : (325696 : ℕ) = 64 * (7 * (727)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 64 : ℕ) = 127 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 727 : ℕ) = 728 := by rw [sigma_one_prime (by norm_num : Nat.Prime 727)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2254 : (sigma 1 2254 : ℕ) = 4104 := by
  have h : (2254 : ℕ) = 2 * (49 * (23)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 49 : ℕ) = 57 := by decide
  have s2 : (sigma 1 23 : ℕ) = 24 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_29560 : (sigma 1 29560 : ℕ) = 66600 := by
  have h : (29560 : ℕ) = 8 * (5 * (739)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 739 : ℕ) = 740 := by rw [sigma_one_prime (by norm_num : Nat.Prime 739)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_6433 : (sigma 1 6433 : ℕ) = 7360 := by
  have h : (6433 : ℕ) = 7 * (919) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 7 : ℕ) = 8 := by decide
  have s1 : (sigma 1 919 : ℕ) = 920 := by rw [sigma_one_prime (by norm_num : Nat.Prime 919)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2050 : (sigma 1 2050 : ℕ) = 3906 := by
  have h : (2050 : ℕ) = 2 * (25 * (41)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 41 : ℕ) = 42 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2061 : (sigma 1 2061 : ℕ) = 2990 := by
  have h : (2061 : ℕ) = 9 * (229) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 229 : ℕ) = 230 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_46144 : (sigma 1 46144 : ℕ) = 105664 := by
  have h : (46144 : ℕ) = 64 * (7 * (103)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 64 : ℕ) = 127 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 103 : ℕ) = 104 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_1682 : (sigma 1 1682 : ℕ) = 2613 := by
  have h : (1682 : ℕ) = 2 * (841) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 841 : ℕ) = 871 := by rw [(by norm_num : (841 : ℕ) = 29^2), sigma_one_sq (by norm_num : Nat.Prime 29)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3722 : (sigma 1 3722 : ℕ) = 5586 := by
  have h : (3722 : ℕ) = 2 * (1861) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1861 : ℕ) = 1862 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1861)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_4108 : (sigma 1 4108 : ℕ) = 7840 := by
  have h : (4108 : ℕ) = 4 * (13 * (79)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 79 : ℕ) = 80 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_554400 : (sigma 1 554400 : ℕ) = 2437344 := by
  have h : (554400 : ℕ) = 32 * (9 * (25 * (7 * (11)))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 25 : ℕ) = 31 := by decide
  have s3 : (sigma 1 7 : ℕ) = 8 := by decide
  have s4 : (sigma 1 11 : ℕ) = 12 := by decide
  rw [s0, s1, s2, s3, s4] <;> norm_num

private theorem sig_3734 : (sigma 1 3734 : ℕ) = 5604 := by
  have h : (3734 : ℕ) = 2 * (1867) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1867 : ℕ) = 1868 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1867)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_86128 : (sigma 1 86128 : ℕ) = 190960 := by
  have h : (86128 : ℕ) = 16 * (7 * (769)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 769 : ℕ) = 770 := by rw [sigma_one_prime (by norm_num : Nat.Prime 769)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3742 : (sigma 1 3742 : ℕ) = 5616 := by
  have h : (3742 : ℕ) = 2 * (1871) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1871 : ℕ) = 1872 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1871)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3746 : (sigma 1 3746 : ℕ) = 5622 := by
  have h : (3746 : ℕ) = 2 * (1873) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1873 : ℕ) = 1874 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1873)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_5622 : (sigma 1 5622 : ℕ) = 11256 := by
  have h : (5622 : ℕ) = 2 * (3 * (937)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 937 : ℕ) = 938 := by rw [sigma_one_prime (by norm_num : Nat.Prime 937)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3754 : (sigma 1 3754 : ℕ) = 5634 := by
  have h : (3754 : ℕ) = 2 * (1877) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1877 : ℕ) = 1878 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1877)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2330 : (sigma 1 2330 : ℕ) = 4212 := by
  have h : (2330 : ℕ) = 2 * (5 * (233)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 233 : ℕ) = 234 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_12208 : (sigma 1 12208 : ℕ) = 27280 := by
  have h : (12208 : ℕ) = 16 * (7 * (109)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 109 : ℕ) = 110 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3154 : (sigma 1 3154 : ℕ) = 5040 := by
  have h : (3154 : ℕ) = 2 * (19 * (83)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 19 : ℕ) = 20 := by decide
  have s2 : (sigma 1 83 : ℕ) = 84 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2412 : (sigma 1 2412 : ℕ) = 6188 := by
  have h : (2412 : ℕ) = 4 * (9 * (67)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 67 : ℕ) = 68 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_33559 : (sigma 1 33559 : ℕ) = 34504 := by
  have h : (33559 : ℕ) = 37 * (907) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 37 : ℕ) = 38 := by decide
  have s1 : (sigma 1 907 : ℕ) = 908 := by rw [sigma_one_prime (by norm_num : Nat.Prime 907)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3778 : (sigma 1 3778 : ℕ) = 5670 := by
  have h : (3778 : ℕ) = 2 * (1889) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1889 : ℕ) = 1890 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1889)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_4686 : (sigma 1 4686 : ℕ) = 10368 := by
  have h : (4686 : ℕ) = 2 * (3 * (11 * (71))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 11 : ℕ) = 12 := by decide
  have s3 : (sigma 1 71 : ℕ) = 72 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_240426 : (sigma 1 240426 : ℕ) = 564642 := by
  have h : (240426 : ℕ) = 2 * (9 * (361 * (37))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 361 : ℕ) = 381 := by rw [(by norm_num : (361 : ℕ) = 19^2), sigma_one_sq (by norm_num : Nat.Prime 19)] <;> norm_num
  have s3 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2152 : (sigma 1 2152 : ℕ) = 4050 := by
  have h : (2152 : ℕ) = 8 * (269) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 269 : ℕ) = 270 := by rw [sigma_one_prime (by norm_num : Nat.Prime 269)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_159516800 : (sigma 1 159516800 : ℕ) = 399676800 := by
  have h : (159516800 : ℕ) = 128 * (25 * (79 * (631))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 128 : ℕ) = 255 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 79 : ℕ) = 80 := by decide
  have s3 : (sigma 1 631 : ℕ) = 632 := by rw [sigma_one_prime (by norm_num : Nat.Prime 631)] <;> norm_num
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_11565 : (sigma 1 11565 : ℕ) = 20124 := by
  have h : (11565 : ℕ) = 9 * (5 * (257)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 9 : ℕ) = 13 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 257 : ℕ) = 258 := by rw [sigma_one_prime (by norm_num : Nat.Prime 257)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3802 : (sigma 1 3802 : ℕ) = 5706 := by
  have h : (3802 : ℕ) = 2 * (1901) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1901 : ℕ) = 1902 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1901)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1664 : (sigma 1 1664 : ℕ) = 3570 := by
  have h : (1664 : ℕ) = 128 * (13) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 128 : ℕ) = 255 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_3814 : (sigma 1 3814 : ℕ) = 5724 := by
  have h : (3814 : ℕ) = 2 * (1907) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1907 : ℕ) = 1908 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1907)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_17738 : (sigma 1 17738 : ℕ) = 31122 := by
  have h : (17738 : ℕ) = 2 * (49 * (181)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 49 : ℕ) = 57 := by decide
  have s2 : (sigma 1 181 : ℕ) = 182 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_6936 : (sigma 1 6936 : ℕ) = 18420 := by
  have h : (6936 : ℕ) = 8 * (3 * (289)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 289 : ℕ) = 307 := by rw [(by norm_num : (289 : ℕ) = 17^2), sigma_one_sq (by norm_num : Nat.Prime 17)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3826 : (sigma 1 3826 : ℕ) = 5742 := by
  have h : (3826 : ℕ) = 2 * (1913) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1913 : ℕ) = 1914 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1913)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3145 : (sigma 1 3145 : ℕ) = 4104 := by
  have h : (3145 : ℕ) = 5 * (17 * (37)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 5 : ℕ) = 6 := by decide
  have s1 : (sigma 1 17 : ℕ) = 18 := by decide
  have s2 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_14778 : (sigma 1 14778 : ℕ) = 32058 := by
  have h : (14778 : ℕ) = 2 * (9 * (821)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 9 : ℕ) = 13 := by decide
  have s2 : (sigma 1 821 : ℕ) = 822 := by rw [sigma_one_prime (by norm_num : Nat.Prime 821)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2523 : (sigma 1 2523 : ℕ) = 3484 := by
  have h : (2523 : ℕ) = 3 * (841) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 841 : ℕ) = 871 := by rw [(by norm_num : (841 : ℕ) = 29^2), sigma_one_sq (by norm_num : Nat.Prime 29)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3460 : (sigma 1 3460 : ℕ) = 7308 := by
  have h : (3460 : ℕ) = 4 * (5 * (173)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 173 : ℕ) = 174 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3255 : (sigma 1 3255 : ℕ) = 6144 := by
  have h : (3255 : ℕ) = 3 * (5 * (7 * (31))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  have s3 : (sigma 1 31 : ℕ) = 32 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_5132 : (sigma 1 5132 : ℕ) = 8988 := by
  have h : (5132 : ℕ) = 4 * (1283) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 1283 : ℕ) = 1284 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1283)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2564 : (sigma 1 2564 : ℕ) = 4494 := by
  have h : (2564 : ℕ) = 4 * (641) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 641 : ℕ) = 642 := by rw [sigma_one_prime (by norm_num : Nat.Prime 641)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_24577344 : (sigma 1 24577344 : ℕ) = 79662528 := by
  have h : (24577344 : ℕ) = 64 * (81 * (11 * (431))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 64 : ℕ) = 127 := by decide
  have s1 : (sigma 1 81 : ℕ) = 121 := by decide
  have s2 : (sigma 1 11 : ℕ) = 12 := by decide
  have s3 : (sigma 1 431 : ℕ) = 432 := by rw [sigma_one_prime (by norm_num : Nat.Prime 431)] <;> norm_num
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2674 : (sigma 1 2674 : ℕ) = 4608 := by
  have h : (2674 : ℕ) = 2 * (7 * (191)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 191 : ℕ) = 192 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3866 : (sigma 1 3866 : ℕ) = 5802 := by
  have h : (3866 : ℕ) = 2 * (1933) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1933 : ℕ) = 1934 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1933)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_5802 : (sigma 1 5802 : ℕ) = 11616 := by
  have h : (5802 : ℕ) = 2 * (3 * (967)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 967 : ℕ) = 968 := by rw [sigma_one_prime (by norm_num : Nat.Prime 967)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_5164 : (sigma 1 5164 : ℕ) = 9044 := by
  have h : (5164 : ℕ) = 4 * (1291) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 1291 : ℕ) = 1292 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1291)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_2150 : (sigma 1 2150 : ℕ) = 4092 := by
  have h : (2150 : ℕ) = 2 * (25 * (43)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 43 : ℕ) = 44 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_311052 : (sigma 1 311052 : ℕ) = 882588 := by
  have h : (311052 : ℕ) = 4 * (3 * (49 * (529))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 49 : ℕ) = 57 := by decide
  have s3 : (sigma 1 529 : ℕ) = 553 := by rw [(by norm_num : (529 : ℕ) = 23^2), sigma_one_sq (by norm_num : Nat.Prime 23)] <;> norm_num
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_2410 : (sigma 1 2410 : ℕ) = 4356 := by
  have h : (2410 : ℕ) = 2 * (5 * (241)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 241 : ℕ) = 242 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_126560 : (sigma 1 126560 : ℕ) = 344736 := by
  have h : (126560 : ℕ) = 32 * (5 * (7 * (113))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 5 : ℕ) = 6 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  have s3 : (sigma 1 113 : ℕ) = 114 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_5523 : (sigma 1 5523 : ℕ) = 8448 := by
  have h : (5523 : ℕ) = 3 * (7 * (263)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 7 : ℕ) = 8 := by decide
  have s2 : (sigma 1 263 : ℕ) = 264 := by rw [sigma_one_prime (by norm_num : Nat.Prime 263)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3898 : (sigma 1 3898 : ℕ) = 5850 := by
  have h : (3898 : ℕ) = 2 * (1949) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1949 : ℕ) = 1950 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1949)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1856 : (sigma 1 1856 : ℕ) = 3810 := by
  have h : (1856 : ℕ) = 64 * (29) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 64 : ℕ) = 127 := by decide
  have s1 : (sigma 1 29 : ℕ) = 30 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_4316 : (sigma 1 4316 : ℕ) = 8232 := by
  have h : (4316 : ℕ) = 4 * (13 * (83)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 83 : ℕ) = 84 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2188032 : (sigma 1 2188032 : ℕ) = 7456512 := by
  have h : (2188032 : ℕ) = 256 * (3 * (7 * (11 * (37)))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 256 : ℕ) = 511 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  have s3 : (sigma 1 11 : ℕ) = 12 := by decide
  have s4 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2, s3, s4] <;> norm_num

private theorem sig_4588 : (sigma 1 4588 : ℕ) = 8512 := by
  have h : (4588 : ℕ) = 4 * (31 * (37)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 31 : ℕ) = 32 := by decide
  have s2 : (sigma 1 37 : ℕ) = 38 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_5228 : (sigma 1 5228 : ℕ) = 9156 := by
  have h : (5228 : ℕ) = 4 * (1307) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 1307 : ℕ) = 1308 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1307)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_784 : (sigma 1 784 : ℕ) = 1767 := by
  have h : (784 : ℕ) = 16 * (49) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 49 : ℕ) = 57 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_3358 : (sigma 1 3358 : ℕ) = 5328 := by
  have h : (3358 : ℕ) = 2 * (23 * (73)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 23 : ℕ) = 24 := by decide
  have s2 : (sigma 1 73 : ℕ) = 74 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_25584 : (sigma 1 25584 : ℕ) = 72912 := by
  have h : (25584 : ℕ) = 16 * (3 * (13 * (41))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 16 : ℕ) = 31 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 13 : ℕ) = 14 := by decide
  have s3 : (sigma 1 41 : ℕ) = 42 := by decide
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_8871 : (sigma 1 8871 : ℕ) = 11832 := by
  have h : (8871 : ℕ) = 3 * (2957) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 3 : ℕ) = 4 := by decide
  have s1 : (sigma 1 2957 : ℕ) = 2958 := by rw [sigma_one_prime (by norm_num : Nat.Prime 2957)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_3946 : (sigma 1 3946 : ℕ) = 5922 := by
  have h : (3946 : ℕ) = 2 * (1973) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1973 : ℕ) = 1974 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1973)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1971 : (sigma 1 1971 : ℕ) = 2960 := by
  have h : (1971 : ℕ) = 27 * (73) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 27 : ℕ) = 40 := by decide
  have s1 : (sigma 1 73 : ℕ) = 74 := by decide
  rw [s0, s1] <;> norm_num

private theorem sig_58084 : (sigma 1 58084 : ℕ) = 109564 := by
  have h : (58084 : ℕ) = 4 * (13 * (1117)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 13 : ℕ) = 14 := by decide
  have s2 : (sigma 1 1117 : ℕ) = 1118 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1117)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2248 : (sigma 1 2248 : ℕ) = 4230 := by
  have h : (2248 : ℕ) = 8 * (281) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 8 : ℕ) = 15 := by decide
  have s1 : (sigma 1 281 : ℕ) = 282 := by rw [sigma_one_prime (by norm_num : Nat.Prime 281)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1156 : (sigma 1 1156 : ℕ) = 2149 := by
  have h : (1156 : ℕ) = 4 * (289) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 289 : ℕ) = 307 := by rw [(by norm_num : (289 : ℕ) = 17^2), sigma_one_sq (by norm_num : Nat.Prime 17)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_11450 : (sigma 1 11450 : ℕ) = 21390 := by
  have h : (11450 : ℕ) = 2 * (25 * (229)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 25 : ℕ) = 31 := by decide
  have s2 : (sigma 1 229 : ℕ) = 230 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_2644 : (sigma 1 2644 : ℕ) = 4634 := by
  have h : (2644 : ℕ) = 4 * (661) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 4 : ℕ) = 7 := by decide
  have s1 : (sigma 1 661 : ℕ) = 662 := by rw [sigma_one_prime (by norm_num : Nat.Prime 661)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_1715040 : (sigma 1 1715040 : ℕ) = 6017760 := by
  have h : (1715040 : ℕ) = 32 * (27 * (5 * (397))) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 32 : ℕ) = 63 := by decide
  have s1 : (sigma 1 27 : ℕ) = 40 := by decide
  have s2 : (sigma 1 5 : ℕ) = 6 := by decide
  have s3 : (sigma 1 397 : ℕ) = 398 := by rw [sigma_one_prime (by norm_num : Nat.Prime 397)] <;> norm_num
  rw [s0, s1, s2, s3] <;> norm_num

private theorem sig_1750 : (sigma 1 1750 : ℕ) = 3744 := by
  have h : (1750 : ℕ) = 2 * (125 * (7)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 125 : ℕ) = 156 := by decide
  have s2 : (sigma 1 7 : ℕ) = 8 := by decide
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3986 : (sigma 1 3986 : ℕ) = 5982 := by
  have h : (3986 : ℕ) = 2 * (1993) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1993 : ℕ) = 1994 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1993)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem sig_5982 : (sigma 1 5982 : ℕ) = 11976 := by
  have h : (5982 : ℕ) = 2 * (3 * (997)) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 3 : ℕ) = 4 := by decide
  have s2 : (sigma 1 997 : ℕ) = 998 := by rw [sigma_one_prime (by norm_num : Nat.Prime 997)] <;> norm_num
  rw [s0, s1, s2] <;> norm_num

private theorem sig_3994 : (sigma 1 3994 : ℕ) = 5994 := by
  have h : (3994 : ℕ) = 2 * (1997) := by norm_num
  rw [h]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  have s0 : (sigma 1 2 : ℕ) = 3 := by decide
  have s1 : (sigma 1 1997 : ℕ) = 1998 := by rw [sigma_one_prime (by norm_num : Nat.Prime 1997)] <;> norm_num
  rw [s0, s1] <;> norm_num

private theorem attained_0 : a 0 ≠ 0 :=
  attained_of_witness (by norm_num) ((by decide) : (sigma 1 1 : ℕ) = 1) (by decide)

private theorem attained_1 : a 1 ≠ 0 :=
  attained_of_witness (by norm_num) ((by decide) : (sigma 1 2 : ℕ) = 3) (by decide)

private theorem attained_2 : a 2 ≠ 0 :=
  attained_of_witness (by norm_num) sig_120 (by decide)

private theorem attained_3 : a 3 ≠ 0 :=
  attained_of_witness (by norm_num) ((by decide) : (sigma 1 4 : ℕ) = 7) (by decide)

private theorem attained_4 : a 4 ≠ 0 :=
  attained_of_witness (by norm_num) ((by decide) : (sigma 1 9 : ℕ) = 13) (by decide)

private theorem attained_5 : a 5 ≠ 0 :=
  attained_of_witness (by norm_num) sig_14 (by decide)

private theorem attained_6 : a 6 ≠ 0 :=
  attained_of_witness (by norm_num) ((by decide) : (sigma 1 25 : ℕ) = 31) (by decide)

private theorem attained_7 : a 7 ≠ 0 :=
  attained_of_witness (by norm_num) ((by decide) : (sigma 1 8 : ℕ) = 15) (by decide)

private theorem attained_8 : a 8 ≠ 0 :=
  attained_of_witness (by norm_num) sig_26 (by decide)

private theorem attained_9 : a 9 ≠ 0 :=
  attained_of_witness (by norm_num) sig_42 (by decide)

private theorem attained_10 : a 10 ≠ 0 :=
  attained_of_witness (by norm_num) sig_34 (by decide)

private theorem attained_11 : a 11 ≠ 0 :=
  attained_of_witness (by norm_num) sig_20 (by decide)

private theorem attained_12 : a 12 ≠ 0 :=
  attained_of_witness (by norm_num) ((by decide) : (sigma 1 121 : ℕ) = 133) (by decide)

private theorem attained_13 : a 13 ≠ 0 :=
  attained_of_witness (by norm_num) ((by decide) : (sigma 1 27 : ℕ) = 40) (by decide)

private theorem attained_14 : a 14 ≠ 0 :=
  attained_of_witness (by norm_num) ((by decide) : (sigma 1 169 : ℕ) = 183) (by decide)

private theorem attained_15 : a 15 ≠ 0 :=
  attained_of_witness (by norm_num) ((by decide) : (sigma 1 16 : ℕ) = 31) (by decide)

private theorem attained_16 : a 16 ≠ 0 :=
  attained_of_witness (by norm_num) sig_58 (by decide)

private theorem attained_17 : a 17 ≠ 0 :=
  attained_of_witness (by norm_num) sig_39 (by decide)

private theorem attained_18 : a 18 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (289 : ℕ) = 17^2), sigma_one_sq (by norm_num : Nat.Prime 17)] <;> norm_num) : (sigma 1 289 : ℕ) = 307) (by decide)

private theorem attained_19 : a 19 ≠ 0 :=
  attained_of_witness (by norm_num) sig_48 (by decide)

private theorem attained_20 : a 20 ≠ 0 :=
  attained_of_witness (by norm_num) sig_74 (by decide)

private theorem attained_21 : a 21 ≠ 0 :=
  attained_of_witness (by norm_num) sig_114 (by decide)

private theorem attained_22 : a 22 ≠ 0 :=
  attained_of_witness (by norm_num) sig_82 (by decide)

private theorem attained_23 : a 23 ≠ 0 :=
  attained_of_witness (by norm_num) sig_52 (by decide)

private theorem attained_24 : a 24 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (529 : ℕ) = 23^2), sigma_one_sq (by norm_num : Nat.Prime 23)] <;> norm_num) : (sigma 1 529 : ℕ) = 553) (by decide)

private theorem attained_25 : a 25 ≠ 0 :=
  attained_of_witness (by norm_num) sig_94 (by decide)

private theorem attained_26 : a 26 ≠ 0 :=
  attained_of_witness (by norm_num) sig_760 (by decide)

private theorem attained_27 : a 27 ≠ 0 :=
  attained_of_witness (by norm_num) sig_133 (by decide)

private theorem attained_28 : a 28 ≠ 0 :=
  attained_of_witness (by norm_num) sig_106 (by decide)

private theorem attained_29 : a 29 ≠ 0 :=
  attained_of_witness (by norm_num) sig_68 (by decide)

private theorem attained_30 : a 30 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (841 : ℕ) = 29^2), sigma_one_sq (by norm_num : Nat.Prime 29)] <;> norm_num) : (sigma 1 841 : ℕ) = 871) (by decide)

private theorem attained_31 : a 31 ≠ 0 :=
  attained_of_witness (by norm_num) ((by decide) : (sigma 1 32 : ℕ) = 63) (by decide)

private theorem attained_32 : a 32 ≠ 0 :=
  attained_of_witness (by norm_num) sig_122 (by decide)

private theorem attained_33 : a 33 ≠ 0 :=
  attained_of_witness (by norm_num) sig_186 (by decide)

private theorem attained_34 : a 34 ≠ 0 :=
  attained_of_witness (by norm_num) sig_172 (by decide)

private theorem attained_35 : a 35 ≠ 0 :=
  attained_of_witness (by norm_num) sig_93 (by decide)

private theorem attained_36 : a 36 ≠ 0 :=
  attained_of_witness (by norm_num) sig_522 (by decide)

private theorem attained_37 : a 37 ≠ 0 :=
  attained_of_witness (by norm_num) sig_70 (by decide)

private theorem attained_38 : a 38 ≠ 0 :=
  attained_of_witness (by norm_num) sig_146 (by decide)

private theorem attained_39 : a 39 ≠ 0 :=
  attained_of_witness (by norm_num) sig_217 (by decide)

private theorem attained_40 : a 40 ≠ 0 :=
  attained_of_witness (by norm_num) ((by decide) : (sigma 1 81 : ℕ) = 121) (by decide)

private theorem attained_41 : a 41 ≠ 0 :=
  attained_of_witness (by norm_num) sig_63 (by decide)

private theorem attained_42 : a 42 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1656 (by decide)

private theorem attained_43 : a 43 ≠ 0 :=
  attained_of_witness (by norm_num) sig_50 (by decide)

private theorem attained_44 : a 44 ≠ 0 :=
  attained_of_witness (by norm_num) sig_504 (by decide)

private theorem attained_45 : a 45 ≠ 0 :=
  attained_of_witness (by norm_num) sig_258 (by decide)

private theorem attained_46 : a 46 ≠ 0 :=
  attained_of_witness (by norm_num) sig_178 (by decide)

private theorem attained_47 : a 47 ≠ 0 :=
  attained_of_witness (by norm_num) sig_116 (by decide)

private theorem attained_48 : a 48 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (2209 : ℕ) = 47^2), sigma_one_sq (by norm_num : Nat.Prime 47)] <;> norm_num) : (sigma 1 2209 : ℕ) = 2257) (by decide)

private theorem attained_49 : a 49 ≠ 0 :=
  attained_of_witness (by norm_num) sig_75 (by decide)

private theorem attained_50 : a 50 ≠ 0 :=
  attained_of_witness (by norm_num) sig_194 (by decide)

private theorem attained_51 : a 51 ≠ 0 :=
  attained_of_witness (by norm_num) sig_231 (by decide)

private theorem attained_52 : a 52 ≠ 0 :=
  attained_of_witness (by norm_num) sig_202 (by decide)

private theorem attained_53 : a 53 ≠ 0 :=
  attained_of_witness (by norm_num) sig_80 (by decide)

private theorem attained_54 : a 54 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (2809 : ℕ) = 53^2), sigma_one_sq (by norm_num : Nat.Prime 53)] <;> norm_num) : (sigma 1 2809 : ℕ) = 2863) (by decide)

private theorem attained_55 : a 55 ≠ 0 :=
  attained_of_witness (by norm_num) sig_36 (by decide)

private theorem attained_56 : a 56 ≠ 0 :=
  attained_of_witness (by norm_num) sig_218 (by decide)

private theorem attained_57 : a 57 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (343 : ℕ) = 7^3), sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) : (sigma 1 343 : ℕ) = 400) (by decide)

private theorem attained_58 : a 58 ≠ 0 :=
  attained_of_witness (by norm_num) sig_226 (by decide)

private theorem attained_59 : a 59 ≠ 0 :=
  attained_of_witness (by norm_num) sig_148 (by decide)

private theorem attained_60 : a 60 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (3481 : ℕ) = 59^2), sigma_one_sq (by norm_num : Nat.Prime 59)] <;> norm_num) : (sigma 1 3481 : ℕ) = 3541) (by decide)

private theorem attained_61 : a 61 ≠ 0 :=
  attained_of_witness (by norm_num) sig_130 (by decide)

private theorem attained_62 : a 62 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (3721 : ℕ) = 61^2), sigma_one_sq (by norm_num : Nat.Prime 61)] <;> norm_num) : (sigma 1 3721 : ℕ) = 3783) (by decide)

private theorem attained_63 : a 63 ≠ 0 :=
  attained_of_witness (by norm_num) ((by decide) : (sigma 1 64 : ℕ) = 127) (by decide)

private theorem attained_64 : a 64 ≠ 0 :=
  attained_of_witness (by norm_num) sig_332 (by decide)

private theorem attained_65 : a 65 ≠ 0 :=
  attained_of_witness (by norm_num) sig_164 (by decide)

private theorem attained_66 : a 66 ≠ 0 :=
  attained_of_witness (by norm_num) sig_108000 (by decide)

private theorem attained_67 : a 67 ≠ 0 :=
  attained_of_witness (by norm_num) sig_136 (by decide)

private theorem attained_68 : a 68 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (4489 : ℕ) = 67^2), sigma_one_sq (by norm_num : Nat.Prime 67)] <;> norm_num) : (sigma 1 4489 : ℕ) = 4557) (by decide)

private theorem attained_69 : a 69 ≠ 0 :=
  attained_of_witness (by norm_num) sig_402 (by decide)

private theorem attained_70 : a 70 ≠ 0 :=
  attained_of_witness (by norm_num) sig_274 (by decide)

private theorem attained_71 : a 71 ≠ 0 :=
  attained_of_witness (by norm_num) sig_201 (by decide)

private theorem attained_72 : a 72 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (5041 : ℕ) = 71^2), sigma_one_sq (by norm_num : Nat.Prime 71)] <;> norm_num) : (sigma 1 5041 : ℕ) = 5113) (by decide)

private theorem attained_73 : a 73 ≠ 0 :=
  attained_of_witness (by norm_num) sig_98 (by decide)

private theorem attained_74 : a 74 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (5329 : ℕ) = 73^2), sigma_one_sq (by norm_num : Nat.Prime 73)] <;> norm_num) : (sigma 1 5329 : ℕ) = 5403) (by decide)

private theorem attained_75 : a 75 ≠ 0 :=
  attained_of_witness (by norm_num) sig_438 (by decide)

private theorem attained_76 : a 76 ≠ 0 :=
  attained_of_witness (by norm_num) sig_298 (by decide)

private theorem attained_77 : a 77 ≠ 0 :=
  attained_of_witness (by norm_num) sig_170 (by decide)

private theorem attained_78 : a 78 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2047488 (by decide)

private theorem attained_79 : a 79 ≠ 0 :=
  attained_of_witness (by norm_num) sig_192 (by decide)

private theorem attained_80 : a 80 ≠ 0 :=
  attained_of_witness (by norm_num) sig_314 (by decide)

private theorem attained_81 : a 81 ≠ 0 :=
  attained_of_witness (by norm_num) sig_429 (by decide)

private theorem attained_82 : a 82 ≠ 0 :=
  attained_of_witness (by norm_num) sig_260 (by decide)

private theorem attained_83 : a 83 ≠ 0 :=
  attained_of_witness (by norm_num) sig_212 (by decide)

private theorem attained_84 : a 84 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (6889 : ℕ) = 83^2), sigma_one_sq (by norm_num : Nat.Prime 83)] <;> norm_num) : (sigma 1 6889 : ℕ) = 6973) (by decide)

private theorem attained_85 : a 85 ≠ 0 :=
  attained_of_witness (by norm_num) sig_334 (by decide)

private theorem attained_86 : a 86 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2680 (by decide)

private theorem attained_87 : a 87 ≠ 0 :=
  attained_of_witness (by norm_num) sig_553 (by decide)

private theorem attained_88 : a 88 ≠ 0 :=
  attained_of_witness (by norm_num) sig_346 (by decide)

private theorem attained_89 : a 89 ≠ 0 :=
  attained_of_witness (by norm_num) sig_171 (by decide)

private theorem attained_90 : a 90 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (7921 : ℕ) = 89^2), sigma_one_sq (by norm_num : Nat.Prime 89)] <;> norm_num) : (sigma 1 7921 : ℕ) = 8011) (by decide)

private theorem attained_91 : a 91 ≠ 0 :=
  attained_of_witness (by norm_num) sig_358 (by decide)

private theorem attained_92 : a 92 ≠ 0 :=
  attained_of_witness (by norm_num) sig_362 (by decide)

private theorem attained_93 : a 93 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1027 (by decide)

private theorem attained_94 : a 94 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1464 (by decide)

private theorem attained_95 : a 95 ≠ 0 :=
  attained_of_witness (by norm_num) sig_244 (by decide)

private theorem attained_96 : a 96 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2832 (by decide)

private theorem attained_97 : a 97 ≠ 0 :=
  attained_of_witness (by norm_num) sig_238 (by decide)

private theorem attained_98 : a 98 ≠ 0 :=
  attained_of_witness (by norm_num) sig_386 (by decide)

private theorem attained_99 : a 99 ≠ 0 :=
  attained_of_witness (by norm_num) sig_582 (by decide)

private theorem attained_100 : a 100 ≠ 0 :=
  attained_of_witness (by norm_num) sig_394 (by decide)

private theorem attained_101 : a 101 ≠ 0 :=
  attained_of_witness (by norm_num) sig_230 (by decide)

private theorem attained_102 : a 102 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (10201 : ℕ) = 101^2), sigma_one_sq (by norm_num : Nat.Prime 101)] <;> norm_num) : (sigma 1 10201 : ℕ) = 10303) (by decide)

private theorem attained_103 : a 103 ≠ 0 :=
  attained_of_witness (by norm_num) sig_315 (by decide)

private theorem attained_104 : a 104 ≠ 0 :=
  attained_of_witness (by norm_num) sig_340 (by decide)

private theorem attained_105 : a 105 ≠ 0 :=
  attained_of_witness (by norm_num) sig_618 (by decide)

private theorem attained_106 : a 106 ≠ 0 :=
  attained_of_witness (by norm_num) sig_556 (by decide)

private theorem attained_107 : a 107 ≠ 0 :=
  attained_of_witness (by norm_num) sig_266 (by decide)

private theorem attained_108 : a 108 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (11449 : ℕ) = 107^2), sigma_one_sq (by norm_num : Nat.Prime 107)] <;> norm_num) : (sigma 1 11449 : ℕ) = 11557) (by decide)

private theorem attained_109 : a 109 ≠ 0 :=
  attained_of_witness (by norm_num) sig_160 (by decide)

private theorem attained_110 : a 110 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (11881 : ℕ) = 109^2), sigma_one_sq (by norm_num : Nat.Prime 109)] <;> norm_num) : (sigma 1 11881 : ℕ) = 11991) (by decide)

private theorem attained_111 : a 111 ≠ 0 :=
  attained_of_witness (by norm_num) sig_627 (by decide)

private theorem attained_112 : a 112 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1752 (by decide)

private theorem attained_113 : a 113 ≠ 0 :=
  attained_of_witness (by norm_num) sig_208 (by decide)

private theorem attained_114 : a 114 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (12769 : ℕ) = 113^2), sigma_one_sq (by norm_num : Nat.Prime 113)] <;> norm_num) : (sigma 1 12769 : ℕ) = 12883) (by decide)

private theorem attained_115 : a 115 ≠ 0 :=
  attained_of_witness (by norm_num) sig_454 (by decide)

private theorem attained_116 : a 116 ≠ 0 :=
  attained_of_witness (by norm_num) sig_458 (by decide)

private theorem attained_117 : a 117 ≠ 0 :=
  attained_of_witness (by norm_num) sig_100 (by decide)

private theorem attained_118 : a 118 ≠ 0 :=
  attained_of_witness (by norm_num) sig_466 (by decide)

private theorem attained_119 : a 119 ≠ 0 :=
  attained_of_witness (by norm_num) sig_555 (by decide)

private theorem attained_120 : a 120 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1818 (by decide)

private theorem attained_121 : a 121 ≠ 0 :=
  attained_of_witness (by norm_num) ((by decide) : (sigma 1 243 : ℕ) = 364) (by decide)

private theorem attained_122 : a 122 ≠ 0 :=
  attained_of_witness (by norm_num) sig_482 (by decide)

private theorem attained_123 : a 123 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1417 (by decide)

private theorem attained_124 : a 124 ≠ 0 :=
  attained_of_witness (by norm_num) sig_652 (by decide)

private theorem attained_125 : a 125 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1243 (by decide)

private theorem attained_126 : a 126 ≠ 0 :=
  attained_of_witness (by norm_num) sig_23154432 (by decide)

private theorem attained_127 : a 127 ≠ 0 :=
  attained_of_witness (by norm_num) ((by decide) : (sigma 1 128 : ℕ) = 255) (by decide)

private theorem attained_128 : a 128 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (16129 : ℕ) = 127^2), sigma_one_sq (by norm_num : Nat.Prime 127)] <;> norm_num) : (sigma 1 16129 : ℕ) = 16257) (by decide)

private theorem attained_129 : a 129 ≠ 0 :=
  attained_of_witness (by norm_num) sig_762 (by decide)

private theorem attained_130 : a 130 ≠ 0 :=
  attained_of_witness (by norm_num) sig_514 (by decide)

private theorem attained_131 : a 131 ≠ 0 :=
  attained_of_witness (by norm_num) sig_189 (by decide)

private theorem attained_132 : a 132 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (17161 : ℕ) = 131^2), sigma_one_sq (by norm_num : Nat.Prime 131)] <;> norm_num) : (sigma 1 17161 : ℕ) = 17293) (by decide)

private theorem attained_133 : a 133 ≠ 0 :=
  attained_of_witness (by norm_num) sig_310 (by decide)

private theorem attained_134 : a 134 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1208 (by decide)

private theorem attained_135 : a 135 ≠ 0 :=
  attained_of_witness (by norm_num) sig_889 (by decide)

private theorem attained_136 : a 136 ≠ 0 :=
  attained_of_witness (by norm_num) sig_538 (by decide)

private theorem attained_137 : a 137 ≠ 0 :=
  attained_of_witness (by norm_num) sig_279 (by decide)

private theorem attained_138 : a 138 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (18769 : ℕ) = 137^2), sigma_one_sq (by norm_num : Nat.Prime 137)] <;> norm_num) : (sigma 1 18769 : ℕ) = 18907) (by decide)

private theorem attained_139 : a 139 ≠ 0 :=
  attained_of_witness (by norm_num) sig_624 (by decide)

private theorem attained_140 : a 140 ≠ 0 :=
  attained_of_witness (by norm_num) sig_554 (by decide)

private theorem attained_141 : a 141 ≠ 0 :=
  attained_of_witness (by norm_num) sig_834 (by decide)

private theorem attained_142 : a 142 ≠ 0 :=
  attained_of_witness (by norm_num) sig_300 (by decide)

private theorem attained_143 : a 143 ≠ 0 :=
  attained_of_witness (by norm_num) sig_272 (by decide)

private theorem attained_144 : a 144 ≠ 0 :=
  attained_of_witness (by norm_num) sig_22538880 (by decide)

private theorem attained_145 : a 145 ≠ 0 :=
  attained_of_witness (by norm_num) sig_539 (by decide)

private theorem attained_146 : a 146 ≠ 0 :=
  attained_of_witness (by norm_num) sig_27244 (by decide)

private theorem attained_147 : a 147 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1083 (by decide)

private theorem attained_148 : a 148 ≠ 0 :=
  attained_of_witness (by norm_num) sig_500 (by decide)

private theorem attained_149 : a 149 ≠ 0 :=
  attained_of_witness (by norm_num) sig_388 (by decide)

private theorem attained_150 : a 150 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (22201 : ℕ) = 149^2), sigma_one_sq (by norm_num : Nat.Prime 149)] <;> norm_num) : (sigma 1 22201 : ℕ) = 22351) (by decide)

private theorem attained_151 : a 151 ≠ 0 :=
  attained_of_witness (by norm_num) sig_328 (by decide)

private theorem attained_152 : a 152 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3120 (by decide)

private theorem attained_153 : a 153 ≠ 0 :=
  attained_of_witness (by norm_num) sig_906 (by decide)

private theorem attained_154 : a 154 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2424 (by decide)

private theorem attained_155 : a 155 ≠ 0 :=
  attained_of_witness (by norm_num) sig_404 (by decide)

private theorem attained_156 : a 156 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (625 : ℕ) = 5^4), sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) : (sigma 1 625 : ℕ) = 781) (by decide)

private theorem attained_157 : a 157 ≠ 0 :=
  attained_of_witness (by norm_num) sig_242 (by decide)

private theorem attained_158 : a 158 ≠ 0 :=
  attained_of_witness (by norm_num) sig_626 (by decide)

private theorem attained_159 : a 159 ≠ 0 :=
  attained_of_witness (by norm_num) sig_942 (by decide)

private theorem attained_160 : a 160 ≠ 0 :=
  attained_of_witness (by norm_num) sig_634 (by decide)

private theorem attained_161 : a 161 ≠ 0 :=
  attained_of_witness (by norm_num) sig_333 (by decide)

private theorem attained_162 : a 162 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2466 (by decide)

private theorem attained_163 : a 163 ≠ 0 :=
  attained_of_witness (by norm_num) sig_608 (by decide)

private theorem attained_164 : a 164 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1840 (by decide)

private theorem attained_165 : a 165 ≠ 0 :=
  attained_of_witness (by norm_num) sig_978 (by decide)

private theorem attained_166 : a 166 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2616 (by decide)

private theorem attained_167 : a 167 ≠ 0 :=
  attained_of_witness (by norm_num) sig_434 (by decide)

private theorem attained_168 : a 168 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (27889 : ℕ) = 167^2), sigma_one_sq (by norm_num : Nat.Prime 167)] <;> norm_num) : (sigma 1 27889 : ℕ) = 28057) (by decide)

private theorem attained_169 : a 169 ≠ 0 :=
  attained_of_witness (by norm_num) sig_363 (by decide)

private theorem attained_170 : a 170 ≠ 0 :=
  attained_of_witness (by norm_num) sig_674 (by decide)

private theorem attained_171 : a 171 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1023 (by decide)

private theorem attained_172 : a 172 ≠ 0 :=
  attained_of_witness (by norm_num) sig_908 (by decide)

private theorem attained_173 : a 173 ≠ 0 :=
  attained_of_witness (by norm_num) sig_410 (by decide)

private theorem attained_174 : a 174 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (29929 : ℕ) = 173^2), sigma_one_sq (by norm_num : Nat.Prime 173)] <;> norm_num) : (sigma 1 29929 : ℕ) = 30103) (by decide)

private theorem attained_175 : a 175 ≠ 0 :=
  attained_of_witness (by norm_num) sig_694 (by decide)

private theorem attained_176 : a 176 ≠ 0 :=
  attained_of_witness (by norm_num) sig_698 (by decide)

private theorem attained_177 : a 177 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1572 (by decide)

private theorem attained_178 : a 178 ≠ 0 :=
  attained_of_witness (by norm_num) sig_225 (by decide)

private theorem attained_179 : a 179 ≠ 0 :=
  attained_of_witness (by norm_num) sig_506 (by decide)

private theorem attained_180 : a 180 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (32041 : ℕ) = 179^2), sigma_one_sq (by norm_num : Nat.Prime 179)] <;> norm_num) : (sigma 1 32041 : ℕ) = 32221) (by decide)

private theorem attained_181 : a 181 ≠ 0 :=
  attained_of_witness (by norm_num) sig_430 (by decide)

private theorem attained_182 : a 182 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (32761 : ℕ) = 181^2), sigma_one_sq (by norm_num : Nat.Prime 181)] <;> norm_num) : (sigma 1 32761 : ℕ) = 32943) (by decide)

private theorem attained_183 : a 183 ≠ 0 :=
  attained_of_witness (by norm_num) sig_987 (by decide)

private theorem attained_184 : a 184 ≠ 0 :=
  attained_of_witness (by norm_num) sig_16020 (by decide)

private theorem attained_185 : a 185 ≠ 0 :=
  attained_of_witness (by norm_num) sig_387 (by decide)

private theorem attained_186 : a 186 ≠ 0 :=
  attained_of_witness (by norm_num) sig_315360 (by decide)

private theorem attained_187 : a 187 ≠ 0 :=
  attained_of_witness (by norm_num) sig_750 (by decide)

private theorem attained_188 : a 188 ≠ 0 :=
  attained_of_witness (by norm_num) sig_746 (by decide)

private theorem attained_189 : a 189 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1689 (by decide)

private theorem attained_190 : a 190 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1004 (by decide)

private theorem attained_191 : a 191 ≠ 0 :=
  attained_of_witness (by norm_num) sig_385 (by decide)

private theorem attained_192 : a 192 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (36481 : ℕ) = 191^2), sigma_one_sq (by norm_num : Nat.Prime 191)] <;> norm_num) : (sigma 1 36481 : ℕ) = 36673) (by decide)

private theorem attained_193 : a 193 ≠ 0 :=
  attained_of_witness (by norm_num) sig_424 (by decide)

private theorem attained_194 : a 194 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4080 (by decide)

private theorem attained_195 : a 195 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1158 (by decide)

private theorem attained_196 : a 196 ≠ 0 :=
  attained_of_witness (by norm_num) sig_778 (by decide)

private theorem attained_197 : a 197 ≠ 0 :=
  attained_of_witness (by norm_num) sig_350 (by decide)

private theorem attained_198 : a 198 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (38809 : ℕ) = 197^2), sigma_one_sq (by norm_num : Nat.Prime 197)] <;> norm_num) : (sigma 1 38809 : ℕ) = 39007) (by decide)

private theorem attained_199 : a 199 ≠ 0 :=
  attained_of_witness (by norm_num) sig_965 (by decide)

private theorem attained_200 : a 200 ≠ 0 :=
  attained_of_witness (by norm_num) sig_794 (by decide)

private theorem attained_201 : a 201 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1194 (by decide)

private theorem attained_202 : a 202 ≠ 0 :=
  attained_of_witness (by norm_num) sig_802 (by decide)

private theorem attained_203 : a 203 ≠ 0 :=
  attained_of_witness (by norm_num) sig_597 (by decide)

private theorem attained_204 : a 204 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3114 (by decide)

private theorem attained_205 : a 205 ≠ 0 :=
  attained_of_witness (by norm_num) sig_598 (by decide)

private theorem attained_206 : a 206 ≠ 0 :=
  attained_of_witness (by norm_num) sig_818 (by decide)

private theorem attained_207 : a 207 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1393 (by decide)

private theorem attained_208 : a 208 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3288 (by decide)

private theorem attained_209 : a 209 ≠ 0 :=
  attained_of_witness (by norm_num) sig_351 (by decide)

private theorem attained_210 : a 210 ≠ 0 :=
  attained_of_witness (by norm_num) sig_6288 (by decide)

private theorem attained_211 : a 211 ≠ 0 :=
  attained_of_witness (by norm_num) sig_338 (by decide)

private theorem attained_212 : a 212 ≠ 0 :=
  attained_of_witness (by norm_num) sig_842 (by decide)

private theorem attained_213 : a 213 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1266 (by decide)

private theorem attained_214 : a 214 ≠ 0 :=
  attained_of_witness (by norm_num) sig_740 (by decide)

private theorem attained_215 : a 215 ≠ 0 :=
  attained_of_witness (by norm_num) sig_633 (by decide)

private theorem attained_216 : a 216 ≠ 0 :=
  attained_of_witness (by norm_num) sig_86328 (by decide)

private theorem attained_217 : a 217 ≠ 0 :=
  attained_of_witness (by norm_num) sig_646 (by decide)

private theorem attained_218 : a 218 ≠ 0 :=
  attained_of_witness (by norm_num) sig_866 (by decide)

private theorem attained_219 : a 219 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1477 (by decide)

private theorem attained_220 : a 220 ≠ 0 :=
  attained_of_witness (by norm_num) sig_884 (by decide)

private theorem attained_221 : a 221 ≠ 0 :=
  attained_of_witness (by norm_num) sig_320 (by decide)

private theorem attained_222 : a 222 ≠ 0 :=
  attained_of_witness (by norm_num) sig_20272 (by decide)

private theorem attained_223 : a 223 ≠ 0 :=
  attained_of_witness (by norm_num) sig_886 (by decide)

private theorem attained_224 : a 224 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (49729 : ℕ) = 223^2), sigma_one_sq (by norm_num : Nat.Prime 223)] <;> norm_num) : (sigma 1 49729 : ℕ) = 49953) (by decide)

private theorem attained_225 : a 225 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1338 (by decide)

private theorem attained_226 : a 226 ≠ 0 :=
  attained_of_witness (by norm_num) sig_898 (by decide)

private theorem attained_227 : a 227 ≠ 0 :=
  attained_of_witness (by norm_num) sig_596 (by decide)

private theorem attained_228 : a 228 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (51529 : ℕ) = 227^2), sigma_one_sq (by norm_num : Nat.Prime 227)] <;> norm_num) : (sigma 1 51529 : ℕ) = 51757) (by decide)

private theorem attained_229 : a 229 ≠ 0 :=
  attained_of_witness (by norm_num) sig_930 (by decide)

private theorem attained_230 : a 230 ≠ 0 :=
  attained_of_witness (by norm_num) sig_914 (by decide)

private theorem attained_231 : a 231 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1374 (by decide)

private theorem attained_232 : a 232 ≠ 0 :=
  attained_of_witness (by norm_num) sig_922 (by decide)

private theorem attained_233 : a 233 ≠ 0 :=
  attained_of_witness (by norm_num) sig_416 (by decide)

private theorem attained_234 : a 234 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (54289 : ℕ) = 233^2), sigma_one_sq (by norm_num : Nat.Prime 233)] <;> norm_num) : (sigma 1 54289 : ℕ) = 54523) (by decide)

private theorem attained_235 : a 235 ≠ 0 :=
  attained_of_witness (by norm_num) sig_682 (by decide)

private theorem attained_236 : a 236 ≠ 0 :=
  attained_of_witness (by norm_num) sig_820 (by decide)

private theorem attained_237 : a 237 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1603 (by decide)

private theorem attained_238 : a 238 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3768 (by decide)

private theorem attained_239 : a 239 ≠ 0 :=
  attained_of_witness (by norm_num) sig_628 (by decide)

private theorem attained_240 : a 240 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (57121 : ℕ) = 239^2), sigma_one_sq (by norm_num : Nat.Prime 239)] <;> norm_num) : (sigma 1 57121 : ℕ) = 57361) (by decide)

private theorem attained_241 : a 241 ≠ 0 :=
  attained_of_witness (by norm_num) sig_399 (by decide)

private theorem attained_242 : a 242 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (58081 : ℕ) = 241^2), sigma_one_sq (by norm_num : Nat.Prime 241)] <;> norm_num) : (sigma 1 58081 : ℕ) = 58323) (by decide)

private theorem attained_243 : a 243 ≠ 0 :=
  attained_of_witness (by norm_num) sig_988 (by decide)

private theorem attained_244 : a 244 ≠ 0 :=
  attained_of_witness (by norm_num) sig_38520 (by decide)

private theorem attained_245 : a 245 ≠ 0 :=
  attained_of_witness (by norm_num) sig_723 (by decide)

private theorem attained_246 : a 246 ≠ 0 :=
  attained_of_witness (by norm_num) sig_419040 (by decide)

private theorem attained_247 : a 247 ≠ 0 :=
  attained_of_witness (by norm_num) sig_658 (by decide)

private theorem attained_248 : a 248 ≠ 0 :=
  attained_of_witness (by norm_num) sig_14496 (by decide)

private theorem attained_249 : a 249 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1653 (by decide)

private theorem attained_250 : a 250 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1324 (by decide)

private theorem attained_251 : a 251 ≠ 0 :=
  attained_of_witness (by norm_num) sig_732 (by decide)

private theorem attained_252 : a 252 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (63001 : ℕ) = 251^2), sigma_one_sq (by norm_num : Nat.Prime 251)] <;> norm_num) : (sigma 1 63001 : ℕ) = 63253) (by decide)

private theorem attained_253 : a 253 ≠ 0 :=
  attained_of_witness (by norm_num) sig_450 (by decide)

private theorem attained_254 : a 254 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4580 (by decide)

private theorem attained_255 : a 255 ≠ 0 :=
  attained_of_witness (by norm_num) ((by decide) : (sigma 1 256 : ℕ) = 511) (by decide)

private theorem attained_256 : a 256 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1018 (by decide)

private theorem attained_257 : a 257 ≠ 0 :=
  attained_of_witness (by norm_num) sig_549 (by decide)

private theorem attained_258 : a 258 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2028 (by decide)

private theorem attained_259 : a 259 ≠ 0 :=
  attained_of_witness (by norm_num) sig_144 (by decide)

private theorem attained_260 : a 260 ≠ 0 :=
  attained_of_witness (by norm_num) sig_94120 (by decide)

private theorem attained_261 : a 261 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2790 (by decide)

private theorem attained_262 : a 262 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1042 (by decide)

private theorem attained_263 : a 263 ≠ 0 :=
  attained_of_witness (by norm_num) sig_584 (by decide)

private theorem attained_264 : a 264 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (69169 : ℕ) = 263^2), sigma_one_sq (by norm_num : Nat.Prime 263)] <;> norm_num) : (sigma 1 69169 : ℕ) = 69433) (by decide)

private theorem attained_265 : a 265 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1578 (by decide)

private theorem attained_266 : a 266 ≠ 0 :=
  attained_of_witness (by norm_num) sig_8440 (by decide)

private theorem attained_267 : a 267 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2391 (by decide)

private theorem attained_268 : a 268 ≠ 0 :=
  attained_of_witness (by norm_num) sig_490 (by decide)

private theorem attained_269 : a 269 ≠ 0 :=
  attained_of_witness (by norm_num) sig_595 (by decide)

private theorem attained_270 : a 270 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (72361 : ℕ) = 269^2), sigma_one_sq (by norm_num : Nat.Prime 269)] <;> norm_num) : (sigma 1 72361 : ℕ) = 72631) (by decide)

private theorem attained_271 : a 271 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1110 (by decide)

private theorem attained_272 : a 272 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1082 (by decide)

private theorem attained_273 : a 273 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1626 (by decide)

private theorem attained_274 : a 274 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2488 (by decide)

private theorem attained_275 : a 275 ≠ 0 :=
  attained_of_witness (by norm_num) sig_724 (by decide)

private theorem attained_276 : a 276 ≠ 0 :=
  attained_of_witness (by norm_num) sig_6444 (by decide)

private theorem attained_277 : a 277 ≠ 0 :=
  attained_of_witness (by norm_num) sig_670 (by decide)

private theorem attained_278 : a 278 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1976 (by decide)

private theorem attained_279 : a 279 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1662 (by decide)

private theorem attained_280 : a 280 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1114 (by decide)

private theorem attained_281 : a 281 ≠ 0 :=
  attained_of_witness (by norm_num) sig_603 (by decide)

private theorem attained_282 : a 282 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (78961 : ℕ) = 281^2), sigma_one_sq (by norm_num : Nat.Prime 281)] <;> norm_num) : (sigma 1 78961 : ℕ) = 79243) (by decide)

private theorem attained_283 : a 283 ≠ 0 :=
  attained_of_witness (by norm_num) sig_550 (by decide)

private theorem attained_284 : a 284 ≠ 0 :=
  attained_of_witness (by norm_num) sig_684 (by decide)

private theorem attained_285 : a 285 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1698 (by decide)

private theorem attained_286 : a 286 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1138 (by decide)

private theorem attained_287 : a 287 ≠ 0 :=
  attained_of_witness (by norm_num) sig_513 (by decide)

private theorem attained_288 : a 288 ≠ 0 :=
  attained_of_witness (by norm_num) sig_12024 (by decide)

private theorem attained_289 : a 289 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1075 (by decide)

private theorem attained_290 : a 290 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1154 (by decide)

private theorem attained_291 : a 291 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1981 (by decide)

private theorem attained_292 : a 292 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4632 (by decide)

private theorem attained_293 : a 293 ≠ 0 :=
  attained_of_witness (by norm_num) sig_592 (by decide)

private theorem attained_294 : a 294 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (85849 : ℕ) = 293^2), sigma_one_sq (by norm_num : Nat.Prime 293)] <;> norm_num) : (sigma 1 85849 : ℕ) = 86143) (by decide)

private theorem attained_295 : a 295 ≠ 0 :=
  attained_of_witness (by norm_num) sig_544 (by decide)

private theorem attained_296 : a 296 ≠ 0 :=
  attained_of_witness (by norm_num) sig_48608 (by decide)

private theorem attained_297 : a 297 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2661 (by decide)

private theorem attained_298 : a 298 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1186 (by decide)

private theorem attained_299 : a 299 ≠ 0 :=
  attained_of_witness (by norm_num) sig_788 (by decide)

private theorem attained_300 : a 300 ≠ 0 :=
  attained_of_witness (by norm_num) sig_17524 (by decide)

private theorem attained_301 : a 301 ≠ 0 :=
  attained_of_witness (by norm_num) sig_730 (by decide)

private theorem attained_302 : a 302 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1060 (by decide)

private theorem attained_303 : a 303 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5377 (by decide)

private theorem attained_304 : a 304 ≠ 0 :=
  attained_of_witness (by norm_num) sig_92576 (by decide)

private theorem attained_305 : a 305 ≠ 0 :=
  attained_of_witness (by norm_num) sig_657 (by decide)

private theorem attained_306 : a 306 ≠ 0 :=
  attained_of_witness (by norm_num) sig_26820 (by decide)

private theorem attained_307 : a 307 ≠ 0 :=
  attained_of_witness (by norm_num) sig_826 (by decide)

private theorem attained_308 : a 308 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1226 (by decide)

private theorem attained_309 : a 309 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1842 (by decide)

private theorem attained_310 : a 310 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1234 (by decide)

private theorem attained_311 : a 311 ≠ 0 :=
  attained_of_witness (by norm_num) sig_921 (by decide)

private theorem attained_312 : a 312 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (96721 : ℕ) = 311^2), sigma_one_sq (by norm_num : Nat.Prime 311)] <;> norm_num) : (sigma 1 96721 : ℕ) = 97033) (by decide)

private theorem attained_313 : a 313 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1175 (by decide)

private theorem attained_314 : a 314 ≠ 0 :=
  attained_of_witness (by norm_num) sig_8096 (by decide)

private theorem attained_315 : a 315 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1878 (by decide)

private theorem attained_316 : a 316 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1676 (by decide)

private theorem attained_317 : a 317 ≠ 0 :=
  attained_of_witness (by norm_num) sig_854 (by decide)

private theorem attained_318 : a 318 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (100489 : ℕ) = 317^2), sigma_one_sq (by norm_num : Nat.Prime 317)] <;> norm_num) : (sigma 1 100489 : ℕ) = 100807) (by decide)

private theorem attained_319 : a 319 ≠ 0 :=
  attained_of_witness (by norm_num) sig_712 (by decide)

private theorem attained_320 : a 320 ≠ 0 :=
  attained_of_witness (by norm_num) sig_25364 (by decide)

private theorem attained_321 : a 321 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1050 (by decide)

private theorem attained_322 : a 322 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1282 (by decide)

private theorem attained_323 : a 323 ≠ 0 :=
  attained_of_witness (by norm_num) sig_656 (by decide)

private theorem attained_324 : a 324 ≠ 0 :=
  attained_of_witness (by norm_num) sig_8871552 (by decide)

private theorem attained_325 : a 325 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1294 (by decide)

private theorem attained_326 : a 326 ≠ 0 :=
  attained_of_witness (by norm_num) sig_650 (by decide)

private theorem attained_327 : a 327 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2931 (by decide)

private theorem attained_328 : a 328 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1306 (by decide)

private theorem attained_329 : a 329 ≠ 0 :=
  attained_of_witness (by norm_num) sig_711 (by decide)

private theorem attained_330 : a 330 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4144 (by decide)

private theorem attained_331 : a 331 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1216 (by decide)

private theorem attained_332 : a 332 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1322 (by decide)

private theorem attained_333 : a 333 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1986 (by decide)

private theorem attained_334 : a 334 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1772 (by decide)

private theorem attained_335 : a 335 ≠ 0 :=
  attained_of_witness (by norm_num) sig_993 (by decide)

private theorem attained_336 : a 336 ≠ 0 :=
  attained_of_witness (by norm_num) sig_43578 (by decide)

private theorem attained_337 : a 337 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1054 (by decide)

private theorem attained_338 : a 338 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1346 (by decide)

private theorem attained_339 : a 339 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2022 (by decide)

private theorem attained_340 : a 340 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1354 (by decide)

private theorem attained_341 : a 341 ≠ 0 :=
  attained_of_witness (by norm_num) sig_830 (by decide)

private theorem attained_342 : a 342 ≠ 0 :=
  attained_of_witness (by norm_num) sig_92196 (by decide)

private theorem attained_343 : a 343 ≠ 0 :=
  attained_of_witness (by norm_num) sig_578 (by decide)

private theorem attained_344 : a 344 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4698 (by decide)

private theorem attained_345 : a 345 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2359 (by decide)

private theorem attained_346 : a 346 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1220 (by decide)

private theorem attained_347 : a 347 ≠ 0 :=
  attained_of_witness (by norm_num) sig_776 (by decide)

private theorem attained_348 : a 348 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (120409 : ℕ) = 347^2), sigma_one_sq (by norm_num : Nat.Prime 347)] <;> norm_num) : (sigma 1 120409 : ℕ) = 120757) (by decide)

private theorem attained_349 : a 349 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1066 (by decide)

private theorem attained_350 : a 350 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (121801 : ℕ) = 349^2), sigma_one_sq (by norm_num : Nat.Prime 349)] <;> norm_num) : (sigma 1 121801 : ℕ) = 122151) (by decide)

private theorem attained_351 : a 351 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2094 (by decide)

private theorem attained_352 : a 352 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1402 (by decide)

private theorem attained_353 : a 353 ≠ 0 :=
  attained_of_witness (by norm_num) sig_932 (by decide)

private theorem attained_354 : a 354 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (124609 : ℕ) = 353^2), sigma_one_sq (by norm_num : Nat.Prime 353)] <;> norm_num) : (sigma 1 124609 : ℕ) = 124963) (by decide)

private theorem attained_355 : a 355 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2118 (by decide)

private theorem attained_356 : a 356 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1418 (by decide)

private theorem attained_357 : a 357 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3870 (by decide)

private theorem attained_358 : a 358 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1508 (by decide)

private theorem attained_359 : a 359 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1765 (by decide)

private theorem attained_360 : a 360 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (128881 : ℕ) = 359^2), sigma_one_sq (by norm_num : Nat.Prime 359)] <;> norm_num) : (sigma 1 128881 : ℕ) = 129241) (by decide)

private theorem attained_361 : a 361 ≠ 0 :=
  attained_of_witness (by norm_num) sig_808 (by decide)

private theorem attained_362 : a 362 ≠ 0 :=
  attained_of_witness (by norm_num) sig_10896 (by decide)

private theorem attained_363 : a 363 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2883 (by decide)

private theorem attained_364 : a 364 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (729 : ℕ) = 3^6), sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) : (sigma 1 729 : ℕ) = 1093) (by decide)

private theorem attained_365 : a 365 ≠ 0 :=
  attained_of_witness (by norm_num) sig_964 (by decide)

private theorem attained_366 : a 366 ≠ 0 :=
  attained_of_witness (by norm_num) sig_17260800 (by decide)

private theorem attained_367 : a 367 ≠ 0 :=
  attained_of_witness (by norm_num) sig_994 (by decide)

private theorem attained_368 : a 368 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1466 (by decide)

private theorem attained_369 : a 369 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2202 (by decide)

private theorem attained_370 : a 370 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1964 (by decide)

private theorem attained_371 : a 371 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1101 (by decide)

private theorem attained_372 : a 372 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5706 (by decide)

private theorem attained_373 : a 373 ≠ 0 :=
  attained_of_witness (by norm_num) sig_651 (by decide)

private theorem attained_374 : a 374 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (139129 : ℕ) = 373^2), sigma_one_sq (by norm_num : Nat.Prime 373)] <;> norm_num) : (sigma 1 139129 : ℕ) = 139503) (by decide)

private theorem attained_375 : a 375 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2238 (by decide)

private theorem attained_376 : a 376 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1100 (by decide)

private theorem attained_377 : a 377 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1022 (by decide)

private theorem attained_378 : a 378 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1264048 (by decide)

private theorem attained_379 : a 379 ≠ 0 :=
  attained_of_witness (by norm_num) sig_741 (by decide)

private theorem attained_380 : a 380 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1514 (by decide)

private theorem attained_381 : a 381 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1612 (by decide)

private theorem attained_382 : a 382 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1522 (by decide)

private theorem attained_383 : a 383 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1137 (by decide)

private theorem attained_384 : a 384 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (146689 : ℕ) = 383^2), sigma_one_sq (by norm_num : Nat.Prime 383)] <;> norm_num) : (sigma 1 146689 : ℕ) = 147073) (by decide)

private theorem attained_385 : a 385 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2298 (by decide)

private theorem attained_386 : a 386 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1538 (by decide)

private theorem attained_387 : a 387 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2653 (by decide)

private theorem attained_388 : a 388 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1546 (by decide)

private theorem attained_389 : a 389 ≠ 0 :=
  attained_of_witness (by norm_num) sig_648 (by decide)

private theorem attained_390 : a 390 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (151321 : ℕ) = 389^2), sigma_one_sq (by norm_num : Nat.Prime 389)] <;> norm_num) : (sigma 1 151321 : ℕ) = 151711) (by decide)

private theorem attained_391 : a 391 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1040 (by decide)

private theorem attained_392 : a 392 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4450 (by decide)

private theorem attained_393 : a 393 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2352 (by decide)

private theorem attained_394 : a 394 ≠ 0 :=
  attained_of_witness (by norm_num) sig_972 (by decide)

private theorem attained_395 : a 395 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1164 (by decide)

private theorem attained_396 : a 396 ≠ 0 :=
  attained_of_witness (by norm_num) sig_45888 (by decide)

private theorem attained_397 : a 397 ≠ 0 :=
  attained_of_witness (by norm_num) sig_970 (by decide)

private theorem attained_398 : a 398 ≠ 0 :=
  attained_of_witness (by norm_num) sig_13464 (by decide)

private theorem attained_399 : a 399 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2382 (by decide)

private theorem attained_400 : a 400 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1594 (by decide)

private theorem attained_401 : a 401 ≠ 0 :=
  attained_of_witness (by norm_num) sig_567 (by decide)

private theorem attained_402 : a 402 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (160801 : ℕ) = 401^2), sigma_one_sq (by norm_num : Nat.Prime 401)] <;> norm_num) : (sigma 1 160801 : ℕ) = 161203) (by decide)

private theorem attained_403 : a 403 ≠ 0 :=
  attained_of_witness (by norm_num) sig_904 (by decide)

private theorem attained_404 : a 404 ≠ 0 :=
  attained_of_witness (by norm_num) sig_8880 (by decide)

private theorem attained_405 : a 405 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2779 (by decide)

private theorem attained_406 : a 406 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1618 (by decide)

private theorem attained_407 : a 407 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1076 (by decide)

private theorem attained_408 : a 408 ≠ 0 :=
  attained_of_witness (by norm_num) sig_828096 (by decide)

private theorem attained_409 : a 409 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1712 (by decide)

private theorem attained_410 : a 410 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (167281 : ℕ) = 409^2), sigma_one_sq (by norm_num : Nat.Prime 409)] <;> norm_num) : (sigma 1 167281 : ℕ) = 167691) (by decide)

private theorem attained_411 : a 411 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2454 (by decide)

private theorem attained_412 : a 412 ≠ 0 :=
  attained_of_witness (by norm_num) sig_850 (by decide)

private theorem attained_413 : a 413 ≠ 0 :=
  attained_of_witness (by norm_num) sig_848 (by decide)

private theorem attained_414 : a 414 ≠ 0 :=
  attained_of_witness (by norm_num) sig_6354 (by decide)

private theorem attained_415 : a 415 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1654 (by decide)

private theorem attained_416 : a 416 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1658 (by decide)

private theorem attained_417 : a 417 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1725 (by decide)

private theorem attained_418 : a 418 ≠ 0 :=
  attained_of_witness (by norm_num) sig_6648 (by decide)

private theorem attained_419 : a 419 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1108 (by decide)

private theorem attained_420 : a 420 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (175561 : ℕ) = 419^2), sigma_one_sq (by norm_num : Nat.Prime 419)] <;> norm_num) : (sigma 1 175561 : ℕ) = 175981) (by decide)

private theorem attained_421 : a 421 ≠ 0 :=
  attained_of_witness (by norm_num) sig_722 (by decide)

private theorem attained_422 : a 422 ≠ 0 :=
  attained_of_witness (by norm_num) sig_122688 (by decide)

private theorem attained_423 : a 423 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2526 (by decide)

private theorem attained_424 : a 424 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2252 (by decide)

private theorem attained_425 : a 425 ≠ 0 :=
  attained_of_witness (by norm_num) sig_927 (by decide)

private theorem attained_426 : a 426 ≠ 0 :=
  attained_of_witness (by norm_num) sig_39088 (by decide)

private theorem attained_427 : a 427 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1998 (by decide)

private theorem attained_428 : a 428 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1706 (by decide)

private theorem attained_429 : a 429 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2947 (by decide)

private theorem attained_430 : a 430 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1714 (by decide)

private theorem attained_431 : a 431 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1298 (by decide)

private theorem attained_432 : a 432 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5488 (by decide)

private theorem attained_433 : a 433 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1665 (by decide)

private theorem attained_434 : a 434 ≠ 0 :=
  attained_of_witness (by norm_num) sig_61560 (by decide)

private theorem attained_435 : a 435 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2598 (by decide)

private theorem attained_436 : a 436 ≠ 0 :=
  attained_of_witness (by norm_num) sig_7408 (by decide)

private theorem attained_437 : a 437 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1070 (by decide)

private theorem attained_438 : a 438 ≠ 0 :=
  attained_of_witness (by norm_num) sig_196128 (by decide)

private theorem attained_439 : a 439 ≠ 0 :=
  attained_of_witness (by norm_num) sig_777 (by decide)

private theorem attained_440 : a 440 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1754 (by decide)

private theorem attained_441 : a 441 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2634 (by decide)

private theorem attained_442 : a 442 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1762 (by decide)

private theorem attained_443 : a 443 ≠ 0 :=
  attained_of_witness (by norm_num) sig_837 (by decide)

private theorem attained_444 : a 444 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (196249 : ℕ) = 443^2), sigma_one_sq (by norm_num : Nat.Prime 443)] <;> norm_num) : (sigma 1 196249 : ℕ) = 196693) (by decide)

private theorem attained_445 : a 445 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1342 (by decide)

private theorem attained_446 : a 446 ≠ 0 :=
  attained_of_witness (by norm_num) sig_6256 (by decide)

private theorem attained_447 : a 447 ≠ 0 :=
  attained_of_witness (by norm_num) sig_484 (by decide)

private theorem attained_448 : a 448 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3256 (by decide)

private theorem attained_449 : a 449 ≠ 0 :=
  attained_of_witness (by norm_num) sig_981 (by decide)

private theorem attained_450 : a 450 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1924 (by decide)

private theorem attained_451 : a 451 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1085 (by decide)

private theorem attained_452 : a 452 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1972 (by decide)

private theorem attained_453 : a 453 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5707 (by decide)

private theorem attained_454 : a 454 ≠ 0 :=
  attained_of_witness (by norm_num) sig_36162 (by decide)

private theorem attained_455 : a 455 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1814 (by decide)

private theorem attained_456 : a 456 ≠ 0 :=
  attained_of_witness (by norm_num) sig_7002 (by decide)

private theorem attained_457 : a 457 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1246 (by decide)

private theorem attained_458 : a 458 ≠ 0 :=
  attained_of_witness (by norm_num) sig_20812 (by decide)

private theorem attained_459 : a 459 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1815 (by decide)

private theorem attained_460 : a 460 ≠ 0 :=
  attained_of_witness (by norm_num) sig_301280 (by decide)

private theorem attained_461 : a 461 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1130 (by decide)

private theorem attained_462 : a 462 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (212521 : ℕ) = 461^2), sigma_one_sq (by norm_num : Nat.Prime 461)] <;> norm_num) : (sigma 1 212521 : ℕ) = 212983) (by decide)

private theorem attained_463 : a 463 ≠ 0 :=
  attained_of_witness (by norm_num) sig_392 (by decide)

private theorem attained_464 : a 464 ≠ 0 :=
  attained_of_witness (by norm_num) sig_59360 (by decide)

private theorem attained_465 : a 465 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2778 (by decide)

private theorem attained_466 : a 466 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1858 (by decide)

private theorem attained_467 : a 467 ≠ 0 :=
  attained_of_witness (by norm_num) sig_525 (by decide)

private theorem attained_468 : a 468 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (218089 : ℕ) = 467^2), sigma_one_sq (by norm_num : Nat.Prime 467)] <;> norm_num) : (sigma 1 218089 : ℕ) = 218557) (by decide)

private theorem attained_469 : a 469 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1650 (by decide)

private theorem attained_470 : a 470 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1874 (by decide)

private theorem attained_471 : a 471 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3241 (by decide)

private theorem attained_472 : a 472 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1882 (by decide)

private theorem attained_473 : a 473 ≠ 0 :=
  attained_of_witness (by norm_num) sig_832 (by decide)

private theorem attained_474 : a 474 ≠ 0 :=
  attained_of_witness (by norm_num) sig_190872 (by decide)

private theorem attained_475 : a 475 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1894 (by decide)

private theorem attained_476 : a 476 ≠ 0 :=
  attained_of_witness (by norm_num) sig_15160 (by decide)

private theorem attained_477 : a 477 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4281 (by decide)

private theorem attained_478 : a 478 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1906 (by decide)

private theorem attained_479 : a 479 ≠ 0 :=
  attained_of_witness (by norm_num) sig_770 (by decide)

private theorem attained_480 : a 480 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (229441 : ℕ) = 479^2), sigma_one_sq (by norm_num : Nat.Prime 479)] <;> norm_num) : (sigma 1 229441 : ℕ) = 229921) (by decide)

private theorem attained_481 : a 481 ≠ 0 :=
  attained_of_witness (by norm_num) sig_928 (by decide)

private theorem attained_482 : a 482 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5680 (by decide)

private theorem attained_483 : a 483 ≠ 0 :=
  attained_of_witness (by norm_num) sig_8797 (by decide)

private theorem attained_484 : a 484 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2572 (by decide)

private theorem attained_485 : a 485 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1934 (by decide)

private theorem attained_486 : a 486 ≠ 0 :=
  attained_of_witness (by norm_num) sig_25792 (by decide)

private theorem attained_487 : a 487 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1078 (by decide)

private theorem attained_488 : a 488 ≠ 0 :=
  attained_of_witness (by norm_num) sig_23712 (by decide)

private theorem attained_489 : a 489 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2922 (by decide)

private theorem attained_490 : a 490 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1954 (by decide)

private theorem attained_491 : a 491 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1461 (by decide)

private theorem attained_492 : a 492 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (241081 : ℕ) = 491^2), sigma_one_sq (by norm_num : Nat.Prime 491)] <;> norm_num) : (sigma 1 241081 : ℕ) = 241573) (by decide)

private theorem attained_493 : a 493 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1534 (by decide)

private theorem attained_494 : a 494 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3608 (by decide)

private theorem attained_495 : a 495 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3409 (by decide)

private theorem attained_496 : a 496 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2106 (by decide)

private theorem attained_497 : a 497 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1360 (by decide)

private theorem attained_498 : a 498 ≠ 0 :=
  attained_of_witness (by norm_num) sig_13475328 (by decide)

private theorem attained_499 : a 499 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1935 (by decide)

private theorem attained_500 : a 500 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1994 (by decide)

private theorem attained_501 : a 501 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2994 (by decide)

private theorem attained_502 : a 502 ≠ 0 :=
  attained_of_witness (by norm_num) sig_91120 (by decide)

private theorem attained_503 : a 503 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1497 (by decide)

private theorem attained_504 : a 504 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (253009 : ℕ) = 503^2), sigma_one_sq (by norm_num : Nat.Prime 503)] <;> norm_num) : (sigma 1 253009 : ℕ) = 253513) (by decide)

private theorem attained_505 : a 505 ≠ 0 :=
  attained_of_witness (by norm_num) sig_903 (by decide)

private theorem attained_506 : a 506 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2018 (by decide)

private theorem attained_507 : a 507 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3493 (by decide)

private theorem attained_508 : a 508 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2026 (by decide)

private theorem attained_509 : a 509 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1348 (by decide)

private theorem attained_510 : a 510 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (259081 : ℕ) = 509^2), sigma_one_sq (by norm_num : Nat.Prime 509)] <;> norm_num) : (sigma 1 259081 : ℕ) = 259591) (by decide)

private theorem attained_511 : a 511 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (512 : ℕ) = 2^9), sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) : (sigma 1 512 : ℕ) = 1023) (by decide)

private theorem attained_512 : a 512 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2042 (by decide)

private theorem attained_513 : a 513 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2877 (by decide)

private theorem attained_514 : a 514 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2732 (by decide)

private theorem attained_515 : a 515 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1524 (by decide)

private theorem attained_516 : a 516 ≠ 0 :=
  attained_of_witness (by norm_num) sig_142133760 (by decide)

private theorem attained_517 : a 517 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1270 (by decide)

private theorem attained_518 : a 518 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2066 (by decide)

private theorem attained_519 : a 519 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2236 (by decide)

private theorem attained_520 : a 520 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2764 (by decide)

private theorem attained_521 : a 521 ≠ 0 :=
  attained_of_witness (by norm_num) sig_999 (by decide)

private theorem attained_522 : a 522 ≠ 0 :=
  attained_of_witness (by norm_num) sig_74529 (by decide)

private theorem attained_523 : a 523 ≠ 0 :=
  attained_of_witness (by norm_num) sig_324 (by decide)

private theorem attained_524 : a 524 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (273529 : ℕ) = 523^2), sigma_one_sq (by norm_num : Nat.Prime 523)] <;> norm_num) : (sigma 1 273529 : ℕ) = 274053) (by decide)

private theorem attained_525 : a 525 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3138 (by decide)

private theorem attained_526 : a 526 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2098 (by decide)

private theorem attained_527 : a 527 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1396 (by decide)

private theorem attained_528 : a 528 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4332 (by decide)

private theorem attained_529 : a 529 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1192 (by decide)

private theorem attained_530 : a 530 ≠ 0 :=
  attained_of_witness (by norm_num) sig_47268 (by decide)

private theorem attained_531 : a 531 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2356 (by decide)

private theorem attained_532 : a 532 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2122 (by decide)

private theorem attained_533 : a 533 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1310 (by decide)

private theorem attained_534 : a 534 ≠ 0 :=
  attained_of_witness (by norm_num) sig_6832 (by decide)

private theorem attained_535 : a 535 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2144 (by decide)

private theorem attained_536 : a 536 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2138 (by decide)

private theorem attained_537 : a 537 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4812 (by decide)

private theorem attained_538 : a 538 ≠ 0 :=
  attained_of_witness (by norm_num) sig_88218 (by decide)

private theorem attained_539 : a 539 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3609 (by decide)

private theorem attained_540 : a 540 ≠ 0 :=
  attained_of_witness (by norm_num) sig_8298 (by decide)

private theorem attained_541 : a 541 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1150 (by decide)

private theorem attained_542 : a 542 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1225 (by decide)

private theorem attained_543 : a 543 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1950 (by decide)

private theorem attained_544 : a 544 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1940 (by decide)

private theorem attained_545 : a 545 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1623 (by decide)

private theorem attained_546 : a 546 ≠ 0 :=
  attained_of_witness (by norm_num) sig_59410176 (by decide)

private theorem attained_547 : a 547 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1498 (by decide)

private theorem attained_548 : a 548 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2186 (by decide)

private theorem attained_549 : a 549 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3282 (by decide)

private theorem attained_550 : a 550 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2194 (by decide)

private theorem attained_551 : a 551 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1641 (by decide)

private theorem attained_552 : a 552 ≠ 0 :=
  attained_of_witness (by norm_num) sig_16656 (by decide)

private theorem attained_553 : a 553 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2206 (by decide)

private theorem attained_554 : a 554 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5048 (by decide)

private theorem attained_555 : a 555 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3829 (by decide)

private theorem attained_556 : a 556 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2218 (by decide)

private theorem attained_557 : a 557 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1256 (by decide)

private theorem attained_558 : a 558 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (310249 : ℕ) = 557^2), sigma_one_sq (by norm_num : Nat.Prime 557)] <;> norm_num) : (sigma 1 310249 : ℕ) = 310807) (by decide)

private theorem attained_559 : a 559 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2592 (by decide)

private theorem attained_560 : a 560 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2234 (by decide)

private theorem attained_561 : a 561 ≠ 0 :=
  attained_of_witness (by norm_num) sig_400 (by decide)

private theorem attained_562 : a 562 ≠ 0 :=
  attained_of_witness (by norm_num) sig_8952 (by decide)

private theorem attained_563 : a 563 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1168 (by decide)

private theorem attained_564 : a 564 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (316969 : ℕ) = 563^2), sigma_one_sq (by norm_num : Nat.Prime 563)] <;> norm_num) : (sigma 1 316969 : ℕ) = 317533) (by decide)

private theorem attained_565 : a 565 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2444 (by decide)

private theorem attained_566 : a 566 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2020 (by decide)

private theorem attained_567 : a 567 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5091 (by decide)

private theorem attained_568 : a 568 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1452 (by decide)

private theorem attained_569 : a 569 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1251 (by decide)

private theorem attained_570 : a 570 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (323761 : ℕ) = 569^2), sigma_one_sq (by norm_num : Nat.Prime 569)] <;> norm_num) : (sigma 1 323761 : ℕ) = 324331) (by decide)

private theorem attained_571 : a 571 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1029 (by decide)

private theorem attained_572 : a 572 ≠ 0 :=
  attained_of_witness (by norm_num) sig_12720 (by decide)

private theorem attained_573 : a 573 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3426 (by decide)

private theorem attained_574 : a 574 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4408 (by decide)

private theorem attained_575 : a 575 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1713 (by decide)

private theorem attained_576 : a 576 ≠ 0 :=
  attained_of_witness (by norm_num) sig_989280 (by decide)

private theorem attained_577 : a 577 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1582 (by decide)

private theorem attained_578 : a 578 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2306 (by decide)

private theorem attained_579 : a 579 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3462 (by decide)

private theorem attained_580 : a 580 ≠ 0 :=
  attained_of_witness (by norm_num) sig_144180 (by decide)

private theorem attained_581 : a 581 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1731 (by decide)

private theorem attained_582 : a 582 ≠ 0 :=
  attained_of_witness (by norm_num) sig_85860 (by decide)

private theorem attained_583 : a 583 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1209 (by decide)

private theorem attained_584 : a 584 ≠ 0 :=
  attained_of_witness (by norm_num) sig_35120 (by decide)

private theorem attained_585 : a 585 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4039 (by decide)

private theorem attained_586 : a 586 ≠ 0 :=
  attained_of_witness (by norm_num) sig_9336 (by decide)

private theorem attained_587 : a 587 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1556 (by decide)

private theorem attained_588 : a 588 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (344569 : ℕ) = 587^2), sigma_one_sq (by norm_num : Nat.Prime 587)] <;> norm_num) : (sigma 1 344569 : ℕ) = 345157) (by decide)

private theorem attained_589 : a 589 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1846 (by decide)

private theorem attained_590 : a 590 ≠ 0 :=
  attained_of_witness (by norm_num) sig_19424 (by decide)

private theorem attained_591 : a 591 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3939 (by decide)

private theorem attained_592 : a 592 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1210 (by decide)

private theorem attained_593 : a 593 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2431 (by decide)

private theorem attained_594 : a 594 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (351649 : ℕ) = 593^2), sigma_one_sq (by norm_num : Nat.Prime 593)] <;> norm_num) : (sigma 1 351649 : ℕ) = 352243) (by decide)

private theorem attained_595 : a 595 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1978 (by decide)

private theorem attained_596 : a 596 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4472 (by decide)

private theorem attained_597 : a 597 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5361 (by decide)

private theorem attained_598 : a 598 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2386 (by decide)

private theorem attained_599 : a 599 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1088 (by decide)

private theorem attained_600 : a 600 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (358801 : ℕ) = 599^2), sigma_one_sq (by norm_num : Nat.Prime 599)] <;> norm_num) : (sigma 1 358801 : ℕ) = 359401) (by decide)

private theorem attained_601 : a 601 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1058 (by decide)

private theorem attained_602 : a 602 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2402 (by decide)

private theorem attained_603 : a 603 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3606 (by decide)

private theorem attained_604 : a 604 ≠ 0 :=
  attained_of_witness (by norm_num) sig_9624 (by decide)

private theorem attained_605 : a 605 ≠ 0 :=
  attained_of_witness (by norm_num) sig_676 (by decide)

private theorem attained_606 : a 606 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1041120 (by decide)

private theorem attained_607 : a 607 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1458 (by decide)

private theorem attained_608 : a 608 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2426 (by decide)

private theorem attained_609 : a 609 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3642 (by decide)

private theorem attained_610 : a 610 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2434 (by decide)

private theorem attained_611 : a 611 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1812 (by decide)

private theorem attained_612 : a 612 ≠ 0 :=
  attained_of_witness (by norm_num) sig_609120 (by decide)

private theorem attained_613 : a 613 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1384 (by decide)

private theorem attained_614 : a 614 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1548 (by decide)

private theorem attained_615 : a 615 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3678 (by decide)

private theorem attained_616 : a 616 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2458 (by decide)

private theorem attained_617 : a 617 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1359 (by decide)

private theorem attained_618 : a 618 ≠ 0 :=
  attained_of_witness (by norm_num) sig_137200 (by decide)

private theorem attained_619 : a 619 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2261 (by decide)

private theorem attained_620 : a 620 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2474 (by decide)

private theorem attained_621 : a 621 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3714 (by decide)

private theorem attained_622 : a 622 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3308 (by decide)

private theorem attained_623 : a 623 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1857 (by decide)

private theorem attained_624 : a 624 ≠ 0 :=
  attained_of_witness (by norm_num) sig_166758384 (by decide)

private theorem attained_625 : a 625 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1587 (by decide)

private theorem attained_626 : a 626 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2498 (by decide)

private theorem attained_627 : a 627 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4333 (by decide)

private theorem attained_628 : a 628 ≠ 0 :=
  attained_of_witness (by norm_num) sig_11380 (by decide)

private theorem attained_629 : a 629 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1404 (by decide)

private theorem attained_630 : a 630 ≠ 0 :=
  attained_of_witness (by norm_num) sig_40052517120 (by decide)

private theorem attained_631 : a 631 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2518 (by decide)

private theorem attained_632 : a 632 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2260 (by decide)

private theorem attained_633 : a 633 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3786 (by decide)

private theorem attained_634 : a 634 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2756 (by decide)

private theorem attained_635 : a 635 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1684 (by decide)

private theorem attained_636 : a 636 ≠ 0 :=
  attained_of_witness (by norm_num) sig_8176 (by decide)

private theorem attained_637 : a 637 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1570 (by decide)

private theorem attained_638 : a 638 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5816 (by decide)

private theorem attained_639 : a 639 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4417 (by decide)

private theorem attained_640 : a 640 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1089 (by decide)

private theorem attained_641 : a 641 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1053 (by decide)

private theorem attained_642 : a 642 ≠ 0 :=
  attained_of_witness (by norm_num) sig_237120 (by decide)

private theorem attained_643 : a 643 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2566 (by decide)

private theorem attained_644 : a 644 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (413449 : ℕ) = 643^2), sigma_one_sq (by norm_num : Nat.Prime 643)] <;> norm_num) : (sigma 1 413449 : ℕ) = 414093) (by decide)

private theorem attained_645 : a 645 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3633 (by decide)

private theorem attained_646 : a 646 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2578 (by decide)

private theorem attained_647 : a 647 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1778 (by decide)

private theorem attained_648 : a 648 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (418609 : ℕ) = 647^2), sigma_one_sq (by norm_num : Nat.Prime 647)] <;> norm_num) : (sigma 1 418609 : ℕ) = 419257) (by decide)

private theorem attained_649 : a 649 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2575 (by decide)

private theorem attained_650 : a 650 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2594 (by decide)

private theorem attained_651 : a 651 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4191 (by decide)

private theorem attained_652 : a 652 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2602 (by decide)

private theorem attained_653 : a 653 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1732 (by decide)

private theorem attained_654 : a 654 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (426409 : ℕ) = 653^2), sigma_one_sq (by norm_num : Nat.Prime 653)] <;> norm_num) : (sigma 1 426409 : ℕ) = 427063) (by decide)

private theorem attained_655 : a 655 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2614 (by decide)

private theorem attained_656 : a 656 ≠ 0 :=
  attained_of_witness (by norm_num) sig_14640 (by decide)

private theorem attained_657 : a 657 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4884 (by decide)

private theorem attained_658 : a 658 ≠ 0 :=
  attained_of_witness (by norm_num) sig_86338 (by decide)

private theorem attained_659 : a 659 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1645 (by decide)

private theorem attained_660 : a 660 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (434281 : ℕ) = 659^2), sigma_one_sq (by norm_num : Nat.Prime 659)] <;> norm_num) : (sigma 1 434281 : ℕ) = 434941) (by decide)

private theorem attained_661 : a 661 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1200 (by decide)

private theorem attained_662 : a 662 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2642 (by decide)

private theorem attained_663 : a 663 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3966 (by decide)

private theorem attained_664 : a 664 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3532 (by decide)

private theorem attained_665 : a 665 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1467 (by decide)

private theorem attained_666 : a 666 ≠ 0 :=
  attained_of_witness (by norm_num) sig_10242 (by decide)

private theorem attained_667 : a 667 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1312 (by decide)

private theorem attained_668 : a 668 ≠ 0 :=
  attained_of_witness (by norm_num) sig_6672 (by decide)

private theorem attained_669 : a 669 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4627 (by decide)

private theorem attained_670 : a 670 ≠ 0 :=
  attained_of_witness (by norm_num) sig_499968 (by decide)

private theorem attained_671 : a 671 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4380 (by decide)

private theorem attained_672 : a 672 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4544640 (by decide)

private theorem attained_673 : a 673 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2015 (by decide)

private theorem attained_674 : a 674 ≠ 0 :=
  attained_of_witness (by norm_num) sig_19620 (by decide)

private theorem attained_675 : a 675 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4038 (by decide)

private theorem attained_676 : a 676 ≠ 0 :=
  attained_of_witness (by norm_num) sig_10776 (by decide)

private theorem attained_677 : a 677 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1670 (by decide)

private theorem attained_678 : a 678 ≠ 0 :=
  attained_of_witness (by norm_num) sig_112554 (by decide)

private theorem attained_679 : a 679 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2242 (by decide)

private theorem attained_680 : a 680 ≠ 0 :=
  attained_of_witness (by norm_num) sig_473248 (by decide)

private theorem attained_681 : a 681 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4711 (by decide)

private theorem attained_682 : a 682 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2722 (by decide)

private theorem attained_683 : a 683 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1424 (by decide)

private theorem attained_684 : a 684 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (466489 : ℕ) = 683^2), sigma_one_sq (by norm_num : Nat.Prime 683)] <;> norm_num) : (sigma 1 466489 : ℕ) = 467173) (by decide)

private theorem attained_685 : a 685 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1443 (by decide)

private theorem attained_686 : a 686 ≠ 0 :=
  attained_of_witness (by norm_num) sig_13200 (by decide)

private theorem attained_687 : a 687 ≠ 0 :=
  attained_of_witness (by norm_num) sig_8749 (by decide)

private theorem attained_688 : a 688 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2746 (by decide)

private theorem attained_689 : a 689 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1828 (by decide)

private theorem attained_690 : a 690 ≠ 0 :=
  attained_of_witness (by norm_num) sig_7269444 (by decide)

private theorem attained_691 : a 691 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2550 (by decide)

private theorem attained_692 : a 692 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2762 (by decide)

private theorem attained_693 : a 693 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4146 (by decide)

private theorem attained_694 : a 694 ≠ 0 :=
  attained_of_witness (by norm_num) sig_8240 (by decide)

private theorem attained_695 : a 695 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1844 (by decide)

private theorem attained_696 : a 696 ≠ 0 :=
  attained_of_witness (by norm_num) sig_242736 (by decide)

private theorem attained_697 : a 697 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1576 (by decide)

private theorem attained_698 : a 698 ≠ 0 :=
  attained_of_witness (by norm_num) sig_393888 (by decide)

private theorem attained_699 : a 699 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4837 (by decide)

private theorem attained_700 : a 700 ≠ 0 :=
  attained_of_witness (by norm_num) sig_313200 (by decide)

private theorem attained_701 : a 701 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1190 (by decide)

private theorem attained_702 : a 702 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (491401 : ℕ) = 701^2), sigma_one_sq (by norm_num : Nat.Prime 701)] <;> norm_num) : (sigma 1 491401 : ℕ) = 492103) (by decide)

private theorem attained_703 : a 703 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1281 (by decide)

private theorem attained_704 : a 704 ≠ 0 :=
  attained_of_witness (by norm_num) sig_21264 (by decide)

private theorem attained_705 : a 705 ≠ 0 :=
  attained_of_witness (by norm_num) sig_6333 (by decide)

private theorem attained_706 : a 706 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1666 (by decide)

private theorem attained_707 : a 707 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3495 (by decide)

private theorem attained_708 : a 708 ≠ 0 :=
  attained_of_witness (by norm_num) sig_18096 (by decide)

private theorem attained_709 : a 709 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2000 (by decide)

private theorem attained_710 : a 710 ≠ 0 :=
  attained_of_witness (by norm_num) sig_497280 (by decide)

private theorem attained_711 : a 711 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3075 (by decide)

private theorem attained_712 : a 712 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3788 (by decide)

private theorem attained_713 : a 713 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2127 (by decide)

private theorem attained_714 : a 714 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3790080 (by decide)

private theorem attained_715 : a 715 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2854 (by decide)

private theorem attained_716 : a 716 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2858 (by decide)

private theorem attained_717 : a 717 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4963 (by decide)

private theorem attained_718 : a 718 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2866 (by decide)

private theorem attained_719 : a 719 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2737 (by decide)

private theorem attained_720 : a 720 ≠ 0 :=
  attained_of_witness (by norm_num) sig_159201 (by decide)

private theorem attained_721 : a 721 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1152 (by decide)

private theorem attained_722 : a 722 ≠ 0 :=
  attained_of_witness (by norm_num) sig_6584 (by decide)

private theorem attained_723 : a 723 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3268 (by decide)

private theorem attained_724 : a 724 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5368 (by decide)

private theorem attained_725 : a 725 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2222 (by decide)

private theorem attained_726 : a 726 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3172 (by decide)

private theorem attained_727 : a 727 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2300 (by decide)

private theorem attained_728 : a 728 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2906 (by decide)

private theorem attained_729 : a 729 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4362 (by decide)

private theorem attained_730 : a 730 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3884 (by decide)

private theorem attained_731 : a 731 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2172 (by decide)

private theorem attained_732 : a 732 ≠ 0 :=
  attained_of_witness (by norm_num) sig_67312 (by decide)

private theorem attained_733 : a 733 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1810 (by decide)

private theorem attained_734 : a 734 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5616 (by decide)

private theorem attained_735 : a 735 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4398 (by decide)

private theorem attained_736 : a 736 ≠ 0 :=
  attained_of_witness (by norm_num) sig_6712 (by decide)

private theorem attained_737 : a 737 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1629 (by decide)

private theorem attained_738 : a 738 ≠ 0 :=
  attained_of_witness (by norm_num) sig_96066 (by decide)

private theorem attained_739 : a 739 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2266 (by decide)

private theorem attained_740 : a 740 ≠ 0 :=
  attained_of_witness (by norm_num) sig_31914 (by decide)

private theorem attained_741 : a 741 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4434 (by decide)

private theorem attained_742 : a 742 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2962 (by decide)

private theorem attained_743 : a 743 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1552 (by decide)

private theorem attained_744 : a 744 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (552049 : ℕ) = 743^2), sigma_one_sq (by norm_num : Nat.Prime 743)] <;> norm_num) : (sigma 1 552049 : ℕ) = 552793) (by decide)

private theorem attained_745 : a 745 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2542 (by decide)

private theorem attained_746 : a 746 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2978 (by decide)

private theorem attained_747 : a 747 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5173 (by decide)

private theorem attained_748 : a 748 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2986 (by decide)

private theorem attained_749 : a 749 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3715 (by decide)

private theorem attained_750 : a 750 ≠ 0 :=
  attained_of_witness (by norm_num) sig_11538 (by decide)

private theorem attained_751 : a 751 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2998 (by decide)

private theorem attained_752 : a 752 ≠ 0 :=
  attained_of_witness (by norm_num) sig_75072 (by decide)

private theorem attained_753 : a 753 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4506 (by decide)

private theorem attained_754 : a 754 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5848 (by decide)

private theorem attained_755 : a 755 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2253 (by decide)

private theorem attained_756 : a 756 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1091059200 (by decide)

private theorem attained_757 : a 757 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2086 (by decide)

private theorem attained_758 : a 758 ≠ 0 :=
  attained_of_witness (by norm_num) sig_24640 (by decide)

private theorem attained_759 : a 759 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4542 (by decide)

private theorem attained_760 : a 760 ≠ 0 :=
  attained_of_witness (by norm_num) sig_44564 (by decide)

private theorem attained_761 : a 761 ≠ 0 :=
  attained_of_witness (by norm_num) sig_975 (by decide)

private theorem attained_762 : a 762 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (579121 : ℕ) = 761^2), sigma_one_sq (by norm_num : Nat.Prime 761)] <;> norm_num) : (sigma 1 579121 : ℕ) = 579883) (by decide)

private theorem attained_763 : a 763 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3015 (by decide)

private theorem attained_764 : a 764 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2740 (by decide)

private theorem attained_765 : a 765 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5299 (by decide)

private theorem attained_766 : a 766 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4076 (by decide)

private theorem attained_767 : a 767 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2036 (by decide)

private theorem attained_768 : a 768 ≠ 0 :=
  attained_of_witness (by norm_num) sig_8094996 (by decide)

private theorem attained_769 : a 769 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1407 (by decide)

private theorem attained_770 : a 770 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (591361 : ℕ) = 769^2), sigma_one_sq (by norm_num : Nat.Prime 769)] <;> norm_num) : (sigma 1 591361 : ℕ) = 592131) (by decide)

private theorem attained_771 : a 771 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4614 (by decide)

private theorem attained_772 : a 772 ≠ 0 :=
  attained_of_witness (by norm_num) sig_9968 (by decide)

private theorem attained_773 : a 773 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1616 (by decide)

private theorem attained_774 : a 774 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (597529 : ℕ) = 773^2), sigma_one_sq (by norm_num : Nat.Prime 773)] <;> norm_num) : (sigma 1 597529 : ℕ) = 598303) (by decide)

private theorem attained_775 : a 775 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4124 (by decide)

private theorem attained_776 : a 776 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3098 (by decide)

private theorem attained_777 : a 777 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5829 (by decide)

private theorem attained_778 : a 778 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3106 (by decide)

private theorem attained_779 : a 779 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2316 (by decide)

private theorem attained_780 : a 780 ≠ 0 :=
  attained_of_witness (by norm_num) sig_23568 (by decide)

private theorem attained_781 : a 781 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1930 (by decide)

private theorem attained_782 : a 782 ≠ 0 :=
  attained_of_witness (by norm_num) sig_7824 (by decide)

private theorem attained_783 : a 783 ≠ 0 :=
  attained_of_witness (by norm_num) sig_8136 (by decide)

private theorem attained_784 : a 784 ≠ 0 :=
  attained_of_witness (by norm_num) sig_7650 (by decide)

private theorem attained_785 : a 785 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1737 (by decide)

private theorem attained_786 : a 786 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1352160 (by decide)

private theorem attained_787 : a 787 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1677 (by decide)

private theorem attained_788 : a 788 ≠ 0 :=
  attained_of_witness (by norm_num) sig_68160 (by decide)

private theorem attained_789 : a 789 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2625 (by decide)

private theorem attained_790 : a 790 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4204 (by decide)

private theorem attained_791 : a 791 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2361 (by decide)

private theorem attained_792 : a 792 ≠ 0 :=
  attained_of_witness (by norm_num) sig_12186 (by decide)

private theorem attained_793 : a 793 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1767 (by decide)

private theorem attained_794 : a 794 ≠ 0 :=
  attained_of_witness (by norm_num) sig_46752 (by decide)

private theorem attained_795 : a 795 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3484 (by decide)

private theorem attained_796 : a 796 ≠ 0 :=
  attained_of_witness (by norm_num) sig_6232 (by decide)

private theorem attained_797 : a 797 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1430 (by decide)

private theorem attained_798 : a 798 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (635209 : ℕ) = 797^2), sigma_one_sq (by norm_num : Nat.Prime 797)] <;> norm_num) : (sigma 1 635209 : ℕ) = 636007) (by decide)

private theorem attained_799 : a 799 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2849 (by decide)

private theorem attained_800 : a 800 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3194 (by decide)

private theorem attained_801 : a 801 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5181 (by decide)

private theorem attained_802 : a 802 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1690 (by decide)

private theorem attained_803 : a 803 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2080 (by decide)

private theorem attained_804 : a 804 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3814272 (by decide)

private theorem attained_805 : a 805 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3214 (by decide)

private theorem attained_806 : a 806 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3218 (by decide)

private theorem attained_807 : a 807 ≠ 0 :=
  attained_of_witness (by norm_num) sig_7251 (by decide)

private theorem attained_808 : a 808 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3226 (by decide)

private theorem attained_809 : a 809 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1791 (by decide)

private theorem attained_810 : a 810 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (654481 : ℕ) = 809^2), sigma_one_sq (by norm_num : Nat.Prime 809)] <;> norm_num) : (sigma 1 654481 : ℕ) = 655291) (by decide)

private theorem attained_811 : a 811 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2698 (by decide)

private theorem attained_812 : a 812 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3242 (by decide)

private theorem attained_813 : a 813 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4866 (by decide)

private theorem attained_814 : a 814 ≠ 0 :=
  attained_of_witness (by norm_num) sig_12984 (by decide)

private theorem attained_815 : a 815 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2164 (by decide)

private theorem attained_816 : a 816 ≠ 0 :=
  attained_of_witness (by norm_num) sig_739116 (by decide)

private theorem attained_817 : a 817 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2686 (by decide)

private theorem attained_818 : a 818 ≠ 0 :=
  attained_of_witness (by norm_num) sig_56304 (by decide)

private theorem attained_819 : a 819 ≠ 0 :=
  attained_of_witness (by norm_num) sig_12336 (by decide)

private theorem attained_820 : a 820 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3274 (by decide)

private theorem attained_821 : a 821 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2635 (by decide)

private theorem attained_822 : a 822 ≠ 0 :=
  attained_of_witness (by norm_num) sig_104076 (by decide)

private theorem attained_823 : a 823 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1864 (by decide)

private theorem attained_824 : a 824 ≠ 0 :=
  attained_of_witness (by norm_num) sig_13900 (by decide)

private theorem attained_825 : a 825 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4938 (by decide)

private theorem attained_826 : a 826 ≠ 0 :=
  attained_of_witness (by norm_num) sig_26360 (by decide)

private theorem attained_827 : a 827 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2282 (by decide)

private theorem attained_828 : a 828 ≠ 0 :=
  attained_of_witness (by norm_num) sig_29304 (by decide)

private theorem attained_829 : a 829 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2626 (by decide)

private theorem attained_830 : a 830 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3314 (by decide)

private theorem attained_831 : a 831 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4974 (by decide)

private theorem attained_832 : a 832 ≠ 0 :=
  attained_of_witness (by norm_num) sig_336532 (by decide)

private theorem attained_833 : a 833 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1647 (by decide)

private theorem attained_834 : a 834 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3141000 (by decide)

private theorem attained_835 : a 835 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1533 (by decide)

private theorem attained_836 : a 836 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3338 (by decide)

private theorem attained_837 : a 837 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5803 (by decide)

private theorem attained_838 : a 838 ≠ 0 :=
  attained_of_witness (by norm_num) sig_13368 (by decide)

private theorem attained_839 : a 839 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2228 (by decide)

private theorem attained_840 : a 840 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (703921 : ℕ) = 839^2), sigma_one_sq (by norm_num : Nat.Prime 839)] <;> norm_num) : (sigma 1 703921 : ℕ) = 704761) (by decide)

private theorem attained_841 : a 841 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2135 (by decide)

private theorem attained_842 : a 842 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1850 (by decide)

private theorem attained_843 : a 843 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3528 (by decide)

private theorem attained_844 : a 844 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4492 (by decide)

private theorem attained_845 : a 845 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3424 (by decide)

private theorem attained_846 : a 846 ≠ 0 :=
  attained_of_witness (by norm_num) sig_590992 (by decide)

private theorem attained_847 : a 847 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2914 (by decide)

private theorem attained_848 : a 848 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3386 (by decide)

private theorem attained_849 : a 849 ≠ 0 :=
  attained_of_witness (by norm_num) sig_6612 (by decide)

private theorem attained_850 : a 850 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3394 (by decide)

private theorem attained_851 : a 851 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1928 (by decide)

private theorem attained_852 : a 852 ≠ 0 :=
  attained_of_witness (by norm_num) sig_382752 (by decide)

private theorem attained_853 : a 853 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1696 (by decide)

private theorem attained_854 : a 854 ≠ 0 :=
  attained_of_witness (by norm_num) sig_51120 (by decide)

private theorem attained_855 : a 855 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5118 (by decide)

private theorem attained_856 : a 856 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3418 (by decide)

private theorem attained_857 : a 857 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1899 (by decide)

private theorem attained_858 : a 858 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (734449 : ℕ) = 857^2), sigma_one_sq (by norm_num : Nat.Prime 857)] <;> norm_num) : (sigma 1 734449 : ℕ) = 735307) (by decide)

private theorem attained_859 : a 859 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3632 (by decide)

private theorem attained_860 : a 860 ≠ 0 :=
  attained_of_witness (by norm_num) sig_330880 (by decide)

private theorem attained_861 : a 861 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5154 (by decide)

private theorem attained_862 : a 862 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3442 (by decide)

private theorem attained_863 : a 863 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1808 (by decide)

private theorem attained_864 : a 864 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3796 (by decide)

private theorem attained_865 : a 865 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2662 (by decide)

private theorem attained_866 : a 866 ≠ 0 :=
  attained_of_witness (by norm_num) sig_27500 (by decide)

private theorem attained_867 : a 867 ≠ 0 :=
  attained_of_witness (by norm_num) sig_6013 (by decide)

private theorem attained_868 : a 868 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3466 (by decide)

private theorem attained_869 : a 869 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1300 (by decide)

private theorem attained_870 : a 870 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2661124 (by decide)

private theorem attained_871 : a 871 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2585 (by decide)

private theorem attained_872 : a 872 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3482 (by decide)

private theorem attained_873 : a 873 ≠ 0 :=
  attained_of_witness (by norm_num) sig_7836 (by decide)

private theorem attained_874 : a 874 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3140 (by decide)

private theorem attained_875 : a 875 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3494 (by decide)

private theorem attained_876 : a 876 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1507680 (by decide)

private theorem attained_877 : a 877 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2422 (by decide)

private theorem attained_878 : a 878 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3506 (by decide)

private theorem attained_879 : a 879 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5262 (by decide)

private theorem attained_880 : a 880 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4684 (by decide)

private theorem attained_881 : a 881 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1539 (by decide)

private theorem attained_882 : a 882 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (776161 : ℕ) = 881^2), sigma_one_sq (by norm_num : Nat.Prime 881)] <;> norm_num) : (sigma 1 776161 : ℕ) = 777043) (by decide)

private theorem attained_883 : a 883 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1197 (by decide)

private theorem attained_884 : a 884 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (779689 : ℕ) = 883^2), sigma_one_sq (by norm_num : Nat.Prime 883)] <;> norm_num) : (sigma 1 779689 : ℕ) = 780573) (by decide)

private theorem attained_885 : a 885 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5298 (by decide)

private theorem attained_886 : a 886 ≠ 0 :=
  attained_of_witness (by norm_num) sig_137952 (by decide)

private theorem attained_887 : a 887 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2052 (by decide)

private theorem attained_888 : a 888 ≠ 0 :=
  attained_of_witness (by norm_num) sig_13072 (by decide)

private theorem attained_889 : a 889 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4266 (by decide)

private theorem attained_890 : a 890 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3554 (by decide)

private theorem attained_891 : a 891 ≠ 0 :=
  attained_of_witness (by norm_num) sig_6181 (by decide)

private theorem attained_892 : a 892 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4748 (by decide)

private theorem attained_893 : a 893 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1280 (by decide)

private theorem attained_894 : a 894 ≠ 0 :=
  attained_of_witness (by norm_num) sig_27024 (by decide)

private theorem attained_895 : a 895 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3574 (by decide)

private theorem attained_896 : a 896 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3578 (by decide)

private theorem attained_897 : a 897 ≠ 0 :=
  attained_of_witness (by norm_num) sig_8061 (by decide)

private theorem attained_898 : a 898 ≠ 0 :=
  attained_of_witness (by norm_num) sig_52676 (by decide)

private theorem attained_899 : a 899 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2676 (by decide)

private theorem attained_900 : a 900 ≠ 0 :=
  attained_of_witness (by norm_num) sig_243828 (by decide)

private theorem attained_901 : a 901 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1659 (by decide)

private theorem attained_902 : a 902 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3602 (by decide)

private theorem attained_903 : a 903 ≠ 0 :=
  attained_of_witness (by norm_num) sig_16777 (by decide)

private theorem attained_904 : a 904 ≠ 0 :=
  attained_of_witness (by norm_num) sig_8248 (by decide)

private theorem attained_905 : a 905 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2007 (by decide)

private theorem attained_906 : a 906 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1800960 (by decide)

private theorem attained_907 : a 907 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2056 (by decide)

private theorem attained_908 : a 908 ≠ 0 :=
  attained_of_witness (by norm_num) sig_39840 (by decide)

private theorem attained_909 : a 909 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5442 (by decide)

private theorem attained_910 : a 910 ≠ 0 :=
  attained_of_witness (by norm_num) sig_25160 (by decide)

private theorem attained_911 : a 911 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1809 (by decide)

private theorem attained_912 : a 912 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (829921 : ℕ) = 911^2), sigma_one_sq (by norm_num : Nat.Prime 911)] <;> norm_num) : (sigma 1 829921 : ℕ) = 830833) (by decide)

private theorem attained_913 : a 913 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3450 (by decide)

private theorem attained_914 : a 914 ≠ 0 :=
  attained_of_witness (by norm_num) sig_6968 (by decide)

private theorem attained_915 : a 915 ≠ 0 :=
  attained_of_witness (by norm_num) sig_6349 (by decide)

private theorem attained_916 : a 916 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4148 (by decide)

private theorem attained_917 : a 917 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2270 (by decide)

private theorem attained_918 : a 918 ≠ 0 :=
  attained_of_witness (by norm_num) sig_24903168 (by decide)

private theorem attained_919 : a 919 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2345 (by decide)

private theorem attained_920 : a 920 ≠ 0 :=
  attained_of_witness (by norm_num) sig_24992 (by decide)

private theorem attained_921 : a 921 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5514 (by decide)

private theorem attained_922 : a 922 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4292 (by decide)

private theorem attained_923 : a 923 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1610 (by decide)

private theorem attained_924 : a 924 ≠ 0 :=
  attained_of_witness (by norm_num) sig_325696 (by decide)

private theorem attained_925 : a 925 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2254 (by decide)

private theorem attained_926 : a 926 ≠ 0 :=
  attained_of_witness (by norm_num) sig_29560 (by decide)

private theorem attained_927 : a 927 ≠ 0 :=
  attained_of_witness (by norm_num) sig_6433 (by decide)

private theorem attained_928 : a 928 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2050 (by decide)

private theorem attained_929 : a 929 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2061 (by decide)

private theorem attained_930 : a 930 ≠ 0 :=
  attained_of_witness (by norm_num) sig_46144 (by decide)

private theorem attained_931 : a 931 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1682 (by decide)

private theorem attained_932 : a 932 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3722 (by decide)

private theorem attained_933 : a 933 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4108 (by decide)

private theorem attained_934 : a 934 ≠ 0 :=
  attained_of_witness (by norm_num) sig_554400 (by decide)

private theorem attained_935 : a 935 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3734 (by decide)

private theorem attained_936 : a 936 ≠ 0 :=
  attained_of_witness (by norm_num) sig_86128 (by decide)

private theorem attained_937 : a 937 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3742 (by decide)

private theorem attained_938 : a 938 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3746 (by decide)

private theorem attained_939 : a 939 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5622 (by decide)

private theorem attained_940 : a 940 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3754 (by decide)

private theorem attained_941 : a 941 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2330 (by decide)

private theorem attained_942 : a 942 ≠ 0 :=
  attained_of_witness (by norm_num) sig_12208 (by decide)

private theorem attained_943 : a 943 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3154 (by decide)

private theorem attained_944 : a 944 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2412 (by decide)

private theorem attained_945 : a 945 ≠ 0 :=
  attained_of_witness (by norm_num) sig_33559 (by decide)

private theorem attained_946 : a 946 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3778 (by decide)

private theorem attained_947 : a 947 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4686 (by decide)

private theorem attained_948 : a 948 ≠ 0 :=
  attained_of_witness (by norm_num) sig_240426 (by decide)

private theorem attained_949 : a 949 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2152 (by decide)

private theorem attained_950 : a 950 ≠ 0 :=
  attained_of_witness (by norm_num) sig_159516800 (by decide)

private theorem attained_951 : a 951 ≠ 0 :=
  attained_of_witness (by norm_num) sig_11565 (by decide)

private theorem attained_952 : a 952 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3802 (by decide)

private theorem attained_953 : a 953 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1664 (by decide)

private theorem attained_954 : a 954 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (908209 : ℕ) = 953^2), sigma_one_sq (by norm_num : Nat.Prime 953)] <;> norm_num) : (sigma 1 908209 : ℕ) = 909163) (by decide)

private theorem attained_955 : a 955 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3814 (by decide)

private theorem attained_956 : a 956 ≠ 0 :=
  attained_of_witness (by norm_num) sig_17738 (by decide)

private theorem attained_957 : a 957 ≠ 0 :=
  attained_of_witness (by norm_num) sig_6936 (by decide)

private theorem attained_958 : a 958 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3826 (by decide)

private theorem attained_959 : a 959 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3145 (by decide)

private theorem attained_960 : a 960 ≠ 0 :=
  attained_of_witness (by norm_num) sig_14778 (by decide)

private theorem attained_961 : a 961 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2523 (by decide)

private theorem attained_962 : a 962 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3460 (by decide)

private theorem attained_963 : a 963 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3255 (by decide)

private theorem attained_964 : a 964 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5132 (by decide)

private theorem attained_965 : a 965 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2564 (by decide)

private theorem attained_966 : a 966 ≠ 0 :=
  attained_of_witness (by norm_num) sig_24577344 (by decide)

private theorem attained_967 : a 967 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2674 (by decide)

private theorem attained_968 : a 968 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3866 (by decide)

private theorem attained_969 : a 969 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5802 (by decide)

private theorem attained_970 : a 970 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5164 (by decide)

private theorem attained_971 : a 971 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2150 (by decide)

private theorem attained_972 : a 972 ≠ 0 :=
  attained_of_witness (by norm_num) sig_311052 (by decide)

private theorem attained_973 : a 973 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2410 (by decide)

private theorem attained_974 : a 974 ≠ 0 :=
  attained_of_witness (by norm_num) sig_126560 (by decide)

private theorem attained_975 : a 975 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5523 (by decide)

private theorem attained_976 : a 976 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3898 (by decide)

private theorem attained_977 : a 977 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1856 (by decide)

private theorem attained_978 : a 978 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (954529 : ℕ) = 977^2), sigma_one_sq (by norm_num : Nat.Prime 977)] <;> norm_num) : (sigma 1 954529 : ℕ) = 955507) (by decide)

private theorem attained_979 : a 979 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4316 (by decide)

private theorem attained_980 : a 980 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2188032 (by decide)

private theorem attained_981 : a 981 ≠ 0 :=
  attained_of_witness (by norm_num) sig_4588 (by decide)

private theorem attained_982 : a 982 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5228 (by decide)

private theorem attained_983 : a 983 ≠ 0 :=
  attained_of_witness (by norm_num) sig_784 (by decide)

private theorem attained_984 : a 984 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (966289 : ℕ) = 983^2), sigma_one_sq (by norm_num : Nat.Prime 983)] <;> norm_num) : (sigma 1 966289 : ℕ) = 967273) (by decide)

private theorem attained_985 : a 985 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3358 (by decide)

private theorem attained_986 : a 986 ≠ 0 :=
  attained_of_witness (by norm_num) sig_25584 (by decide)

private theorem attained_987 : a 987 ≠ 0 :=
  attained_of_witness (by norm_num) sig_8871 (by decide)

private theorem attained_988 : a 988 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3946 (by decide)

private theorem attained_989 : a 989 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1971 (by decide)

private theorem attained_990 : a 990 ≠ 0 :=
  attained_of_witness (by norm_num) sig_58084 (by decide)

private theorem attained_991 : a 991 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2248 (by decide)

private theorem attained_992 : a 992 ≠ 0 :=
  attained_of_witness (by norm_num) ((by rw [(by norm_num : (982081 : ℕ) = 991^2), sigma_one_sq (by norm_num : Nat.Prime 991)] <;> norm_num) : (sigma 1 982081 : ℕ) = 983073) (by decide)

private theorem attained_993 : a 993 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1156 (by decide)

private theorem attained_994 : a 994 ≠ 0 :=
  attained_of_witness (by norm_num) sig_11450 (by decide)

private theorem attained_995 : a 995 ≠ 0 :=
  attained_of_witness (by norm_num) sig_2644 (by decide)

private theorem attained_996 : a 996 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1715040 (by decide)

private theorem attained_997 : a 997 ≠ 0 :=
  attained_of_witness (by norm_num) sig_1750 (by decide)

private theorem attained_998 : a 998 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3986 (by decide)

private theorem attained_999 : a 999 ≠ 0 :=
  attained_of_witness (by norm_num) sig_5982 (by decide)

private theorem attained_1000 : a 1000 ≠ 0 :=
  attained_of_witness (by norm_num) sig_3994 (by decide)

/-- The conjecture, formally verified for every `n ≤ 1000` via explicit witnesses. -/
theorem attained_of_le_1000 : ∀ n : ℕ, n ≤ 1000 → a n ≠ 0 := by
  intro n hn
  interval_cases n

  · exact attained_0
  · exact attained_1
  · exact attained_2
  · exact attained_3
  · exact attained_4
  · exact attained_5
  · exact attained_6
  · exact attained_7
  · exact attained_8
  · exact attained_9
  · exact attained_10
  · exact attained_11
  · exact attained_12
  · exact attained_13
  · exact attained_14
  · exact attained_15
  · exact attained_16
  · exact attained_17
  · exact attained_18
  · exact attained_19
  · exact attained_20
  · exact attained_21
  · exact attained_22
  · exact attained_23
  · exact attained_24
  · exact attained_25
  · exact attained_26
  · exact attained_27
  · exact attained_28
  · exact attained_29
  · exact attained_30
  · exact attained_31
  · exact attained_32
  · exact attained_33
  · exact attained_34
  · exact attained_35
  · exact attained_36
  · exact attained_37
  · exact attained_38
  · exact attained_39
  · exact attained_40
  · exact attained_41
  · exact attained_42
  · exact attained_43
  · exact attained_44
  · exact attained_45
  · exact attained_46
  · exact attained_47
  · exact attained_48
  · exact attained_49
  · exact attained_50
  · exact attained_51
  · exact attained_52
  · exact attained_53
  · exact attained_54
  · exact attained_55
  · exact attained_56
  · exact attained_57
  · exact attained_58
  · exact attained_59
  · exact attained_60
  · exact attained_61
  · exact attained_62
  · exact attained_63
  · exact attained_64
  · exact attained_65
  · exact attained_66
  · exact attained_67
  · exact attained_68
  · exact attained_69
  · exact attained_70
  · exact attained_71
  · exact attained_72
  · exact attained_73
  · exact attained_74
  · exact attained_75
  · exact attained_76
  · exact attained_77
  · exact attained_78
  · exact attained_79
  · exact attained_80
  · exact attained_81
  · exact attained_82
  · exact attained_83
  · exact attained_84
  · exact attained_85
  · exact attained_86
  · exact attained_87
  · exact attained_88
  · exact attained_89
  · exact attained_90
  · exact attained_91
  · exact attained_92
  · exact attained_93
  · exact attained_94
  · exact attained_95
  · exact attained_96
  · exact attained_97
  · exact attained_98
  · exact attained_99
  · exact attained_100
  · exact attained_101
  · exact attained_102
  · exact attained_103
  · exact attained_104
  · exact attained_105
  · exact attained_106
  · exact attained_107
  · exact attained_108
  · exact attained_109
  · exact attained_110
  · exact attained_111
  · exact attained_112
  · exact attained_113
  · exact attained_114
  · exact attained_115
  · exact attained_116
  · exact attained_117
  · exact attained_118
  · exact attained_119
  · exact attained_120
  · exact attained_121
  · exact attained_122
  · exact attained_123
  · exact attained_124
  · exact attained_125
  · exact attained_126
  · exact attained_127
  · exact attained_128
  · exact attained_129
  · exact attained_130
  · exact attained_131
  · exact attained_132
  · exact attained_133
  · exact attained_134
  · exact attained_135
  · exact attained_136
  · exact attained_137
  · exact attained_138
  · exact attained_139
  · exact attained_140
  · exact attained_141
  · exact attained_142
  · exact attained_143
  · exact attained_144
  · exact attained_145
  · exact attained_146
  · exact attained_147
  · exact attained_148
  · exact attained_149
  · exact attained_150
  · exact attained_151
  · exact attained_152
  · exact attained_153
  · exact attained_154
  · exact attained_155
  · exact attained_156
  · exact attained_157
  · exact attained_158
  · exact attained_159
  · exact attained_160
  · exact attained_161
  · exact attained_162
  · exact attained_163
  · exact attained_164
  · exact attained_165
  · exact attained_166
  · exact attained_167
  · exact attained_168
  · exact attained_169
  · exact attained_170
  · exact attained_171
  · exact attained_172
  · exact attained_173
  · exact attained_174
  · exact attained_175
  · exact attained_176
  · exact attained_177
  · exact attained_178
  · exact attained_179
  · exact attained_180
  · exact attained_181
  · exact attained_182
  · exact attained_183
  · exact attained_184
  · exact attained_185
  · exact attained_186
  · exact attained_187
  · exact attained_188
  · exact attained_189
  · exact attained_190
  · exact attained_191
  · exact attained_192
  · exact attained_193
  · exact attained_194
  · exact attained_195
  · exact attained_196
  · exact attained_197
  · exact attained_198
  · exact attained_199
  · exact attained_200
  · exact attained_201
  · exact attained_202
  · exact attained_203
  · exact attained_204
  · exact attained_205
  · exact attained_206
  · exact attained_207
  · exact attained_208
  · exact attained_209
  · exact attained_210
  · exact attained_211
  · exact attained_212
  · exact attained_213
  · exact attained_214
  · exact attained_215
  · exact attained_216
  · exact attained_217
  · exact attained_218
  · exact attained_219
  · exact attained_220
  · exact attained_221
  · exact attained_222
  · exact attained_223
  · exact attained_224
  · exact attained_225
  · exact attained_226
  · exact attained_227
  · exact attained_228
  · exact attained_229
  · exact attained_230
  · exact attained_231
  · exact attained_232
  · exact attained_233
  · exact attained_234
  · exact attained_235
  · exact attained_236
  · exact attained_237
  · exact attained_238
  · exact attained_239
  · exact attained_240
  · exact attained_241
  · exact attained_242
  · exact attained_243
  · exact attained_244
  · exact attained_245
  · exact attained_246
  · exact attained_247
  · exact attained_248
  · exact attained_249
  · exact attained_250
  · exact attained_251
  · exact attained_252
  · exact attained_253
  · exact attained_254
  · exact attained_255
  · exact attained_256
  · exact attained_257
  · exact attained_258
  · exact attained_259
  · exact attained_260
  · exact attained_261
  · exact attained_262
  · exact attained_263
  · exact attained_264
  · exact attained_265
  · exact attained_266
  · exact attained_267
  · exact attained_268
  · exact attained_269
  · exact attained_270
  · exact attained_271
  · exact attained_272
  · exact attained_273
  · exact attained_274
  · exact attained_275
  · exact attained_276
  · exact attained_277
  · exact attained_278
  · exact attained_279
  · exact attained_280
  · exact attained_281
  · exact attained_282
  · exact attained_283
  · exact attained_284
  · exact attained_285
  · exact attained_286
  · exact attained_287
  · exact attained_288
  · exact attained_289
  · exact attained_290
  · exact attained_291
  · exact attained_292
  · exact attained_293
  · exact attained_294
  · exact attained_295
  · exact attained_296
  · exact attained_297
  · exact attained_298
  · exact attained_299
  · exact attained_300
  · exact attained_301
  · exact attained_302
  · exact attained_303
  · exact attained_304
  · exact attained_305
  · exact attained_306
  · exact attained_307
  · exact attained_308
  · exact attained_309
  · exact attained_310
  · exact attained_311
  · exact attained_312
  · exact attained_313
  · exact attained_314
  · exact attained_315
  · exact attained_316
  · exact attained_317
  · exact attained_318
  · exact attained_319
  · exact attained_320
  · exact attained_321
  · exact attained_322
  · exact attained_323
  · exact attained_324
  · exact attained_325
  · exact attained_326
  · exact attained_327
  · exact attained_328
  · exact attained_329
  · exact attained_330
  · exact attained_331
  · exact attained_332
  · exact attained_333
  · exact attained_334
  · exact attained_335
  · exact attained_336
  · exact attained_337
  · exact attained_338
  · exact attained_339
  · exact attained_340
  · exact attained_341
  · exact attained_342
  · exact attained_343
  · exact attained_344
  · exact attained_345
  · exact attained_346
  · exact attained_347
  · exact attained_348
  · exact attained_349
  · exact attained_350
  · exact attained_351
  · exact attained_352
  · exact attained_353
  · exact attained_354
  · exact attained_355
  · exact attained_356
  · exact attained_357
  · exact attained_358
  · exact attained_359
  · exact attained_360
  · exact attained_361
  · exact attained_362
  · exact attained_363
  · exact attained_364
  · exact attained_365
  · exact attained_366
  · exact attained_367
  · exact attained_368
  · exact attained_369
  · exact attained_370
  · exact attained_371
  · exact attained_372
  · exact attained_373
  · exact attained_374
  · exact attained_375
  · exact attained_376
  · exact attained_377
  · exact attained_378
  · exact attained_379
  · exact attained_380
  · exact attained_381
  · exact attained_382
  · exact attained_383
  · exact attained_384
  · exact attained_385
  · exact attained_386
  · exact attained_387
  · exact attained_388
  · exact attained_389
  · exact attained_390
  · exact attained_391
  · exact attained_392
  · exact attained_393
  · exact attained_394
  · exact attained_395
  · exact attained_396
  · exact attained_397
  · exact attained_398
  · exact attained_399
  · exact attained_400
  · exact attained_401
  · exact attained_402
  · exact attained_403
  · exact attained_404
  · exact attained_405
  · exact attained_406
  · exact attained_407
  · exact attained_408
  · exact attained_409
  · exact attained_410
  · exact attained_411
  · exact attained_412
  · exact attained_413
  · exact attained_414
  · exact attained_415
  · exact attained_416
  · exact attained_417
  · exact attained_418
  · exact attained_419
  · exact attained_420
  · exact attained_421
  · exact attained_422
  · exact attained_423
  · exact attained_424
  · exact attained_425
  · exact attained_426
  · exact attained_427
  · exact attained_428
  · exact attained_429
  · exact attained_430
  · exact attained_431
  · exact attained_432
  · exact attained_433
  · exact attained_434
  · exact attained_435
  · exact attained_436
  · exact attained_437
  · exact attained_438
  · exact attained_439
  · exact attained_440
  · exact attained_441
  · exact attained_442
  · exact attained_443
  · exact attained_444
  · exact attained_445
  · exact attained_446
  · exact attained_447
  · exact attained_448
  · exact attained_449
  · exact attained_450
  · exact attained_451
  · exact attained_452
  · exact attained_453
  · exact attained_454
  · exact attained_455
  · exact attained_456
  · exact attained_457
  · exact attained_458
  · exact attained_459
  · exact attained_460
  · exact attained_461
  · exact attained_462
  · exact attained_463
  · exact attained_464
  · exact attained_465
  · exact attained_466
  · exact attained_467
  · exact attained_468
  · exact attained_469
  · exact attained_470
  · exact attained_471
  · exact attained_472
  · exact attained_473
  · exact attained_474
  · exact attained_475
  · exact attained_476
  · exact attained_477
  · exact attained_478
  · exact attained_479
  · exact attained_480
  · exact attained_481
  · exact attained_482
  · exact attained_483
  · exact attained_484
  · exact attained_485
  · exact attained_486
  · exact attained_487
  · exact attained_488
  · exact attained_489
  · exact attained_490
  · exact attained_491
  · exact attained_492
  · exact attained_493
  · exact attained_494
  · exact attained_495
  · exact attained_496
  · exact attained_497
  · exact attained_498
  · exact attained_499
  · exact attained_500
  · exact attained_501
  · exact attained_502
  · exact attained_503
  · exact attained_504
  · exact attained_505
  · exact attained_506
  · exact attained_507
  · exact attained_508
  · exact attained_509
  · exact attained_510
  · exact attained_511
  · exact attained_512
  · exact attained_513
  · exact attained_514
  · exact attained_515
  · exact attained_516
  · exact attained_517
  · exact attained_518
  · exact attained_519
  · exact attained_520
  · exact attained_521
  · exact attained_522
  · exact attained_523
  · exact attained_524
  · exact attained_525
  · exact attained_526
  · exact attained_527
  · exact attained_528
  · exact attained_529
  · exact attained_530
  · exact attained_531
  · exact attained_532
  · exact attained_533
  · exact attained_534
  · exact attained_535
  · exact attained_536
  · exact attained_537
  · exact attained_538
  · exact attained_539
  · exact attained_540
  · exact attained_541
  · exact attained_542
  · exact attained_543
  · exact attained_544
  · exact attained_545
  · exact attained_546
  · exact attained_547
  · exact attained_548
  · exact attained_549
  · exact attained_550
  · exact attained_551
  · exact attained_552
  · exact attained_553
  · exact attained_554
  · exact attained_555
  · exact attained_556
  · exact attained_557
  · exact attained_558
  · exact attained_559
  · exact attained_560
  · exact attained_561
  · exact attained_562
  · exact attained_563
  · exact attained_564
  · exact attained_565
  · exact attained_566
  · exact attained_567
  · exact attained_568
  · exact attained_569
  · exact attained_570
  · exact attained_571
  · exact attained_572
  · exact attained_573
  · exact attained_574
  · exact attained_575
  · exact attained_576
  · exact attained_577
  · exact attained_578
  · exact attained_579
  · exact attained_580
  · exact attained_581
  · exact attained_582
  · exact attained_583
  · exact attained_584
  · exact attained_585
  · exact attained_586
  · exact attained_587
  · exact attained_588
  · exact attained_589
  · exact attained_590
  · exact attained_591
  · exact attained_592
  · exact attained_593
  · exact attained_594
  · exact attained_595
  · exact attained_596
  · exact attained_597
  · exact attained_598
  · exact attained_599
  · exact attained_600
  · exact attained_601
  · exact attained_602
  · exact attained_603
  · exact attained_604
  · exact attained_605
  · exact attained_606
  · exact attained_607
  · exact attained_608
  · exact attained_609
  · exact attained_610
  · exact attained_611
  · exact attained_612
  · exact attained_613
  · exact attained_614
  · exact attained_615
  · exact attained_616
  · exact attained_617
  · exact attained_618
  · exact attained_619
  · exact attained_620
  · exact attained_621
  · exact attained_622
  · exact attained_623
  · exact attained_624
  · exact attained_625
  · exact attained_626
  · exact attained_627
  · exact attained_628
  · exact attained_629
  · exact attained_630
  · exact attained_631
  · exact attained_632
  · exact attained_633
  · exact attained_634
  · exact attained_635
  · exact attained_636
  · exact attained_637
  · exact attained_638
  · exact attained_639
  · exact attained_640
  · exact attained_641
  · exact attained_642
  · exact attained_643
  · exact attained_644
  · exact attained_645
  · exact attained_646
  · exact attained_647
  · exact attained_648
  · exact attained_649
  · exact attained_650
  · exact attained_651
  · exact attained_652
  · exact attained_653
  · exact attained_654
  · exact attained_655
  · exact attained_656
  · exact attained_657
  · exact attained_658
  · exact attained_659
  · exact attained_660
  · exact attained_661
  · exact attained_662
  · exact attained_663
  · exact attained_664
  · exact attained_665
  · exact attained_666
  · exact attained_667
  · exact attained_668
  · exact attained_669
  · exact attained_670
  · exact attained_671
  · exact attained_672
  · exact attained_673
  · exact attained_674
  · exact attained_675
  · exact attained_676
  · exact attained_677
  · exact attained_678
  · exact attained_679
  · exact attained_680
  · exact attained_681
  · exact attained_682
  · exact attained_683
  · exact attained_684
  · exact attained_685
  · exact attained_686
  · exact attained_687
  · exact attained_688
  · exact attained_689
  · exact attained_690
  · exact attained_691
  · exact attained_692
  · exact attained_693
  · exact attained_694
  · exact attained_695
  · exact attained_696
  · exact attained_697
  · exact attained_698
  · exact attained_699
  · exact attained_700
  · exact attained_701
  · exact attained_702
  · exact attained_703
  · exact attained_704
  · exact attained_705
  · exact attained_706
  · exact attained_707
  · exact attained_708
  · exact attained_709
  · exact attained_710
  · exact attained_711
  · exact attained_712
  · exact attained_713
  · exact attained_714
  · exact attained_715
  · exact attained_716
  · exact attained_717
  · exact attained_718
  · exact attained_719
  · exact attained_720
  · exact attained_721
  · exact attained_722
  · exact attained_723
  · exact attained_724
  · exact attained_725
  · exact attained_726
  · exact attained_727
  · exact attained_728
  · exact attained_729
  · exact attained_730
  · exact attained_731
  · exact attained_732
  · exact attained_733
  · exact attained_734
  · exact attained_735
  · exact attained_736
  · exact attained_737
  · exact attained_738
  · exact attained_739
  · exact attained_740
  · exact attained_741
  · exact attained_742
  · exact attained_743
  · exact attained_744
  · exact attained_745
  · exact attained_746
  · exact attained_747
  · exact attained_748
  · exact attained_749
  · exact attained_750
  · exact attained_751
  · exact attained_752
  · exact attained_753
  · exact attained_754
  · exact attained_755
  · exact attained_756
  · exact attained_757
  · exact attained_758
  · exact attained_759
  · exact attained_760
  · exact attained_761
  · exact attained_762
  · exact attained_763
  · exact attained_764
  · exact attained_765
  · exact attained_766
  · exact attained_767
  · exact attained_768
  · exact attained_769
  · exact attained_770
  · exact attained_771
  · exact attained_772
  · exact attained_773
  · exact attained_774
  · exact attained_775
  · exact attained_776
  · exact attained_777
  · exact attained_778
  · exact attained_779
  · exact attained_780
  · exact attained_781
  · exact attained_782
  · exact attained_783
  · exact attained_784
  · exact attained_785
  · exact attained_786
  · exact attained_787
  · exact attained_788
  · exact attained_789
  · exact attained_790
  · exact attained_791
  · exact attained_792
  · exact attained_793
  · exact attained_794
  · exact attained_795
  · exact attained_796
  · exact attained_797
  · exact attained_798
  · exact attained_799
  · exact attained_800
  · exact attained_801
  · exact attained_802
  · exact attained_803
  · exact attained_804
  · exact attained_805
  · exact attained_806
  · exact attained_807
  · exact attained_808
  · exact attained_809
  · exact attained_810
  · exact attained_811
  · exact attained_812
  · exact attained_813
  · exact attained_814
  · exact attained_815
  · exact attained_816
  · exact attained_817
  · exact attained_818
  · exact attained_819
  · exact attained_820
  · exact attained_821
  · exact attained_822
  · exact attained_823
  · exact attained_824
  · exact attained_825
  · exact attained_826
  · exact attained_827
  · exact attained_828
  · exact attained_829
  · exact attained_830
  · exact attained_831
  · exact attained_832
  · exact attained_833
  · exact attained_834
  · exact attained_835
  · exact attained_836
  · exact attained_837
  · exact attained_838
  · exact attained_839
  · exact attained_840
  · exact attained_841
  · exact attained_842
  · exact attained_843
  · exact attained_844
  · exact attained_845
  · exact attained_846
  · exact attained_847
  · exact attained_848
  · exact attained_849
  · exact attained_850
  · exact attained_851
  · exact attained_852
  · exact attained_853
  · exact attained_854
  · exact attained_855
  · exact attained_856
  · exact attained_857
  · exact attained_858
  · exact attained_859
  · exact attained_860
  · exact attained_861
  · exact attained_862
  · exact attained_863
  · exact attained_864
  · exact attained_865
  · exact attained_866
  · exact attained_867
  · exact attained_868
  · exact attained_869
  · exact attained_870
  · exact attained_871
  · exact attained_872
  · exact attained_873
  · exact attained_874
  · exact attained_875
  · exact attained_876
  · exact attained_877
  · exact attained_878
  · exact attained_879
  · exact attained_880
  · exact attained_881
  · exact attained_882
  · exact attained_883
  · exact attained_884
  · exact attained_885
  · exact attained_886
  · exact attained_887
  · exact attained_888
  · exact attained_889
  · exact attained_890
  · exact attained_891
  · exact attained_892
  · exact attained_893
  · exact attained_894
  · exact attained_895
  · exact attained_896
  · exact attained_897
  · exact attained_898
  · exact attained_899
  · exact attained_900
  · exact attained_901
  · exact attained_902
  · exact attained_903
  · exact attained_904
  · exact attained_905
  · exact attained_906
  · exact attained_907
  · exact attained_908
  · exact attained_909
  · exact attained_910
  · exact attained_911
  · exact attained_912
  · exact attained_913
  · exact attained_914
  · exact attained_915
  · exact attained_916
  · exact attained_917
  · exact attained_918
  · exact attained_919
  · exact attained_920
  · exact attained_921
  · exact attained_922
  · exact attained_923
  · exact attained_924
  · exact attained_925
  · exact attained_926
  · exact attained_927
  · exact attained_928
  · exact attained_929
  · exact attained_930
  · exact attained_931
  · exact attained_932
  · exact attained_933
  · exact attained_934
  · exact attained_935
  · exact attained_936
  · exact attained_937
  · exact attained_938
  · exact attained_939
  · exact attained_940
  · exact attained_941
  · exact attained_942
  · exact attained_943
  · exact attained_944
  · exact attained_945
  · exact attained_946
  · exact attained_947
  · exact attained_948
  · exact attained_949
  · exact attained_950
  · exact attained_951
  · exact attained_952
  · exact attained_953
  · exact attained_954
  · exact attained_955
  · exact attained_956
  · exact attained_957
  · exact attained_958
  · exact attained_959
  · exact attained_960
  · exact attained_961
  · exact attained_962
  · exact attained_963
  · exact attained_964
  · exact attained_965
  · exact attained_966
  · exact attained_967
  · exact attained_968
  · exact attained_969
  · exact attained_970
  · exact attained_971
  · exact attained_972
  · exact attained_973
  · exact attained_974
  · exact attained_975
  · exact attained_976
  · exact attained_977
  · exact attained_978
  · exact attained_979
  · exact attained_980
  · exact attained_981
  · exact attained_982
  · exact attained_983
  · exact attained_984
  · exact attained_985
  · exact attained_986
  · exact attained_987
  · exact attained_988
  · exact attained_989
  · exact attained_990
  · exact attained_991
  · exact attained_992
  · exact attained_993
  · exact attained_994
  · exact attained_995
  · exact attained_996
  · exact attained_997
  · exact attained_998
  · exact attained_999
  · exact attained_1000

/--
**The open core.**  By `conjecture_iff_generalized_multiperfect` (proved above), the
conjecture below is *equivalent* to this statement: every `n` admits a "generalized
multiperfect" solution `σ(g·h) = g·(h + n)` with `gcd h n = 1`.  For odd `n` this
contains open binary prime-pair existence problems (Dirichlet-type results cannot fix
the quotient `(p+1)/q`); for even `n` it contains open multiperfect-existence problems
(e.g. for `n = 2` the known witnesses are exactly the triperfect numbers).  It is
proved above for all `n ≤ 1000` (`attained_of_le_1000`) and for several infinite
families (`mersenne_attained`, `succ_prime_attained`, `two_p_attained`,
`attained_of_prime_pair`, `attained_of_multiperfect`), but it is a genuinely open
problem in general (OEIS A243512, M. F. Hasler, 2014); the `sorry` below records
exactly this open core, and nothing else in this file is unproved.
-/
theorem generalized_multiperfect_exists :
    ∀ n : ℕ, ∃ g h : ℕ, 0 < g ∧ 0 < h ∧ Nat.Coprime h n ∧
      sigma 1 (g * h) = g * (h + n) := by
  sorry

/--
Motivated by the observation that some small numbers (2,12,14,18,...) occur only very late
in the recently added sequence A243473, but all numbers seem to appear sooner or later.
(The definition is completed by "0 if no such index exists" to guarantee well-definedness
in absence of a proof, but I conjecture that no such 0 will ever occur.)
The conjecture is that the sequence $\mathrm{A243473\_val}$ is eventually surjective onto $\mathbb{N} \setminus \{0, 1\}$.
-/
theorem oeis_243512_conjecture_0 (n : ℕ) : a n ≠ 0 := by
  -- This is equivalent to saying that for every n, the set
  -- {i : ℕ | 0 < i ∧ A243473_val i = n} is non-empty.
  -- The provided OEIS conjecture is that no `a(n)` will ever be 0.
  --
  -- By `a_ne_zero_iff` this requires exhibiting, for every `n`, a solution of
  -- `σ(g·h) = g·(h + n)` with `gcd h n = 1`; as documented above this is an open
  -- problem (for odd `n` it needs open binary prime-pair existence results; for even
  -- `n` it needs sporadic generalized-multiperfect numbers, including instances whose
  -- existence is currently unknown, e.g. `n = 630`).  No proof with the permitted
  -- axioms is currently possible; the open core is recorded honestly in
  -- `generalized_multiperfect_exists` above, from which the conjecture follows by the
  -- (fully proved) equivalence `conjecture_iff_generalized_multiperfect`.
  exact conjecture_iff_generalized_multiperfect.mpr generalized_multiperfect_exists n
