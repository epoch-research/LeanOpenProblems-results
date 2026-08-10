import FormalConjectures.Util.ProblemImports

open Nat

/--
A211420: $a(n) = \frac{(8n)! n!}{(4n)! (3n)! (2n)!}$
Since the OEIS entry states that this ratio is always an integer, we define it directly as a natural number.
The division in Lean's `Nat` type is integer division, which is exact here.
-/
def A211420 (n : ℕ) : ℕ :=
  (8 * n).factorial * n.factorial / ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial)

namespace A211420Proof

/-- The base floor-function inequality (integrality of the factorial ratio),
reduced to the fractional part `s = n % m`. -/
private lemma claim0s (m s : ℕ) (hs : s < m) : 4*s/m + 3*s/m + 2*s/m ≤ 8*s/m := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le s) hs
  have h2 := Nat.div_add_mod (2*s) m
  have h3 := Nat.div_add_mod (3*s) m
  have h4 := Nat.div_add_mod (4*s) m
  have h8 := Nat.div_add_mod (8*s) m
  have m2 : (2*s) % m < m := Nat.mod_lt _ hm
  have m3 : (3*s) % m < m := Nat.mod_lt _ hm
  have m4 : (4*s) % m < m := Nat.mod_lt _ hm
  have m8 : (8*s) % m < m := Nat.mod_lt _ hm
  have b2 : 2*s/m < 2 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have b3 : 3*s/m < 3 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have b4 : 4*s/m < 4 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  have b8 : 8*s/m < 8 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  set a := 2*s/m with ha
  set b := 3*s/m with hb
  set c := 4*s/m with hc
  set d := 8*s/m with hd
  clear_value a b c d
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;> omega

/-- The base floor inequality for all `n`. -/
private lemma claim0 (n m : ℕ) : 4*n/m + 3*n/m + 2*n/m ≤ 8*n/m + n/m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hn := Nat.div_add_mod n m
  set q := n / m with hq
  set s := n % m with hsdef
  have hs : s < m := Nat.mod_lt _ hm
  have e : ∀ t : ℕ, t * n / m = t * q + t * s / m := by
    intro t
    conv_lhs => rw [← hn]
    rw [show t*(m*q+s) = m*(t*q) + t*s by ring, Nat.mul_add_div hm]
  have key := claim0s m s hs
  rw [e 4, e 3, e 2, e 8]
  omega

/-- **Claim A**: if `m ∣ k*n + i` with `1 ≤ i`, `8*i ≤ m`, `k ∈ {1,2,3}`, then the
Landau function `⌊8n/m⌋+⌊n/m⌋-⌊4n/m⌋-⌊3n/m⌋-⌊2n/m⌋` is at least 1.
Indeed, writing `s = n % m`, we get `k*s + i = c*m` with `1 ≤ c ≤ k`, so `s/m` is
just below one of `1/3, 1/2, 2/3, 1`, where the Landau function equals 1. -/
private lemma claimA (k i m n : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (hi : 1 ≤ i) (him : 8*i ≤ m)
    (hdvd : m ∣ k*n + i) :
    4*n/m + 3*n/m + 2*n/m + 1 ≤ 8*n/m + n/m := by
  have hm : 0 < m := by omega
  have hn := Nat.div_add_mod n m
  set q := n / m with hq
  set s := n % m with hsdef
  have hs : s < m := Nat.mod_lt _ hm
  -- transfer the congruence to s
  have hdvd' : m ∣ k*s + i := by
    have h1 : k*s + i ≡ k*n + i [MOD m] := ((Nat.mod_modEq n m).mul_left k).add_right i
    have h2 : k*n + i ≡ 0 [MOD m] := (Nat.modEq_zero_iff_dvd).2 hdvd
    exact (Nat.modEq_zero_iff_dvd).1 (h1.trans h2)
  obtain ⟨c, hc⟩ := hdvd'
  -- rewrite the goal in terms of q and s
  have e : ∀ t : ℕ, t * n / m = t * q + t * s / m := by
    intro t
    conv_lhs => rw [← hn]
    rw [show t*(m*q+s) = m*(t*q) + t*s by ring, Nat.mul_add_div hm]
  rw [e 4, e 3, e 2, e 8]
  -- bound c
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · simp at hc; omega
    · exact h
  have hc3 : c ≤ 3 := by
    by_contra hcon
    push_neg at hcon
    have h4 : m*4 ≤ m*c := Nat.mul_le_mul_left m (by omega)
    rw [← hc] at h4
    have hks : k*s ≤ 3*s := Nat.mul_le_mul_right s hk3
    omega
  clear hdvd hn hq hsdef
  interval_cases k <;> interval_cases c
  -- (k,c) = (1,1)
  · have d2 : 2*s/m = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have d3 : 3*s/m = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have d4 : 4*s/m = 3 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have d8 : 8*s/m = 7 := Nat.div_eq_of_lt_le (by omega) (by omega)
    omega
  -- (1,2) impossible
  · omega
  -- (1,3) impossible
  · omega
  -- (2,1)
  · have d2 : 2*s/m = 0 := Nat.div_eq_of_lt (by omega)
    have d3 : 3*s/m = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have d4 : 4*s/m = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have d8 : 8*s/m = 3 := Nat.div_eq_of_lt_le (by omega) (by omega)
    omega
  -- (2,2)
  · have d2 : 2*s/m = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have d3 : 3*s/m = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have d4 : 4*s/m = 3 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have d8 : 8*s/m = 7 := Nat.div_eq_of_lt_le (by omega) (by omega)
    omega
  -- (2,3) impossible
  · omega
  -- (3,1)
  · have d2 : 2*s/m = 0 := Nat.div_eq_of_lt (by omega)
    have d3 : 3*s/m = 0 := Nat.div_eq_of_lt (by omega)
    have d4 : 4*s/m = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have d8 : 8*s/m = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    omega
  -- (3,2)
  · have d2 : 2*s/m = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have d3 : 3*s/m = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have d4 : 4*s/m = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have d8 : 8*s/m = 5 := Nat.div_eq_of_lt_le (by omega) (by omega)
    omega
  -- (3,3)
  · have d2 : 2*s/m = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have d3 : 3*s/m = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have d4 : 4*s/m = 3 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have d8 : 8*s/m = 7 := Nat.div_eq_of_lt_le (by omega) (by omega)
    omega

/-- **Claim A'** : the per-level inequality when the level `m` is large (`m ≥ 8r`). -/
private lemma claimA' (k r m n : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (hr : 1 ≤ r) (hm8 : 8*r ≤ m) :
    (k*n+r)/m + 4*n/m + 3*n/m + 2*n/m ≤ 8*n/m + n/m + k*n/m := by
  have hm : 0 < m := by omega
  have h0 := claim0 n m
  have hub : (k*n+r)/m ≤ k*n/m + 1 := by
    calc (k*n+r)/m ≤ (k*n+m)/m := Nat.div_le_div_right (by omega)
    _ = k*n/m + 1 := Nat.add_div_right _ hm
  have hlb : k*n/m ≤ (k*n+r)/m := Nat.div_le_div_right (by omega)
  rcases Nat.lt_or_ge ((k*n+r)/m) (k*n/m + 1) with hlt | hge
  · omega
  · -- (k*n+r)/m = k*n/m + 1 : there is a multiple of m in (k*n, k*n+r]
    have heq : (k*n+r)/m = k*n/m + 1 := by omega
    have hmul : m * ((k*n+r)/m) ≤ k*n + r := by
      have := Nat.div_add_mod (k*n+r) m
      omega
    have hmul2 : m * ((k*n+r)/m) = m * (k*n/m) + m := by rw [heq]; ring
    have hknlt : k*n < m * (k*n/m) + m := by
      have h1 := Nat.div_add_mod (k*n) m
      have h2 : (k*n) % m < m := Nat.mod_lt _ hm
      omega
    have hknge : m * (k*n/m) ≤ k*n := Nat.mul_div_le (k*n) m
    -- the witness i
    set i := m * (k*n/m) + m - k*n with hidef
    have hi1 : 1 ≤ i := by omega
    have hir : i ≤ r := by omega
    have hdvd : m ∣ k*n + i := by
      refine ⟨k*n/m + 1, ?_⟩
      have hd : m * (k*n/m + 1) = m*(k*n/m) + m := by ring
      omega
    have := claimA k i m n hk1 hk3 hi1 (by omega) hdvd
    omega

/-- Per-level inequality with defect term, for every level `m`. -/
private lemma perj (k r m n : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (hr : 1 ≤ r) :
    (k*n+r)/m + 4*n/m + 3*n/m + 2*n/m
      ≤ 8*n/m + n/m + k*n/m + (if m < 8*r then r else 0) := by
  split_ifs with h
  · -- defect case: (k*n+r)/m ≤ k*n/m + r plus claim0
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have h1 : (k*n+r)/m ≤ k*n/m + r := by
      calc (k*n+r)/m ≤ (k*n + r*m)/m := Nat.div_le_div_right (by nlinarith)
      _ = k*n/m + r := Nat.add_mul_div_right _ _ hm
    have h0 := claim0 n m
    omega
  · exact claimA' k r m n hk1 hk3 hr (by omega)

/-- Legendre's formula in the form we need. -/
private lemma legendre {p : ℕ} (hp : p.Prime) {t b : ℕ} (hb : t < b) :
    (t !).factorization p = ∑ j ∈ Finset.Ico 1 b, t / p ^ j := by
  haveI := Fact.mk hp
  rw [Nat.factorization_def _ hp]
  exact padicValNat_factorial (lt_of_le_of_lt (Nat.log_le_self p t) hb)

/-- Integrality of A211420: `(4n)!(3n)!(2n)! ∣ (8n)! n!`. -/
private lemma integrality (n : ℕ) : (4*n)! * (3*n)! * (2*n)! ∣ (8*n)! * n ! := by
  have f8 : (8*n)! ≠ 0 := Nat.factorial_ne_zero _
  have f4 : (4*n)! ≠ 0 := Nat.factorial_ne_zero _
  have f3 : (3*n)! ≠ 0 := Nat.factorial_ne_zero _
  have f2 : (2*n)! ≠ 0 := Nat.factorial_ne_zero _
  have f1 : n ! ≠ 0 := Nat.factorial_ne_zero _
  rw [← Nat.factorization_le_iff_dvd (by positivity) (by positivity), Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul (mul_ne_zero f4 f3) f2, Nat.factorization_mul f4 f3,
      Nat.factorization_mul f8 f1]
    simp only [Finsupp.coe_add, Pi.add_apply]
    rw [legendre hp (show 8*n < 8*n+1 by omega), legendre hp (show 4*n < 8*n+1 by omega),
      legendre hp (show 3*n < 8*n+1 by omega), legendre hp (show 2*n < 8*n+1 by omega),
      legendre hp (show n < 8*n+1 by omega)]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => claim0 n (p ^ j)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- Bound on the total defect over all levels. -/
private lemma defect_bound (p r b : ℕ) (hp : 2 ≤ p) (hr : 1 ≤ r) :
    (∑ j ∈ Finset.Ico 1 b, (if p ^ j < 8*r then r else 0)) ≤ r * (r + 2) := by
  have step1 : ∀ j ∈ Finset.Ico 1 b,
      (if p ^ j < 8*r then r else 0) ≤ (if j < r + 3 then r else 0) := by
    intro j _
    split_ifs with h1 h2
    · exact le_rfl
    · -- j ≥ r+3 but p^j < 8r : contradiction
      exfalso
      push_neg at h2
      have e1 : 2 ^ j ≤ p ^ j := Nat.pow_le_pow_left hp j
      have e2 : 2 ^ (r+3) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) h2
      have e3 : 2 ^ (r+3) = 8 * 2 ^ r := by rw [pow_add]; ring
      have e4 : r < 2 ^ r := Nat.lt_two_pow_self
      omega
    · exact Nat.zero_le _
    · exact le_rfl
  calc (∑ j ∈ Finset.Ico 1 b, (if p ^ j < 8*r then r else 0))
      ≤ ∑ j ∈ Finset.Ico 1 b, (if j < r + 3 then r else 0) := Finset.sum_le_sum step1
    _ = ∑ j ∈ (Finset.Ico 1 b).filter (fun j => j < r + 3), r := (Finset.sum_filter _ _).symm
    _ ≤ ∑ j ∈ Finset.Ico 1 (r + 3), r := by
        apply Finset.sum_le_sum_of_subset
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_Ico] at hx ⊢
        omega
    _ ≤ r * (r + 2) := by
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
        have h : r + 3 - 1 = r + 2 := by omega
        rw [h, Nat.mul_comm]

end A211420Proof

open A211420Proof in
/--
General Conjecture:
There are constants $C(k, r)$, for $k \in \{1, 2, 3\}$ and $r \ge 1$,
such that $a(n) \cdot C(k, r) / ((k \cdot n + 1)(k \cdot n + 2)\cdots(k \cdot n + r))$ is an integer for all $n$.
The denominator product $\prod_{i=1}^r (k \cdot n + i)$ is formalized using Nat.ascFactorial,
where $\text{ascFactorial } x r = x(x+1)\cdots(x+r-1)$.
Letting $x = k \cdot n + 1$ gives the desired product.
-/
theorem A211420_general_divisibility_conjecture :
  ∀ (k : ℕ) (r : ℕ), (k = 1 ∨ k = 2 ∨ k = 3) → (r ≥ 1) → ∃ C : ℕ, ∀ n : ℕ,
    Nat.ascFactorial (k * n + 1) r ∣ C * (A211420 n) := by
  intro k r hk hr
  have hk1 : 1 ≤ k := by rcases hk with h|h|h <;> omega
  have hk3 : k ≤ 3 := by rcases hk with h|h|h <;> omega
  refine ⟨((8*r)!) ^ (r*(r+3)), fun n => ?_⟩
  have hC0 : ((8*r)!) ^ (r*(r+3)) ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero _)
  have haval : ((4*n)! * (3*n)! * (2*n)!) * A211420 n = (8*n)! * n ! := by
    simp only [A211420]
    exact Nat.mul_div_cancel' (integrality n)
  have ha0 : A211420 n ≠ 0 := by
    intro h
    rw [h, Nat.mul_zero] at haval
    have hpos : (0:ℕ) < (8*n)! * n ! := by positivity
    omega
  have hasc0 : (k*n + 1).ascFactorial r ≠ 0 := (Nat.ascFactorial_pos (k*n) r).ne'
  rw [← Nat.factorization_le_iff_dvd hasc0 (mul_ne_zero hC0 ha0), Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  swap
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  set b := 8*n + r + 1 with hb
  have L8 := legendre hp (show 8*n < b by omega)
  have L4 := legendre hp (show 4*n < b by omega)
  have L3 := legendre hp (show 3*n < b by omega)
  have L2 := legendre hp (show 2*n < b by omega)
  have L1 := legendre hp (show n < b by omega)
  have Lk := legendre hp (show k*n < b by
    have : k*n ≤ 3*n := Nat.mul_le_mul_right n hk3
    omega)
  have Lkr := legendre hp (show k*n + r < b by
    have : k*n ≤ 3*n := Nat.mul_le_mul_right n hk3
    omega)
  -- factorization of the ascFactorial via factorials
  have F1 : ((k*n)!).factorization p + ((k*n + 1).ascFactorial r).factorization p
      = ((k*n + r)!).factorization p := by
    rw [← Nat.factorial_mul_ascFactorial (k*n) r,
      Nat.factorization_mul (Nat.factorial_ne_zero _) hasc0]
    simp
  -- factorization identity from integrality
  have F2 : ((4*n)!).factorization p + ((3*n)!).factorization p + ((2*n)!).factorization p
      + (A211420 n).factorization p = ((8*n)!).factorization p + (n !).factorization p := by
    have h := congrArg (fun x : ℕ => x.factorization p) haval
    simp only at h
    rw [Nat.factorization_mul (by positivity) ha0,
      Nat.factorization_mul (by positivity) (Nat.factorial_ne_zero (2*n)),
      Nat.factorization_mul (Nat.factorial_ne_zero (4*n)) (Nat.factorial_ne_zero (3*n)),
      Nat.factorization_mul (Nat.factorial_ne_zero (8*n)) (Nat.factorial_ne_zero n)] at h
    simpa using h
  -- split the RHS
  have hCsplit : ((((8*r)!) ^ (r*(r+3))) * A211420 n).factorization p
      = (r*(r+3)) * ((8*r)!).factorization p + (A211420 n).factorization p := by
    rw [Nat.factorization_mul hC0 ha0, Nat.factorization_pow]
    simp [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [hCsplit]
  -- the key summed inequality
  have key1 : (∑ j ∈ Finset.Ico 1 b, ((k*n+r)/p^j + 4*n/p^j + 3*n/p^j + 2*n/p^j))
      ≤ ∑ j ∈ Finset.Ico 1 b, (8*n/p^j + n/p^j + k*n/p^j + (if p^j < 8*r then r else 0)) :=
    Finset.sum_le_sum fun j _ => perj k r (p^j) n hk1 hk3 hr
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at key1
  rcases Nat.lt_or_ge p (8*r) with hplt | hpge
  · -- small prime: use the defect bound and the positivity of the valuation of (8r)!
    have key2 := defect_bound p r b hp.two_le hr
    have hvp : 1 ≤ ((8*r)!).factorization p :=
      Nat.Prime.factorization_pos_of_dvd hp (Nat.factorial_ne_zero _)
        (Nat.dvd_factorial hp.pos (by omega))
    have hle : r*(r+3) ≤ r*(r+3) * ((8*r)!).factorization p :=
      Nat.le_mul_of_pos_right _ hvp
    have hsplit : r*(r+3) = r*(r+2) + r := by ring
    omega
  · -- large prime: no defect at all
    have key0 : (∑ j ∈ Finset.Ico 1 b, ((k*n+r)/p^j + 4*n/p^j + 3*n/p^j + 2*n/p^j))
        ≤ ∑ j ∈ Finset.Ico 1 b, (8*n/p^j + n/p^j + k*n/p^j) :=
      Finset.sum_le_sum fun j hj => claimA' k r (p^j) n hk1 hk3 hr
        (le_trans hpge (Nat.le_self_pow (by
          have := (Finset.mem_Ico.1 hj).1; omega) p))
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib] at key0
    omega
