import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A004290: Least positive multiple of $n$ that when written in base 10 uses only 0's and 1's.
-/
noncomputable def A004290 (n : ℕ) : ℕ :=
  -- The set of positive multiples of $n$ that are composed only of 0's and 1's in base 10.
  let S := { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }

  -- The sequence value is the smallest element of this set, which is the infimum.
  -- For n=0, the set is empty, and sInf on the empty set of ℕ is 0. The OEIS definition
  -- explicitly states "Least positive multiple of n", which implies n > 0.
  -- However, if S is empty, sInf S = 0. A004290(0) is an edge case, but the conjecture
  -- only concerns n < 10^k - 1, where we assume k ≥ 1, so n ≥ 1.
  sInf S



/-!
## Status of this formalization

* Part 1 (`A004290 (10^k) = 10^k`) and Part 2 (`A004290 (10^k - 1) = (10^(9k) - 1)/9`)
  are proven below (`A004290Aux.part1`, `A004290Aux.part2`).  The main ingredient for
  Part 2 is the classical lemma that every positive multiple of `10^k - 1` has decimal
  digit sum at least `9k` (`A004290Aux.ds_ge_of_dvd`), proved by strong induction using
  subadditivity of the digit sum and splitting off the lowest `k` digits.

* Part 3 (`∀ n < 10^k - 1, A004290 n < A004290 (10^k - 1)`) is the genuinely open
  question of Radcliffe.  Writing `n = 2^j · n'` with `gcd(n', 10) = 1`, `d = ord_{n'}(10)`
  and `q = (10^d - 1)/n'`, a 0/1 multiple of `n'` with at most `L` digits exists iff some
  `t ∈ [1, q-1]` has the `d`-digit block of `t·n'` digit-wise bounded by
  `M_r = ⌊(L-1-r)/d⌋ + 1`.  For `d ≥ 9(d-k)` this says: the first `9(d-k)+j` decimal digits
  of `t/q` contain no `9`.  An exhaustive computer search over all `q ≤ 10^8` (this covers,
  for every `k`, all `n'` with `ord_{n'}(10) ≤ k + 7`), brute force for all `n < 10^7`
  (i.e. `k ≤ 7`), and a BFS check of all `n' < 10^9` with `ord_{n'}(10) ≤ 100`, found no
  counterexample; the closest calls are `q = 103` and `q = 139` (`n' = (10^34-1)/103`,
  `n' = (10^46-1)/139`), where exactly one such `t` exists and the least 0/1 multiple has
  exactly `9k` digits, the same length as `a(10^k - 1)`.  In the remaining (generic) regime
  `ord_{n'}(10) ≥ k + 8` the expected number of admissible `t` is at least `3.87^8`, so a
  counterexample is not expected; on the other hand no proof of Part 3 is known, and the
  razor-thin cases above show that any proof must control the decimal digits of `t/q` for
  all `q`.  Part 3 is therefore left as `sorry`.
-/

namespace A004290Aux

/-- digit sum in base 10 -/
def ds : ℕ → ℕ
  | 0 => 0
  | (n+1) => (n+1) % 10 + ds ((n+1) / 10)
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by norm_num)

lemma ds_zero : ds 0 = 0 := by simp [ds]

lemma ds_eq (n : ℕ) : ds n = n % 10 + ds (n / 10) := by
  cases n with
  | zero => simp [ds]
  | succ n => rw [ds]

lemma ds_lt (n : ℕ) (h : n < 10) : ds n = n := by
  rw [ds_eq, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, ds_zero]; simp

lemma ds_mul_add (a b : ℕ) (hb : b < 10) : ds (10 * a + b) = ds a + b := by
  rw [ds_eq]
  have h1 : (10 * a + b) % 10 = b := by omega
  have h2 : (10 * a + b) / 10 = a := by omega
  rw [h1, h2]; ring

lemma ds_digits_sum (n : ℕ) : (Nat.digits 10 n).sum = ds n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [ds_zero]
    · rw [Nat.digits_def' (by norm_num) h, List.sum_cons, ih (n / 10) (Nat.div_lt_self h (by norm_num)), ← ds_eq]

end A004290Aux

namespace A004290Aux

lemma ds_succ_le (n : ℕ) : ds (n + 1) ≤ ds n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge (n % 10) 9 with h | h
    · -- no carry
      have e1 : n + 1 = 10 * (n / 10) + (n % 10 + 1) := by omega
      have e2 : n = 10 * (n / 10) + n % 10 := by omega
      rw [e1, ds_mul_add _ _ (by omega)]
      conv_rhs => rw [e2, ds_mul_add _ _ (by omega)]
      omega
    · -- carry: n % 10 = 9
      have h9 : n % 10 = 9 := by omega
      have e1 : n + 1 = 10 * (n / 10 + 1) + 0 := by omega
      have e2 : n = 10 * (n / 10) + 9 := by omega
      rw [e1, ds_mul_add _ _ (by omega)]
      conv_rhs => rw [e2, ds_mul_add _ _ (by omega)]
      have := ih (n / 10) (by omega)
      omega

lemma ds_add_le (a b : ℕ) : ds (a + b) ≤ ds a + ds b := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0; simp [ds_zero]
    · -- write a = 10 a' + a0, b = 10 b' + b0
      have ea : a = 10 * (a / 10) + a % 10 := by omega
      have eb : b = 10 * (b / 10) + b % 10 := by omega
      rcases Nat.lt_or_ge (a % 10 + b % 10) 10 with hc | hc
      · have e : a + b = 10 * (a / 10 + b / 10) + (a % 10 + b % 10) := by omega
        rw [e, ds_mul_add _ _ hc]
        have := ih (a / 10) (by omega) (b / 10)
        conv_rhs => rw [ea, eb, ds_mul_add _ _ (by omega), ds_mul_add _ _ (by omega)]
        omega
      · have e : a + b = 10 * (a / 10 + b / 10 + 1) + (a % 10 + b % 10 - 10) := by omega
        rw [e, ds_mul_add _ _ (by omega)]
        have h1 := ih (a / 10) (by omega) (b / 10)
        have h2 := ds_succ_le (a / 10 + b / 10)
        conv_rhs => rw [ea, eb, ds_mul_add _ _ (by omega), ds_mul_add _ _ (by omega)]
        omega

lemma ds_mod_nine (n : ℕ) : ds n % 9 = n % 9 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [ds_zero]
    · rw [ds_eq]
      have := ih (n / 10) (Nat.div_lt_self hpos (by norm_num))
      omega

/-- splitting off the low `k` digits -/
lemma ds_add_pow_mul (k a b : ℕ) (ha : a < 10 ^ k) : ds (a + 10 ^ k * b) = ds a + ds b := by
  induction k generalizing a b with
  | zero =>
    simp at ha; subst ha; simp [ds_zero]
  | succ k ih =>
    -- a + 10^(k+1) b = 10 * (a/10 + 10^k b) + a%10
    have e : a + 10 ^ (k+1) * b = 10 * (a / 10 + 10 ^ k * b) + a % 10 := by
      rw [pow_succ, mul_comm (10 ^ k) 10, mul_assoc]; omega
    rw [e, ds_mul_add _ _ (by omega), ih (a / 10) b (by rw [pow_succ] at ha; omega)]
    conv_rhs => rw [show a = 10 * (a / 10) + a % 10 by omega, ds_mul_add _ _ (by omega)]
    omega

lemma ds_pow_sub_one (k : ℕ) : ds (10 ^ k - 1) = 9 * k := by
  induction k with
  | zero => simp [ds_zero]
  | succ k ih =>
    have e : 10 ^ (k+1) - 1 = 10 * (10 ^ k - 1) + 9 := by
      have : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
      rw [pow_succ]; omega
    rw [e, ds_mul_add _ _ (by norm_num), ih]; ring

end A004290Aux

namespace A004290Aux

/-- Key lemma: every positive multiple of `10^k - 1` has digit sum at least `9k`. -/
lemma ds_ge_of_dvd (k : ℕ) (hk : 0 < k) : ∀ N : ℕ, 0 < N → (10 ^ k - 1) ∣ N → 9 * k ≤ ds N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN hdvd
    have hpk : 10 ≤ 10 ^ k := by
      calc 10 = 10 ^ 1 := by norm_num
        _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    rcases Nat.lt_or_ge N (10 ^ k) with hlt | hge
    · -- N = 10^k - 1
      have h1 : 10 ^ k - 1 ≤ N := Nat.le_of_dvd hN hdvd
      obtain ⟨c, hc⟩ := hdvd
      have hc1 : c = 1 := by
        rcases c with _ | _ | c
        · omega
        · rfl
        · exfalso
          have : (10 ^ k - 1) * (c + 1 + 1) ≥ (10 ^ k - 1) * 2 := Nat.mul_le_mul_left _ (by omega)
          omega
      subst hc1
      rw [hc, mul_one, ds_pow_sub_one]
    · -- split N = a + 10^k * b
      set a := N % 10 ^ k with ha
      set b := N / 10 ^ k with hb
      have hN' : N = a + 10 ^ k * b := by rw [ha, hb]; exact (Nat.mod_add_div N (10 ^ k)).symm
      have hb1 : 1 ≤ b := by
        rw [hb]; exact (Nat.one_le_div_iff (by omega)).mpr hge
      have halt : a < 10 ^ k := Nat.mod_lt _ (by omega)
      have hS : (10 ^ k - 1) ∣ a + b := by
        have : a + b + (10 ^ k - 1) * b = N := by
          rw [hN']
          have : (10 ^ k - 1) * b = 10 ^ k * b - b := by
            rw [Nat.sub_mul, one_mul]
          rw [this]
          have : b ≤ 10 ^ k * b := Nat.le_mul_of_pos_left b (by omega)
          omega
        have hd : (10 ^ k - 1) ∣ (a + b + (10 ^ k - 1) * b) := this ▸ hdvd
        exact (Nat.dvd_add_left (Dvd.intro _ rfl)).mp hd
      have hSpos : 0 < a + b := by omega
      have hSlt : a + b < N := by
        rw [hN']
        have : b < 10 ^ k * b := by
          calc b = 1 * b := (one_mul b).symm
            _ < 10 ^ k * b := Nat.mul_lt_mul_of_pos_right (by omega) hb1
        omega
      have ih' := ih (a + b) hSlt hSpos hS
      calc 9 * k ≤ ds (a + b) := ih'
        _ ≤ ds a + ds b := ds_add_le a b
        _ = ds N := by rw [hN', ds_add_pow_mul k a b halt]

end A004290Aux

namespace A004290Aux

/-- repunit with `L` ones -/
def rep (L : ℕ) : ℕ := (10 ^ L - 1) / 9

lemma nine_dvd_pow_sub_one (L : ℕ) : 9 ∣ 10 ^ L - 1 := by
  have := Nat.sub_dvd_pow_sub_pow 10 1 L
  simpa using this

lemma nine_mul_rep (L : ℕ) : 9 * rep L = 10 ^ L - 1 := by
  unfold rep; exact Nat.mul_div_cancel' (nine_dvd_pow_sub_one L)

lemma rep_zero : rep 0 = 0 := by simp [rep]

lemma rep_succ (L : ℕ) : rep (L + 1) = 10 * rep L + 1 := by
  have h1 := nine_mul_rep L
  have h2 := nine_mul_rep (L + 1)
  have h3 : 1 ≤ 10 ^ L := Nat.one_le_pow _ _ (by norm_num)
  have : 9 * rep (L + 1) = 9 * (10 * rep L + 1) := by
    rw [h2, pow_succ]; omega
  omega

lemma rep_pos (L : ℕ) (hL : 0 < L) : 0 < rep L := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [rep_succ]; omega

lemma digits_rep (L : ℕ) : Nat.digits 10 (rep L) = List.replicate L 1 := by
  induction L with
  | zero => simp [rep_zero]
  | succ L ih =>
    rw [rep_succ, Nat.digits_def' (by norm_num) (by omega)]
    have h1 : (10 * rep L + 1) % 10 = 1 := by omega
    have h2 : (10 * rep L + 1) / 10 = rep L := by omega
    rw [h1, h2, ih, List.replicate_succ]

lemma rep_lt_pow (L : ℕ) : rep L < 10 ^ L := by
  have := nine_mul_rep L
  have : 1 ≤ 10 ^ L := Nat.one_le_pow _ _ (by norm_num)
  omega

lemma ds_rep (L : ℕ) : ds (rep L) = L := by
  rw [← ds_digits_sum, digits_rep]; simp

/-- `10^k - 1` divides the repunit with `9k` ones -/
lemma pow_sub_one_dvd_rep (k : ℕ) : (10 ^ k - 1) ∣ rep (9 * k) := by
  -- work in ℤ
  have h9 : (9 : ℤ) ∣ (10 : ℤ) ^ k - 1 := by
    have := nine_dvd_pow_sub_one k
    have h1 : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have : ((9 : ℕ) : ℤ) ∣ ((10 ^ k - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr this
    push_cast [h1] at this
    exact this
  -- key: 9 * (10^k - 1) ∣ 10^(9k) - 1
  have key : (9 * (10 ^ k - 1) : ℤ) ∣ (10 : ℤ) ^ (9 * k) - 1 := by
    set x : ℤ := 10 ^ k with hx
    have e : (10 : ℤ) ^ (9 * k) - 1 = (x - 1) * (x^8 + x^7 + x^6 + x^5 + x^4 + x^3 + x^2 + x + 1) := by
      rw [hx, mul_comm 9 k, pow_mul]; ring
    rw [e]
    have : (9 : ℤ) ∣ x^8 + x^7 + x^6 + x^5 + x^4 + x^3 + x^2 + x + 1 := by
      have e2 : x^8 + x^7 + x^6 + x^5 + x^4 + x^3 + x^2 + x + 1 =
        (x - 1) * (x^7 + 2*x^6 + 3*x^5 + 4*x^4 + 5*x^3 + 6*x^2 + 7*x + 8) + 9 := by ring
      rw [e2]
      exact dvd_add (Dvd.dvd.mul_right h9 _) (dvd_refl 9)
    obtain ⟨c, hc⟩ := this
    rw [hc]
    exact ⟨c, by ring⟩
  have h1 : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have h2 : 1 ≤ 10 ^ (9 * k) := Nat.one_le_pow _ _ (by norm_num)
  have key' : 9 * (10 ^ k - 1) ∣ 10 ^ (9 * k) - 1 := by
    have : ((9 * (10 ^ k - 1) : ℕ) : ℤ) ∣ ((10 ^ (9 * k) - 1 : ℕ) : ℤ) := by
      push_cast [h1, h2]; exact key
    exact Int.natCast_dvd_natCast.mp this
  rw [← nine_mul_rep (9 * k)] at key'
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) key'

end A004290Aux

namespace A004290Aux

lemma ofDigits_replicate_one (L : ℕ) : Nat.ofDigits 10 (List.replicate L 1) = rep L := by
  induction L with
  | zero => simp [rep_zero]
  | succ L ih => rw [List.replicate_succ, Nat.ofDigits_cons, ih, rep_succ]; ring

lemma all_one_of_sum (l : List ℕ) (h : ∀ x ∈ l, x ≤ 1) (hs : l.sum = l.length) : ∀ x ∈ l, x = 1 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : a ≤ 1 := h a (List.mem_cons_self ..)
    have ht : ∀ x ∈ t, x ≤ 1 := fun x hx => h x (List.mem_cons_of_mem a hx)
    have hsum : t.sum ≤ t.length := by
      have := List.sum_le_card_nsmul t 1 ht
      simpa using this
    simp only [List.sum_cons, List.length_cons] at hs
    have ha1 : a = 1 := by omega
    have hts : t.sum = t.length := by omega
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha1
    · exact ih ht hts x hx

lemma digits_pow_ten (k : ℕ) : Nat.digits 10 (10 ^ k) = List.replicate k 0 ++ [1] := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.digits_def' (by norm_num) (by positivity)]
    have h1 : 10 ^ (k+1) % 10 = 0 := by rw [pow_succ]; simp
    have h2 : 10 ^ (k+1) / 10 = 10 ^ k := by rw [pow_succ]; simp
    rw [h1, h2, ih, List.replicate_succ]; rfl

/-- Any `m ∈ S (10^k - 1)` is at least the repunit with `9k` ones. -/
lemma rep_le_of_mem (k : ℕ) (hk : 0 < k) (m : ℕ) (hm : 0 < m) (hdvd : (10 ^ k - 1) ∣ m)
    (hdig : ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1) : rep (9 * k) ≤ m := by
  set L := (Nat.digits 10 m).length with hL
  have hle1 : ∀ d ∈ Nat.digits 10 m, d ≤ 1 := fun d hd => by rcases hdig d hd with h | h <;> omega
  have hds : 9 * k ≤ ds m := ds_ge_of_dvd k hk m hm hdvd
  have hsum : (Nat.digits 10 m).sum ≤ L := by
    have := List.sum_le_card_nsmul (Nat.digits 10 m) 1 hle1
    simpa using this
  rw [← ds_digits_sum] at hds
  rcases Nat.lt_or_ge (9 * k) L with hlt | hge
  · -- L ≥ 9k+1, so m ≥ 10^(9k) > rep (9k)
    have h1 : 10 ^ L ≤ 10 * m := Nat.base_pow_length_digits_le 10 m (by norm_num) (by omega)
    have h2 : 10 ^ (9 * k + 1) ≤ 10 ^ L := Nat.pow_le_pow_right (by norm_num) hlt
    have h3 : 10 ^ (9 * k) < 10 ^ (9 * k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h4 := rep_lt_pow (9 * k)
    rw [pow_succ] at h2 h3
    omega
  · -- L = 9k and all digits are 1
    have hLe : L = 9 * k := by omega
    have hs : (Nat.digits 10 m).sum = (Nat.digits 10 m).length := by omega
    have hall := all_one_of_sum _ hle1 hs
    have hrep : Nat.digits 10 m = List.replicate (9 * k) 1 := by
      rw [List.eq_replicate_iff]; exact ⟨by omega, hall⟩
    have : m = rep (9 * k) := by
      rw [← Nat.ofDigits_digits 10 m, hrep, ofDigits_replicate_one]
    omega

end A004290Aux


namespace A004290Aux

theorem part1 (k : ℕ) : A004290 (10 ^ k) = 10 ^ k := by
  unfold A004290
  apply IsLeast.csInf_eq
  refine ⟨⟨by positivity, dvd_refl _, ?_⟩, ?_⟩
  · intro d hd
    rw [digits_pow_ten] at hd
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hd
    omega
  · rintro m ⟨hm, hdvd, -⟩
    exact Nat.le_of_dvd hm hdvd

theorem part2 (k : ℕ) (hk : k > 0) : A004290 (10 ^ k - 1) = (10 ^ (9 * k) - 1) / 9 := by
  unfold A004290
  show sInf _ = rep (9 * k)
  apply IsLeast.csInf_eq
  refine ⟨⟨rep_pos _ (by omega), pow_sub_one_dvd_rep k, ?_⟩, ?_⟩
  · intro d hd
    rw [digits_rep] at hd
    simp only [List.mem_replicate] at hd
    omega
  · rintro m ⟨hm, hdvd, hdig⟩
    exact rep_le_of_mem k hk m hm hdvd hdig

end A004290Aux

/--
Conjecture from A004290 by David Radcliffe:
a(10^k) = 10^k and a(10^k - 1) = (10^(9k) - 1) / 9 for all k.
Is a(n) < a(10^k - 1) for all n < 10^k - 1?
We formalize the second, unproven part. The first two parts are stated as assumptions
to establish the right-hand side of the inequality.
-/
theorem oeis_a004290_conjecture_radcliffe (k : ℕ) (hk : k > 0) :
  (A004290 (10 ^ k) = 10 ^ k) ∧
  (A004290 (10 ^ k - 1) = (10 ^ (9 * k) - 1) / 9) ∧
  (∀ n : ℕ, n < 10 ^ k - 1 → A004290 n < A004290 (10 ^ k - 1)) :=
by
  refine ⟨A004290Aux.part1 k, A004290Aux.part2 k hk, ?_⟩
  -- Part 3 (the open question).  See the discussion in `A004290Aux` above.
  sorry

theorem oeis_a004290_conjecture_radcliffe.disproof : ¬ (type_of% @oeis_a004290_conjecture_radcliffe) := sorry
