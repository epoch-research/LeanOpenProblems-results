import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0


open Nat BigOperators

/--
A303639: Number of ways to write $n$ as $a^2 + b^2 + \binom{2c+1}{c} + \binom{2d+1}{d}$,
where $a,b,c,d$ are nonnegative integers with $a \le b$ and $c \le d$.
-/
def a (n : ℕ) : ℕ :=
  -- Helper for the binomial coefficient term: B(k) = binomial(2*k+1, k)
  let B (k : ℕ) : ℕ := (2 * k + 1).choose k

  -- The maximum value for $a, b$ is $\lfloor \sqrt{n} \rfloor$.
  -- We use a safe upper bound for iteration. `n.sqrt + 1` is slightly more than needed, but safe.
  let R_sq := Finset.range (n.sqrt + 1)
  -- The maximum value for $c, d$ is when B(c) is not too large. Since B(0)=1, B(1)=3, B(2)=10,
  -- a rough upper bound for k is needed, n+1 is certainly safe but inefficient.
  -- A tighter bound is not strictly necessary for definition.
  -- Since $\binom{2k+1}{k} \approx 4^k / \sqrt{\pi k}$, we only need to iterate c and d up to around log_4(n).
  -- For formalization, we keep the provided `n+1` range or a slightly better one.
  let R_binom := Finset.range (n + 1)

  R_sq.sum fun a =>
    R_sq.sum fun b =>
      R_binom.sum fun c =>
        R_binom.sum fun d =>
          if a ≤ b ∧ c ≤ d ∧ a ^ 2 + b ^ 2 + B c + B d = n then 1 else 0

/-- The binomial term `choose (2*k+1) k` is monotone in `k`. -/
private lemma B_mono : Monotone (fun k : ℕ => (2 * k + 1).choose k) := by
  apply monotone_nat_of_le_succ
  intro k
  calc
    (2 * k + 1).choose k ≤ (2 * (k + 1) + 1).choose k := by
      apply Nat.choose_le_choose
      omega
    _ ≤ (2 * (k + 1) + 1).choose (k + 1) := by
      apply Nat.choose_le_succ_of_lt_half_left
      omega

private lemma B_large {k : ℕ} (hk : 16 ≤ k) :
    800322180 < (2 * k + 1).choose k := by
  calc
    800322180 < (33).choose 16 := by decide
    _ ≤ (2 * k + 1).choose k := B_mono hk

private lemma not_sq_add_sq_of_bad_prime {m p e : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 3) (hepos : 0 < e) (heodd : ¬ Even e)
    (hdiv : p ^ e ∣ m) (hnotdiv : ¬ p ^ (e + 1) ∣ m) :
    ¬ ∃ x y : ℕ, x ^ 2 + y ^ 2 = m := by
  intro h
  have hm0 : m ≠ 0 := by
    intro hm
    subst m
    exact hnotdiv (dvd_zero _)
  letI : Fact p.Prime := ⟨hp⟩
  have hp_dvd : p ∣ m := by
    have hp1 : p ^ 1 ∣ m := (pow_dvd_pow p hepos).trans hdiv
    simpa using hp1
  have hmem : p ∈ m.primeFactors := hp.mem_primeFactors hp_dvd hm0
  have hv_ge : e ≤ padicValNat p m := (padicValNat_dvd_iff_le hm0).1 hdiv
  have hv_lt : ¬ e + 1 ≤ padicValNat p m := by
    intro hv
    exact hnotdiv ((padicValNat_dvd_iff_le hm0).2 hv)
  have hodd : ¬ Even (padicValNat p m) := by
    have hv : padicValNat p m = e := by omega
    rw [hv]
    exact heodd
  have h' : ∃ x y : ℕ, m = x ^ 2 + y ^ 2 := by
    rcases h with ⟨x, y, hxy⟩
    exact ⟨x, y, hxy.symm⟩
  rw [Nat.eq_sq_add_sq_iff] at h'
  exact hodd (h' p hmem hp4)

private def Bsmall : Fin 16 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 10
  | ⟨3, _⟩ => 35
  | ⟨4, _⟩ => 126
  | ⟨5, _⟩ => 462
  | ⟨6, _⟩ => 1716
  | ⟨7, _⟩ => 6435
  | ⟨8, _⟩ => 24310
  | ⟨9, _⟩ => 92378
  | ⟨10, _⟩ => 352716
  | ⟨11, _⟩ => 1352078
  | ⟨12, _⟩ => 5200300
  | ⟨13, _⟩ => 20058300
  | ⟨14, _⟩ => 77558760
  | ⟨15, _⟩ => 300540195
  | ⟨_, _⟩ => 1

private lemma B_eq_Bsmall (k : Fin 16) : (2 * k.val + 1).choose k.val = Bsmall k := by
  fin_cases k <;> decide

private lemma cert_prime_647 : Nat.Prime 647 := by norm_num
private lemma cert_prime_163 : Nat.Prime 163 := by norm_num
private lemma cert_prime_67 : Nat.Prime 67 := by norm_num
private lemma cert_prime_3 : Nat.Prime 3 := by norm_num
private lemma cert_prime_23 : Nat.Prime 23 := by norm_num
private lemma cert_prime_467 : Nat.Prime 467 := by norm_num
private lemma cert_prime_223 : Nat.Prime 223 := by norm_num
private lemma cert_prime_991 : Nat.Prime 991 := by norm_num
private lemma cert_prime_7 : Nat.Prime 7 := by norm_num
private lemma cert_prime_887 : Nat.Prime 887 := by norm_num
private lemma cert_prime_26905651 : Nat.Prime 26905651 := by norm_num
private lemma cert_prime_1999 : Nat.Prime 1999 := by norm_num
private lemma cert_prime_643 : Nat.Prime 643 := by norm_num
private lemma cert_prime_19 : Nat.Prime 19 := by norm_num
private lemma cert_prime_78607 : Nat.Prime 78607 := by norm_num
private lemma cert_prime_27594131 : Nat.Prime 27594131 := by norm_num
private lemma cert_prime_31 : Nat.Prime 31 := by norm_num
private lemma cert_prime_11 : Nat.Prime 11 := by norm_num
private lemma cert_prime_200080511 : Nat.Prime 200080511 := by norm_num
private lemma cert_prime_284003 : Nat.Prime 284003 := by norm_num
private lemma cert_prime_4326031 : Nat.Prime 4326031 := by norm_num
private lemma cert_prime_399984727 : Nat.Prime 399984727 := by norm_num
private lemma cert_prime_79512187 : Nat.Prime 79512187 := by norm_num
private lemma cert_prime_127 : Nat.Prime 127 := by norm_num
private lemma cert_prime_2819 : Nat.Prime 2819 := by norm_num
private lemma cert_prime_43 : Nat.Prime 43 := by norm_num
private lemma cert_prime_5843 : Nat.Prime 5843 := by norm_num
private lemma cert_prime_7923067 : Nat.Prime 7923067 := by norm_num
private lemma cert_prime_719 : Nat.Prime 719 := by norm_num
private lemma cert_prime_563 : Nat.Prime 563 := by norm_num
private lemma cert_prime_200057419 : Nat.Prime 200057419 := by norm_num
private lemma cert_prime_12504647 : Nat.Prime 12504647 := by norm_num
private lemma cert_prime_139 : Nat.Prime 139 := by norm_num
private lemma cert_prime_227 : Nat.Prime 227 := by norm_num
private lemma cert_prime_199 : Nat.Prime 199 := by norm_num
private lemma cert_prime_3331 : Nat.Prime 3331 := by norm_num
private lemma cert_prime_689891 : Nat.Prime 689891 := by norm_num
private lemma cert_prime_59 : Nat.Prime 59 := by norm_num
private lemma cert_prime_7591 : Nat.Prime 7591 := by norm_num
private lemma cert_prime_19990307 : Nat.Prime 19990307 := by norm_num

private lemma no_sq_cert_0_0 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322178 :=
  not_sq_add_sq_of_bad_prime (p := 647) (e := 1) cert_prime_647
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_0_1 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322176 :=
  not_sq_add_sq_of_bad_prime (p := 163) (e := 1) cert_prime_163
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_0_2 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322169 :=
  not_sq_add_sq_of_bad_prime (p := 67) (e := 1) cert_prime_67
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_0_3 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322144 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_0_4 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322053 :=
  not_sq_add_sq_of_bad_prime (p := 23) (e := 1) cert_prime_23
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_0_5 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800321717 :=
  not_sq_add_sq_of_bad_prime (p := 467) (e := 1) cert_prime_467
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_0_6 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800320463 :=
  not_sq_add_sq_of_bad_prime (p := 223) (e := 1) cert_prime_223
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_0_7 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800315744 :=
  not_sq_add_sq_of_bad_prime (p := 991) (e := 1) cert_prime_991
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_0_8 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800297869 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_0_9 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800229801 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_0_10 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799969463 :=
  not_sq_add_sq_of_bad_prime (p := 23) (e := 1) cert_prime_23
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_0_11 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798970101 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_0_12 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795121879 :=
  not_sq_add_sq_of_bad_prime (p := 887) (e := 1) cert_prime_887
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_0_13 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780263879 :=
  not_sq_add_sq_of_bad_prime (p := 26905651) (e := 1) cert_prime_26905651
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_0_14 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722763419 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_0_15 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499781984 :=
  not_sq_add_sq_of_bad_prime (p := 1999) (e := 1) cert_prime_1999
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_1_0 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322176 :=
  not_sq_add_sq_of_bad_prime (p := 163) (e := 1) cert_prime_163
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_1_1 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322174 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 3) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_1_2 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322167 :=
  not_sq_add_sq_of_bad_prime (p := 643) (e := 1) cert_prime_643
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_1_3 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322142 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_1_4 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322051 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_1_5 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800321715 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 7) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_1_6 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800320461 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_1_7 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800315742 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_1_8 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800297867 :=
  not_sq_add_sq_of_bad_prime (p := 78607) (e := 1) cert_prime_78607
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_1_9 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800229799 :=
  not_sq_add_sq_of_bad_prime (p := 27594131) (e := 1) cert_prime_27594131
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_1_10 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799969461 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_1_11 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798970099 :=
  not_sq_add_sq_of_bad_prime (p := 31) (e := 1) cert_prime_31
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_1_12 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795121877 :=
  not_sq_add_sq_of_bad_prime (p := 11) (e := 1) cert_prime_11
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_1_13 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780263877 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_1_14 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722763417 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_1_15 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499781982 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_2_0 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322169 :=
  not_sq_add_sq_of_bad_prime (p := 67) (e := 1) cert_prime_67
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_2_1 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322167 :=
  not_sq_add_sq_of_bad_prime (p := 643) (e := 1) cert_prime_643
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_2_2 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322160 :=
  not_sq_add_sq_of_bad_prime (p := 11) (e := 1) cert_prime_11
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_2_3 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322135 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_2_4 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322044 :=
  not_sq_add_sq_of_bad_prime (p := 200080511) (e := 1) cert_prime_200080511
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_2_5 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800321708 :=
  not_sq_add_sq_of_bad_prime (p := 23) (e := 1) cert_prime_23
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_2_6 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800320454 :=
  not_sq_add_sq_of_bad_prime (p := 284003) (e := 1) cert_prime_284003
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_2_7 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800315735 :=
  not_sq_add_sq_of_bad_prime (p := 4326031) (e := 1) cert_prime_4326031
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_2_8 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800297860 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_2_9 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800229792 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_2_10 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799969454 :=
  not_sq_add_sq_of_bad_prime (p := 399984727) (e := 1) cert_prime_399984727
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_2_11 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798970092 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_2_12 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795121870 :=
  not_sq_add_sq_of_bad_prime (p := 79512187) (e := 1) cert_prime_79512187
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_2_13 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780263870 :=
  not_sq_add_sq_of_bad_prime (p := 127) (e := 1) cert_prime_127
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_2_14 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722763410 :=
  not_sq_add_sq_of_bad_prime (p := 2819) (e := 1) cert_prime_2819
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_2_15 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499781975 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_3_0 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322144 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_3_1 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322142 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_3_2 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322135 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_3_3 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322110 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_3_4 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322019 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_3_5 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800321683 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_3_6 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800320429 :=
  not_sq_add_sq_of_bad_prime (p := 43) (e := 1) cert_prime_43
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_3_7 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800315710 :=
  not_sq_add_sq_of_bad_prime (p := 5843) (e := 1) cert_prime_5843
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_3_8 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800297835 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_3_9 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800229767 :=
  not_sq_add_sq_of_bad_prime (p := 7923067) (e := 1) cert_prime_7923067
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_3_10 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799969429 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_3_11 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798970067 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_3_12 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795121845 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_3_13 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780263845 :=
  not_sq_add_sq_of_bad_prime (p := 23) (e := 1) cert_prime_23
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_3_14 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722763385 :=
  not_sq_add_sq_of_bad_prime (p := 23) (e := 1) cert_prime_23
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_3_15 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499781950 :=
  not_sq_add_sq_of_bad_prime (p := 23) (e := 1) cert_prime_23
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_4_0 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322053 :=
  not_sq_add_sq_of_bad_prime (p := 23) (e := 1) cert_prime_23
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_4_1 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322051 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_4_2 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322044 :=
  not_sq_add_sq_of_bad_prime (p := 200080511) (e := 1) cert_prime_200080511
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_4_3 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322019 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_4_4 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800321928 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_4_5 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800321592 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_4_6 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800320338 :=
  not_sq_add_sq_of_bad_prime (p := 719) (e := 1) cert_prime_719
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_4_7 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800315619 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_4_8 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800297744 :=
  not_sq_add_sq_of_bad_prime (p := 563) (e := 1) cert_prime_563
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_4_9 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800229676 :=
  not_sq_add_sq_of_bad_prime (p := 200057419) (e := 1) cert_prime_200057419
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_4_10 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799969338 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 3) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_4_11 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798969976 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_4_12 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795121754 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_4_13 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780263754 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_4_14 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722763294 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_4_15 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499781859 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_5_0 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800321717 :=
  not_sq_add_sq_of_bad_prime (p := 467) (e := 1) cert_prime_467
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_5_1 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800321715 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 7) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_5_2 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800321708 :=
  not_sq_add_sq_of_bad_prime (p := 23) (e := 1) cert_prime_23
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_5_3 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800321683 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_5_4 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800321592 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_5_5 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800321256 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 3) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_5_6 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800320002 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_5_7 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800315283 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_5_8 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800297408 :=
  not_sq_add_sq_of_bad_prime (p := 12504647) (e := 1) cert_prime_12504647
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_5_9 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800229340 :=
  not_sq_add_sq_of_bad_prime (p := 23) (e := 1) cert_prime_23
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_5_10 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799969002 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_5_11 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798969640 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_5_12 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795121418 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_5_13 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780263418 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_5_14 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722762958 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_5_15 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499781523 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_6_0 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800320463 :=
  not_sq_add_sq_of_bad_prime (p := 223) (e := 1) cert_prime_223
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_6_1 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800320461 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_6_2 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800320454 :=
  not_sq_add_sq_of_bad_prime (p := 284003) (e := 1) cert_prime_284003
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_6_3 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800320429 :=
  not_sq_add_sq_of_bad_prime (p := 43) (e := 1) cert_prime_43
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_6_4 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800320338 :=
  not_sq_add_sq_of_bad_prime (p := 719) (e := 1) cert_prime_719
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_6_5 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800320002 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_6_6 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800318748 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_6_7 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800314029 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_6_8 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800296154 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_6_9 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800228086 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_6_10 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799967748 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_6_11 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798968386 :=
  not_sq_add_sq_of_bad_prime (p := 139) (e := 1) cert_prime_139
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_6_12 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795120164 :=
  not_sq_add_sq_of_bad_prime (p := 227) (e := 1) cert_prime_227
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_6_13 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780262164 :=
  not_sq_add_sq_of_bad_prime (p := 11) (e := 1) cert_prime_11
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_6_14 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722761704 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 5) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_6_15 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499780269 :=
  not_sq_add_sq_of_bad_prime (p := 67) (e := 1) cert_prime_67
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_7_0 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800315744 :=
  not_sq_add_sq_of_bad_prime (p := 991) (e := 1) cert_prime_991
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_7_1 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800315742 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_7_2 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800315735 :=
  not_sq_add_sq_of_bad_prime (p := 4326031) (e := 1) cert_prime_4326031
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_7_3 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800315710 :=
  not_sq_add_sq_of_bad_prime (p := 5843) (e := 1) cert_prime_5843
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_7_4 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800315619 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_7_5 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800315283 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_7_6 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800314029 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_7_7 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800309310 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_7_8 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800291435 :=
  not_sq_add_sq_of_bad_prime (p := 199) (e := 1) cert_prime_199
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_7_9 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800223367 :=
  not_sq_add_sq_of_bad_prime (p := 31) (e := 1) cert_prime_31
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_7_10 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799963029 :=
  not_sq_add_sq_of_bad_prime (p := 31) (e := 1) cert_prime_31
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_7_11 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798963667 :=
  not_sq_add_sq_of_bad_prime (p := 3331) (e := 1) cert_prime_3331
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_7_12 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795115445 :=
  not_sq_add_sq_of_bad_prime (p := 139) (e := 1) cert_prime_139
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_7_13 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780257445 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_7_14 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722756985 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_7_15 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499775550 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_8_0 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800297869 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_8_1 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800297867 :=
  not_sq_add_sq_of_bad_prime (p := 78607) (e := 1) cert_prime_78607
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_8_2 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800297860 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_8_3 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800297835 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_8_4 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800297744 :=
  not_sq_add_sq_of_bad_prime (p := 563) (e := 1) cert_prime_563
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_8_5 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800297408 :=
  not_sq_add_sq_of_bad_prime (p := 12504647) (e := 1) cert_prime_12504647
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_8_6 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800296154 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_8_7 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800291435 :=
  not_sq_add_sq_of_bad_prime (p := 199) (e := 1) cert_prime_199
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_8_8 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800273560 :=
  not_sq_add_sq_of_bad_prime (p := 689891) (e := 1) cert_prime_689891
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_8_9 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800205492 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_8_10 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799945154 :=
  not_sq_add_sq_of_bad_prime (p := 223) (e := 1) cert_prime_223
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_8_11 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798945792 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_8_12 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795097570 :=
  not_sq_add_sq_of_bad_prime (p := 59) (e := 1) cert_prime_59
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_8_13 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780239570 :=
  not_sq_add_sq_of_bad_prime (p := 11) (e := 1) cert_prime_11
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_8_14 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722739110 :=
  not_sq_add_sq_of_bad_prime (p := 7591) (e := 1) cert_prime_7591
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_8_15 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499757675 :=
  not_sq_add_sq_of_bad_prime (p := 19990307) (e := 1) cert_prime_19990307
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_9_0 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800229801 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_9_1 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800229799 :=
  not_sq_add_sq_of_bad_prime (p := 27594131) (e := 1) cert_prime_27594131
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_9_2 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800229792 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_9_3 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800229767 :=
  not_sq_add_sq_of_bad_prime (p := 7923067) (e := 1) cert_prime_7923067
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_9_4 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800229676 :=
  not_sq_add_sq_of_bad_prime (p := 200057419) (e := 1) cert_prime_200057419
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_9_5 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800229340 :=
  not_sq_add_sq_of_bad_prime (p := 23) (e := 1) cert_prime_23
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_9_6 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800228086 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_9_7 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800223367 :=
  not_sq_add_sq_of_bad_prime (p := 31) (e := 1) cert_prime_31
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_9_8 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800205492 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_9_9 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800137424 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_9_10 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799877086 :=
  not_sq_add_sq_of_bad_prime (p := 887) (e := 1) cert_prime_887
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_9_11 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798877724 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_9_12 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795029502 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_9_13 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780171502 :=
  not_sq_add_sq_of_bad_prime (p := 11) (e := 1) cert_prime_11
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_9_14 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722671042 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_9_15 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499689607 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_10_0 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799969463 :=
  not_sq_add_sq_of_bad_prime (p := 23) (e := 1) cert_prime_23
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_10_1 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799969461 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_10_2 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799969454 :=
  not_sq_add_sq_of_bad_prime (p := 399984727) (e := 1) cert_prime_399984727
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_10_3 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799969429 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_10_4 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799969338 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 3) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_10_5 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799969002 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_10_6 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799967748 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_10_7 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799963029 :=
  not_sq_add_sq_of_bad_prime (p := 31) (e := 1) cert_prime_31
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_10_8 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799945154 :=
  not_sq_add_sq_of_bad_prime (p := 223) (e := 1) cert_prime_223
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_10_9 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799877086 :=
  not_sq_add_sq_of_bad_prime (p := 887) (e := 1) cert_prime_887
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_10_10 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 799616748 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_10_11 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798617386 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_10_12 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 794769164 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_10_13 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 779911164 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_10_14 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722410704 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 3) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_10_15 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499429269 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_11_0 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798970101 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_11_1 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798970099 :=
  not_sq_add_sq_of_bad_prime (p := 31) (e := 1) cert_prime_31
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_11_2 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798970092 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_11_3 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798970067 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_11_4 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798969976 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_11_5 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798969640 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_11_6 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798968386 :=
  not_sq_add_sq_of_bad_prime (p := 139) (e := 1) cert_prime_139
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_11_7 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798963667 :=
  not_sq_add_sq_of_bad_prime (p := 3331) (e := 1) cert_prime_3331
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_11_8 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798945792 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_11_9 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798877724 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_11_10 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 798617386 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_11_11 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 797618024 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_11_12 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 793769802 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_11_13 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 778911802 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_11_14 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 721411342 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_11_15 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 498429907 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_12_0 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795121879 :=
  not_sq_add_sq_of_bad_prime (p := 887) (e := 1) cert_prime_887
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_12_1 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795121877 :=
  not_sq_add_sq_of_bad_prime (p := 11) (e := 1) cert_prime_11
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_12_2 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795121870 :=
  not_sq_add_sq_of_bad_prime (p := 79512187) (e := 1) cert_prime_79512187
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_12_3 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795121845 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_12_4 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795121754 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_12_5 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795121418 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_12_6 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795120164 :=
  not_sq_add_sq_of_bad_prime (p := 227) (e := 1) cert_prime_227
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_12_7 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795115445 :=
  not_sq_add_sq_of_bad_prime (p := 139) (e := 1) cert_prime_139
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_12_8 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795097570 :=
  not_sq_add_sq_of_bad_prime (p := 59) (e := 1) cert_prime_59
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_12_9 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 795029502 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_12_10 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 794769164 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_12_11 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 793769802 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_12_12 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 789921580 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_12_13 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 775063580 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_12_14 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 717563120 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_12_15 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 494581685 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_13_0 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780263879 :=
  not_sq_add_sq_of_bad_prime (p := 26905651) (e := 1) cert_prime_26905651
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_13_1 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780263877 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_13_2 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780263870 :=
  not_sq_add_sq_of_bad_prime (p := 127) (e := 1) cert_prime_127
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_13_3 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780263845 :=
  not_sq_add_sq_of_bad_prime (p := 23) (e := 1) cert_prime_23
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_13_4 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780263754 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_13_5 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780263418 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_13_6 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780262164 :=
  not_sq_add_sq_of_bad_prime (p := 11) (e := 1) cert_prime_11
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_13_7 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780257445 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_13_8 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780239570 :=
  not_sq_add_sq_of_bad_prime (p := 11) (e := 1) cert_prime_11
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_13_9 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 780171502 :=
  not_sq_add_sq_of_bad_prime (p := 11) (e := 1) cert_prime_11
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_13_10 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 779911164 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_13_11 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 778911802 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_13_12 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 775063580 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_13_13 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 760205580 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_13_14 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 702705120 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_13_15 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 479723685 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_14_0 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722763419 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_14_1 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722763417 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_14_2 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722763410 :=
  not_sq_add_sq_of_bad_prime (p := 2819) (e := 1) cert_prime_2819
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_14_3 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722763385 :=
  not_sq_add_sq_of_bad_prime (p := 23) (e := 1) cert_prime_23
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_14_4 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722763294 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_14_5 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722762958 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_14_6 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722761704 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 5) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_14_7 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722756985 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_14_8 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722739110 :=
  not_sq_add_sq_of_bad_prime (p := 7591) (e := 1) cert_prime_7591
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_14_9 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722671042 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_14_10 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 722410704 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 3) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_14_11 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 721411342 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_14_12 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 717563120 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_14_13 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 702705120 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_14_14 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 645204660 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_14_15 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 422223225 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_15_0 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499781984 :=
  not_sq_add_sq_of_bad_prime (p := 1999) (e := 1) cert_prime_1999
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_15_1 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499781982 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_15_2 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499781975 :=
  not_sq_add_sq_of_bad_prime (p := 7) (e := 1) cert_prime_7
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_15_3 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499781950 :=
  not_sq_add_sq_of_bad_prime (p := 23) (e := 1) cert_prime_23
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_15_4 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499781859 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_15_5 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499781523 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_15_6 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499780269 :=
  not_sq_add_sq_of_bad_prime (p := 67) (e := 1) cert_prime_67
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_15_7 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499775550 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_15_8 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499757675 :=
  not_sq_add_sq_of_bad_prime (p := 19990307) (e := 1) cert_prime_19990307
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_15_9 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499689607 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_15_10 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 499429269 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_15_11 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 498429907 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_15_12 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 494581685 :=
  not_sq_add_sq_of_bad_prime (p := 19) (e := 1) cert_prime_19
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_15_13 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 479723685 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_15_14 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 422223225 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)
private lemma no_sq_cert_15_15 : ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 199241790 :=
  not_sq_add_sq_of_bad_prime (p := 3) (e := 1) cert_prime_3
    (by decide) (by decide) (by decide) (by decide) (by decide)

private lemma no_sq_fin_row_0 (d : Fin 16) :
    ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322180 - (Bsmall ⟨0, by norm_num⟩ + Bsmall d) := by
  fin_cases d <;> simp [Bsmall]
  · simpa [Bsmall] using no_sq_cert_0_0
  · simpa [Bsmall] using no_sq_cert_0_1
  · simpa [Bsmall] using no_sq_cert_0_2
  · simpa [Bsmall] using no_sq_cert_0_3
  · simpa [Bsmall] using no_sq_cert_0_4
  · simpa [Bsmall] using no_sq_cert_0_5
  · simpa [Bsmall] using no_sq_cert_0_6
  · simpa [Bsmall] using no_sq_cert_0_7
  · simpa [Bsmall] using no_sq_cert_0_8
  · simpa [Bsmall] using no_sq_cert_0_9
  · simpa [Bsmall] using no_sq_cert_0_10
  · simpa [Bsmall] using no_sq_cert_0_11
  · simpa [Bsmall] using no_sq_cert_0_12
  · simpa [Bsmall] using no_sq_cert_0_13
  · simpa [Bsmall] using no_sq_cert_0_14
  · simpa [Bsmall] using no_sq_cert_0_15
private lemma no_sq_fin_row_1 (d : Fin 16) :
    ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322180 - (Bsmall ⟨1, by norm_num⟩ + Bsmall d) := by
  fin_cases d <;> simp [Bsmall]
  · simpa [Bsmall] using no_sq_cert_1_0
  · simpa [Bsmall] using no_sq_cert_1_1
  · simpa [Bsmall] using no_sq_cert_1_2
  · simpa [Bsmall] using no_sq_cert_1_3
  · simpa [Bsmall] using no_sq_cert_1_4
  · simpa [Bsmall] using no_sq_cert_1_5
  · simpa [Bsmall] using no_sq_cert_1_6
  · simpa [Bsmall] using no_sq_cert_1_7
  · simpa [Bsmall] using no_sq_cert_1_8
  · simpa [Bsmall] using no_sq_cert_1_9
  · simpa [Bsmall] using no_sq_cert_1_10
  · simpa [Bsmall] using no_sq_cert_1_11
  · simpa [Bsmall] using no_sq_cert_1_12
  · simpa [Bsmall] using no_sq_cert_1_13
  · simpa [Bsmall] using no_sq_cert_1_14
  · simpa [Bsmall] using no_sq_cert_1_15
private lemma no_sq_fin_row_2 (d : Fin 16) :
    ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322180 - (Bsmall ⟨2, by norm_num⟩ + Bsmall d) := by
  fin_cases d <;> simp [Bsmall]
  · simpa [Bsmall] using no_sq_cert_2_0
  · simpa [Bsmall] using no_sq_cert_2_1
  · simpa [Bsmall] using no_sq_cert_2_2
  · simpa [Bsmall] using no_sq_cert_2_3
  · simpa [Bsmall] using no_sq_cert_2_4
  · simpa [Bsmall] using no_sq_cert_2_5
  · simpa [Bsmall] using no_sq_cert_2_6
  · simpa [Bsmall] using no_sq_cert_2_7
  · simpa [Bsmall] using no_sq_cert_2_8
  · simpa [Bsmall] using no_sq_cert_2_9
  · simpa [Bsmall] using no_sq_cert_2_10
  · simpa [Bsmall] using no_sq_cert_2_11
  · simpa [Bsmall] using no_sq_cert_2_12
  · simpa [Bsmall] using no_sq_cert_2_13
  · simpa [Bsmall] using no_sq_cert_2_14
  · simpa [Bsmall] using no_sq_cert_2_15
private lemma no_sq_fin_row_3 (d : Fin 16) :
    ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322180 - (Bsmall ⟨3, by norm_num⟩ + Bsmall d) := by
  fin_cases d <;> simp [Bsmall]
  · simpa [Bsmall] using no_sq_cert_3_0
  · simpa [Bsmall] using no_sq_cert_3_1
  · simpa [Bsmall] using no_sq_cert_3_2
  · simpa [Bsmall] using no_sq_cert_3_3
  · simpa [Bsmall] using no_sq_cert_3_4
  · simpa [Bsmall] using no_sq_cert_3_5
  · simpa [Bsmall] using no_sq_cert_3_6
  · simpa [Bsmall] using no_sq_cert_3_7
  · simpa [Bsmall] using no_sq_cert_3_8
  · simpa [Bsmall] using no_sq_cert_3_9
  · simpa [Bsmall] using no_sq_cert_3_10
  · simpa [Bsmall] using no_sq_cert_3_11
  · simpa [Bsmall] using no_sq_cert_3_12
  · simpa [Bsmall] using no_sq_cert_3_13
  · simpa [Bsmall] using no_sq_cert_3_14
  · simpa [Bsmall] using no_sq_cert_3_15
private lemma no_sq_fin_row_4 (d : Fin 16) :
    ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322180 - (Bsmall ⟨4, by norm_num⟩ + Bsmall d) := by
  fin_cases d <;> simp [Bsmall]
  · simpa [Bsmall] using no_sq_cert_4_0
  · simpa [Bsmall] using no_sq_cert_4_1
  · simpa [Bsmall] using no_sq_cert_4_2
  · simpa [Bsmall] using no_sq_cert_4_3
  · simpa [Bsmall] using no_sq_cert_4_4
  · simpa [Bsmall] using no_sq_cert_4_5
  · simpa [Bsmall] using no_sq_cert_4_6
  · simpa [Bsmall] using no_sq_cert_4_7
  · simpa [Bsmall] using no_sq_cert_4_8
  · simpa [Bsmall] using no_sq_cert_4_9
  · simpa [Bsmall] using no_sq_cert_4_10
  · simpa [Bsmall] using no_sq_cert_4_11
  · simpa [Bsmall] using no_sq_cert_4_12
  · simpa [Bsmall] using no_sq_cert_4_13
  · simpa [Bsmall] using no_sq_cert_4_14
  · simpa [Bsmall] using no_sq_cert_4_15
private lemma no_sq_fin_row_5 (d : Fin 16) :
    ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322180 - (Bsmall ⟨5, by norm_num⟩ + Bsmall d) := by
  fin_cases d <;> simp [Bsmall]
  · simpa [Bsmall] using no_sq_cert_5_0
  · simpa [Bsmall] using no_sq_cert_5_1
  · simpa [Bsmall] using no_sq_cert_5_2
  · simpa [Bsmall] using no_sq_cert_5_3
  · simpa [Bsmall] using no_sq_cert_5_4
  · simpa [Bsmall] using no_sq_cert_5_5
  · simpa [Bsmall] using no_sq_cert_5_6
  · simpa [Bsmall] using no_sq_cert_5_7
  · simpa [Bsmall] using no_sq_cert_5_8
  · simpa [Bsmall] using no_sq_cert_5_9
  · simpa [Bsmall] using no_sq_cert_5_10
  · simpa [Bsmall] using no_sq_cert_5_11
  · simpa [Bsmall] using no_sq_cert_5_12
  · simpa [Bsmall] using no_sq_cert_5_13
  · simpa [Bsmall] using no_sq_cert_5_14
  · simpa [Bsmall] using no_sq_cert_5_15
private lemma no_sq_fin_row_6 (d : Fin 16) :
    ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322180 - (Bsmall ⟨6, by norm_num⟩ + Bsmall d) := by
  fin_cases d <;> simp [Bsmall]
  · simpa [Bsmall] using no_sq_cert_6_0
  · simpa [Bsmall] using no_sq_cert_6_1
  · simpa [Bsmall] using no_sq_cert_6_2
  · simpa [Bsmall] using no_sq_cert_6_3
  · simpa [Bsmall] using no_sq_cert_6_4
  · simpa [Bsmall] using no_sq_cert_6_5
  · simpa [Bsmall] using no_sq_cert_6_6
  · simpa [Bsmall] using no_sq_cert_6_7
  · simpa [Bsmall] using no_sq_cert_6_8
  · simpa [Bsmall] using no_sq_cert_6_9
  · simpa [Bsmall] using no_sq_cert_6_10
  · simpa [Bsmall] using no_sq_cert_6_11
  · simpa [Bsmall] using no_sq_cert_6_12
  · simpa [Bsmall] using no_sq_cert_6_13
  · simpa [Bsmall] using no_sq_cert_6_14
  · simpa [Bsmall] using no_sq_cert_6_15
private lemma no_sq_fin_row_7 (d : Fin 16) :
    ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322180 - (Bsmall ⟨7, by norm_num⟩ + Bsmall d) := by
  fin_cases d <;> simp [Bsmall]
  · simpa [Bsmall] using no_sq_cert_7_0
  · simpa [Bsmall] using no_sq_cert_7_1
  · simpa [Bsmall] using no_sq_cert_7_2
  · simpa [Bsmall] using no_sq_cert_7_3
  · simpa [Bsmall] using no_sq_cert_7_4
  · simpa [Bsmall] using no_sq_cert_7_5
  · simpa [Bsmall] using no_sq_cert_7_6
  · simpa [Bsmall] using no_sq_cert_7_7
  · simpa [Bsmall] using no_sq_cert_7_8
  · simpa [Bsmall] using no_sq_cert_7_9
  · simpa [Bsmall] using no_sq_cert_7_10
  · simpa [Bsmall] using no_sq_cert_7_11
  · simpa [Bsmall] using no_sq_cert_7_12
  · simpa [Bsmall] using no_sq_cert_7_13
  · simpa [Bsmall] using no_sq_cert_7_14
  · simpa [Bsmall] using no_sq_cert_7_15
private lemma no_sq_fin_row_8 (d : Fin 16) :
    ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322180 - (Bsmall ⟨8, by norm_num⟩ + Bsmall d) := by
  fin_cases d <;> simp [Bsmall]
  · simpa [Bsmall] using no_sq_cert_8_0
  · simpa [Bsmall] using no_sq_cert_8_1
  · simpa [Bsmall] using no_sq_cert_8_2
  · simpa [Bsmall] using no_sq_cert_8_3
  · simpa [Bsmall] using no_sq_cert_8_4
  · simpa [Bsmall] using no_sq_cert_8_5
  · simpa [Bsmall] using no_sq_cert_8_6
  · simpa [Bsmall] using no_sq_cert_8_7
  · simpa [Bsmall] using no_sq_cert_8_8
  · simpa [Bsmall] using no_sq_cert_8_9
  · simpa [Bsmall] using no_sq_cert_8_10
  · simpa [Bsmall] using no_sq_cert_8_11
  · simpa [Bsmall] using no_sq_cert_8_12
  · simpa [Bsmall] using no_sq_cert_8_13
  · simpa [Bsmall] using no_sq_cert_8_14
  · simpa [Bsmall] using no_sq_cert_8_15
private lemma no_sq_fin_row_9 (d : Fin 16) :
    ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322180 - (Bsmall ⟨9, by norm_num⟩ + Bsmall d) := by
  fin_cases d <;> simp [Bsmall]
  · simpa [Bsmall] using no_sq_cert_9_0
  · simpa [Bsmall] using no_sq_cert_9_1
  · simpa [Bsmall] using no_sq_cert_9_2
  · simpa [Bsmall] using no_sq_cert_9_3
  · simpa [Bsmall] using no_sq_cert_9_4
  · simpa [Bsmall] using no_sq_cert_9_5
  · simpa [Bsmall] using no_sq_cert_9_6
  · simpa [Bsmall] using no_sq_cert_9_7
  · simpa [Bsmall] using no_sq_cert_9_8
  · simpa [Bsmall] using no_sq_cert_9_9
  · simpa [Bsmall] using no_sq_cert_9_10
  · simpa [Bsmall] using no_sq_cert_9_11
  · simpa [Bsmall] using no_sq_cert_9_12
  · simpa [Bsmall] using no_sq_cert_9_13
  · simpa [Bsmall] using no_sq_cert_9_14
  · simpa [Bsmall] using no_sq_cert_9_15
private lemma no_sq_fin_row_10 (d : Fin 16) :
    ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322180 - (Bsmall ⟨10, by norm_num⟩ + Bsmall d) := by
  fin_cases d <;> simp [Bsmall]
  · simpa [Bsmall] using no_sq_cert_10_0
  · simpa [Bsmall] using no_sq_cert_10_1
  · simpa [Bsmall] using no_sq_cert_10_2
  · simpa [Bsmall] using no_sq_cert_10_3
  · simpa [Bsmall] using no_sq_cert_10_4
  · simpa [Bsmall] using no_sq_cert_10_5
  · simpa [Bsmall] using no_sq_cert_10_6
  · simpa [Bsmall] using no_sq_cert_10_7
  · simpa [Bsmall] using no_sq_cert_10_8
  · simpa [Bsmall] using no_sq_cert_10_9
  · simpa [Bsmall] using no_sq_cert_10_10
  · simpa [Bsmall] using no_sq_cert_10_11
  · simpa [Bsmall] using no_sq_cert_10_12
  · simpa [Bsmall] using no_sq_cert_10_13
  · simpa [Bsmall] using no_sq_cert_10_14
  · simpa [Bsmall] using no_sq_cert_10_15
private lemma no_sq_fin_row_11 (d : Fin 16) :
    ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322180 - (Bsmall ⟨11, by norm_num⟩ + Bsmall d) := by
  fin_cases d <;> simp [Bsmall]
  · simpa [Bsmall] using no_sq_cert_11_0
  · simpa [Bsmall] using no_sq_cert_11_1
  · simpa [Bsmall] using no_sq_cert_11_2
  · simpa [Bsmall] using no_sq_cert_11_3
  · simpa [Bsmall] using no_sq_cert_11_4
  · simpa [Bsmall] using no_sq_cert_11_5
  · simpa [Bsmall] using no_sq_cert_11_6
  · simpa [Bsmall] using no_sq_cert_11_7
  · simpa [Bsmall] using no_sq_cert_11_8
  · simpa [Bsmall] using no_sq_cert_11_9
  · simpa [Bsmall] using no_sq_cert_11_10
  · simpa [Bsmall] using no_sq_cert_11_11
  · simpa [Bsmall] using no_sq_cert_11_12
  · simpa [Bsmall] using no_sq_cert_11_13
  · simpa [Bsmall] using no_sq_cert_11_14
  · simpa [Bsmall] using no_sq_cert_11_15
private lemma no_sq_fin_row_12 (d : Fin 16) :
    ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322180 - (Bsmall ⟨12, by norm_num⟩ + Bsmall d) := by
  fin_cases d <;> simp [Bsmall]
  · simpa [Bsmall] using no_sq_cert_12_0
  · simpa [Bsmall] using no_sq_cert_12_1
  · simpa [Bsmall] using no_sq_cert_12_2
  · simpa [Bsmall] using no_sq_cert_12_3
  · simpa [Bsmall] using no_sq_cert_12_4
  · simpa [Bsmall] using no_sq_cert_12_5
  · simpa [Bsmall] using no_sq_cert_12_6
  · simpa [Bsmall] using no_sq_cert_12_7
  · simpa [Bsmall] using no_sq_cert_12_8
  · simpa [Bsmall] using no_sq_cert_12_9
  · simpa [Bsmall] using no_sq_cert_12_10
  · simpa [Bsmall] using no_sq_cert_12_11
  · simpa [Bsmall] using no_sq_cert_12_12
  · simpa [Bsmall] using no_sq_cert_12_13
  · simpa [Bsmall] using no_sq_cert_12_14
  · simpa [Bsmall] using no_sq_cert_12_15
private lemma no_sq_fin_row_13 (d : Fin 16) :
    ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322180 - (Bsmall ⟨13, by norm_num⟩ + Bsmall d) := by
  fin_cases d <;> simp [Bsmall]
  · simpa [Bsmall] using no_sq_cert_13_0
  · simpa [Bsmall] using no_sq_cert_13_1
  · simpa [Bsmall] using no_sq_cert_13_2
  · simpa [Bsmall] using no_sq_cert_13_3
  · simpa [Bsmall] using no_sq_cert_13_4
  · simpa [Bsmall] using no_sq_cert_13_5
  · simpa [Bsmall] using no_sq_cert_13_6
  · simpa [Bsmall] using no_sq_cert_13_7
  · simpa [Bsmall] using no_sq_cert_13_8
  · simpa [Bsmall] using no_sq_cert_13_9
  · simpa [Bsmall] using no_sq_cert_13_10
  · simpa [Bsmall] using no_sq_cert_13_11
  · simpa [Bsmall] using no_sq_cert_13_12
  · simpa [Bsmall] using no_sq_cert_13_13
  · simpa [Bsmall] using no_sq_cert_13_14
  · simpa [Bsmall] using no_sq_cert_13_15
private lemma no_sq_fin_row_14 (d : Fin 16) :
    ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322180 - (Bsmall ⟨14, by norm_num⟩ + Bsmall d) := by
  fin_cases d <;> simp [Bsmall]
  · simpa [Bsmall] using no_sq_cert_14_0
  · simpa [Bsmall] using no_sq_cert_14_1
  · simpa [Bsmall] using no_sq_cert_14_2
  · simpa [Bsmall] using no_sq_cert_14_3
  · simpa [Bsmall] using no_sq_cert_14_4
  · simpa [Bsmall] using no_sq_cert_14_5
  · simpa [Bsmall] using no_sq_cert_14_6
  · simpa [Bsmall] using no_sq_cert_14_7
  · simpa [Bsmall] using no_sq_cert_14_8
  · simpa [Bsmall] using no_sq_cert_14_9
  · simpa [Bsmall] using no_sq_cert_14_10
  · simpa [Bsmall] using no_sq_cert_14_11
  · simpa [Bsmall] using no_sq_cert_14_12
  · simpa [Bsmall] using no_sq_cert_14_13
  · simpa [Bsmall] using no_sq_cert_14_14
  · simpa [Bsmall] using no_sq_cert_14_15
private lemma no_sq_fin_row_15 (d : Fin 16) :
    ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322180 - (Bsmall ⟨15, by norm_num⟩ + Bsmall d) := by
  fin_cases d <;> simp [Bsmall]
  · simpa [Bsmall] using no_sq_cert_15_0
  · simpa [Bsmall] using no_sq_cert_15_1
  · simpa [Bsmall] using no_sq_cert_15_2
  · simpa [Bsmall] using no_sq_cert_15_3
  · simpa [Bsmall] using no_sq_cert_15_4
  · simpa [Bsmall] using no_sq_cert_15_5
  · simpa [Bsmall] using no_sq_cert_15_6
  · simpa [Bsmall] using no_sq_cert_15_7
  · simpa [Bsmall] using no_sq_cert_15_8
  · simpa [Bsmall] using no_sq_cert_15_9
  · simpa [Bsmall] using no_sq_cert_15_10
  · simpa [Bsmall] using no_sq_cert_15_11
  · simpa [Bsmall] using no_sq_cert_15_12
  · simpa [Bsmall] using no_sq_cert_15_13
  · simpa [Bsmall] using no_sq_cert_15_14
  · simpa [Bsmall] using no_sq_cert_15_15

private lemma no_sq_fin (c d : Fin 16) :
    ¬ ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322180 - (Bsmall c + Bsmall d) := by
  fin_cases c <;> simp [Bsmall]
  · simpa [Bsmall] using no_sq_fin_row_0 d
  · simpa [Bsmall] using no_sq_fin_row_1 d
  · simpa [Bsmall] using no_sq_fin_row_2 d
  · simpa [Bsmall] using no_sq_fin_row_3 d
  · simpa [Bsmall] using no_sq_fin_row_4 d
  · simpa [Bsmall] using no_sq_fin_row_5 d
  · simpa [Bsmall] using no_sq_fin_row_6 d
  · simpa [Bsmall] using no_sq_fin_row_7 d
  · simpa [Bsmall] using no_sq_fin_row_8 d
  · simpa [Bsmall] using no_sq_fin_row_9 d
  · simpa [Bsmall] using no_sq_fin_row_10 d
  · simpa [Bsmall] using no_sq_fin_row_11 d
  · simpa [Bsmall] using no_sq_fin_row_12 d
  · simpa [Bsmall] using no_sq_fin_row_13 d
  · simpa [Bsmall] using no_sq_fin_row_14 d
  · simpa [Bsmall] using no_sq_fin_row_15 d

private lemma no_rep_800322180 (x y c d : ℕ) :
    ¬ (x ≤ y ∧ c ≤ d ∧
      x ^ 2 + y ^ 2 + (2 * c + 1).choose c + (2 * d + 1).choose d = 800322180) := by
  rintro ⟨hxy, hcd, hsum⟩
  have hc_le : c ≤ 15 := by
    by_contra hc
    have hc16 : 16 ≤ c := by omega
    have hbig := B_large hc16
    have hle : (2 * c + 1).choose c ≤ 800322180 := by omega
    omega
  have hd_le : d ≤ 15 := by
    by_contra hd
    have hd16 : 16 ≤ d := by omega
    have hbig := B_large hd16
    have hle : (2 * d + 1).choose d ≤ 800322180 := by omega
    omega
  let cf : Fin 16 := ⟨c, by omega⟩
  let df : Fin 16 := ⟨d, by omega⟩
  have hs : ∃ u v : ℕ, u ^ 2 + v ^ 2 = 800322180 - (Bsmall cf + Bsmall df) := by
    refine ⟨x, y, ?_⟩
    rw [← B_eq_Bsmall cf, ← B_eq_Bsmall df]
    change x ^ 2 + y ^ 2 = 800322180 - ((2 * c + 1).choose c + (2 * d + 1).choose d)
    omega
  exact (no_sq_fin cf df) hs

private lemma a_800322180_eq_zero : a 800322180 = 0 := by
  unfold a
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  apply Finset.sum_eq_zero
  intro c hc
  apply Finset.sum_eq_zero
  intro d hd
  have hfalse : ¬ (x ≤ y ∧ c ≤ d ∧
      x ^ 2 + y ^ 2 + (2 * c + 1).choose c + (2 * d + 1).choose d = 800322180) :=
    no_rep_800322180 x y c d
  simp [hfalse]

/--
The conjecture is false: `800322180` is a counterexample.
-/
theorem oeis_303639_conjecture_0.disproof :
    ¬ ∀ (n : ℕ), n > 1 → a n > 0 := by
  intro h
  have hpos : a 800322180 > 0 := h 800322180 (by norm_num)
  rw [a_800322180_eq_zero] at hpos
  omega
