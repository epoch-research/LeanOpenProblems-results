import FormalConjectures.Util.ProblemImports
open Nat

/--
A001359 Lesser of twin primes.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n > 0 then
    (n - 1).nth (fun p => Nat.Prime p ∧ Nat.Prime (p + 2))
  else
    0

open Finset Nat.ModEq

def has_divisor_up_to (n : ℕ) : ℕ → Bool
| 0 => false
| 1 => false
| k + 1 => if n % (k + 1) == 0 then true else has_divisor_up_to n k

def fast_is_prime (n : ℕ) : Bool :=
  if n < 2 then false
  else if n == 2 then true
  else if n == 3 then true
  else not (has_divisor_up_to n (if n ≤ 88 then n - 1 else 88))

def count_tr (p : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | n + 1, acc => count_tr p n (acc + if p n then 1 else 0)

lemma count_tr_eq (p : ℕ → Bool) (n : ℕ) (acc : ℕ) :
    count_tr p n acc = count (fun x => p x = true) n + acc := by
  induction n generalizing acc with
  | zero => simp [count_tr, count]
  | succ n ih =>
    rw [count_tr, ih, count_succ]
    omega

lemma count_eq_count_tr (p : ℕ → Bool) (n : ℕ) :
    count (fun x => p x = true) n = count_tr p n 0 := by
  rw [count_tr_eq, add_zero]

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

lemma b1 : count (fun x => fast_is_prime x = true) 2000 = 303 := by
  rw [count_eq_count_tr]; rfl

lemma b2 : count (fun x => fast_is_prime (2000 + x) = true) 2000 = 247 := by
  rw [count_eq_count_tr]; rfl

lemma b3 : count (fun x => fast_is_prime (4000 + x) = true) 2000 = 233 := by
  rw [count_eq_count_tr]; rfl

lemma b4_7841 : count (fun x => fast_is_prime (6000 + x) = true) 1841 = 207 := by
  rw [count_eq_count_tr]; rfl

lemma has_divisor_up_to_iff (n : ℕ) (k : ℕ) :
    has_divisor_up_to n k = true ↔ ∃ d, 2 ≤ d ∧ d ≤ k ∧ d ∣ n := by
  induction k with
  | zero =>
    simp [has_divisor_up_to]
  | succ k ih =>
    rcases k with _ | k
    · simp [has_divisor_up_to]
      rintro d hd_ge hd_le
      omega
    · simp only [has_divisor_up_to]
      by_cases h : n % (k + 2) = 0
      · simp [h]
        use k + 2
        have : k + 2 ∣ n := Nat.dvd_of_mod_eq_zero h
        omega
      · simp [h, ih]
        constructor
        · rintro ⟨d, hd2, hdk, hd_dvd⟩
          refine ⟨d, hd2, by omega, hd_dvd⟩
        · rintro ⟨d, hd2, hdk, hd_dvd⟩
          have : d ≠ k + 2 := by
            rintro rfl
            apply h
            exact Nat.mod_eq_zero_of_dvd hd_dvd
          refine ⟨d, hd2, by omega, hd_dvd⟩

lemma has_divisor_up_to_eq_false (n : ℕ) (k : ℕ) :
    has_divisor_up_to n k = false ↔ ∀ d, 2 ≤ d → d ≤ k → ¬ d ∣ n := by
  constructor
  · intro h d hd2 hdk hd_dvd
    have h_true : has_divisor_up_to n k = true := by
      rw [has_divisor_up_to_iff]
      exact ⟨d, hd2, hdk, hd_dvd⟩
    rw [h] at h_true
    contradiction
  · intro h
    by_contra hc
    rw [Bool.not_eq_false] at hc
    rw [has_divisor_up_to_iff] at hc
    rcases hc with ⟨d, hd2, hdk, hd_dvd⟩
    exact h d hd2 hdk hd_dvd

lemma fast_is_prime_eq_prime (n : ℕ) (hn_lt : n < 7921) :
    fast_is_prime n = true ↔ Nat.Prime n := by
  rcases lt_or_ge n 2 with hn_lt_2 | hn_ge_2
  · by_cases h : n = 0
    · subst h
      unfold fast_is_prime
      simp
      exact Nat.not_prime_zero
    · have : n = 1 := by omega
      subst this
      unfold fast_is_prime
      simp
      exact Nat.not_prime_one
  · rcases eq_or_ne n 2 with rfl | hn_ne_2
    · unfold fast_is_prime
      simp
      exact Nat.prime_two
    · rcases eq_or_ne n 3 with rfl | hn_ne_3
      · unfold fast_is_prime
        simp
        exact Nat.prime_three
      · have hn_ge_4 : 4 ≤ n := by omega
        have hn_ne_2_bool : (n == 2) = false := by simp [hn_ne_2]
        have hn_ne_3_bool : (n == 3) = false := by simp [hn_ne_3]
        have hn_lt_2_bool : (n < 2) = false := by simp [hn_ge_2]
        unfold fast_is_prime
        simp [hn_lt_2_bool, hn_ne_2_bool, hn_ne_3_bool]
        constructor
        · intro h
          rw [Nat.prime_def_le_sqrt]
          refine ⟨hn_ge_2, ?_⟩
          intro m hm2 hm_sqrt
          have hK : m ≤ if n ≤ 88 then n - 1 else 88 := by
            split_ifs with h_le
            · have : n.sqrt < n := Nat.sqrt_lt_self (by omega)
              omega
            · have h_sqrt_lt : n.sqrt < 89 := by
                rw [Nat.sqrt_lt]
                omega
              omega
          rw [has_divisor_up_to_eq_false] at h
          exact h m hm2 hK
        · intro h
          have h_prime : Nat.Prime n := h
          rw [Nat.prime_def_le_sqrt] at h
          rw [has_divisor_up_to_eq_false]
          intro d hd2 hdK hd_dvd
          have hd_ne_n : d ≠ n := by
            split_ifs at hdK with h_le
            · omega
            · omega
          have hd_ne_one : d ≠ 1 := by omega
          rcases (Nat.Prime.eq_one_or_self_of_dvd h_prime d hd_dvd) with hd_one | hd_self
          · exact hd_ne_one hd_one
          · exact hd_ne_n hd_self

lemma count_tr_add (p : ℕ → Bool) (a b : ℕ) (acc : ℕ) :
    count_tr p (a + b) acc = count_tr (fun x => p (a + x)) b (count_tr p a acc) := by
  simp [count_tr_eq, count_add]
  omega

lemma step1 : count_tr fast_is_prime 2000 0 = 303 := by rfl
lemma step2 : count_tr (fun x => fast_is_prime (2000 + x)) 2000 303 = 550 := by rfl
lemma step3 : count_tr (fun x => fast_is_prime (2000 + (2000 + x))) 2000 550 = 783 := by rfl
lemma step4 : count_tr (fun x => fast_is_prime (2000 + (2000 + (2000 + x)))) 1841 783 = 990 := by rfl
lemma step4_7853 : count_tr (fun x => fast_is_prime (2000 + (2000 + (2000 + x)))) 1853 783 = 991 := by rfl

lemma count_tr_7841 : count_tr fast_is_prime 7841 0 = 990 := by
  have h1 : 7841 = 2000 + 5841 := rfl
  have h2 : 5841 = 2000 + 3841 := rfl
  have h3 : 3841 = 2000 + 1841 := rfl
  rw [h1, count_tr_add, step1]
  rw [h2, count_tr_add, step2]
  rw [h3, count_tr_add, step3]
  exact step4

lemma count_tr_7853 : count_tr fast_is_prime 7853 0 = 991 := by
  have h1 : 7853 = 2000 + 5853 := rfl
  have h2 : 5853 = 2000 + 3853 := rfl
  have h3 : 3853 = 2000 + 1853 := rfl
  rw [h1, count_tr_add, step1]
  rw [h2, count_tr_add, step2]
  rw [h3, count_tr_add, step3]
  exact step4_7853

lemma count_congr_of_iff {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] {n : ℕ}
    (h : ∀ k < n, p k ↔ q k) : count p n = count q n := by
  have h1 : count p n ≤ count q n := count_mono_left (fun k hk => (h k hk).mp)
  have h2 : count q n ≤ count p n := count_mono_left (fun k hk => (h k hk).mpr)
  omega

lemma prime_7841 : Nat.Prime 7841 := by
  have h_eq : fast_is_prime 7841 = true := rfl
  rw [← fast_is_prime_eq_prime 7841 (by decide)]
  exact h_eq

lemma prime_7853 : Nat.Prime 7853 := by
  have h_eq : fast_is_prime 7853 = true := rfl
  rw [← fast_is_prime_eq_prime 7853 (by decide)]
  exact h_eq

lemma count_prime_7841 : count Nat.Prime 7841 = 990 := by
  have h_congr : count Nat.Prime 7841 = count (fun x => fast_is_prime x = true) 7841 := by
    apply count_congr_of_iff
    intro k hk
    rw [fast_is_prime_eq_prime k (by omega)]
  rw [h_congr, count_eq_count_tr, count_tr_7841]

lemma count_prime_7853 : count Nat.Prime 7853 = 991 := by
  have h_congr : count Nat.Prime 7853 = count (fun x => fast_is_prime x = true) 7853 := by
    apply count_congr_of_iff
    intro k hk
    rw [fast_is_prime_eq_prime k (by omega)]
  rw [h_congr, count_eq_count_tr, count_tr_7853]

lemma Pk_lt_Pk_succ (k : ℕ) (hk : k > 0) : Nat.nth Nat.Prime (k - 1) < Nat.nth Nat.Prime k := by
  have h_inf := Nat.infinite_setOf_prime
  rw [Nat.nth_lt_nth h_inf]
  omega

lemma nth_prime_prime (n : ℕ) : Nat.Prime (Nat.nth Nat.Prime n) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

lemma Pk_ge_three (k : ℕ) (hk : k > 1) : Nat.nth Nat.Prime (k - 1) ≥ 3 := by
  have h_inf := Nat.infinite_setOf_prime
  have h_le : 1 ≤ k - 1 := by omega
  have h_mono : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime (k - 1) := by
    rw [Nat.nth_le_nth h_inf]
    exact h_le
  have h_nth_one : Nat.nth Nat.Prime 1 = 3 := by
    have h_count_three : count Nat.Prime 3 = 1 := by decide
    rw [← h_count_three]
    exact Nat.nth_count Nat.prime_three
  omega

lemma nth_prime_990 : Nat.nth Nat.Prime 990 = 7841 := by
  have h_count : count Nat.Prime 7841 = 990 := count_prime_7841
  rw [← h_count]
  exact Nat.nth_count prime_7841

lemma nth_prime_991 : Nat.nth Nat.Prime 991 = 7853 := by
  have h_count : count Nat.Prime 7853 = 991 := count_prime_7853
  rw [← h_count]
  exact Nat.nth_count prime_7853

lemma wilson_modEq (n : ℕ) (hn : Nat.Prime n) : (n - 1).factorial ≡ n - 1 [MOD n] := by
  haveI : Fact n.Prime := ⟨hn⟩
  have h_ne : n ≠ 1 := hn.ne_one
  have h_wilson := (Nat.prime_iff_fac_equiv_neg_one h_ne).mp hn
  have h_neg_one : (-1 : ZMod n) = ((n - 1 : ℕ) : ZMod n) := by
    have hp : n.Prime := Fact.out
    have h_two_le := hp.two_le
    have h_le : 1 ≤ n := by omega
    rw [Nat.cast_sub h_le]
    rw [ZMod.natCast_self]
    simp
  rw [h_neg_one] at h_wilson
  rw [← ZMod.natCast_eq_natCast_iff ((n - 1)!) (n - 1) n]
  exact h_wilson

lemma product_identity (k : ℕ) (hk : k > 1) :
    let Pk := Nat.nth Nat.Prime (k - 1);
    let Pk_succ := Nat.nth Nat.Prime k;
    let Wk_prod : ℕ := Finset.prod (Finset.Icc (Pk + 1) (Pk_succ - 2)) id;
    (Pk_succ - 1).factorial = Pk.factorial * Wk_prod * (Pk_succ - 1) := by
  intro Pk Pk_succ Wk_prod
  have h_inf := Nat.infinite_setOf_prime
  have hpk : Pk.Prime := nth_prime_prime (k - 1)
  have hpk_succ : Pk_succ.Prime := nth_prime_prime k
  have hpk_ge3 : Pk ≥ 3 := Pk_ge_three k hk
  have h_lt : Pk < Pk_succ := Pk_lt_Pk_succ k (by omega)
  have h_odd (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) : p % 2 = 1 := by
    have : p % 2 < 2 := Nat.mod_lt p (by decide)
    have h_or : p % 2 = 0 ∨ p % 2 = 1 := by omega
    rcases h_or with h0 | h1
    · have : 2 ∣ p := Nat.dvd_of_mod_eq_zero h0
      rcases hp.eq_one_or_self_of_dvd 2 this with h_one | h_self
      · contradiction
      · omega
    · exact h1
  have h_diff : Pk_succ - Pk ≥ 2 := by
    have h_odd1 := h_odd Pk hpk hpk_ge3
    have h_odd2 := h_odd Pk_succ hpk_succ (by omega)
    omega
  have h_le1 : 1 ≤ Pk + 1 := by omega
  have h_le2 : Pk + 1 ≤ Pk_succ := by omega
  have h_le3 : Pk + 1 ≤ Pk_succ - 1 := by omega

  have h_split1 : (∏ i ∈ Finset.Ico 1 Pk_succ, id i) = (∏ i ∈ Finset.Ico 1 (Pk + 1), id i) * (∏ i ∈ Finset.Ico (Pk + 1) Pk_succ, id i) := by
    rw [← Finset.prod_Ico_consecutive id h_le1 h_le2]
  have h_split2 : (∏ i ∈ Finset.Ico (Pk + 1) Pk_succ, id i) = (∏ i ∈ Finset.Ico (Pk + 1) (Pk_succ - 1), id i) * (Pk_succ - 1) := by
    have h_eq : Pk_succ = (Pk_succ - 1) + 1 := by omega
    nth_rw 1 [h_eq]
    rw [Finset.prod_Ico_succ_top h_le3]
    rfl
  have h_fac1 : (∏ i ∈ Finset.Ico 1 (Pk + 1), id i) = Pk.factorial := by
    simp only [id]
    rw [Finset.prod_Ico_id_eq_factorial]
  have h_fac_total : (∏ i ∈ Finset.Ico 1 Pk_succ, id i) = (Pk_succ - 1).factorial := by
    have h_eq : Pk_succ = (Pk_succ - 1) + 1 := by omega
    nth_rw 1 [h_eq]
    simp only [id]
    rw [Finset.prod_Ico_id_eq_factorial]

  have h_Icc : Finset.Ico (Pk + 1) (Pk_succ - 1) = Finset.Icc (Pk + 1) (Pk_succ - 2) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega

  rw [h_split1, h_split2, h_fac1, h_Icc] at h_fac_total
  rw [← h_fac_total]
  ring

lemma gcd_self_sub_one (n : ℕ) (hn : n ≥ 2) : Nat.gcd n (n - 1) = 1 := by
  have h_dvd : Nat.gcd n (n - 1) ∣ 1 := by
    have h1 : Nat.gcd n (n - 1) ∣ n := Nat.gcd_dvd_left n (n - 1)
    have h2 : Nat.gcd n (n - 1) ∣ n - 1 := Nat.gcd_dvd_right n (n - 1)
    have h_sub := Nat.dvd_sub h1 h2
    have h_eq : n - (n - 1) = 1 := by omega
    rwa [h_eq] at h_sub
  exact Nat.dvd_one.mp h_dvd

lemma factorial_mul_W_mod_eq_one (k : ℕ) (hk : k > 1) :
    let Pk := Nat.nth Nat.Prime (k - 1);
    let Pk_succ := Nat.nth Nat.Prime k;
    let Wk_prod := Finset.prod (Finset.Icc (Pk + 1) (Pk_succ - 2)) id;
    Pk.factorial * Wk_prod ≡ 1 [MOD Pk_succ] := by
  intro Pk Pk_succ Wk_prod
  have hpk_succ : Pk_succ.Prime := nth_prime_prime k
  have hpk_ge3 : Pk ≥ 3 := Pk_ge_three k hk
  have h_lt : Pk < Pk_succ := Pk_lt_Pk_succ k (by omega)
  have h_prod := product_identity k hk
  have h_wilson := wilson_modEq Pk_succ hpk_succ
  rw [h_prod] at h_wilson
  have h_rew : Pk_succ - 1 = 1 * (Pk_succ - 1) := by omega
  nth_rw 2 [h_rew] at h_wilson
  have h_coprime : Nat.gcd Pk_succ (Pk_succ - 1) = 1 := gcd_self_sub_one Pk_succ (by omega)
  exact Nat.ModEq.cancel_right_of_coprime h_coprime h_wilson

/--
Conjecture: A001359 Primes `prime(k)` such that `prime(k)! == 1 (mod prime(k+1))` with the exception of
`prime(991) = 7841` and other unknown primes `prime(k)` for which
`(prime(k)+1)*(prime(k)+2)*...*(prime(k+1)-2) == 1 (mod prime(k+1))` where `prime(k+1) - prime(k) > 2`.
Here, `prime(k)` denotes the k-th prime number (1-indexed, so prime(k) = Nat.nth Nat.Prime (k-1) for k > 0).
-/
theorem oeis_1359_conjecture_6 :
  -- k is the 1-based index. We start with k > 1, corresponding to the first twin prime 3 (P_2).
  ∀ (k : ℕ), k > 1 →
  let Pk      := Nat.nth Nat.Prime (k - 1); -- Pk is the k-th prime
  let Pk_succ := Nat.nth Nat.Prime k;       -- Pk_succ is the (k+1)-th prime
  let Congruence := Nat.factorial Pk ≡ 1 [MOD Pk_succ];
  let IsLesserTwinPrime := Nat.Prime (Pk + 2);

  -- The product Wk_prod is $\prod_{i=P_k+1}^{P_{k+1}-2} i$. This defines the value W_k in the OEIS comment.
  let Wk_prod : ℕ := Finset.prod (Finset.Icc (Pk + 1) (Pk_succ - 2)) id;

  -- The set of primes satisfying the congruence is the set of lesser twin primes
  -- union the set of exceptional indices C \ T.
  Iff Congruence (
    IsLesserTwinPrime ∨
    (k = 991) ∨
    (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])
  )
:= by
  intro k hk Pk Pk_succ Congruence IsLesserTwinPrime Wk_prod
  have h_inf := Nat.infinite_setOf_prime
  have hpk : Pk.Prime := nth_prime_prime (k - 1)
  have hpk_succ : Pk_succ.Prime := nth_prime_prime k
  have hpk_ge3 : Pk ≥ 3 := Pk_ge_three k hk
  have h_lt : Pk < Pk_succ := Pk_lt_Pk_succ k (by omega)
  have h_odd (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) : p % 2 = 1 := by
    have : p % 2 < 2 := Nat.mod_lt p (by decide)
    have h_or : p % 2 = 0 ∨ p % 2 = 1 := by omega
    rcases h_or with h0 | h1
    · have : 2 ∣ p := Nat.dvd_of_mod_eq_zero h0
      rcases hp.eq_one_or_self_of_dvd 2 this with h_one | h_self
      · contradiction
      · omega
    · exact h1
  have h_diff : Pk_succ - Pk ≥ 2 := by
    have h_odd1 := h_odd Pk hpk hpk_ge3
    have h_odd2 := h_odd Pk_succ hpk_succ (by omega)
    omega

  have h_W : Pk.factorial * Wk_prod ≡ 1 [MOD Pk_succ] := factorial_mul_W_mod_eq_one k hk

  constructor
  · intro h_congr
    rcases lt_or_eq_of_le h_diff with h_gt | h_eq
    · right; right
      refine ⟨h_gt, ?_⟩
      have h_one : Pk.factorial * Wk_prod ≡ 1 * Wk_prod [MOD Pk_succ] := Nat.ModEq.mul_right Wk_prod h_congr
      have h_trans : 1 * Wk_prod ≡ 1 [MOD Pk_succ] := Nat.ModEq.trans (Nat.ModEq.symm h_one) h_W
      have h_eq : 1 * Wk_prod = Wk_prod := by omega
      rwa [h_eq] at h_trans
    · left
      change IsLesserTwinPrime
      change Nat.Prime (Pk + 2)
      have : Pk_succ = Pk + 2 := by omega
      rw [← this]
      exact hpk_succ
  · rintro (h_twin | h_991 | h_except)
    · have h_eq : Pk_succ = Pk + 2 := by
        by_contra hc
        have h_between : Pk < Pk + 2 ∧ Pk + 2 < Pk_succ := by omega
        have h_no_prime : ∀ p, Nat.Prime p → Pk < p → p < Pk_succ → False := by
          intro p hp hp_gt hp_lt
          have h_c1 : count Nat.Prime Pk < count Nat.Prime p := count_strict_mono hpk hp_gt
          have h_c2 : count Nat.Prime p < count Nat.Prime Pk_succ := count_strict_mono hp hp_lt
          have h_c_pk : count Nat.Prime Pk = k - 1 := by
            exact count_nth_of_infinite h_inf (k - 1)
          have h_c_pks : count Nat.Prime Pk_succ = k := by
            exact count_nth_of_infinite h_inf k
          omega
        exact h_no_prime (Pk + 2) h_twin (by omega) (by omega)
      have h_empty : Finset.Icc (Pk + 1) (Pk_succ - 2) = ∅ := by
        rw [h_eq]
        ext x
        simp
      have h_W_eq : Wk_prod = 1 := by
        change (Finset.Icc (Pk + 1) (Pk_succ - 2)).prod id = 1
        rw [h_empty]
        rfl
      rw [h_W_eq] at h_W
      rwa [mul_one] at h_W
    · subst h_991
      have h_Pk : Pk = 7841 := nth_prime_990
      have h_Pks : Pk_succ = 7853 := nth_prime_991
      have h_W991 : Wk_prod ≡ 1 [MOD Pk_succ] := by
        change (Finset.Icc (Pk + 1) (Pk_succ - 2)).prod id ≡ 1 [MOD Pk_succ]
        rw [h_Pk, h_Pks]
        decide
      have h_one : Pk.factorial * Wk_prod ≡ Pk.factorial * 1 [MOD Pk_succ] := Nat.ModEq.mul_left Pk.factorial h_W991
      have h_trans : Pk.factorial * 1 ≡ 1 [MOD Pk_succ] := Nat.ModEq.trans (Nat.ModEq.symm h_one) h_W
      rwa [mul_one] at h_trans
    · have h_W1 := h_except.2
      have h_one : Pk.factorial * Wk_prod ≡ Pk.factorial * 1 [MOD Pk_succ] := Nat.ModEq.mul_left Pk.factorial h_W1
      have h_trans : Pk.factorial * 1 ≡ 1 [MOD Pk_succ] := Nat.ModEq.trans (Nat.ModEq.symm h_one) h_W
      rwa [mul_one] at h_trans
