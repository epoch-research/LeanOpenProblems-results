import FormalConjectures.Util.ProblemImports

open Int

/--
Helper function for A382590, computing the pair $(a(n), b(n))$ such that:
$a(n) = a(n-1)b(n-2) + a(n-2)b(n-1)$
$b(n) = a(n-1)b(n-2) - a(n-2)b(n-1)$
-/
def A382590_pair : ℕ → ℤ × ℤ
| 0 => (1, 1)
| 1 => (2, 1)
| n + 2 =>
  let (a_n_plus_1, b_n_plus_1) := A382590_pair (n + 1)
  let (a_n, b_n) := A382590_pair n
  (a_n_plus_1 * b_n + a_n * b_n_plus_1, a_n_plus_1 * b_n - a_n * b_n_plus_1)

/--
A382590: $a(n)$ is the sequence defined by the mutual recurrence relations:
$a(n) = a(n-1)b(n-2) + a(n-2)b(n-1)$ and $b(n) = a(n-1)b(n-2) - a(n-2)b(n-1)$
starting with $a(0) = b(0) = b(1) = 1$ and a(1) = 2.
The terms are in $\mathbb{Z}$ due to negative values.
-/
def A382590 (n : ℕ) : ℤ := (A382590_pair n).fst

open Nat

/--
The k-th prime factor of an integer n (where k>=1), counted with multiplicity.
This is defined as the k-th element (0-indexed k-1) of `Nat.primeFactorsList n.natAbs`.
Returns 1 if n has fewer than k prime factors or if n is 0, 1, or -1, following the informal convention.
-/
def kth_prime_factor (k : ℕ) (n : ℤ) : ℕ :=
  if h₀ : k = 0 then 1 else
  let n_abs := Int.natAbs n
  let L := primeFactorsList n_abs
  -- prime factors list length is L.length. We look for k-th element, index k-1.
  if h_len : k - 1 ≥ L.length then 1 else
  L[k - 1]

/--
A382590 This sequence appears to have a very peculiar (conjectured) property.
For any k > 1, if you take the k-th prime factor of each term, you get an eventually periodic sequence.
This seems to hold even when we change a(1) as long as it is an integer > 1.
-/
lemma A382590_pair_fst_add_two (n : ℕ) :
    (A382590_pair (n + 2)).fst =
      (A382590_pair (n + 1)).fst * (A382590_pair n).snd +
        (A382590_pair n).fst * (A382590_pair (n + 1)).snd := by
  rw [A382590_pair]

lemma A382590_pair_snd_add_two (n : ℕ) :
    (A382590_pair (n + 2)).snd =
      (A382590_pair (n + 1)).fst * (A382590_pair n).snd -
        (A382590_pair n).fst * (A382590_pair (n + 1)).snd := by
  rw [A382590_pair]


lemma zmod15_period_aux (m : ℕ) :
    (((A382590_pair (m + 15)).fst : ZMod 15) = ((A382590_pair (m + 3)).fst : ZMod 15) ∧
     ((A382590_pair (m + 15)).snd : ZMod 15) = ((A382590_pair (m + 3)).snd : ZMod 15)) ∧
    (((A382590_pair (m + 16)).fst : ZMod 15) = ((A382590_pair (m + 4)).fst : ZMod 15) ∧
     ((A382590_pair (m + 16)).snd : ZMod 15) = ((A382590_pair (m + 4)).snd : ZMod 15)) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have h15a := ih.1.1
      have h15b := ih.1.2
      have h16a := ih.2.1
      have h16b := ih.2.2
      constructor
      · exact ⟨h16a, h16b⟩
      · constructor
        · -- goal m+1+16 vs m+1+4 i.e. m+17 vs m+5
          change (((A382590_pair ((m + 15) + 2)).fst : ZMod 15) = ((A382590_pair ((m + 3) + 2)).fst : ZMod 15))
          rw [A382590_pair_fst_add_two (m + 15), A382590_pair_fst_add_two (m + 3)]
          norm_num [h15a, h15b, h16a, h16b]
        · change (((A382590_pair ((m + 15) + 2)).snd : ZMod 15) = ((A382590_pair ((m + 3) + 2)).snd : ZMod 15))
          rw [A382590_pair_snd_add_two (m + 15), A382590_pair_snd_add_two (m + 3)]
          norm_num [h15a, h15b, h16a, h16b]


lemma A382590_zmod15_ne_zero_ge3 (m : ℕ) :
    ((A382590_pair (m + 3)).fst : ZMod 15) ≠ 0 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm : m < 12
      · interval_cases m <;> decide
      · have hle : 12 ≤ m := le_of_not_gt hm
        let t := m - 12
        have htlt : t < m := by omega
        have hm_eq : m + 3 = t + 15 := by omega
        have hper := (zmod15_period_aux t).1.1
        rw [hm_eq, hper]
        exact ih t htlt

lemma A382590_ne_zero (n : ℕ) : A382590 n ≠ 0 := by
  intro hz
  have hzmod : ((A382590 n : ℤ) : ZMod 15) = 0 := by rw [hz]; norm_num
  unfold A382590 at hzmod
  by_cases hn : n < 3
  · interval_cases n <;> norm_num [A382590_pair] at hzmod <;> revert hzmod <;> decide
  · have hle : 3 ≤ n := le_of_not_gt hn
    let m := n - 3
    have hn_eq : n = m + 3 := by omega
    rw [hn_eq] at hzmod
    exact A382590_zmod15_ne_zero_ge3 m hzmod


lemma A382590_pair_even_ge4 (m : ℕ) :
    (2 : ℤ) ∣ (A382590_pair (m + 4)).fst ∧
    (2 : ℤ) ∣ (A382590_pair (m + 4)).snd := by
  induction m using Nat.twoStepInduction with
  | zero => norm_num [A382590_pair]
  | one => norm_num [A382590_pair]
  | more m hm hm1 =>
      have hma := hm.1; have hmb := hm.2
      have hm1a := hm1.1; have hm1b := hm1.2
      change (2 : ℤ) ∣ (A382590_pair ((m + 4) + 2)).fst ∧
        (2 : ℤ) ∣ (A382590_pair ((m + 4) + 2)).snd
      constructor
      · rw [A382590_pair_fst_add_two (m + 4)]
        exact dvd_add (dvd_mul_of_dvd_left hm1a _) (dvd_mul_of_dvd_left hma _)
      · rw [A382590_pair_snd_add_two (m + 4)]
        exact dvd_sub (dvd_mul_of_dvd_left hm1a _) (dvd_mul_of_dvd_left hma _)

lemma A382590_pair_pow_two_dvd (k n : ℕ) (h : 2 * k + 4 ≤ n) :
    ((2 : ℤ) ^ k) ∣ (A382590_pair n).fst ∧
    ((2 : ℤ) ^ k) ∣ (A382590_pair n).snd := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      cases k with
      | zero =>
          have h4 : 4 ≤ n := by omega
          let m := n - 4
          have hn : n = m + 4 := by omega
          rw [hn]
          simpa using A382590_pair_even_ge4 m
      | succ j =>
          let K := j + 1
          let r := n - 2
          have hn : n = r + 2 := by omega
          have hr : 2 * (j + 1) + 4 ≤ r := by omega
          have hr1 : 2 * (j + 1) + 4 ≤ r + 1 := by omega
          have hprev := ih r hr
          have hprev1 := ih (r + 1) hr1
          have hlepow : ((2 : ℤ) ^ ((j + 1) + 1)) ∣ ((2 : ℤ) ^ (j + 1) * (2 : ℤ) ^ (j + 1)) := by
            rw [← pow_add]
            exact pow_dvd_pow (2 : ℤ) (by omega)
          rw [hn]
          constructor
          · rw [A382590_pair_fst_add_two r]
            exact dvd_add
              (hlepow.trans (mul_dvd_mul hprev1.1 hprev.2))
              (hlepow.trans (mul_dvd_mul hprev.1 hprev1.2))
          · rw [A382590_pair_snd_add_two r]
            exact dvd_sub
              (hlepow.trans (mul_dvd_mul hprev1.1 hprev.2))
              (hlepow.trans (mul_dvd_mul hprev.1 hprev1.2))


lemma primeFactorsList_take_replicate_two {m k : ℕ} (hm0 : m ≠ 0) (hdvd : 2 ^ k ∣ m) :
    (Nat.primeFactorsList m).take k = List.replicate k 2 := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
      have h2dvd : 2 ∣ m := by
        show 2 ^ 1 ∣ m
        exact (pow_dvd_pow (2 : ℕ) (Nat.succ_pos k)).trans hdvd
      have hmin : Nat.minFac m = 2 := (Nat.minFac_eq_two_iff m).2 h2dvd
      have hm2 : 2 ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h2dvd
      have hm_eq : m = (m - 2) + 2 := by omega
      have hdiv0 : m / 2 ≠ 0 := by omega
      have hdivdvd : 2 ^ k ∣ m / 2 := by
        rcases hdvd with ⟨c, hc⟩
        use c
        rw [hc, pow_succ']
        rw [Nat.mul_assoc]
        rw [mul_comm 2 (2 ^ k * c)]
        exact Nat.mul_div_left (2 ^ k * c) (by norm_num : 0 < 2)
      have hmin' : Nat.minFac ((m - 2) + 2) = 2 := by rwa [← hm_eq]
      rw [hm_eq, Nat.primeFactorsList_add_two, hmin']
      have hdiv_eq : ((m - 2) + 2) / 2 = m / 2 := by rw [← hm_eq]
      rw [hdiv_eq]
      simpa [List.replicate_succ] using congrArg (fun l => (2 : ℕ) :: l) (ih hdiv0 hdivdvd)

lemma primeFactorsList_get_two_of_pow_dvd {m k : ℕ} (hk : 1 ≤ k) (hm0 : m ≠ 0)
    (hdvd : 2 ^ k ∣ m) :
    (if h_len : k - 1 ≥ (Nat.primeFactorsList m).length then 1 else (Nat.primeFactorsList m)[k - 1]) = 2 := by
  have htake := primeFactorsList_take_replicate_two hm0 hdvd
  have hlen : k ≤ (Nat.primeFactorsList m).length := by
    have := congrArg List.length htake
    simpa using this.symm
  have hnot : ¬ k - 1 ≥ (Nat.primeFactorsList m).length := by omega
  simp [hnot]
  have hidx : k - 1 < k := by omega
  have hidxL : k - 1 < (Nat.primeFactorsList m).length := by omega
  have hopt := congrArg (fun l : List ℕ => l[k - 1]?) htake
  simp [hidx] at hopt
  rw [List.getElem?_eq_getElem hidxL] at hopt
  exact Option.some.inj hopt

lemma kth_prime_factor_A382590_eq_two (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k + 4 ≤ n) :
    kth_prime_factor k (A382590 n) = 2 := by
  have hzdvd : ((2 : ℤ) ^ k) ∣ A382590 n := (A382590_pair_pow_two_dvd k n hn).1
  have hm0 : Int.natAbs (A382590 n) ≠ 0 := by
    simpa [Int.natAbs_eq_zero] using A382590_ne_zero n
  have hdvdNat : 2 ^ k ∣ Int.natAbs (A382590 n) := by
    exact Int.natCast_dvd.mp (by simpa [A382590, Int.natCast_pow] using hzdvd)
  rw [kth_prime_factor]
  have h0 : ¬ k = 0 := by omega
  simp [h0, primeFactorsList_get_two_of_pow_dvd hk hm0 hdvdNat]

theorem A382590_conjecture_kth_prime_factor_is_eventually_periodic :
  ∀ k : ℕ, k ≥ 2 →
    ∃ N₀ p : ℕ, p > 0 ∧ ∀ n : ℕ, n ≥ N₀ →
      kth_prime_factor k (A382590 (n + p)) = kth_prime_factor k (A382590 n) := by
  intro k hk
  refine ⟨2 * k + 4, 1, by omega, ?_⟩
  intro n hn
  have hk1 : 1 ≤ k := by omega
  rw [kth_prime_factor_A382590_eq_two k n hk1 hn]
  rw [kth_prime_factor_A382590_eq_two k (n + 1) hk1 (by omega)]
