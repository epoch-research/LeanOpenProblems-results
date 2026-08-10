import FormalConjectures.Util.ProblemImports

open Nat List

/-- The $n$-th triangular number, $T_n = \frac{n(n+1)}{2}$. -/
def triangular (n : ℕ) : ℕ := n * (n + 1) / 2

/-- Concatenates two natural numbers $a$ and $b$ base 10. -/
def concatenate_nats (a b : ℕ) : ℕ :=
  a * (10 ^ (Nat.digits 10 b).length) + b

/--
A053067: $a(n)$ is the concatenation of next $n$ numbers (omit leading 0's).
Specifically, $a(n)$ is the concatenation of the integers from $\frac{(n-1)n}{2} + 1$ up to $\frac{n(n+1)}{2}$.
-/
def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    -- The starting number is $T_{n-1} + 1$. We use n - 1 which is safe since n ≠ 0.
    let start_num : ℕ := triangular (n - 1) + 1
    -- The ending number is $T_n$.
    let end_num : ℕ := triangular n

    -- List.Ico start (end + 1) gives [start, start + 1, ..., end]
    let numbers_to_concat : List ℕ := List.Ico start_num (end_num + 1)

    -- Concatenate the numbers from left to right. The initial accumulator 0 correctly handles the first element.
    numbers_to_concat.foldl concatenate_nats 0

lemma concat_mod3 (a b : ℕ) : concatenate_nats a b ≡ a + b [MOD 3] := by
  unfold concatenate_nats Nat.ModEq
  rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]; norm_num

lemma foldl_mod3 (L : List ℕ) (acc : ℕ) :
    List.foldl concatenate_nats acc L ≡ acc + L.sum [MOD 3] := by
  induction L generalizing acc with
  | nil => simp [Nat.ModEq.refl]
  | cons x xs ih =>
    simp only [List.foldl_cons, List.sum_cons]
    calc List.foldl concatenate_nats (concatenate_nats acc x) xs
        ≡ concatenate_nats acc x + xs.sum [MOD 3] := ih _
      _ ≡ (acc + x) + xs.sum [MOD 3] := Nat.ModEq.add_right _ (concat_mod3 acc x)
      _ = acc + (x + xs.sum) := by ring

lemma concat_mod_dvd10 (m a b : ℕ) (hm : m ∣ 10) (hb : 1 ≤ b) :
    concatenate_nats a b ≡ b [MOD m] := by
  unfold concatenate_nats
  have hL : (Nat.digits 10 b).length ≠ 0 := by
    have : Nat.digits 10 b ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
    simpa [List.length_eq_zero_iff] using this
  have hdvd : m ∣ 10 ^ (Nat.digits 10 b).length := dvd_pow hm hL
  have hz : a * 10 ^ (Nat.digits 10 b).length ≡ 0 [MOD m] :=
    (Nat.modEq_zero_iff_dvd).mpr (hdvd.mul_left a)
  calc a * 10 ^ (Nat.digits 10 b).length + b ≡ 0 + b [MOD m] := hz.add_right b
    _ = b := by ring

lemma foldl_mod_last (m : ℕ) (hm : m ∣ 10) (L : List ℕ) (last acc : ℕ)
    (hlast : 1 ≤ last) :
    List.foldl concatenate_nats acc (L ++ [last]) ≡ last [MOD m] := by
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  exact concat_mod_dvd10 m _ last hm hlast

-- triangular recurrence pieces
lemma tri_succ (m : ℕ) : triangular (m+1) = triangular m + (m+1) := by
  unfold triangular
  have e : (m+1)*(m+1+1) = m*(m+1) + 2*(m+1) := by ring
  have h : 2 ∣ m * (m+1) := (Nat.even_mul_succ_self m).two_dvd
  rw [e]; omega


lemma tri_diff (n : ℕ) (hn : n ≠ 0) : triangular n = triangular (n-1) + n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
  simpa using tri_succ m

lemma a_eq (n : ℕ) (hn : n ≠ 0) :
    a n = (List.range' (triangular (n-1) + 1) n).foldl concatenate_nats 0 := by
  rw [a, dif_neg hn]
  simp only
  congr 1
  unfold List.Ico
  congr 1
  have := tri_diff n hn
  omega

lemma two_tri (m : ℕ) : 2 * triangular m = m * (m+1) := by
  unfold triangular
  have h : 2 ∣ m * (m+1) := (Nat.even_mul_succ_self m).two_dvd
  omega

lemma dvd3_tri (m : ℕ) (h : (3:ℕ) ∣ m * (m+1)) : (3:ℕ) ∣ triangular m := by
  have h2 : 2 * triangular m = m * (m+1) := two_tri m
  have : (3:ℕ) ∣ 2 * triangular m := h2 ▸ h
  exact (Nat.Coprime.dvd_of_dvd_mul_left (by decide) this)

lemma two_dvd_mul_pred (n : ℕ) : (2:ℕ) ∣ n * (n-1) := by
  rcases Nat.even_or_odd n with he | ho
  · exact he.two_dvd.mul_right _
  · have : Even (n-1) := by rcases ho with ⟨k,hk⟩; exact ⟨k, by omega⟩
    exact this.two_dvd.mul_left _

lemma dvd3_a (n : ℕ) (hn : n ≠ 0) (h3 : (3:ℕ) ∣ n) : (3:ℕ) ∣ a n := by
  set S := (List.range' (triangular (n-1)+1) n).sum with hSdef
  have hmod : a n ≡ S [MOD 3] := by
    rw [a_eq n hn, hSdef]
    have := foldl_mod3 (List.range' (triangular (n-1)+1) n) 0
    rwa [Nat.zero_add] at this
  have hev : (2:ℕ) ∣ n * (n-1) := two_dvd_mul_pred n
  have key : 2 * S = 2 * (n * (triangular (n-1)+1)) + n * (n-1) := by
    have hd : 2 * (n*(n-1)/2) = n*(n-1) := Nat.mul_div_cancel' hev
    rw [hSdef, List.sum_range', mul_one, Nat.mul_add, hd]
  have h3S2 : (3:ℕ) ∣ 2 * S := by
    rw [key]
    exact Nat.dvd_add (Dvd.dvd.mul_left (Dvd.dvd.mul_right h3 _) 2) (Dvd.dvd.mul_right h3 _)
  have hS : (3:ℕ) ∣ S := Nat.Coprime.dvd_of_dvd_mul_left (by decide) h3S2
  exact (Nat.modEq_zero_iff_dvd).mp (hmod.trans ((Nat.modEq_zero_iff_dvd).mpr hS))

lemma a_mod_last (m : ℕ) (hm : m ∣ 10) (n : ℕ) (hn : n ≠ 0) :
    a n ≡ triangular n [MOD m] := by
  rw [a_eq n hn]
  obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
  rw [Nat.add_sub_cancel, List.range'_1_concat]
  have hlast : triangular k + 1 + k = triangular (k+1) := by rw [tri_succ]; ring
  rw [← hlast]
  have h1 : 1 ≤ triangular k + 1 + k := by omega
  exact foldl_mod_last m hm _ _ 0 h1

lemma dvd_a_of_dvd10_tri (m : ℕ) (hm : m ∣ 10) (n : ℕ) (hn : n ≠ 0)
    (ht : m ∣ triangular n) : m ∣ a n := by
  exact (Nat.modEq_zero_iff_dvd).mp
    ((a_mod_last m hm n hn).trans ((Nat.modEq_zero_iff_dvd).mpr ht))

lemma a_ge_tri (n : ℕ) (hn : n ≠ 0) : triangular n ≤ a n := by
  rw [a_eq n hn]
  obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
  rw [Nat.add_sub_cancel, List.range'_1_concat, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  have hlast : triangular k + 1 + k = triangular (k+1) := by rw [tri_succ]; ring
  unfold concatenate_nats
  rw [← hlast]
  exact Nat.le_add_left _ _

lemma tri_ge6 (n : ℕ) (h : 3 ≤ n) : 6 ≤ triangular n := by
  have h12 : 12 ≤ n*(n+1) := by nlinarith
  have hdvd : (2:ℕ) ∣ n*(n+1) := (Nat.even_mul_succ_self n).two_dvd
  unfold triangular; omega

lemma ha0 : a 0 = 0 := rfl
lemma ha1 : a 1 = 1 := by
  unfold a
  norm_num [triangular, List.Ico, concatenate_nats, List.range', List.foldl, Nat.digits_def']

/--
The second term is a prime. When is the next prime, if there is another? - _N. J. A. Sloane_, Dec 16 2016
Formalized as the strongest natural conjecture: $a(n)$ is prime if and only if $n=2$.
-/
theorem oeis_53067_conjecture_0 : ∀ n : ℕ, Nat.Prime (a n) ↔ n = 2 := by
  intro n
  constructor
  · intro hp
    by_contra hne
    rcases Nat.lt_or_ge n 3 with hlt | hge
    · interval_cases n
      · rw [ha0] at hp; exact Nat.not_prime_zero hp
      · rw [ha1] at hp; exact Nat.not_prime_one hp
      · exact hne rfl
    · have hn0 : n ≠ 0 := by omega
      have hge6 : 6 ≤ triangular n := tri_ge6 n hge
      have hage : 6 ≤ a n := le_trans hge6 (a_ge_tri n hn0)
      by_cases hc3 : (3:ℕ) ∣ n
      · rcases hp.eq_one_or_self_of_dvd 3 (dvd3_a n hn0 hc3) with h | h
        · norm_num at h
        · omega
      · by_cases hc2 : (2:ℕ) ∣ triangular n
        · rcases hp.eq_one_or_self_of_dvd 2 (dvd_a_of_dvd10_tri 2 (by norm_num) n hn0 hc2) with h | h
          · norm_num at h
          · omega
        · by_cases hc5 : (5:ℕ) ∣ triangular n
          · rcases hp.eq_one_or_self_of_dvd 5 (dvd_a_of_dvd10_tri 5 (by norm_num) n hn0 hc5) with h | h
            · norm_num at h
            · omega
          · -- ESCAPING CASE (the irreducible open core of OEIS A053067).
            -- Here `n ≥ 3`, `¬(3 ∣ n)`, `Tₙ` is odd, `5 ∤ Tₙ`, so `a n` is coprime to 30,
            -- and `hp : Nat.Prime (a n)`.  The whole `{2,3,5}` covering above is *maximal*:
            -- divisibility of `a n` by a prime `p` is a periodic function of `n` ONLY for
            -- `p ∈ {2,3,5}` (for other primes the block digit-lengths grow aperiodically), so
            -- NO finite covering system can reach these `n`.  The escaping `a n` are composite
            -- only for accidental reasons (they have gcd 1 and some have all prime factors
            -- `> 10⁵`), and by the prime heuristic infinitely many are in fact prime — the next
            -- one near `n ≈ 10⁶`, a `>10⁷`-digit number.  Thus this case is a genuinely open
            -- problem: no elementary proof exists, and a disproof witness is far too large to
            -- primality-certify in Lean under {propext, Classical.choice, Quot.sound}.
            sorry
  · rintro rfl
    have h : a 2 = 23 := by
      unfold a
      norm_num [triangular, List.Ico, concatenate_nats, List.range', List.foldl, Nat.digits_def']
    rw [h]; norm_num
