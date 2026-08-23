import FormalConjectures.Util.ProblemImports

open Nat
open Finset
open scoped Classical

/--
A182126: $a(n) = \text{prime}(n) \cdot \text{prime}(n+1) \bmod \text{prime}(n+2)$.
The function $\text{prime}(k)$ is the $k$-th prime number, with $\text{prime}(1)=2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let p_n := fun k : ℕ => (Nat.nth Nat.Prime (k - 1))
  if n = 0 then 0 -- Handle the 0 case for the otherwise 1-indexed sequence
  else (p_n n * p_n (n + 1)) % p_n (n + 2)

/--
Let $C(v, x)$ be the number of times $v$ appears in the sequence $a(1), a(2), \ldots, a(x)$.
$C(v, x) = |\{ n \in \{1, \dots, x\} : a(n) = v \}|$.
-/
noncomputable def count_a (x v : ℕ) : ℕ :=
  -- The index set is {1, 2, ..., x}. We use range (x+1) which is {0, ..., x} and filter by 1 ≤ n.
  ((range (x + 1)).filter fun n => 1 ≤ n ∧ a n = v).card

/--
A value $v₀$ is a most frequent value in $a(1), \ldots, a(x)$ if its count is greater
than or equal to the count of every other value $v$.
-/
def is_most_frequent (x v₀ : ℕ) : Prop :=
  ∀ v : ℕ, count_a x v₀ ≥ count_a x v

/-- The `n`-th prime, 1-indexed (`primeN 1 = 2`). -/
noncomputable def primeN (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

lemma a_zero : a 0 = 0 := by
  simp [a]

lemma a_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    a n = (primeN n * primeN (n + 1)) % primeN (n + 2) := by
  simp [a, primeN, hn]

lemma primeN_prime (n : ℕ) : (primeN n).Prime := by
  simp [primeN, Nat.prime_nth_prime]

lemma primeN_one : primeN 1 = 2 := by simp [primeN]
lemma primeN_two : primeN 2 = 3 := by simp [primeN]
lemma primeN_three : primeN 3 = 5 := by simp [primeN]
lemma primeN_four : primeN 4 = 7 := by simp [primeN]
lemma primeN_five : primeN 5 = 11 := by simp [primeN]

lemma primeN_eq_nth_count {k p : ℕ} (hp : p.Prime)
    (hc : Nat.count Nat.Prime p = k) : primeN (k + 1) = p := by
  simp [primeN]
  rw [← hc]
  exact Nat.nth_count hp

lemma a_one : a 1 = 1 := by
  rw [a_of_ne_zero (by decide)]
  simp [primeN_one, primeN_two, primeN_three]

lemma a_two : a 2 = 1 := by
  rw [a_of_ne_zero (by decide)]
  simp [primeN_two, primeN_three, primeN_four]

lemma a_three : a 3 = 2 := by
  rw [a_of_ne_zero (by decide)]
  simp [primeN_three, primeN_four, primeN_five]

lemma primeN_strictMono : StrictMonoOn primeN (Set.Ici 1) := by
  intro m hm n hn hmn
  have hinf : (setOf Nat.Prime).Infinite := infinite_setOf_prime
  have : m - 1 < n - 1 := by
    simp only [Set.mem_Ici] at hm hn
    omega
  simpa [primeN] using Nat.nth_strictMono hinf this

lemma primeN_lt {m n : ℕ} (hm : 1 ≤ m) (h : m < n) : primeN m < primeN n :=
  primeN_strictMono hm (le_trans hm h.le) h

lemma primeN_le {m n : ℕ} (hm : 1 ≤ m) (h : m ≤ n) : primeN m ≤ primeN n := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_rfl
  · exact (primeN_lt hm hlt).le

lemma two_le_primeN {n : ℕ} (hn : 1 ≤ n) : 2 ≤ primeN n := by
  simpa [primeN_one] using primeN_le (by decide : 1 ≤ 1) hn

lemma primeN_pos {n : ℕ} (hn : 1 ≤ n) : 0 < primeN n :=
  lt_of_lt_of_le (by decide : 0 < 2) (two_le_primeN hn)

lemma three_le_primeN {n : ℕ} (hn : 2 ≤ n) : 3 ≤ primeN n := by
  simpa [primeN_two] using primeN_le (by decide : 1 ≤ 2) hn

lemma a_lt_primeN {n : ℕ} (hn : 1 ≤ n) : a n < primeN (n + 2) := by
  rw [a_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)]
  exact Nat.mod_lt _ (primeN_pos (by omega))

lemma count_a_eq_Icc (x v : ℕ) :
    count_a x v = ((Icc 1 x).filter fun n => a n = v).card := by
  classical
  unfold count_a
  congr 1
  ext n
  simp only [mem_filter, mem_range, mem_Icc, and_assoc]
  constructor
  · intro ⟨hn, h1, ha⟩
    exact ⟨h1, Nat.lt_succ_iff.mp hn, ha⟩
  · intro ⟨h1, hx, ha⟩
    exact ⟨Nat.lt_succ_of_le hx, h1, ha⟩

lemma count_a_le (x v : ℕ) : count_a x v ≤ x := by
  rw [count_a_eq_Icc]
  calc
    ((Icc 1 x).filter fun n => a n = v).card ≤ (Icc 1 x).card := card_filter_le _ _
    _ = x := by simp [Nat.card_Icc]

lemma count_a_mono_left {x y v : ℕ} (h : x ≤ y) :
    count_a x v ≤ count_a y v := by
  classical
  rw [count_a_eq_Icc, count_a_eq_Icc]
  refine card_le_card ?_
  intro n hn
  simp only [mem_filter, mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, le_trans hn.1.2 h⟩, hn.2⟩

/-- Gap between consecutive 1-indexed primes: `gap n = prime(n+1) - prime(n)`. -/
noncomputable def gap (n : ℕ) : ℕ := primeN (n + 1) - primeN n

lemma primeN_succ_eq {n : ℕ} (hn : 1 ≤ n) :
    primeN (n + 1) = primeN n + gap n := by
  have hle : primeN n ≤ primeN (n + 1) := primeN_le hn (Nat.le_succ _)
  simp [gap, Nat.add_sub_of_le hle]

lemma gap_pos {n : ℕ} (hn : 1 ≤ n) : 0 < gap n := by
  have : primeN n < primeN (n + 1) := primeN_lt hn (Nat.lt_succ_self _)
  simpa [gap] using Nat.sub_pos_of_lt this

lemma two_step_span {n : ℕ} (hn : 1 ≤ n) :
    primeN (n + 2) = primeN n + gap n + gap (n + 1) := by
  rw [primeN_succ_eq (by omega : 1 ≤ n + 1), primeN_succ_eq hn, Nat.add_assoc]

lemma two_step_sub {n : ℕ} (hn : 1 ≤ n) :
    primeN (n + 2) - primeN n = gap n + gap (n + 1) := by
  have h := two_step_span hn
  omega

lemma one_step_sub_succ (n : ℕ) :
    primeN (n + 2) - primeN (n + 1) = gap (n + 1) :=
  rfl

/-- `p*q ≡ (r-p)*(r-q) [MOD r]`. -/
lemma mul_modEq_gaps (p q r : ℕ) (hp : p ≤ r) (hq : q ≤ r) :
    p * q ≡ (r - p) * (r - q) [MOD r] := by
  rw [Nat.modEq_iff_dvd]
  have hp' : ((r - p : ℕ) : ℤ) = (r : ℤ) - p := Int.ofNat_sub hp
  have hq' : ((r - q : ℕ) : ℤ) = (r : ℤ) - q := Int.ofNat_sub hq
  have : (((r - p) * (r - q) : ℕ) : ℤ) - (p * q : ℕ) =
      (r : ℤ) * ((r : ℤ) - p - q) := by
    push_cast [hp', hq']
    ring
  exact ⟨(r : ℤ) - p - q, by linarith⟩

lemma a_eq_gap_prod_mod {n : ℕ} (hn : 1 ≤ n) :
    a n = ((gap n + gap (n + 1)) * gap (n + 1)) % primeN (n + 2) := by
  rw [a_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)]
  have hp : primeN n ≤ primeN (n + 2) := (primeN_lt hn (by omega)).le
  have hq : primeN (n + 1) ≤ primeN (n + 2) := (primeN_lt (by omega) (by omega)).le
  have h := mul_modEq_gaps (primeN n) (primeN (n + 1)) (primeN (n + 2)) hp hq
  rw [show (primeN n * primeN (n + 1)) % primeN (n + 2) =
        ((primeN (n + 2) - primeN n) * (primeN (n + 2) - primeN (n + 1))) %
          primeN (n + 2) from h]
  rw [two_step_sub hn, one_step_sub_succ n]

lemma a_eq_gap_prod {n : ℕ} (hn : 1 ≤ n)
    (hnowrap : (gap n + gap (n + 1)) * gap (n + 1) < primeN (n + 2)) :
    a n = (gap n + gap (n + 1)) * gap (n + 1) := by
  rw [a_eq_gap_prod_mod hn, Nat.mod_eq_of_lt hnowrap]

lemma gap_even {n : ℕ} (hn : 2 ≤ n) : 2 ∣ gap n := by
  have hp : (primeN n).Prime := primeN_prime n
  have hq : (primeN (n + 1)).Prime := primeN_prime (n + 1)
  have hp2 : 2 < primeN n := lt_of_lt_of_le (by decide : 2 < 3) (three_le_primeN hn)
  have hq2 : 2 < primeN (n + 1) :=
    lt_of_lt_of_le hp2 (primeN_le (by omega) (Nat.le_succ n))
  have hpodd : primeN n % 2 = 1 :=
    hp.eq_two_or_odd.resolve_left (Nat.ne_of_gt hp2)
  have hqodd : primeN (n + 1) % 2 = 1 :=
    hq.eq_two_or_odd.resolve_left (Nat.ne_of_gt hq2)
  have hle : primeN n ≤ primeN (n + 1) := primeN_le (by omega) (Nat.le_succ n)
  have : (primeN (n + 1) - primeN n) % 2 = 0 := by
    rw [Nat.sub_mod_eq_zero_of_mod_eq]
    rw [hqodd, hpodd]
  exact (dvd_iff_mod_eq_zero.mpr this)

lemma exists_most_frequent (x : ℕ) (hx : 0 < x) :
    ∃ v₀, is_most_frequent x v₀ := by
  classical
  let s := (Icc 1 x).image a
  have hs : s.Nonempty := by
    have h1 : 1 ∈ Icc 1 x := by
      rw [mem_Icc]; exact ⟨le_rfl, Nat.succ_le_of_lt hx⟩
    exact ⟨a 1, mem_image_of_mem a h1⟩
  obtain ⟨v₀, hv₀, hmax⟩ := exists_max_image s (fun v => count_a x v) hs
  refine ⟨v₀, fun v => ?_⟩
  by_cases hv : v ∈ s
  · exact hmax v hv
  · have hz : count_a x v = 0 := by
      rw [count_a_eq_Icc, Finset.card_eq_zero, filter_eq_empty_iff]
      intro n hn ha
      exact hv (mem_image.mpr ⟨n, hn, ha⟩)
    simp [hz]

lemma count_a_three_one : count_a 3 1 = 2 := by
  rw [count_a_eq_Icc]
  have h1 : a 1 = 1 := a_one
  have h2 : a 2 = 1 := a_two
  have h3 : a 3 = 2 := a_three
  classical
  have : (Icc 1 3).filter (fun n => a n = 1) = {1, 2} := by
    ext n
    simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]
    constructor
    · intro ⟨⟨hlo, hhi⟩, ha⟩
      interval_cases n <;> simp_all
    · intro h
      rcases h with rfl | rfl <;> simp [h1, h2]
  rw [this]
  decide

lemma one_not_most_frequent_three : ¬ is_most_frequent 3 2 := by
  intro h
  have := h 1
  rw [count_a_three_one] at this
  -- count 2 at x=3 is 1 (only n=3)
  have c2 : count_a 3 2 = 1 := by
    rw [count_a_eq_Icc]
    have h3 : a 3 = 2 := a_three
    have h1 : a 1 = 1 := a_one
    have h2 : a 2 = 1 := a_two
    classical
    have : (Icc 1 3).filter (fun n => a n = 2) = {3} := by
      ext n
      simp only [mem_filter, mem_Icc, mem_singleton]
      constructor
      · intro ⟨⟨hlo, hhi⟩, ha⟩
        interval_cases n <;> simp_all
      · intro h
        subst h
        simp [h3]
    rw [this]
    decide
  omega

/-- Product of the two gaps; `a n` is this quantity modulo `primeN (n+2)`. -/
noncomputable def gapProd (n : ℕ) : ℕ := (gap n + gap (n + 1)) * gap (n + 1)

lemma a_eq_gapProd_mod {n : ℕ} (hn : 1 ≤ n) :
    a n = gapProd n % primeN (n + 2) := by
  simpa [gapProd] using a_eq_gap_prod_mod hn

lemma a_eq_gapProd {n : ℕ} (hn : 1 ≤ n)
    (hnowrap : gapProd n < primeN (n + 2)) :
    a n = gapProd n := by
  simpa [gapProd] using a_eq_gap_prod hn hnowrap

/-- After the first prime, consecutive gaps are even, so the unreduced
`gapProd` is divisible by 4. -/
lemma four_dvd_gapProd {n : ℕ} (hn : 2 ≤ n) : 4 ∣ gapProd n := by
  have h1 : 2 ∣ gap n := gap_even hn
  have h2 : 2 ∣ gap (n + 1) := gap_even (by omega)
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  refine ⟨(k + l) * l, ?_⟩
  calc
    gapProd n = (2 * k + 2 * l) * (2 * l) := by simp [gapProd, hk, hl]
    _ = 4 * ((k + l) * l) := by ring

lemma even_of_four_dvd {m : ℕ} (h : 4 ∣ m) : 2 ∣ m :=
  dvd_trans (by decide : 2 ∣ 4) h

/-- If there is no wrap-around, `a n` is a multiple of 4 for `n ≥ 2`. -/
lemma four_dvd_a_of_nowrap {n : ℕ} (hn : 2 ≤ n)
    (hnowrap : gapProd n < primeN (n + 2)) : 4 ∣ a n := by
  have : a n = gapProd n := a_eq_gapProd (by omega) hnowrap
  exact this ▸ four_dvd_gapProd hn

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

lemma count_prime_137 : Nat.count Nat.Prime 137 = 32 := by decide
lemma count_prime_139 : Nat.count Nat.Prime 139 = 33 := by decide
lemma count_prime_149 : Nat.count Nat.Prime 149 = 34 := by decide

lemma nth_prime_32 : Nat.nth Nat.Prime 32 = 137 := by
  have hP : Nat.Prime 137 := by decide
  rw [← count_prime_137]; exact Nat.nth_count hP

lemma nth_prime_33 : Nat.nth Nat.Prime 33 = 139 := by
  have hP : Nat.Prime 139 := by decide
  rw [← count_prime_139]; exact Nat.nth_count hP

lemma nth_prime_34 : Nat.nth Nat.Prime 34 = 149 := by
  have hP : Nat.Prime 149 := by decide
  rw [← count_prime_149]; exact Nat.nth_count hP

lemma primeN_33 : primeN 33 = 137 := by simpa [primeN] using nth_prime_32
lemma primeN_34 : primeN 34 = 139 := by simpa [primeN] using nth_prime_33
lemma primeN_35 : primeN 35 = 149 := by simpa [primeN] using nth_prime_34

lemma a_thirty_three : a 33 = 120 := by
  rw [a_of_ne_zero (by decide : 33 ≠ 0), primeN_33, primeN_34, primeN_35]

lemma count_prime_179 : Nat.count Nat.Prime 179 = 40 := by decide
lemma count_prime_181 : Nat.count Nat.Prime 181 = 41 := by decide
lemma count_prime_191 : Nat.count Nat.Prime 191 = 42 := by decide
lemma nth_prime_40 : Nat.nth Nat.Prime 40 = 179 := by
  have hP : Nat.Prime 179 := by decide
  rw [← count_prime_179]; exact Nat.nth_count hP
lemma nth_prime_41 : Nat.nth Nat.Prime 41 = 181 := by
  have hP : Nat.Prime 181 := by decide
  rw [← count_prime_181]; exact Nat.nth_count hP
lemma nth_prime_42 : Nat.nth Nat.Prime 42 = 191 := by
  have hP : Nat.Prime 191 := by decide
  rw [← count_prime_191]; exact Nat.nth_count hP
lemma primeN_41 : primeN 41 = 179 := by simpa [primeN] using nth_prime_40
lemma primeN_42 : primeN 42 = 181 := by simpa [primeN] using nth_prime_41
lemma primeN_43 : primeN 43 = 191 := by simpa [primeN] using nth_prime_42
lemma a_forty_one : a 41 = 120 := by
  rw [a_of_ne_zero (by decide : 41 ≠ 0), primeN_41, primeN_42, primeN_43]

lemma count_prime_239 : Nat.count Nat.Prime 239 = 51 := by decide
lemma count_prime_241 : Nat.count Nat.Prime 241 = 52 := by decide
lemma count_prime_251 : Nat.count Nat.Prime 251 = 53 := by decide
lemma nth_prime_51 : Nat.nth Nat.Prime 51 = 239 := by
  have hP : Nat.Prime 239 := by decide
  rw [← count_prime_239]; exact Nat.nth_count hP
lemma nth_prime_52 : Nat.nth Nat.Prime 52 = 241 := by
  have hP : Nat.Prime 241 := by decide
  rw [← count_prime_241]; exact Nat.nth_count hP
lemma nth_prime_53 : Nat.nth Nat.Prime 53 = 251 := by
  have hP : Nat.Prime 251 := by decide
  rw [← count_prime_251]; exact Nat.nth_count hP
lemma primeN_52 : primeN 52 = 239 := by simpa [primeN] using nth_prime_51
lemma primeN_53 : primeN 53 = 241 := by simpa [primeN] using nth_prime_52
lemma primeN_54 : primeN 54 = 251 := by simpa [primeN] using nth_prime_53
lemma a_fifty_two : a 52 = 120 := by
  rw [a_of_ne_zero (by decide : 52 ≠ 0), primeN_52, primeN_53, primeN_54]

lemma count_prime_281 : Nat.count Nat.Prime 281 = 59 := by decide
lemma count_prime_283 : Nat.count Nat.Prime 283 = 60 := by decide
lemma count_prime_293 : Nat.count Nat.Prime 293 = 61 := by decide
lemma nth_prime_59 : Nat.nth Nat.Prime 59 = 281 := by
  have hP : Nat.Prime 281 := by decide
  rw [← count_prime_281]; exact Nat.nth_count hP
lemma nth_prime_60 : Nat.nth Nat.Prime 60 = 283 := by
  have hP : Nat.Prime 283 := by decide
  rw [← count_prime_283]; exact Nat.nth_count hP
lemma nth_prime_61 : Nat.nth Nat.Prime 61 = 293 := by
  have hP : Nat.Prime 293 := by decide
  rw [← count_prime_293]; exact Nat.nth_count hP
lemma primeN_60 : primeN 60 = 281 := by simpa [primeN] using nth_prime_59
lemma primeN_61 : primeN 61 = 283 := by simpa [primeN] using nth_prime_60
lemma primeN_62 : primeN 62 = 293 := by simpa [primeN] using nth_prime_61
lemma a_sixty : a 60 = 120 := by
  rw [a_of_ne_zero (by decide : 60 ≠ 0), primeN_60, primeN_61, primeN_62]

lemma count_prime_307 : Nat.count Nat.Prime 307 = 62 := by decide
lemma nth_prime_62 : Nat.nth Nat.Prime 62 = 307 := by
  have hP : Nat.Prime 307 := by decide
  rw [← count_prime_307]; exact Nat.nth_count hP
lemma primeN_63 : primeN 63 = 307 := by simpa [primeN] using nth_prime_62

lemma a_sixty_one : a 61 = 29 := by
  rw [a_of_ne_zero (by decide : 61 ≠ 0), primeN_61, primeN_62, primeN_63]

lemma count_prime_317 : Nat.count Nat.Prime 317 = 65 := by decide
lemma count_prime_331 : Nat.count Nat.Prime 331 = 66 := by decide
lemma count_prime_337 : Nat.count Nat.Prime 337 = 67 := by decide
lemma nth_prime_65 : Nat.nth Nat.Prime 65 = 317 := by
  have hP : Nat.Prime 317 := by decide
  rw [← count_prime_317]; exact Nat.nth_count hP
lemma nth_prime_66 : Nat.nth Nat.Prime 66 = 331 := by
  have hP : Nat.Prime 331 := by decide
  rw [← count_prime_331]; exact Nat.nth_count hP
lemma nth_prime_67 : Nat.nth Nat.Prime 67 = 337 := by
  have hP : Nat.Prime 337 := by decide
  rw [← count_prime_337]; exact Nat.nth_count hP
lemma primeN_66 : primeN 66 = 317 := by simpa [primeN] using nth_prime_65
lemma primeN_67 : primeN 67 = 331 := by simpa [primeN] using nth_prime_66
lemma primeN_68 : primeN 68 = 337 := by simpa [primeN] using nth_prime_67
lemma a_sixty_six : a 66 = 120 := by
  rw [a_of_ne_zero (by decide : 66 ≠ 0), primeN_66, primeN_67, primeN_68]

lemma count_prime_347 : Nat.count Nat.Prime 347 = 68 := by decide
lemma count_prime_349 : Nat.count Nat.Prime 349 = 69 := by decide
lemma count_prime_353 : Nat.count Nat.Prime 353 = 70 := by decide
lemma nth_prime_68 : Nat.nth Nat.Prime 68 = 347 := by
  have hP : Nat.Prime 347 := by decide
  rw [← count_prime_347]; exact Nat.nth_count hP
lemma nth_prime_69 : Nat.nth Nat.Prime 69 = 349 := by
  have hP : Nat.Prime 349 := by decide
  rw [← count_prime_349]; exact Nat.nth_count hP
lemma nth_prime_70 : Nat.nth Nat.Prime 70 = 353 := by
  have hP : Nat.Prime 353 := by decide
  rw [← count_prime_353]; exact Nat.nth_count hP
lemma primeN_69 : primeN 69 = 347 := by simpa [primeN] using nth_prime_68
lemma primeN_70 : primeN 70 = 349 := by simpa [primeN] using nth_prime_69
lemma primeN_71 : primeN 71 = 353 := by simpa [primeN] using nth_prime_70

lemma count_prime_359 : Nat.count Nat.Prime 359 = 71 := by decide
lemma count_prime_367 : Nat.count Nat.Prime 367 = 72 := by decide
lemma count_prime_373 : Nat.count Nat.Prime 373 = 73 := by decide
lemma count_prime_379 : Nat.count Nat.Prime 379 = 74 := by decide
lemma count_prime_383 : Nat.count Nat.Prime 383 = 75 := by decide
lemma count_prime_389 : Nat.count Nat.Prime 389 = 76 := by decide
lemma count_prime_397 : Nat.count Nat.Prime 397 = 77 := by decide
lemma count_prime_401 : Nat.count Nat.Prime 401 = 78 := by decide
lemma count_prime_409 : Nat.count Nat.Prime 409 = 79 := by decide
lemma nth_prime_71 : Nat.nth Nat.Prime 71 = 359 := by
  have hP : Nat.Prime 359 := by decide
  rw [← count_prime_359]; exact Nat.nth_count hP
lemma nth_prime_72 : Nat.nth Nat.Prime 72 = 367 := by
  have hP : Nat.Prime 367 := by decide
  rw [← count_prime_367]; exact Nat.nth_count hP
lemma nth_prime_73 : Nat.nth Nat.Prime 73 = 373 := by
  have hP : Nat.Prime 373 := by decide
  rw [← count_prime_373]; exact Nat.nth_count hP
lemma nth_prime_74 : Nat.nth Nat.Prime 74 = 379 := by
  have hP : Nat.Prime 379 := by decide
  rw [← count_prime_379]; exact Nat.nth_count hP
lemma nth_prime_75 : Nat.nth Nat.Prime 75 = 383 := by
  have hP : Nat.Prime 383 := by decide
  rw [← count_prime_383]; exact Nat.nth_count hP
lemma nth_prime_76 : Nat.nth Nat.Prime 76 = 389 := by
  have hP : Nat.Prime 389 := by decide
  rw [← count_prime_389]; exact Nat.nth_count hP
lemma nth_prime_77 : Nat.nth Nat.Prime 77 = 397 := by
  have hP : Nat.Prime 397 := by decide
  rw [← count_prime_397]; exact Nat.nth_count hP
lemma nth_prime_78 : Nat.nth Nat.Prime 78 = 401 := by
  have hP : Nat.Prime 401 := by decide
  rw [← count_prime_401]; exact Nat.nth_count hP
lemma nth_prime_79 : Nat.nth Nat.Prime 79 = 409 := by
  have hP : Nat.Prime 409 := by decide
  rw [← count_prime_409]; exact Nat.nth_count hP
lemma primeN_72 : primeN 72 = 359 := by simpa [primeN] using nth_prime_71
lemma primeN_73 : primeN 73 = 367 := by simpa [primeN] using nth_prime_72
lemma primeN_74 : primeN 74 = 373 := by simpa [primeN] using nth_prime_73
lemma primeN_75 : primeN 75 = 379 := by simpa [primeN] using nth_prime_74
lemma primeN_76 : primeN 76 = 383 := by simpa [primeN] using nth_prime_75
lemma primeN_77 : primeN 77 = 389 := by simpa [primeN] using nth_prime_76
lemma primeN_78 : primeN 78 = 397 := by simpa [primeN] using nth_prime_77
lemma primeN_79 : primeN 79 = 401 := by simpa [primeN] using nth_prime_78
lemma primeN_80 : primeN 80 = 409 := by simpa [primeN] using nth_prime_79

lemma count_prime_419 : Nat.count Nat.Prime 419 = 80 := by decide
lemma count_prime_421 : Nat.count Nat.Prime 421 = 81 := by decide
lemma count_prime_431 : Nat.count Nat.Prime 431 = 82 := by decide
lemma nth_prime_80 : Nat.nth Nat.Prime 80 = 419 := by
  have hP : Nat.Prime 419 := by decide
  rw [← count_prime_419]; exact Nat.nth_count hP
lemma nth_prime_81 : Nat.nth Nat.Prime 81 = 421 := by
  have hP : Nat.Prime 421 := by decide
  rw [← count_prime_421]; exact Nat.nth_count hP
lemma nth_prime_82 : Nat.nth Nat.Prime 82 = 431 := by
  have hP : Nat.Prime 431 := by decide
  rw [← count_prime_431]; exact Nat.nth_count hP
lemma primeN_81 : primeN 81 = 419 := by simpa [primeN] using nth_prime_80
lemma primeN_82 : primeN 82 = 421 := by simpa [primeN] using nth_prime_81
lemma primeN_83 : primeN 83 = 431 := by simpa [primeN] using nth_prime_82
lemma a_eighty_one : a 81 = 120 := by
  rw [a_of_ne_zero (by decide : 81 ≠ 0), primeN_81, primeN_82, primeN_83]

lemma a_ne_zero {n : ℕ} (hn : 1 ≤ n) : a n ≠ 0 := by
  rw [a_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)]
  intro h
  have hdiv : primeN (n + 2) ∣ primeN n * primeN (n + 1) :=
    Nat.dvd_of_mod_eq_zero h
  have hpr : (primeN (n + 2)).Prime := primeN_prime (n + 2)
  rcases (Nat.Prime.dvd_mul hpr).mp hdiv with h1 | h2
  · have heq : primeN (n + 2) = primeN n :=
      (Nat.prime_dvd_prime_iff_eq hpr (primeN_prime n)).mp h1
    have hlt : primeN n < primeN (n + 2) := primeN_lt hn (by omega)
    exact Nat.ne_of_lt hlt heq.symm
  · have heq : primeN (n + 2) = primeN (n + 1) :=
      (Nat.prime_dvd_prime_iff_eq hpr (primeN_prime (n + 1))).mp h2
    have hlt : primeN (n + 1) < primeN (n + 2) := primeN_lt (by omega) (by omega)
    exact Nat.ne_of_lt hlt heq.symm

lemma count_a_one_le {x : ℕ} (hx : 33 ≤ x) : 1 ≤ count_a x 120 := by
  rw [count_a_eq_Icc]
  refine Finset.card_pos.mpr ⟨33, ?_⟩
  simp only [mem_filter, mem_Icc]
  exact ⟨⟨by decide, hx⟩, a_thirty_three⟩

lemma count_a_six_le {x : ℕ} (hx : 81 ≤ x) : 6 ≤ count_a x 120 := by
  rw [count_a_eq_Icc]
  classical
  have hs : ({33, 41, 52, 60, 66, 81} : Finset ℕ) ⊆
      (Icc 1 x).filter (fun n => a n = 120) := by
    intro n hn
    simp only [mem_insert, mem_singleton] at hn
    simp only [mem_filter, mem_Icc]
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨by decide, le_trans (by decide : 33 ≤ 81) hx⟩, a_thirty_three⟩
    · exact ⟨⟨by decide, le_trans (by decide : 41 ≤ 81) hx⟩, a_forty_one⟩
    · exact ⟨⟨by decide, le_trans (by decide : 52 ≤ 81) hx⟩, a_fifty_two⟩
    · exact ⟨⟨by decide, le_trans (by decide : 60 ≤ 81) hx⟩, a_sixty⟩
    · exact ⟨⟨by decide, le_trans (by decide : 66 ≤ 81) hx⟩, a_sixty_six⟩
    · exact ⟨⟨by decide, hx⟩, a_eighty_one⟩
  have hcard : ({33, 41, 52, 60, 66, 81} : Finset ℕ).card = 6 := by decide
  have := card_le_card hs
  omega

/-- The admissible even-even gap pairs producing unreduced value 120. -/
lemma gapProd_120_pairs {n : ℕ} (hn : 2 ≤ n) (h : gapProd n = 120) :
    (gap n, gap (n + 1)) = (2, 10) ∨
    (gap n, gap (n + 1)) = (14, 6) ∨
    (gap n, gap (n + 1)) = (26, 4) ∨
    (gap n, gap (n + 1)) = (58, 2) := by
  have hg2e : 2 ∣ gap (n + 1) := gap_even (by omega)
  have hg1e : 2 ∣ gap n := gap_even hn
  have hg2pos : 0 < gap (n + 1) := gap_pos (by omega)
  have hg1pos : 0 < gap n := gap_pos (by omega)
  -- gapProd n = (g1 + g2) * g2 = 120
  have hprod : (gap n + gap (n + 1)) * gap (n + 1) = 120 := h
  have hg2le : gap (n + 1) ≤ 10 := by
    have : gap (n + 1) * gap (n + 1) < 120 := by
      have : gap n + gap (n + 1) > gap (n + 1) := by omega
      nlinarith
    nlinarith
  have hg2 : gap (n + 1) = 2 ∨ gap (n + 1) = 4 ∨ gap (n + 1) = 6 ∨
      gap (n + 1) = 8 ∨ gap (n + 1) = 10 := by
    have : gap (n + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hg2e
    interval_cases gap (n + 1) <;> simp_all
  rcases hg2 with h2 | h2 | h2 | h2 | h2
  · have : gap n = 58 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · have : gap n = 26 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · have : gap n = 14 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · -- g2 = 8 ⇒ (g1+8)*8 = 120 ⇒ g1+8 = 15 ⇒ g1 = 7, not even
    have : gap n = 7 := by
      have := hprod
      simp [h2] at this
      omega
    have : 2 ∣ gap n := hg1e
    omega
  · have : gap n = 2 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]

/-- The admissible even-even gap pairs producing unreduced value 72. -/
lemma gapProd_72_pairs {n : ℕ} (hn : 2 ≤ n) (h : gapProd n = 72) :
    (gap n, gap (n + 1)) = (6, 6) ∨
    (gap n, gap (n + 1)) = (14, 4) ∨
    (gap n, gap (n + 1)) = (34, 2) := by
  have hg2e : 2 ∣ gap (n + 1) := gap_even (by omega)
  have hg1e : 2 ∣ gap n := gap_even hn
  have hprod : (gap n + gap (n + 1)) * gap (n + 1) = 72 := h
  have hg2 : gap (n + 1) = 2 ∨ gap (n + 1) = 4 ∨ gap (n + 1) = 6 ∨
      gap (n + 1) = 8 := by
    have : gap (n + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hg2e
    have hg2pos : 0 < gap (n + 1) := gap_pos (by omega)
    have hg2le : gap (n + 1) ≤ 8 := by
      have : gap (n + 1) * gap (n + 1) < 72 := by
        have : gap n + gap (n + 1) > gap (n + 1) := by
          have := gap_pos (by omega : 1 ≤ n)
          omega
        nlinarith
      nlinarith
    interval_cases gap (n + 1) <;> simp_all
  rcases hg2 with h2 | h2 | h2 | h2
  · have : gap n = 34 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · have : gap n = 14 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · have : gap n = 6 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · -- g2 = 8 ⇒ (g1+8)*8 = 72 ⇒ g1+8 = 9 ⇒ g1 = 1, not even
    have : gap n = 1 := by
      have := hprod
      simp [h2] at this
      omega
    have : 2 ∣ gap n := hg1e
    omega

/-- The admissible even-even gap pairs producing unreduced value 96. -/
lemma gapProd_96_pairs {n : ℕ} (hn : 2 ≤ n) (h : gapProd n = 96) :
    (gap n, gap (n + 1)) = (4, 8) ∨
    (gap n, gap (n + 1)) = (10, 6) ∨
    (gap n, gap (n + 1)) = (20, 4) ∨
    (gap n, gap (n + 1)) = (46, 2) := by
  have hg2e : 2 ∣ gap (n + 1) := gap_even (by omega)
  have hg1e : 2 ∣ gap n := gap_even hn
  have hprod : (gap n + gap (n + 1)) * gap (n + 1) = 96 := h
  have hg2pos : 0 < gap (n + 1) := gap_pos (by omega)
  have hg2le : gap (n + 1) ≤ 9 := by
    have : gap (n + 1) * gap (n + 1) < 96 := by
      have : gap n + gap (n + 1) > gap (n + 1) := by
        have := gap_pos (by omega : 1 ≤ n)
        omega
      nlinarith
    nlinarith
  have hg2 : gap (n + 1) = 2 ∨ gap (n + 1) = 4 ∨ gap (n + 1) = 6 ∨
      gap (n + 1) = 8 := by
    have : gap (n + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hg2e
    interval_cases gap (n + 1) <;> simp_all
  rcases hg2 with h2 | h2 | h2 | h2
  · have : gap n = 46 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · have : gap n = 20 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · have : gap n = 10 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · have : gap n = 4 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]

/-- The admissible even-even gap pairs producing unreduced value 24. -/
lemma gapProd_24_pairs {n : ℕ} (hn : 2 ≤ n) (h : gapProd n = 24) :
    (gap n, gap (n + 1)) = (2, 4) ∨
    (gap n, gap (n + 1)) = (10, 2) := by
  have hg2e : 2 ∣ gap (n + 1) := gap_even (by omega)
  have hg1e : 2 ∣ gap n := gap_even hn
  have hprod : (gap n + gap (n + 1)) * gap (n + 1) = 24 := h
  have hg2pos : 0 < gap (n + 1) := gap_pos (by omega)
  have hg2le : gap (n + 1) ≤ 4 := by
    have : gap (n + 1) * gap (n + 1) < 24 := by
      have : gap n + gap (n + 1) > gap (n + 1) := by
        have := gap_pos (by omega : 1 ≤ n)
        omega
      nlinarith
    nlinarith
  have hg2 : gap (n + 1) = 2 ∨ gap (n + 1) = 4 := by
    have : gap (n + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hg2e
    interval_cases gap (n + 1) <;> simp_all
  rcases hg2 with h2 | h2
  · have : gap n = 10 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · have : gap n = 2 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]

/-- The only even-even pair producing unreduced value 12 is `(4, 2)`. -/
lemma gapProd_12_pairs {n : ℕ} (hn : 2 ≤ n) (h : gapProd n = 12) :
    (gap n, gap (n + 1)) = (4, 2) := by
  have hg2e : 2 ∣ gap (n + 1) := gap_even (by omega)
  have hg1e : 2 ∣ gap n := gap_even hn
  have hprod : (gap n + gap (n + 1)) * gap (n + 1) = 12 := h
  have hg2pos : 0 < gap (n + 1) := gap_pos (by omega)
  have hg2le : gap (n + 1) ≤ 3 := by
    have : gap (n + 1) * gap (n + 1) < 12 := by
      have : gap n + gap (n + 1) > gap (n + 1) := by
        have := gap_pos (by omega : 1 ≤ n)
        omega
      nlinarith
    nlinarith
  have hg2 : gap (n + 1) = 2 := by
    have : gap (n + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hg2e
    interval_cases gap (n + 1) <;> simp_all
  have : gap n = 4 := by
    have := hprod
    simp [hg2] at this
    omega
  simp [this, hg2]

/-- The only even-even pair producing unreduced value 16 is `(6, 2)`. -/
lemma gapProd_16_pairs {n : ℕ} (hn : 2 ≤ n) (h : gapProd n = 16) :
    (gap n, gap (n + 1)) = (6, 2) := by
  have hg2e : 2 ∣ gap (n + 1) := gap_even (by omega)
  have hprod : (gap n + gap (n + 1)) * gap (n + 1) = 16 := h
  have hg2pos : 0 < gap (n + 1) := gap_pos (by omega)
  have hg2le : gap (n + 1) ≤ 3 := by
    have : gap (n + 1) * gap (n + 1) < 16 := by
      have : gap n + gap (n + 1) > gap (n + 1) := by
        have := gap_pos (by omega : 1 ≤ n)
        omega
      nlinarith
    nlinarith
  have hg2 : gap (n + 1) = 2 := by
    have : gap (n + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hg2e
    interval_cases gap (n + 1) <;> simp_all
  have : gap n = 6 := by
    have := hprod
    simp [hg2] at this
    omega
  simp [this, hg2]

/-- The only even-even pair producing unreduced value 28 is `(12, 2)`. -/
lemma gapProd_28_pairs {n : ℕ} (hn : 2 ≤ n) (h : gapProd n = 28) :
    (gap n, gap (n + 1)) = (12, 2) := by
  have hg2e : 2 ∣ gap (n + 1) := gap_even (by omega)
  have hg1e : 2 ∣ gap n := gap_even hn
  have hprod : (gap n + gap (n + 1)) * gap (n + 1) = 28 := h
  have hg2pos : 0 < gap (n + 1) := gap_pos (by omega)
  have hg2le : gap (n + 1) ≤ 5 := by
    have : gap (n + 1) * gap (n + 1) < 28 := by
      have : gap n + gap (n + 1) > gap (n + 1) := by
        have := gap_pos (by omega : 1 ≤ n)
        omega
      nlinarith
    nlinarith
  have hg2 : gap (n + 1) = 2 ∨ gap (n + 1) = 4 := by
    have : gap (n + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hg2e
    interval_cases gap (n + 1) <;> simp_all
  rcases hg2 with h2 | h2
  · have : gap n = 12 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · have := hprod
    simp [h2] at this
    omega

/-- The only even-even pair producing unreduced value 36 is `(16, 2)`. -/
lemma gapProd_36_pairs {n : ℕ} (hn : 2 ≤ n) (h : gapProd n = 36) :
    (gap n, gap (n + 1)) = (16, 2) := by
  have hg2e : 2 ∣ gap (n + 1) := gap_even (by omega)
  have hg1e : 2 ∣ gap n := gap_even hn
  have hprod : (gap n + gap (n + 1)) * gap (n + 1) = 36 := h
  have hg2pos : 0 < gap (n + 1) := gap_pos (by omega)
  have hg2le : gap (n + 1) ≤ 5 := by
    have : gap (n + 1) * gap (n + 1) < 36 := by
      have : gap n + gap (n + 1) > gap (n + 1) := by
        have := gap_pos (by omega : 1 ≤ n)
        omega
      nlinarith
    nlinarith
  have hg2 : gap (n + 1) = 2 ∨ gap (n + 1) = 4 := by
    have : gap (n + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hg2e
    interval_cases gap (n + 1) <;> simp_all
  rcases hg2 with h2 | h2
  · have : gap n = 16 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · have := hprod
    simp [h2] at this
    omega

/-- The admissible even-even gap pairs producing unreduced value 40. -/
lemma gapProd_40_pairs {n : ℕ} (hn : 2 ≤ n) (h : gapProd n = 40) :
    (gap n, gap (n + 1)) = (18, 2) ∨
    (gap n, gap (n + 1)) = (6, 4) := by
  have hg2e : 2 ∣ gap (n + 1) := gap_even (by omega)
  have hg1e : 2 ∣ gap n := gap_even hn
  have hprod : (gap n + gap (n + 1)) * gap (n + 1) = 40 := h
  have hg2pos : 0 < gap (n + 1) := gap_pos (by omega)
  have hg2le : gap (n + 1) ≤ 6 := by
    have : gap (n + 1) * gap (n + 1) < 40 := by
      have : gap n + gap (n + 1) > gap (n + 1) := by
        have := gap_pos (by omega : 1 ≤ n)
        omega
      nlinarith
    nlinarith
  have hg2 : gap (n + 1) = 2 ∨ gap (n + 1) = 4 ∨ gap (n + 1) = 6 := by
    have : gap (n + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hg2e
    interval_cases gap (n + 1) <;> simp_all
  rcases hg2 with h2 | h2 | h2
  · have : gap n = 18 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · have : gap n = 6 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · have := hprod
    simp [h2] at this
    omega

/-- The admissible even-even gap pairs producing unreduced value 48. -/
lemma gapProd_48_pairs {n : ℕ} (hn : 2 ≤ n) (h : gapProd n = 48) :
    (gap n, gap (n + 1)) = (22, 2) ∨
    (gap n, gap (n + 1)) = (8, 4) ∨
    (gap n, gap (n + 1)) = (2, 6) := by
  have hg2e : 2 ∣ gap (n + 1) := gap_even (by omega)
  have hg1e : 2 ∣ gap n := gap_even hn
  have hprod : (gap n + gap (n + 1)) * gap (n + 1) = 48 := h
  have hg2pos : 0 < gap (n + 1) := gap_pos (by omega)
  have hg2le : gap (n + 1) ≤ 6 := by
    have : gap (n + 1) * gap (n + 1) < 48 := by
      have : gap n + gap (n + 1) > gap (n + 1) := by
        have := gap_pos (by omega : 1 ≤ n)
        omega
      nlinarith
    nlinarith
  have hg2 : gap (n + 1) = 2 ∨ gap (n + 1) = 4 ∨ gap (n + 1) = 6 := by
    have : gap (n + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hg2e
    interval_cases gap (n + 1) <;> simp_all
  rcases hg2 with h2 | h2 | h2
  · have : gap n = 22 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · have : gap n = 8 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · have : gap n = 2 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]

/-- The admissible even-even gap pairs producing unreduced value 60. -/
lemma gapProd_60_pairs {n : ℕ} (hn : 2 ≤ n) (h : gapProd n = 60) :
    (gap n, gap (n + 1)) = (28, 2) ∨
    (gap n, gap (n + 1)) = (4, 6) := by
  have hg2e : 2 ∣ gap (n + 1) := gap_even (by omega)
  have hg1e : 2 ∣ gap n := gap_even hn
  have hprod : (gap n + gap (n + 1)) * gap (n + 1) = 60 := h
  have hg2pos : 0 < gap (n + 1) := gap_pos (by omega)
  have hg2le : gap (n + 1) ≤ 7 := by
    have : gap (n + 1) * gap (n + 1) < 60 := by
      have : gap n + gap (n + 1) > gap (n + 1) := by
        have := gap_pos (by omega : 1 ≤ n)
        omega
      nlinarith
    nlinarith
  have hg2 : gap (n + 1) = 2 ∨ gap (n + 1) = 4 ∨ gap (n + 1) = 6 := by
    have : gap (n + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hg2e
    interval_cases gap (n + 1) <;> simp_all
  rcases hg2 with h2 | h2 | h2
  · have : gap n = 28 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · have := hprod
    simp [h2] at this
    omega
  · have : gap n = 4 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]

/-- The admissible even-even gap pairs producing unreduced value 64. -/
lemma gapProd_64_pairs {n : ℕ} (hn : 2 ≤ n) (h : gapProd n = 64) :
    (gap n, gap (n + 1)) = (30, 2) ∨
    (gap n, gap (n + 1)) = (12, 4) := by
  have hg2e : 2 ∣ gap (n + 1) := gap_even (by omega)
  have hg1e : 2 ∣ gap n := gap_even hn
  have hprod : (gap n + gap (n + 1)) * gap (n + 1) = 64 := h
  have hg2pos : 0 < gap (n + 1) := gap_pos (by omega)
  have hg2le : gap (n + 1) ≤ 7 := by
    have : gap (n + 1) * gap (n + 1) < 64 := by
      have : gap n + gap (n + 1) > gap (n + 1) := by
        have := gap_pos (by omega : 1 ≤ n)
        omega
      nlinarith
    nlinarith
  have hg2 : gap (n + 1) = 2 ∨ gap (n + 1) = 4 ∨ gap (n + 1) = 6 := by
    have : gap (n + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hg2e
    interval_cases gap (n + 1) <;> simp_all
  rcases hg2 with h2 | h2 | h2
  · have : gap n = 30 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · have : gap n = 12 := by
      have := hprod
      simp [h2] at this
      omega
    simp [this, h2]
  · have := hprod
    simp [h2] at this
    omega

/-- Every unreduced value at `n ≥ 2` arises from a unique even-even gap pair
    with second gap strictly less than the square root of the value. -/
lemma gapProd_pair_spec {n v : ℕ} (hn : 2 ≤ n) (h : gapProd n = v) :
    ∃ g1 g2 : ℕ, 2 ∣ g1 ∧ 2 ∣ g2 ∧ 0 < g1 ∧ 0 < g2 ∧
      gap n = g1 ∧ gap (n + 1) = g2 ∧ (g1 + g2) * g2 = v ∧ g2 * g2 < v := by
  have hg1e : 2 ∣ gap n := gap_even hn
  have hg2e : 2 ∣ gap (n + 1) := gap_even (by omega)
  have hg1p : 0 < gap n := gap_pos (by omega)
  have hg2p : 0 < gap (n + 1) := gap_pos (by omega)
  refine ⟨gap n, gap (n + 1), hg1e, hg2e, hg1p, hg2p, rfl, rfl, h, ?_⟩
  have : gap n + gap (n + 1) > gap (n + 1) := by omega
  have hprod : (gap n + gap (n + 1)) * gap (n + 1) = v := h
  nlinarith

lemma count_a_pos_of_mem {x v n : ℕ} (hn : n ∈ Icc 1 x) (ha : a n = v) :
    0 < count_a x v := by
  rw [count_a_eq_Icc]
  exact Finset.card_pos.mpr ⟨n, mem_filter.mpr ⟨hn, ha⟩⟩

/-- `n` contributes the unreduced value `v` (no modular wrap). -/
def is_nowrap_pattern (n v : ℕ) : Prop :=
  2 ≤ n ∧ gapProd n = v ∧ gapProd n < primeN (n + 2)

lemma a_eq_of_nowrap_pattern {n v : ℕ} (h : is_nowrap_pattern n v) : a n = v := by
  obtain ⟨hn, hgp, hlt⟩ := h
  have : a n = gapProd n := a_eq_gapProd (by omega) hlt
  exact this.trans hgp

lemma count_a_ge_nowrap (x v : ℕ) :
    ((Icc 2 x).filter (fun n => is_nowrap_pattern n v)).card ≤ count_a x v := by
  classical
  rw [count_a_eq_Icc]
  refine card_le_card ?_
  intro n hn
  simp only [mem_filter, mem_Icc] at hn ⊢
  obtain ⟨⟨h2, hx⟩, hpat⟩ := hn
  exact ⟨⟨by omega, hx⟩, a_eq_of_nowrap_pattern hpat⟩

lemma ten_pow_nine : 10 ^ 9 = 1000000000 := by decide

lemma thirty_three_lt_ten_pow_nine : 33 < 10 ^ 9 := by
  rw [ten_pow_nine]; decide

lemma eighty_one_lt_ten_pow_nine : 81 < 10 ^ 9 := by
  rw [ten_pow_nine]; decide

/-- `a n` wraps when the unreduced gap product is at least the next prime. -/
def wraps (n : ℕ) : Prop := 1 ≤ n ∧ ¬ gapProd n < primeN (n + 2)

lemma wraps_iff {n : ℕ} (hn : 1 ≤ n) :
    wraps n ↔ primeN (n + 2) ≤ gapProd n := by
  unfold wraps gapProd
  constructor
  · intro h
    have : ¬ (gap n + gap (n + 1)) * gap (n + 1) < primeN (n + 2) := h.2
    omega
  · intro h
    exact ⟨hn, not_lt.mpr h⟩

lemma a_eq_gapProd_or_wrap {n : ℕ} (hn : 1 ≤ n) :
    a n = gapProd n ∨ wraps n := by
  by_cases h : gapProd n < primeN (n + 2)
  · exact Or.inl (a_eq_gapProd hn h)
  · exact Or.inr ⟨hn, h⟩

lemma gap_one : gap 1 = 1 := by simp [gap, primeN_one, primeN_two]
lemma gap_two : gap 2 = 2 := by simp [gap, primeN_two, primeN_three]
lemma gapProd_one : gapProd 1 = 6 := by simp [gapProd, gap_one, gap_two]

lemma wraps_one : wraps 1 := by
  refine ⟨le_rfl, ?_⟩
  simp [gapProd_one, primeN_three]

lemma wraps_sixty_one : wraps 61 := by
  refine ⟨by decide, ?_⟩
  have hgp : gapProd 61 = 336 := by
    simp [gapProd, gap, primeN_61, primeN_62, primeN_63]
  have : ¬ 336 < 307 := by decide
  simp [hgp, primeN_63, this]

lemma primeN_six : primeN 6 = 13 :=
  primeN_eq_nth_count (by decide) (by decide)
lemma primeN_seven : primeN 7 = 17 :=
  primeN_eq_nth_count (by decide) (by decide)
lemma primeN_eight : primeN 8 = 19 :=
  primeN_eq_nth_count (by decide) (by decide)
lemma primeN_nine : primeN 9 = 23 :=
  primeN_eq_nth_count (by decide) (by decide)
lemma primeN_ten : primeN 10 = 29 :=
  primeN_eq_nth_count (by decide) (by decide)
lemma primeN_eleven : primeN 11 = 31 :=
  primeN_eq_nth_count (by decide) (by decide)
lemma primeN_twelve : primeN 12 = 37 :=
  primeN_eq_nth_count (by decide) (by decide)

lemma a_five : a 5 = 7 := by
  rw [a_of_ne_zero (by decide)]
  simp [primeN_five, primeN_six, primeN_seven]

lemma a_seven : a 7 = 1 := by
  rw [a_of_ne_zero (by decide)]
  simp [primeN_seven, primeN_eight, primeN_nine]

lemma a_eight : a 8 = 2 := by
  rw [a_of_ne_zero (by decide)]
  simp [primeN_eight, primeN_nine, primeN_ten]

lemma a_ten : a 10 = 11 := by
  rw [a_of_ne_zero (by decide)]
  simp [primeN_ten, primeN_eleven, primeN_twelve]

lemma wraps_two : wraps 2 := by
  refine ⟨by decide, ?_⟩
  simp [gapProd, gap, primeN_two, primeN_three, primeN_four]

lemma wraps_three : wraps 3 := by
  refine ⟨by decide, ?_⟩
  simp [gapProd, gap, primeN_three, primeN_four, primeN_five]

lemma wraps_five : wraps 5 := by
  refine ⟨by decide, ?_⟩
  simp [gapProd, gap, primeN_five, primeN_six, primeN_seven]

lemma wraps_seven : wraps 7 := by
  refine ⟨by decide, ?_⟩
  simp [gapProd, gap, primeN_seven, primeN_eight, primeN_nine]

lemma wraps_eight : wraps 8 := by
  refine ⟨by decide, ?_⟩
  simp [gapProd, gap, primeN_eight, primeN_nine, primeN_ten]

lemma wraps_ten : wraps 10 := by
  refine ⟨by decide, ?_⟩
  simp [gapProd, gap, primeN_ten, primeN_eleven, primeN_twelve]

lemma primeN_fourteen : primeN 14 = 43 :=
  primeN_eq_nth_count (by decide) (by decide)
lemma primeN_fifteen : primeN 15 = 47 :=
  primeN_eq_nth_count (by decide) (by decide)
lemma primeN_sixteen : primeN 16 = 53 :=
  primeN_eq_nth_count (by decide) (by decide)
lemma primeN_seventeen : primeN 17 = 59 :=
  primeN_eq_nth_count (by decide) (by decide)

lemma a_fourteen : a 14 = 7 := by
  rw [a_of_ne_zero (by decide)]
  simp [primeN_fourteen, primeN_fifteen, primeN_sixteen]

lemma a_fifteen : a 15 = 13 := by
  rw [a_of_ne_zero (by decide)]
  simp [primeN_fifteen, primeN_sixteen, primeN_seventeen]

lemma wraps_fourteen : wraps 14 := by
  refine ⟨by decide, ?_⟩
  simp [gapProd, gap, primeN_fourteen, primeN_fifteen, primeN_sixteen]

lemma wraps_fifteen : wraps 15 := by
  refine ⟨by decide, ?_⟩
  simp [gapProd, gap, primeN_fifteen, primeN_sixteen, primeN_seventeen]

lemma primeN_twenty_three : primeN 23 = 83 :=
  primeN_eq_nth_count (by decide) (by decide)
lemma primeN_twenty_four : primeN 24 = 89 :=
  primeN_eq_nth_count (by decide) (by decide)
lemma primeN_twenty_five : primeN 25 = 97 :=
  primeN_eq_nth_count (by decide) (by decide)
lemma primeN_twenty_nine : primeN 29 = 109 :=
  primeN_eq_nth_count (by decide) (by decide)
lemma primeN_thirty : primeN 30 = 113 :=
  primeN_eq_nth_count (by decide) (by decide)
lemma primeN_thirty_one : primeN 31 = 127 :=
  primeN_eq_nth_count (by decide) (by decide)

lemma a_twenty_three : a 23 = 15 := by
  rw [a_of_ne_zero (by decide)]
  simp [primeN_twenty_three, primeN_twenty_four, primeN_twenty_five]

lemma a_twenty_nine : a 29 = 125 := by
  rw [a_of_ne_zero (by decide)]
  simp [primeN_twenty_nine, primeN_thirty, primeN_thirty_one]

lemma wraps_twenty_three : wraps 23 := by
  refine ⟨by decide, ?_⟩
  simp [gapProd, gap, primeN_twenty_three, primeN_twenty_four, primeN_twenty_five]

lemma wraps_twenty_nine : wraps 29 := by
  refine ⟨by decide, ?_⟩
  simp [gapProd, gap, primeN_twenty_nine, primeN_thirty, primeN_thirty_one]

lemma primeN_forty_six : primeN 46 = 199 :=
  primeN_eq_nth_count (by decide) (by decide)
lemma primeN_forty_seven : primeN 47 = 211 :=
  primeN_eq_nth_count (by decide) (by decide)
lemma primeN_forty_eight : primeN 48 = 223 :=
  primeN_eq_nth_count (by decide) (by decide)

lemma a_forty_six : a 46 = 65 := by
  rw [a_of_ne_zero (by decide)]
  simp [primeN_forty_six, primeN_forty_seven, primeN_forty_eight]

lemma wraps_forty_six : wraps 46 := by
  refine ⟨by decide, ?_⟩
  simp [gapProd, gap, primeN_forty_six, primeN_forty_seven, primeN_forty_eight]

/-- The 13 known wrap indices. -/
lemma wraps_of_known :
    wraps 1 ∧ wraps 2 ∧ wraps 3 ∧ wraps 5 ∧ wraps 7 ∧ wraps 8 ∧
    wraps 10 ∧ wraps 14 ∧ wraps 15 ∧ wraps 23 ∧ wraps 29 ∧
    wraps 46 ∧ wraps 61 :=
  ⟨wraps_one, wraps_two, wraps_three, wraps_five, wraps_seven, wraps_eight,
   wraps_ten, wraps_fourteen, wraps_fifteen, wraps_twenty_three,
   wraps_twenty_nine, wraps_forty_six, wraps_sixty_one⟩

lemma primeN_thirteen : primeN 13 = 41 :=
  primeN_eq_nth_count (by decide) (by decide)

lemma not_wraps_four : ¬ wraps 4 := by
  intro h
  have := (wraps_iff (by decide : 1 ≤ 4)).mp h
  simp [gapProd, gap, primeN_four, primeN_five, primeN_six] at this

lemma not_wraps_six : ¬ wraps 6 := by
  intro h
  have := (wraps_iff (by decide : 1 ≤ 6)).mp h
  simp [gapProd, gap, primeN_six, primeN_seven, primeN_eight] at this

lemma not_wraps_nine : ¬ wraps 9 := by
  intro h
  have := (wraps_iff (by decide : 1 ≤ 9)).mp h
  simp [gapProd, gap, primeN_nine, primeN_ten, primeN_eleven] at this

lemma not_wraps_eleven : ¬ wraps 11 := by
  intro h
  have := (wraps_iff (by decide : 1 ≤ 11)).mp h
  simp [gapProd, gap, primeN_eleven, primeN_twelve, primeN_thirteen] at this

lemma not_wraps_twelve : ¬ wraps 12 := by
  intro h
  have := (wraps_iff (by decide : 1 ≤ 12)).mp h
  simp [gapProd, gap, primeN_twelve, primeN_thirteen, primeN_fourteen] at this

lemma not_wraps_thirteen : ¬ wraps 13 := by
  intro h
  have := (wraps_iff (by decide : 1 ≤ 13)).mp h
  simp [gapProd, gap, primeN_thirteen, primeN_fourteen, primeN_fifteen] at this

/-- Known wrap values: the only `a n` produced by the 13 wraps. -/
lemma wrap_value_one : a 1 = 1 := a_one
lemma wrap_value_two : a 2 = 1 := a_two
lemma wrap_value_three : a 3 = 2 := a_three
lemma wrap_value_five : a 5 = 7 := a_five
lemma wrap_value_seven : a 7 = 1 := a_seven
lemma wrap_value_eight : a 8 = 2 := a_eight
lemma wrap_value_ten : a 10 = 11 := a_ten
lemma wrap_value_fourteen : a 14 = 7 := a_fourteen
lemma wrap_value_fifteen : a 15 = 13 := a_fifteen
lemma wrap_value_twenty_three : a 23 = 15 := a_twenty_three
lemma wrap_value_twenty_nine : a 29 = 125 := a_twenty_nine
lemma wrap_value_forty_six : a 46 = 65 := a_forty_six
lemma wrap_value_sixty_one : a 61 = 29 := a_sixty_one

lemma wraps_iff_le_fifteen {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 15) :
    wraps n ↔ n ∈ ({1, 2, 3, 5, 7, 8, 10, 14, 15} : Finset ℕ) := by
  constructor
  · intro hw
    interval_cases n
    · simp
    · simp
    · simp
    · exact (not_wraps_four hw).elim
    · simp
    · exact (not_wraps_six hw).elim
    · simp
    · simp
    · exact (not_wraps_nine hw).elim
    · simp
    · exact (not_wraps_eleven hw).elim
    · exact (not_wraps_twelve hw).elim
    · exact (not_wraps_thirteen hw).elim
    · simp
    · simp
  · intro h
    simp only [mem_insert, mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact wraps_one
    · exact wraps_two
    · exact wraps_three
    · exact wraps_five
    · exact wraps_seven
    · exact wraps_eight
    · exact wraps_ten
    · exact wraps_fourteen
    · exact wraps_fifteen


/- ### Computable prime table below 320, used to finish the wrap census up to `n = 61`. -/

def primesLT (N : ℕ) : List ℕ := (List.range N).filter Nat.Prime

lemma mem_primesLT_iff {N p : ℕ} : p ∈ primesLT N ↔ p.Prime ∧ p < N := by
  simp [primesLT, List.mem_filter, List.mem_range, and_comm]

lemma length_primesLT (N : ℕ) : (primesLT N).length = Nat.count Nat.Prime N := by
  simp [primesLT, Nat.count_eq_card_filter_range]
  rfl

lemma sortedLT_primesLT (N : ℕ) : (primesLT N).SortedLT := by
  simpa [primesLT] using (List.sortedLT_range N).pairwise.filter Nat.Prime |>.sortedLT

lemma primesLT_get_lt {N i j : ℕ} (hi : i < (primesLT N).length)
    (hj : j < (primesLT N).length) (hij : i < j) :
    (primesLT N)[i] < (primesLT N)[j] :=
  (sortedLT_primesLT N).getElem_lt_getElem_of_lt hij

lemma primesLT_get_prime {N k : ℕ} (hk : k < (primesLT N).length) :
    ((primesLT N)[k]).Prime :=
  (mem_primesLT_iff.mp (List.getElem_mem hk)).1

lemma primesLT_get_lt_N {N k : ℕ} (hk : k < (primesLT N).length) :
    (primesLT N)[k] < N :=
  (mem_primesLT_iff.mp (List.getElem_mem hk)).2

lemma count_primesLT_get {N k : ℕ} (hk : k < (primesLT N).length) :
    Nat.count Nat.Prime (primesLT N)[k] = k := by
  rw [Nat.count_eq_card_filter_range]
  refine Finset.card_eq_of_bijective
    (fun i (hi : i < k) => (primesLT N)[i]'(lt_trans hi hk)) ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_range] at hx
    obtain ⟨hxlt, hxP⟩ := hx
    have hxN : x < N := lt_trans hxlt (primesLT_get_lt_N hk)
    have hmem : x ∈ primesLT N := mem_primesLT_iff.mpr ⟨hxP, hxN⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
    have hik : i < k := by
      by_contra hge
      have : k ≤ i := Nat.le_of_not_gt hge
      rcases eq_or_lt_of_le this with rfl | hlt
      · exact lt_irrefl _ hxlt
      · exact lt_asymm hxlt (primesLT_get_lt hk hi hlt)
    exact ⟨i, hik, rfl⟩
  · intro i hi
    simp only [mem_filter, mem_range]
    exact ⟨primesLT_get_lt (lt_trans hi hk) hk hi, primesLT_get_prime (lt_trans hi hk)⟩
  · intro i j hi hj hij
    have hsm := (sortedLT_primesLT N).strictMono_get
    have : (⟨i, lt_trans hi hk⟩ : Fin _) = ⟨j, lt_trans hj hk⟩ :=
      hsm.injective (by simpa using hij)
    exact Fin.mk.inj this

lemma nth_prime_eq_primesLT_get {N k : ℕ} (hk : k < (primesLT N).length) :
    Nat.nth Nat.Prime k = (primesLT N)[k] := by
  have hp : ((primesLT N)[k]).Prime := primesLT_get_prime hk
  have hcnt : Nat.count Nat.Prime (primesLT N)[k] = k := count_primesLT_get hk
  have := Nat.nth_count hp
  rwa [hcnt] at this

lemma primesLT_320_length : (primesLT 320).length = 66 := by decide

lemma get_primesLT_320 (k val : ℕ) (hk : k < 66)
    (hval : (primesLT 320)[k]'(by
      have := primesLT_320_length
      omega) = val) :
    Nat.nth Nat.Prime k = val := by
  have hk' : k < (primesLT 320).length := by
    have := primesLT_320_length
    omega
  rw [nth_prime_eq_primesLT_get hk']
  exact hval

lemma primeN_18 : primeN 18 = 61 := by
  simp only [primeN]; exact get_primesLT_320 17 61 (by decide) (by decide)
lemma primeN_19 : primeN 19 = 67 := by
  simp only [primeN]; exact get_primesLT_320 18 67 (by decide) (by decide)
lemma primeN_20 : primeN 20 = 71 := by
  simp only [primeN]; exact get_primesLT_320 19 71 (by decide) (by decide)
lemma primeN_21 : primeN 21 = 73 := by
  simp only [primeN]; exact get_primesLT_320 20 73 (by decide) (by decide)
lemma primeN_22 : primeN 22 = 79 := by
  simp only [primeN]; exact get_primesLT_320 21 79 (by decide) (by decide)
lemma primeN_26 : primeN 26 = 101 := by
  simp only [primeN]; exact get_primesLT_320 25 101 (by decide) (by decide)
lemma primeN_27 : primeN 27 = 103 := by
  simp only [primeN]; exact get_primesLT_320 26 103 (by decide) (by decide)
lemma primeN_28 : primeN 28 = 107 := by
  simp only [primeN]; exact get_primesLT_320 27 107 (by decide) (by decide)
lemma primeN_32 : primeN 32 = 131 := by
  simp only [primeN]; exact get_primesLT_320 31 131 (by decide) (by decide)
lemma primeN_36 : primeN 36 = 151 := by
  simp only [primeN]; exact get_primesLT_320 35 151 (by decide) (by decide)
lemma primeN_37 : primeN 37 = 157 := by
  simp only [primeN]; exact get_primesLT_320 36 157 (by decide) (by decide)
lemma primeN_38 : primeN 38 = 163 := by
  simp only [primeN]; exact get_primesLT_320 37 163 (by decide) (by decide)
lemma primeN_39 : primeN 39 = 167 := by
  simp only [primeN]; exact get_primesLT_320 38 167 (by decide) (by decide)
lemma primeN_40 : primeN 40 = 173 := by
  simp only [primeN]; exact get_primesLT_320 39 173 (by decide) (by decide)
lemma primeN_44 : primeN 44 = 193 := by
  simp only [primeN]; exact get_primesLT_320 43 193 (by decide) (by decide)
lemma primeN_45 : primeN 45 = 197 := by
  simp only [primeN]; exact get_primesLT_320 44 197 (by decide) (by decide)
lemma primeN_49 : primeN 49 = 227 := by
  simp only [primeN]; exact get_primesLT_320 48 227 (by decide) (by decide)
lemma primeN_50 : primeN 50 = 229 := by
  simp only [primeN]; exact get_primesLT_320 49 229 (by decide) (by decide)
lemma primeN_51 : primeN 51 = 233 := by
  simp only [primeN]; exact get_primesLT_320 50 233 (by decide) (by decide)
lemma primeN_55 : primeN 55 = 257 := by
  simp only [primeN]; exact get_primesLT_320 54 257 (by decide) (by decide)
lemma primeN_56 : primeN 56 = 263 := by
  simp only [primeN]; exact get_primesLT_320 55 263 (by decide) (by decide)
lemma primeN_57 : primeN 57 = 269 := by
  simp only [primeN]; exact get_primesLT_320 56 269 (by decide) (by decide)
lemma primeN_58 : primeN 58 = 271 := by
  simp only [primeN]; exact get_primesLT_320 57 271 (by decide) (by decide)
lemma primeN_59 : primeN 59 = 277 := by
  simp only [primeN]; exact get_primesLT_320 58 277 (by decide) (by decide)

lemma not_wraps_of_primes {n : ℕ} (hn : 1 ≤ n)
    (h : ¬ primeN (n + 2) ≤ (primeN (n + 2) - primeN n) * (primeN (n + 2) - primeN (n + 1))) :
    ¬ wraps n := by
  intro hw
  have hle : primeN (n + 2) ≤ gapProd n := (wraps_iff hn).mp hw
  have hspan : primeN (n + 2) - primeN n = gap n + gap (n + 1) := two_step_sub hn
  have hg2 : primeN (n + 2) - primeN (n + 1) = gap (n + 1) := rfl
  unfold gapProd at hle
  rw [← hspan, ← hg2] at hle
  exact h hle

lemma not_wraps_16 : ¬ wraps 16 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_sixteen, primeN_seventeen, primeN_18]
lemma not_wraps_17 : ¬ wraps 17 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_seventeen, primeN_18, primeN_19]
lemma not_wraps_18 : ¬ wraps 18 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_18, primeN_19, primeN_20]
lemma not_wraps_19 : ¬ wraps 19 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_19, primeN_20, primeN_21]
lemma not_wraps_20 : ¬ wraps 20 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_20, primeN_21, primeN_22]
lemma not_wraps_21 : ¬ wraps 21 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_21, primeN_22, primeN_twenty_three]
lemma not_wraps_22 : ¬ wraps 22 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_22, primeN_twenty_three, primeN_twenty_four]
lemma not_wraps_24 : ¬ wraps 24 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_twenty_four, primeN_twenty_five, primeN_26]
lemma not_wraps_25 : ¬ wraps 25 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_twenty_five, primeN_26, primeN_27]
lemma not_wraps_26 : ¬ wraps 26 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_26, primeN_27, primeN_28]
lemma not_wraps_27 : ¬ wraps 27 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_27, primeN_28, primeN_twenty_nine]
lemma not_wraps_28 : ¬ wraps 28 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_28, primeN_twenty_nine, primeN_thirty]
lemma not_wraps_30 : ¬ wraps 30 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_thirty, primeN_thirty_one, primeN_32]
lemma not_wraps_31 : ¬ wraps 31 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_thirty_one, primeN_32, primeN_33]
lemma not_wraps_32 : ¬ wraps 32 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_32, primeN_33, primeN_34]
lemma not_wraps_34 : ¬ wraps 34 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_34, primeN_35, primeN_36]
lemma not_wraps_35 : ¬ wraps 35 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_35, primeN_36, primeN_37]
lemma not_wraps_36 : ¬ wraps 36 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_36, primeN_37, primeN_38]
lemma not_wraps_37 : ¬ wraps 37 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_37, primeN_38, primeN_39]
lemma not_wraps_38 : ¬ wraps 38 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_38, primeN_39, primeN_40]
lemma not_wraps_39 : ¬ wraps 39 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_39, primeN_40, primeN_41]
lemma not_wraps_40 : ¬ wraps 40 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_40, primeN_41, primeN_42]
lemma not_wraps_42 : ¬ wraps 42 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_42, primeN_43, primeN_44]
lemma not_wraps_43 : ¬ wraps 43 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_43, primeN_44, primeN_45]
lemma not_wraps_44 : ¬ wraps 44 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_44, primeN_45, primeN_forty_six]
lemma not_wraps_45 : ¬ wraps 45 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_45, primeN_forty_six, primeN_forty_seven]
lemma not_wraps_47 : ¬ wraps 47 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_forty_seven, primeN_forty_eight, primeN_49]
lemma not_wraps_48 : ¬ wraps 48 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_forty_eight, primeN_49, primeN_50]
lemma not_wraps_49 : ¬ wraps 49 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_49, primeN_50, primeN_51]
lemma not_wraps_50 : ¬ wraps 50 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_50, primeN_51, primeN_52]
lemma not_wraps_51 : ¬ wraps 51 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_51, primeN_52, primeN_53]
lemma not_wraps_53 : ¬ wraps 53 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_53, primeN_54, primeN_55]
lemma not_wraps_54 : ¬ wraps 54 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_54, primeN_55, primeN_56]
lemma not_wraps_55 : ¬ wraps 55 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_55, primeN_56, primeN_57]
lemma not_wraps_56 : ¬ wraps 56 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_56, primeN_57, primeN_58]
lemma not_wraps_57 : ¬ wraps 57 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_57, primeN_58, primeN_59]
lemma not_wraps_58 : ¬ wraps 58 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_58, primeN_59, primeN_60]
lemma not_wraps_59 : ¬ wraps 59 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_59, primeN_60, primeN_61]
lemma not_wraps_62 : ¬ wraps 62 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_62, primeN_63]
  -- need primeN 64
  have : primeN 64 = 311 := by
    simp only [primeN]; exact get_primesLT_320 63 311 (by decide) (by decide)
  simp [this]

-- We still need primeN 64 and a few more for n=33,41,52,60 which are wraps already.
-- n=33 is a 120, not a wrap. not_wraps_33:
lemma primeN_64 : primeN 64 = 311 := by
  simp only [primeN]; exact get_primesLT_320 63 311 (by decide) (by decide)
lemma primeN_65 : primeN 65 = 313 := by
  simp only [primeN]; exact get_primesLT_320 64 313 (by decide) (by decide)

lemma not_wraps_63 : ¬ wraps 63 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_63, primeN_64, primeN_65]
lemma not_wraps_64 : ¬ wraps 64 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_64, primeN_65, primeN_66]
lemma not_wraps_65 : ¬ wraps 65 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_65, primeN_66, primeN_67]

lemma not_wraps_66 : ¬ wraps 66 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_66, primeN_67, primeN_68]
lemma not_wraps_67 : ¬ wraps 67 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_67, primeN_68, primeN_69]
lemma not_wraps_68 : ¬ wraps 68 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_68, primeN_69, primeN_70]
lemma not_wraps_69 : ¬ wraps 69 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_69, primeN_70, primeN_71]
lemma not_wraps_70 : ¬ wraps 70 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_70, primeN_71, primeN_72]
lemma not_wraps_71 : ¬ wraps 71 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_71, primeN_72, primeN_73]
lemma not_wraps_72 : ¬ wraps 72 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_72, primeN_73, primeN_74]
lemma not_wraps_73 : ¬ wraps 73 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_73, primeN_74, primeN_75]
lemma not_wraps_74 : ¬ wraps 74 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_74, primeN_75, primeN_76]
lemma not_wraps_75 : ¬ wraps 75 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_75, primeN_76, primeN_77]
lemma not_wraps_76 : ¬ wraps 76 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_76, primeN_77, primeN_78]
lemma not_wraps_77 : ¬ wraps 77 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_77, primeN_78, primeN_79]
lemma not_wraps_78 : ¬ wraps 78 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_78, primeN_79, primeN_80]
lemma not_wraps_79 : ¬ wraps 79 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_79, primeN_80, primeN_81]
lemma not_wraps_80 : ¬ wraps 80 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_80, primeN_81, primeN_82]

lemma not_wraps_81 : ¬ wraps 81 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_81, primeN_82, primeN_83]

lemma not_wraps_33 : ¬ wraps 33 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_33, primeN_34, primeN_35]
lemma not_wraps_41 : ¬ wraps 41 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_41, primeN_42, primeN_43]
lemma not_wraps_52 : ¬ wraps 52 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_52, primeN_53, primeN_54]
lemma not_wraps_60 : ¬ wraps 60 := by
  refine not_wraps_of_primes (by decide) ?_
  simp [primeN_60, primeN_61, primeN_62]

/-- Complete wrap census on `1 ≤ n ≤ 61`. -/
lemma wraps_iff_le_sixty_one {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 61) :
    wraps n ↔ n ∈ ({1, 2, 3, 5, 7, 8, 10, 14, 15, 23, 29, 46, 61} : Finset ℕ) := by
  constructor
  · intro hw
    interval_cases n
    · simp
    · simp
    · simp
    · exact (not_wraps_four hw).elim
    · simp
    · exact (not_wraps_six hw).elim
    · simp
    · simp
    · exact (not_wraps_nine hw).elim
    · simp
    · exact (not_wraps_eleven hw).elim
    · exact (not_wraps_twelve hw).elim
    · exact (not_wraps_thirteen hw).elim
    · simp
    · simp
    · exact (not_wraps_16 hw).elim
    · exact (not_wraps_17 hw).elim
    · exact (not_wraps_18 hw).elim
    · exact (not_wraps_19 hw).elim
    · exact (not_wraps_20 hw).elim
    · exact (not_wraps_21 hw).elim
    · exact (not_wraps_22 hw).elim
    · simp
    · exact (not_wraps_24 hw).elim
    · exact (not_wraps_25 hw).elim
    · exact (not_wraps_26 hw).elim
    · exact (not_wraps_27 hw).elim
    · exact (not_wraps_28 hw).elim
    · simp
    · exact (not_wraps_30 hw).elim
    · exact (not_wraps_31 hw).elim
    · exact (not_wraps_32 hw).elim
    · exact (not_wraps_33 hw).elim
    · exact (not_wraps_34 hw).elim
    · exact (not_wraps_35 hw).elim
    · exact (not_wraps_36 hw).elim
    · exact (not_wraps_37 hw).elim
    · exact (not_wraps_38 hw).elim
    · exact (not_wraps_39 hw).elim
    · exact (not_wraps_40 hw).elim
    · exact (not_wraps_41 hw).elim
    · exact (not_wraps_42 hw).elim
    · exact (not_wraps_43 hw).elim
    · exact (not_wraps_44 hw).elim
    · exact (not_wraps_45 hw).elim
    · simp
    · exact (not_wraps_47 hw).elim
    · exact (not_wraps_48 hw).elim
    · exact (not_wraps_49 hw).elim
    · exact (not_wraps_50 hw).elim
    · exact (not_wraps_51 hw).elim
    · exact (not_wraps_52 hw).elim
    · exact (not_wraps_53 hw).elim
    · exact (not_wraps_54 hw).elim
    · exact (not_wraps_55 hw).elim
    · exact (not_wraps_56 hw).elim
    · exact (not_wraps_57 hw).elim
    · exact (not_wraps_58 hw).elim
    · exact (not_wraps_59 hw).elim
    · exact (not_wraps_60 hw).elim
    · simp
  · intro h
    simp only [mem_insert, mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact wraps_one
    · exact wraps_two
    · exact wraps_three
    · exact wraps_five
    · exact wraps_seven
    · exact wraps_eight
    · exact wraps_ten
    · exact wraps_fourteen
    · exact wraps_fifteen
    · exact wraps_twenty_three
    · exact wraps_twenty_nine
    · exact wraps_forty_six
    · exact wraps_sixty_one

/-- Known wrap values on `n ≤ 61`. -/
lemma wrap_a_mem {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 61) (hw : wraps n) :
    a n ∈ ({1, 2, 7, 11, 13, 15, 29, 65, 125} : Finset ℕ) := by
  have := (wraps_iff_le_sixty_one hn hn').mp hw
  simp only [mem_insert, mem_singleton] at this ⊢
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl a_one
  · exact Or.inl a_two
  · exact Or.inr (Or.inl a_three)
  · exact Or.inr (Or.inr (Or.inl a_five))
  · exact Or.inl a_seven
  · exact Or.inr (Or.inl a_eight)
  · exact Or.inr (Or.inr (Or.inr (Or.inl a_ten)))
  · exact Or.inr (Or.inr (Or.inl a_fourteen))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl a_fifteen))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl a_twenty_three)))))
  · simp [a_twenty_nine]
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl a_forty_six)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl a_sixty_one))))))


lemma four_dvd_a_of_not_wrap {n : ℕ} (hn : 2 ≤ n) (h : ¬ wraps n) :
    4 ∣ a n := by
  have hnw : gapProd n < primeN (n + 2) := by
    unfold wraps at h
    simp only [not_and, not_not] at h
    exact h (by omega)
  exact four_dvd_a_of_nowrap hn hnw

/-- None of the 13 known wrap values is divisible by 4. -/
lemma known_wrap_not_four_dvd {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 61)
    (hw : wraps n) : ¬ 4 ∣ a n := by
  have hmem := wrap_a_mem hn hn' hw
  simp only [mem_insert, mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide

/-- An occurrence of a multiple of 4 at `n ≤ 61` cannot be a wrap. -/
lemma four_dvd_not_wrap_of_le_sixty_one {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 61)
    (h4 : 4 ∣ a n) : ¬ wraps n :=
  fun hw => known_wrap_not_four_dvd hn hn' hw h4

/-- If there is no wrap then `a n` equals the unreduced gap product. -/
lemma nowrap_gapProd_eq {n : ℕ} (hn : 1 ≤ n) (hw : ¬ wraps n) :
    a n = gapProd n := by
  have hlt : gapProd n < primeN (n + 2) := by
    unfold wraps at hw
    simp only [not_and, not_not] at hw
    exact hw hn
  exact a_eq_gapProd hn hlt

/-- An occurrence of a 4-multiple at `n ≤ 61` is an unreduced gap product. -/
lemma four_dvd_eq_gapProd_of_le_sixty_one {n : ℕ} (hn : 2 ≤ n) (hn' : n ≤ 61)
    (h4 : 4 ∣ a n) : a n = gapProd n :=
  nowrap_gapProd_eq (by omega) (four_dvd_not_wrap_of_le_sixty_one (by omega) hn' h4)

/-- Two-step span is the sum of two consecutive gaps. -/
lemma two_step_span_eq_add {n : ℕ} (hn : 1 ≤ n) :
    primeN (n + 2) - primeN n = gap n + gap (n + 1) :=
  two_step_sub hn

/-- If the two-step gap is `< √(p_{n+2})` then there is no wrap
    (since `gapProd ≤ (g1+g2)^2`). -/
lemma not_wrap_of_small_span {n : ℕ} (hn : 1 ≤ n)
    (h : (primeN (n + 2) - primeN n) ^ 2 < primeN (n + 2)) :
    ¬ wraps n := by
  intro hw
  have hle : primeN (n + 2) ≤ gapProd n := (wraps_iff hn).mp hw
  have hspan : primeN (n + 2) - primeN n = gap n + gap (n + 1) := two_step_sub hn
  have hg2le : gap (n + 1) ≤ gap n + gap (n + 1) := Nat.le_add_left _ _
  have hgp : gapProd n ≤ (gap n + gap (n + 1)) ^ 2 := by
    unfold gapProd
    nlinarith
  have : primeN (n + 2) ≤ (primeN (n + 2) - primeN n) ^ 2 := by
    calc
      primeN (n + 2) ≤ gapProd n := hle
      _ ≤ (gap n + gap (n + 1)) ^ 2 := hgp
      _ = (primeN (n + 2) - primeN n) ^ 2 := by rw [hspan]
  exact not_le_of_gt h this

lemma mem_image_a_of_count_pos {x v : ℕ} (h : 0 < count_a x v) :
    ∃ n ∈ Icc 1 x, a n = v := by
  rw [count_a_eq_Icc] at h
  obtain ⟨n, hn⟩ := Finset.card_pos.mp h
  exact ⟨n, (mem_filter.mp hn).1, (mem_filter.mp hn).2⟩

lemma mode_eq_a {x v₀ : ℕ} (hv : is_most_frequent x v₀) (hx : 33 ≤ x) :
    ∃ n ∈ Icc 1 x, a n = v₀ := by
  have : 0 < count_a x v₀ :=
    lt_of_lt_of_le (count_a_one_le hx) (hv 120)
  exact mem_image_a_of_count_pos this

/- ### Chebyshev-type lower bound on `primeCounting` from central binomials. -/

lemma centralBinom_dvd_factorial (n : ℕ) : centralBinom n ∣ (2 * n).factorial := by
  rw [centralBinom_eq_two_mul_choose, choose_eq_factorial_div_factorial (by omega : n ≤ 2 * n)]
  refine Nat.div_dvd_of_dvd ?_
  exact Nat.factorial_mul_factorial_dvd_factorial (by omega : n ≤ 2 * n)

lemma prime_dvd_centralBinom_le {n p : ℕ} (hp : p.Prime) (hd : p ∣ centralBinom n) :
    p ≤ 2 * n := by
  have : p ∣ (2 * n).factorial := dvd_trans hd (centralBinom_dvd_factorial n)
  exact (hp.dvd_factorial.mp this)

lemma primeFactors_subset_primes_le {k m : ℕ} (h : ∀ p, p.Prime → p ∣ k → p ≤ m) :
    k.primeFactors ⊆ (range (m + 1)).filter Nat.Prime := by
  intro p hp
  have hpP : p.Prime := prime_of_mem_primeFactors hp
  have hpd : p ∣ k := dvd_of_mem_primeFactors hp
  have hple : p ≤ m := h p hpP hpd
  simp [mem_filter, mem_range, hpP, Nat.lt_succ_of_le hple]

lemma primeFactors_card_le_pi {k m : ℕ} (h : ∀ p, p.Prime → p ∣ k → p ≤ m) :
    k.primeFactors.card ≤ primeCounting m := by
  have hs := primeFactors_subset_primes_le h
  have hcard := card_le_card hs
  have : ((range (m + 1)).filter Nat.Prime).card = primeCounting m := by
    simp [primeCounting, primeCounting', Nat.count_eq_card_filter_range]
  rwa [this] at hcard

lemma centralBinom_primeFactors_card_le {n : ℕ} :
    n.centralBinom.primeFactors.card ≤ primeCounting (2 * n) :=
  primeFactors_card_le_pi (fun _ hp hd => prime_dvd_centralBinom_le hp hd)

lemma centralBinom_le_two_mul_pow_omega {n : ℕ} (hn : 1 ≤ n) :
    centralBinom n ≤ (2 * n) ^ n.centralBinom.primeFactors.card := by
  have hne : centralBinom n ≠ 0 := centralBinom_ne_zero n
  have h2n : 2 * n ≠ 0 := by omega
  have hle : ∀ p ∈ n.centralBinom.primeFactors,
      p ^ (n.centralBinom.factorization p) ≤ 2 * n := by
    intro p hp
    have hpp : p.Prime := prime_of_mem_primeFactors hp
    have hv : n.centralBinom.factorization p ≤ Nat.log p (2 * n) := by
      rw [centralBinom_eq_two_mul_choose]
      exact factorization_choose_le_log
    exact (Nat.pow_le_pow_right (Nat.Prime.one_lt hpp).le hv).trans
      (Nat.pow_log_le_self p h2n)
  calc
    centralBinom n = n.centralBinom.factorization.prod (· ^ ·) :=
      (factorization_prod_pow_eq_self hne).symm
    _ = ∏ p ∈ n.centralBinom.primeFactors,
          p ^ n.centralBinom.factorization p := by
        rw [Finsupp.prod_of_support_subset (s := n.centralBinom.primeFactors)]
        · rw [Nat.support_factorization]
        · intro i hi; simp
    _ ≤ ∏ _p ∈ n.centralBinom.primeFactors, (2 * n) :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun p hp => hle p hp)
    _ = (2 * n) ^ n.centralBinom.primeFactors.card :=
        Finset.prod_const _

lemma centralBinom_le_two_mul_pow_pi {n : ℕ} (hn : 1 ≤ n) :
    centralBinom n ≤ (2 * n) ^ primeCounting (2 * n) :=
  (centralBinom_le_two_mul_pow_omega hn).trans
    (Nat.pow_le_pow_right (by omega) centralBinom_primeFactors_card_le)

lemma four_pow_div_n_lt_centralBinom {n : ℕ} (hn : 4 ≤ n) :
    (4 : ℝ) ^ n / n < centralBinom n := by
  have : (4 : ℕ) ^ n < n * centralBinom n := four_pow_lt_mul_centralBinom n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : (0:ℕ) < 4) hn)
  have : (4 : ℝ) ^ n < (n : ℝ) * centralBinom n := by exact_mod_cast this
  exact (div_lt_iff₀ hnpos).mpr (by linarith)

lemma chebyshev_pi_lower {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log n ≤
      (primeCounting (2 * n) : ℝ) * Real.log (2 * n) := by
  have hC : (4 : ℝ) ^ n / n < centralBinom n := four_pow_div_n_lt_centralBinom hn
  have hle : (centralBinom n : ℝ) ≤ (2 * n : ℝ) ^ primeCounting (2 * n) := by
    exact_mod_cast centralBinom_le_two_mul_pow_pi (by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : (0:ℕ) < 4) hn)
  have h4n : (0 : ℝ) < (4 : ℝ) ^ n / n :=
    div_pos (pow_pos (by norm_num : (0:ℝ) < 4) n) hn0
  have hlt : (4 : ℝ) ^ n / n < (2 * n : ℝ) ^ primeCounting (2 * n) :=
    lt_of_lt_of_le hC hle
  have hlog := Real.log_lt_log h4n hlt
  have hlogL : Real.log ((4 : ℝ) ^ n / n) = (n : ℝ) * Real.log 4 - Real.log n := by
    rw [Real.log_div (pow_ne_zero n (by norm_num : (4:ℝ) ≠ 0)) (ne_of_gt hn0),
        Real.log_pow]
    try ring
  have hlogR : Real.log ((2 * n : ℝ) ^ primeCounting (2 * n)) =
      (primeCounting (2 * n) : ℝ) * Real.log (2 * n) := by
    rw [Real.log_pow]
  linarith

lemma primeCounting_primeN (n : ℕ) (hn : 1 ≤ n) :
    primeCounting (primeN n) = n := by
  have hinf : (setOf Nat.Prime).Infinite := infinite_setOf_prime
  have hcnt := Nat.count_nth_succ_of_infinite (p := Nat.Prime) hinf (n - 1)
  have : n - 1 + 1 = n := Nat.sub_add_cancel hn
  simpa [primeCounting, primeCounting', primeN, this] using hcnt

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- `120 = 8 * 3 * 5` with the three factors pairwise coprime. -/
lemma hundred_twenty_eq : 120 = 8 * 3 * 5 := by decide

lemma hundred_twenty_dvd_iff {m : ℕ} :
    120 ∣ m ↔ 8 ∣ m ∧ 3 ∣ m ∧ 5 ∣ m := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact dvd_trans (by decide : 8 ∣ 120) h
    · exact dvd_trans (by decide : 3 ∣ 120) h
    · exact dvd_trans (by decide : 5 ∣ 120) h
  · intro ⟨h8, h3, h5⟩
    have h24 : 24 ∣ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 8 3) h8 h3
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 24 5) h24 h5

/-- After the first prime, `gapProd n = 4 * c * (b + c)` with `b, c ≥ 1`. -/
lemma gapProd_four_mul {n : ℕ} (hn : 2 ≤ n) :
    ∃ b c : ℕ, 0 < b ∧ 0 < c ∧ gap n = 2 * b ∧ gap (n + 1) = 2 * c ∧
      gapProd n = 4 * c * (b + c) := by
  have h1 : 2 ∣ gap n := gap_even hn
  have h2 : 2 ∣ gap (n + 1) := gap_even (by omega)
  obtain ⟨b, hb⟩ := h1
  obtain ⟨c, hc⟩ := h2
  have hbpos : 0 < b := by
    have := gap_pos (by omega : 1 ≤ n)
    omega
  have hcpos : 0 < c := by
    have := gap_pos (by omega : 1 ≤ n + 1)
    omega
  refine ⟨b, c, hbpos, hcpos, hb, hc, ?_⟩
  unfold gapProd
  rw [hb, hc]
  ring

/-- Unreduced gap products are at least `8` once both gaps are even. -/
lemma gapProd_ge_eight {n : ℕ} (hn : 2 ≤ n) : 8 ≤ gapProd n := by
  obtain ⟨b, c, hbpos, hcpos, _, _, hgp⟩ := gapProd_four_mul hn
  have : 2 ≤ c * (b + c) := by
    have : 1 ≤ b + c := by omega
    nlinarith
  have : 8 ≤ 4 * c * (b + c) := by nlinarith
  exact le_trans this (le_of_eq hgp.symm)

lemma nowrap_a_ge_eight {n : ℕ} (hn : 2 ≤ n) (hw : ¬ wraps n) : 8 ≤ a n := by
  have : a n = gapProd n := nowrap_gapProd_eq (by omega) hw
  exact le_trans (gapProd_ge_eight hn) (le_of_eq this.symm)

/-- `4` has no even-even factorization, so it never occurs as a nowrap value. -/
lemma four_not_gapProd {n : ℕ} (hn : 2 ≤ n) : gapProd n ≠ 4 := by
  have := gapProd_ge_eight hn
  omega

/-- `8 ∤ gapProd n` iff `(gap n, gap (n+1)) ≡ (0, 2) (mod 4)`. -/
lemma eight_not_dvd_gapProd_iff {n : ℕ} (hn : 2 ≤ n) :
    ¬ 8 ∣ gapProd n ↔ (gap n % 4 = 0 ∧ gap (n + 1) % 4 = 2) := by
  obtain ⟨b, c, hbpos, hcpos, hgb, hgc, hgp⟩ := gapProd_four_mul hn
  have hgp' : gapProd n = 4 * (c * (b + c)) := by rw [hgp, mul_assoc]
  have h8 : 8 ∣ gapProd n ↔ Even (c * (b + c)) := by
    constructor
    · intro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      have : 4 * (c * (b + c)) = 8 * t := by rw [← hgp', ht]
      omega
    · intro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [hgp', ht]; ring
  have : ¬ 8 ∣ gapProd n ↔ (b % 2 = 0 ∧ c % 2 = 1) := by
    rw [h8, even_iff_two_dvd, dvd_iff_mod_eq_zero]
    have : c * (b + c) % 2 = (c % 2) * ((b % 2 + c % 2) % 2) % 2 := by
      rw [Nat.mul_mod, Nat.add_mod]
    constructor
    · intro h
      have hc1 : c % 2 = 1 := by
        have : c % 2 = 0 ∨ c % 2 = 1 := Nat.mod_two_eq_zero_or_one c
        rcases this with hc | hc
        · have : c * (b + c) % 2 = 0 := by
            rw [Nat.mul_mod, hc]; simp
          exact (h this).elim
        · exact hc
      have hb0 : b % 2 = 0 := by
        have hbalt : b % 2 = 0 ∨ b % 2 = 1 := Nat.mod_two_eq_zero_or_one b
        rcases hbalt with hb | hb
        · exact hb
        · have hzero : c * (b + c) % 2 = 0 := by
            rw [Nat.mul_mod, Nat.add_mod, hb, hc1]
          exact (h hzero).elim
      exact ⟨hb0, hc1⟩
    · intro ⟨hb0, hc1⟩ hdiv
      have hone : c * (b + c) % 2 = 1 := by
        rw [Nat.mul_mod, Nat.add_mod, hb0, hc1]
      omega
  constructor
  · intro h
    have ⟨hb0, hc1⟩ := this.mp h
    constructor
    · have : 2 * b % 4 = 0 := by omega
      rwa [← hgb] at this
    · have : 2 * c % 4 = 2 := by omega
      rwa [← hgc] at this
  · intro ⟨hg1, hg2⟩
    apply this.mpr
    constructor
    · have : 2 * b % 4 = 0 := by rwa [← hgb]
      omega
    · have : 2 * c % 4 = 2 := by rwa [← hgc]
      omega

/-- A nowrap occurrence of a non-multiple of 8 has the unique residue
    pattern `(g₁, g₂) ≡ (0, 2) (mod 4)`. -/
lemma missing_eight_gap_pattern {n : ℕ} (hn : 2 ≤ n)
    (hw : ¬ wraps n) (h8 : ¬ 8 ∣ a n) :
    gap n % 4 = 0 ∧ gap (n + 1) % 4 = 2 := by
  have hgp : a n = gapProd n := by
    have : gapProd n < primeN (n + 2) := by
      have hn1 : 1 ≤ n := by omega
      exact lt_of_not_ge (fun hle => hw ((wraps_iff hn1).mpr hle))
    exact a_eq_gapProd (by omega) this
  have : ¬ 8 ∣ gapProd n := by simpa [hgp] using h8
  exact (eight_not_dvd_gapProd_iff hn).mp this

/-- The only even-even factorization of 8 is `(2,2)`, which occurs solely at `n = 2`. -/
lemma gapProd_eq_eight_iff {n : ℕ} (hn : 2 ≤ n) :
    gapProd n = 8 ↔ n = 2 := by
  constructor
  · intro h
    have hg2e : 2 ∣ gap (n + 1) := gap_even (by omega)
    have hg1e : 2 ∣ gap n := gap_even hn
    have hprod : (gap n + gap (n + 1)) * gap (n + 1) = 8 := h
    have hg2pos : 0 < gap (n + 1) := gap_pos (by omega)
    have hg1pos : 0 < gap n := gap_pos (by omega)
    have hg2le : gap (n + 1) ≤ 2 := by
      have : gap (n + 1) * gap (n + 1) < 8 := by
        have : gap n + gap (n + 1) > gap (n + 1) := by omega
        nlinarith
      nlinarith
    have hg2 : gap (n + 1) = 2 := by
      have : gap (n + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hg2e
      interval_cases gap (n + 1) <;> simp_all
    have hg1 : gap n = 2 := by
      have := hprod
      simp [hg2] at this
      omega
    -- Consecutive gaps of 2,2 means p, p+2, p+4 with p = primeN n ≥ 3.
    have hp : primeN n = 3 := by
      have h3 : 3 ≤ primeN n := three_le_primeN hn
      have hnext : primeN (n + 1) = primeN n + 2 := by
        have := primeN_succ_eq (by omega : 1 ≤ n)
        simp [hg1] at this
        exact this
      have hnext2 : primeN (n + 2) = primeN n + 4 := by
        have := primeN_succ_eq (by omega : 1 ≤ n + 1)
        rw [hnext] at this
        simp [hg2] at this
        omega
      -- One of p, p+2, p+4 is divisible by 3; since all are prime, p = 3.
      have hpP : (primeN n).Prime := primeN_prime n
      have hqP : (primeN (n + 1)).Prime := primeN_prime (n + 1)
      have hrP : (primeN (n + 2)).Prime := primeN_prime (n + 2)
      have hmod : primeN n % 3 = 0 ∨ (primeN n + 2) % 3 = 0 ∨ (primeN n + 4) % 3 = 0 := by
        have : primeN n % 3 = 0 ∨ primeN n % 3 = 1 ∨ primeN n % 3 = 2 := by
          omega
        rcases this with h | h | h <;> omega
      rcases hmod with h | h | h
      · have : 3 ∣ primeN n := Nat.dvd_of_mod_eq_zero h
        have : primeN n = 3 :=
          ((hpP.eq_one_or_self_of_dvd 3 this).resolve_left (by decide)).symm
        exact this
      · have : 3 ∣ primeN (n + 1) := by
          rw [hnext]; exact Nat.dvd_of_mod_eq_zero h
        have : primeN (n + 1) = 3 :=
          ((hqP.eq_one_or_self_of_dvd 3 this).resolve_left (by decide)).symm
        have : primeN n = 1 := by omega
        have : 2 ≤ primeN n := two_le_primeN (by omega)
        omega
      · have : 3 ∣ primeN (n + 2) := by
          have : primeN (n + 2) = primeN n + 4 := hnext2
          rw [this]; exact Nat.dvd_of_mod_eq_zero h
        have : primeN (n + 2) = 3 :=
          ((hrP.eq_one_or_self_of_dvd 3 this).resolve_left (by decide)).symm
        omega
    -- primeN n = 3 and n ≥ 2 ⇒ n = 2
    have : primeN 2 = 3 := primeN_two
    have hmono : n ≤ 2 := by
      by_contra hgt
      have : 2 < n := Nat.lt_of_not_ge hgt
      have : primeN 2 < primeN n := primeN_lt (by decide : 1 ≤ 2) this
      omega
    omega
  · rintro rfl
    simp [gapProd, gap, primeN_two, primeN_three, primeN_four]

/-- `3 ∣ gapProd n` iff `3` divides the second gap or the two-step span. -/
lemma three_dvd_gapProd_iff {n : ℕ} :
    3 ∣ gapProd n ↔ 3 ∣ gap (n + 1) ∨ 3 ∣ (gap n + gap (n + 1)) := by
  unfold gapProd
  constructor
  · intro h
    have h' : 3 ∣ gap (n + 1) * (gap n + gap (n + 1)) := by
      rwa [mul_comm]
    exact (Nat.Prime.dvd_mul (by decide : Nat.Prime 3)).mp h'
  · intro h
    rcases h with h | h
    · exact dvd_mul_of_dvd_right h _
    · exact dvd_mul_of_dvd_left h _

lemma mod_three_eq_one_or_two {k : ℕ} (h : ¬ 3 ∣ k) :
    k % 3 = 1 ∨ k % 3 = 2 := by
  have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h0 | h1 | h2
  · exact False.elim (h (Nat.dvd_of_mod_eq_zero h0))
  · exact Or.inl h1
  · exact Or.inr h2

/-- If `3` divides none of `g₁`, `g₂`, `g₁+g₂`, the offsets occupy every residue
    class modulo `3`. -/
lemma offsets_cover_mod_three {g1 g2 : ℕ}
    (h1 : ¬ 3 ∣ g1) (h2 : ¬ 3 ∣ g2) (h12 : ¬ 3 ∣ (g1 + g2)) :
    ({(0 : ℕ), g1 % 3, (g1 + g2) % 3} : Finset ℕ) = {0, 1, 2} := by
  have hg1 := mod_three_eq_one_or_two h1
  have hg12 := mod_three_eq_one_or_two h12
  have hne : g1 % 3 ≠ (g1 + g2) % 3 := by
    intro heq
    have : g2 % 3 = 0 := by
      have hsum : (g1 + g2) % 3 = (g1 % 3 + g2 % 3) % 3 := Nat.add_mod _ _ _
      omega
    exact h2 (Nat.dvd_of_mod_eq_zero this)
  rcases hg1 with h11 | h12'
  · rcases hg12 with h121 | h122
    · exact (hne (h11.trans h121.symm)).elim
    · ext x
      simp only [mem_insert, mem_singleton]
      constructor
      · intro hx
        rcases hx with rfl | rfl | rfl
        · simp
        · simp [h11]
        · simp [h122]
      · intro hx
        rcases hx with rfl | rfl | rfl <;> simp [h11, h122]
  · rcases hg12 with h121 | h122
    · ext x
      simp only [mem_insert, mem_singleton]
      constructor
      · intro hx
        rcases hx with rfl | rfl | rfl
        · simp
        · simp [h12']
        · simp [h121]
      · intro hx
        rcases hx with rfl | rfl | rfl <;> simp [h12', h121]
    · exact (hne (h12'.trans h122.symm)).elim

/-- A 3-tuple whose offsets occupy all residues mod 3 must include the prime `3`,
    hence occurs only at `n = 2`. -/
lemma covered_offsets_eq_two {n : ℕ} (hn : 2 ≤ n)
    (h1 : ¬ 3 ∣ gap n) (h2 : ¬ 3 ∣ gap (n + 1))
    (h12 : ¬ 3 ∣ (gap n + gap (n + 1))) : n = 2 := by
  have hpP : (primeN n).Prime := primeN_prime n
  have hqP : (primeN (n + 1)).Prime := primeN_prime (n + 1)
  have hrP : (primeN (n + 2)).Prime := primeN_prime (n + 2)
  have hpeq : primeN (n + 1) = primeN n + gap n := primeN_succ_eq (by omega)
  have hreq : primeN (n + 2) = primeN n + gap n + gap (n + 1) := by
    have := primeN_succ_eq (by omega : 1 ≤ n + 1)
    rw [hpeq] at this
    omega
  have hpmod : primeN n % 3 = 0 ∨ primeN n % 3 = 1 ∨ primeN n % 3 = 2 := by omega
  have hne : gap n % 3 ≠ (gap n + gap (n + 1)) % 3 := by
    intro heq
    have hsum : (gap n + gap (n + 1)) % 3 =
        (gap n % 3 + gap (n + 1) % 3) % 3 := Nat.add_mod _ _ _
    have : gap (n + 1) % 3 = 0 := by omega
    exact h2 (Nat.dvd_of_mod_eq_zero this)
  -- One of the three primes is 0 mod 3, hence equals 3.
  have hzero : primeN n % 3 = 0 ∨
      (primeN n + gap n) % 3 = 0 ∨
      (primeN n + gap n + gap (n + 1)) % 3 = 0 := by
    have hg1r : gap n % 3 = 1 ∨ gap n % 3 = 2 := mod_three_eq_one_or_two h1
    have hspanr : (gap n + gap (n + 1)) % 3 = 1 ∨
        (gap n + gap (n + 1)) % 3 = 2 := mod_three_eq_one_or_two h12
    rcases hpmod with hp0 | hp1 | hp2
    · exact Or.inl hp0
    · -- translate offsets by 1
      have : (1 + gap n % 3) % 3 = 0 ∨
          (1 + (gap n + gap (n + 1)) % 3) % 3 = 0 := by
        rcases hg1r with a | a <;> rcases hspanr with b | b
        · exact (hne (a.trans b.symm)).elim
        · simp [a, b]
        · simp [a, b]
        · exact (hne (a.trans b.symm)).elim
      rcases this with t | t
      · right; left
        rw [Nat.add_mod, hp1]; simpa using t
      · right; right
        rw [Nat.add_assoc, Nat.add_mod, hp1]
        simpa [Nat.add_mod] using t
    · have : (2 + gap n % 3) % 3 = 0 ∨
          (2 + (gap n + gap (n + 1)) % 3) % 3 = 0 := by
        rcases hg1r with a | a <;> rcases hspanr with b | b
        · exact (hne (a.trans b.symm)).elim
        · simp [a, b]
        · simp [a, b]
        · exact (hne (a.trans b.symm)).elim
      rcases this with t | t
      · right; left
        rw [Nat.add_mod, hp2]; simpa using t
      · right; right
        rw [Nat.add_assoc, Nat.add_mod, hp2]
        simpa [Nat.add_mod] using t
  rcases hzero with hz | hz | hz
  · have : 3 ∣ primeN n := Nat.dvd_of_mod_eq_zero hz
    have : primeN n = 3 :=
      ((hpP.eq_one_or_self_of_dvd 3 this).resolve_left (by decide)).symm
    have : n ≤ 2 := by
      by_contra hgt
      have : 2 < n := Nat.lt_of_not_ge hgt
      have : primeN 2 < primeN n := primeN_lt (by decide : 1 ≤ 2) this
      simp [primeN_two] at this
      omega
    omega
  · have : 3 ∣ primeN (n + 1) := by
      rw [hpeq]; exact Nat.dvd_of_mod_eq_zero hz
    have hq : primeN (n + 1) = 3 :=
      ((hqP.eq_one_or_self_of_dvd 3 this).resolve_left (by decide)).symm
    have : primeN n < 3 := by
      have : primeN n < primeN (n + 1) := primeN_lt (by omega) (by omega)
      omega
    have : 3 ≤ primeN n := three_le_primeN hn
    omega
  · have : 3 ∣ primeN (n + 2) := by
      rw [hreq]; exact Nat.dvd_of_mod_eq_zero hz
    have : primeN (n + 2) = 3 :=
      ((hrP.eq_one_or_self_of_dvd 3 this).resolve_left (by decide)).symm
    have : primeN n < 3 := by
      have : primeN n < primeN (n + 2) := primeN_lt (by omega) (by omega)
      omega
    have : 3 ≤ primeN n := three_le_primeN hn
    omega

/-- After `n = 2`, a missing factor of `3` in `gapProd` forces `3 ∣ gap n`
    and `3 ∤ gap (n+1)`. -/
lemma missing_three_gap_pattern {n : ℕ} (hn : 2 < n) (h : ¬ 3 ∣ gapProd n) :
    3 ∣ gap n ∧ ¬ 3 ∣ gap (n + 1) := by
  have hiff := (three_dvd_gapProd_iff (n := n)).not.mp h
  simp only [not_or] at hiff
  obtain ⟨hg2, hspan⟩ := hiff
  have hg1 : 3 ∣ gap n := by
    by_contra hg1
    have := covered_offsets_eq_two (by omega) hg1 hg2 hspan
    omega
  exact ⟨hg1, hg2⟩

/-- `5 ∣ gapProd n` iff `5` divides the second gap or the two-step span. -/
lemma five_dvd_gapProd_iff {n : ℕ} :
    5 ∣ gapProd n ↔ 5 ∣ gap (n + 1) ∨ 5 ∣ (gap n + gap (n + 1)) := by
  unfold gapProd
  constructor
  · intro h
    have h' : 5 ∣ gap (n + 1) * (gap n + gap (n + 1)) := by
      rwa [mul_comm]
    exact (Nat.Prime.dvd_mul (by decide : Nat.Prime 5)).mp h'
  · intro h
    rcases h with h | h
    · exact dvd_mul_of_dvd_right h _
    · exact dvd_mul_of_dvd_left h _

/-- A nowrap value not divisible by 5 has neither the second gap nor the
    two-step span divisible by 5. -/
lemma missing_five_gap_pattern {n : ℕ} (hn : 1 ≤ n) (hw : ¬ wraps n)
    (h5 : ¬ 5 ∣ a n) :
    ¬ 5 ∣ gap (n + 1) ∧ ¬ 5 ∣ (gap n + gap (n + 1)) := by
  have hgp : a n = gapProd n := nowrap_gapProd_eq hn hw
  have : ¬ 5 ∣ gapProd n := by simpa [hgp] using h5
  have hiff := (five_dvd_gapProd_iff (n := n)).not.mp this
  simpa [not_or] using hiff

/-- A convenient Chebyshev lower bound: `π(2n) ≥ (n log 4 - log n) / log(2n)`. -/
lemma primeCounting_two_mul_ge {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log n ≤
      (primeCounting (2 * n) : ℝ) * Real.log (2 * n) :=
  chebyshev_pi_lower hn

lemma primeCounting_two_mul_pos {n : ℕ} (hn : 4 ≤ n) :
    0 < primeCounting (2 * n) := by
  have h8 : 1 ≤ primeCounting 8 := by
    unfold primeCounting primeCounting'
    decide
  have : 8 ≤ 2 * n := by omega
  exact lt_of_lt_of_le (by decide : 0 < 1) (le_trans h8 (monotone_primeCounting this))

/-- The two-step gaps of wrapping indices are at least `√p`. -/
lemma wrap_span_sq_ge {n : ℕ} (hw : wraps n) :
    primeN (n + 2) ≤ (primeN (n + 2) - primeN n) ^ 2 := by
  have hn : 1 ≤ n := hw.1
  have hle : primeN (n + 2) ≤ gapProd n := (wraps_iff hn).mp hw
  have hspan : primeN (n + 2) - primeN n = gap n + gap (n + 1) := two_step_sub hn
  have hgp : gapProd n ≤ (gap n + gap (n + 1)) ^ 2 := by
    unfold gapProd
    nlinarith [gap_pos hn, gap_pos (by omega : 1 ≤ n + 1)]
  calc
    primeN (n + 2) ≤ gapProd n := hle
    _ ≤ (gap n + gap (n + 1)) ^ 2 := hgp
    _ = (primeN (n + 2) - primeN n) ^ 2 := by rw [hspan]

lemma log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  ring

lemma primeCounting_pred_prime {p : ℕ} (hp : p.Prime) :
    primeCounting (p - 1) + 1 = primeCounting p := by
  have hppos : 1 ≤ p := Nat.Prime.one_le hp
  have h1 : p - 1 + 1 = p := Nat.sub_add_cancel hppos
  have heq : Nat.count Nat.Prime (p + 1) = Nat.count Nat.Prime p + 1 := by
    rw [Nat.count_succ]; simp [hp]
  simp only [primeCounting, primeCounting']
  rw [h1]
  exact heq.symm

lemma primeN_le_of_primeCounting {k m : ℕ} (hk : 1 ≤ k)
    (h : k ≤ primeCounting m) : primeN k ≤ m := by
  by_contra hlt
  have hgt : m < primeN k := Nat.lt_of_not_ge hlt
  have : primeCounting m ≤ primeCounting (primeN k - 1) :=
    monotone_primeCounting (Nat.le_pred_of_lt hgt)
  have hπ : primeCounting (primeN k) = k := primeCounting_primeN k hk
  have hpred := primeCounting_pred_prime (primeN_prime k)
  omega

/-- Bertrand's postulate for the 1-indexed prime sequence. -/
lemma primeN_succ_le_two_mul {n : ℕ} (hn : 1 ≤ n) :
    primeN (n + 1) ≤ 2 * primeN n := by
  have hp : 0 < primeN n := lt_of_lt_of_le (by decide : 0 < 2) (two_le_primeN hn)
  obtain ⟨p, hpP, hlt, hle⟩ :=
    exists_prime_lt_and_le_two_mul (primeN n) (Nat.pos_iff_ne_zero.mp hp)
  have hπn : primeCounting (primeN n) = n := primeCounting_primeN n hn
  have hstep : n + 1 ≤ primeCounting p := by
    have hpred := primeCounting_pred_prime hpP
    have hle' : primeCounting (primeN n) ≤ primeCounting (p - 1) :=
      monotone_primeCounting (Nat.le_pred_of_lt hlt)
    omega
  exact le_trans (primeN_le_of_primeCounting (by omega) hstep) hle

/-- A wrap whose second gap is 2 forces the triple `(p, 2p-1, 2p+1)`,
which is covered modulo 3 for `p > 3`. Hence no such wrap exists for `n ≥ 3`. -/
lemma not_wrap_of_second_gap_two {n : ℕ} (hn : 3 ≤ n)
    (hg2 : gap (n + 1) = 2) : ¬ wraps n := by
  intro hw
  have hn1 : 1 ≤ n := by omega
  have hwrap : primeN (n + 2) ≤ gapProd n := (wraps_iff hn1).mp hw
  set p := primeN n
  set q := primeN (n + 1)
  set r := primeN (n + 2)
  have hq_eq : q = p + gap n := by
    simpa [p, q] using primeN_succ_eq hn1
  have hr_eq : r = q + 2 := by
    have := primeN_succ_eq (by omega : 1 ≤ n + 1)
    simpa [r, q, hg2] using this
  have hgp : gapProd n = 2 * (gap n + 2) := by
    simp [gapProd, hg2]; ring
  have hprod : r ≤ 2 * (gap n + 2) := by
    simpa [hgp] using hwrap
  have hprod' : r ≤ 2 * (q - p + 2) := by
    simpa [gap, p, q] using hprod
  have hr_ge : 2 * p ≤ r := by
    have h1 : q + 2 ≤ 2 * (q - p + 2) := by simpa [hr_eq] using hprod'
    omega
  have hB : q ≤ 2 * p := by
    simpa [q, p] using primeN_succ_le_two_mul hn1
  have hp5 : 5 ≤ p := by
    have : primeN 3 ≤ p := by
      simpa [p] using primeN_le (by decide : 1 ≤ 3) (by omega : 3 ≤ n)
    simpa [primeN_three] using this
  have hpP : p.Prime := by simpa [p] using primeN_prime n
  have hqP : q.Prime := by simpa [q] using primeN_prime (n + 1)
  have hrP : r.Prime := by simpa [r] using primeN_prime (n + 2)
  have hp_odd : p % 2 = 1 :=
    hpP.eq_two_or_odd.resolve_left (Nat.ne_of_gt (by omega : 2 < p))
  have hq_odd : q % 2 = 1 :=
    hqP.eq_two_or_odd.resolve_left (Nat.ne_of_gt (by omega : 2 < q))
  have hmid : 2 * p = q + 1 := by omega
  have hq' : q = 2 * p - 1 := by omega
  have hr' : r = 2 * p + 1 := by omega
  have hpmod : p % 3 = 1 ∨ p % 3 = 2 := by
    have : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases this with h0 | h1 | h2
    · have : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
      have : p = 3 :=
        ((hpP.eq_one_or_self_of_dvd 3 this).resolve_left (by decide)).symm
      omega
    · exact Or.inl h1
    · exact Or.inr h2
  rcases hpmod with hm1 | hm2
  · have hr0 : r % 3 = 0 := by
      rw [hr', Nat.add_mod, Nat.mul_mod, hm1]
    have hd : 3 ∣ r := Nat.dvd_of_mod_eq_zero hr0
    have : r = 3 :=
      ((hrP.eq_one_or_self_of_dvd 3 hd).resolve_left (by decide)).symm
    omega
  · have hq0 : q % 3 = 0 := by
      have hqp : q + 1 = 2 * p := hmid.symm
      have hL : (q + 1) % 3 = (2 * p) % 3 := by rw [hqp]
      have hR : (2 * p) % 3 = 1 := by rw [Nat.mul_mod, hm2]
      have hL' : (q % 3 + 1) % 3 = 1 := by
        rwa [Nat.add_mod, Nat.mod_eq_of_lt (by decide : 1 < 3), hR] at hL
      have hqmod : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
      rcases hqmod with h | h | h
      · exact h
      · simp [h] at hL'
      · simp [h] at hL'
    have hd : 3 ∣ q := Nat.dvd_of_mod_eq_zero hq0
    have : q = 3 :=
      ((hqP.eq_one_or_self_of_dvd 3 hd).resolve_left (by decide)).symm
    omega

/-- After `n = 2`, a second gap of `2` forces the unreduced formula (no wrap). -/
lemma a_eq_gapProd_of_second_gap_two {n : ℕ} (hn : 3 ≤ n)
    (hg2 : gap (n + 1) = 2) : a n = gapProd n :=
  nowrap_gapProd_eq (by omega) (not_wrap_of_second_gap_two hn hg2)

/-- After `n = 2`, a wrap cannot have second gap `2`, so the second gap is at least `4`. -/
lemma wrap_second_gap_ge_four {n : ℕ} (hn : 3 ≤ n) (hw : wraps n) :
    4 ≤ gap (n + 1) := by
  have hg2e : 2 ∣ gap (n + 1) := gap_even (by omega)
  have hg2pos : 0 < gap (n + 1) := gap_pos (by omega)
  have hne : gap (n + 1) ≠ 2 := fun h => not_wrap_of_second_gap_two hn h hw
  omega

/-- The unreduced product decomposes as `a n + k * primeN (n+2)` with `k = gapProd n / r`. -/
lemma gapProd_eq_a_add_mul {n : ℕ} (hn : 1 ≤ n) :
    gapProd n = a n + (gapProd n / primeN (n + 2)) * primeN (n + 2) := by
  have hr : 0 < primeN (n + 2) := primeN_pos (by omega)
  have ha : a n = gapProd n % primeN (n + 2) := a_eq_gapProd_mod hn
  rw [ha]
  exact (Nat.mod_add_div (gapProd n) (primeN (n + 2))).symm.trans (by ring)

/-- A wrap whose value is divisible by 4 must wrap at least four times
    (`gapProd ≥ 4 * p_{n+2}`). -/
lemma four_dvd_wrap_super {n : ℕ} (hn : 2 ≤ n) (hw : wraps n) (h4 : 4 ∣ a n) :
    4 * primeN (n + 2) ≤ gapProd n := by
  have hn1 : 1 ≤ n := by omega
  have hrP : (primeN (n + 2)).Prime := primeN_prime (n + 2)
  have hr_odd : primeN (n + 2) % 2 = 1 :=
    hrP.eq_two_or_odd.resolve_left (Nat.ne_of_gt (by
      have : 3 ≤ primeN (n + 2) := three_le_primeN (by omega)
      omega))
  have hgp4 : 4 ∣ gapProd n := four_dvd_gapProd hn
  have hdecomp := gapProd_eq_a_add_mul hn1
  set r := primeN (n + 2)
  set k := gapProd n / r
  have hkpos : 1 ≤ k := by
    have : r ≤ gapProd n := (wraps_iff hn1).mp hw
    exact Nat.div_pos this (primeN_pos (by omega : 1 ≤ n + 2))
  -- a = gapProd - k*r, so 4 ∣ a and 4 ∣ gapProd ⇒ 4 ∣ k*r. r odd ⇒ 4 ∣ k.
  have hsum : a n + k * r = gapProd n := hdecomp.symm
  have hkr : 4 ∣ k * r := by
    obtain ⟨t, ht⟩ := h4
    obtain ⟨u, hu⟩ := hgp4
    -- a + k*r = gapProd, so 4t + k*r = 4u
    refine ⟨u - t, ?_⟩
    have hsum' : a n + k * r = 4 * u := by
      rw [hsum, hu]
    have : k * r = 4 * u - 4 * t := by
      have : a n + k * r = 4 * t + k * r := by simp [ht]
      omega
    omega
  have hk4 : 4 ∣ k := by
    have h2 : ¬ 2 ∣ r := by
      intro hd
      have : r % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
      omega
    have hcop : Nat.Coprime 4 r := by
      have hg1 : Nat.gcd 4 r ∣ 4 := Nat.gcd_dvd_left 4 r
      have hg2 : Nat.gcd 4 r ∣ r := Nat.gcd_dvd_right 4 r
      have hle : Nat.gcd 4 r ≤ 4 := Nat.le_of_dvd (by decide) hg1
      match hgcd : Nat.gcd 4 r with
      | 0 =>
          have : 0 < Nat.gcd 4 r := Nat.gcd_pos_of_pos_left r (by decide)
          omega
      | 1 => exact Nat.coprime_iff_gcd_eq_one.mpr hgcd
      | 2 => exact False.elim (h2 (by simpa [hgcd] using hg2))
      | 3 =>
          have : 3 ∣ 4 := by simpa [hgcd] using hg1
          omega
      | 4 =>
          have : 2 ∣ r := dvd_trans (by decide : 2 ∣ 4) (by simpa [hgcd] using hg2)
          exact False.elim (h2 this)
      | n+5 =>
          have : 5 ≤ Nat.gcd 4 r := by omega
          omega
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop hkr
  have hk4le : 4 ≤ k := by
    obtain ⟨t, ht⟩ := hk4
    have : 1 ≤ t := by
      have : 1 ≤ 4 * t := by
        rw [← ht]
        exact hkpos
      omega
    omega
  have hdiv : k * r ≤ gapProd n := Nat.div_mul_le_self _ _
  calc
    4 * r ≤ k * r := Nat.mul_le_mul_right _ hk4le
    _ ≤ gapProd n := hdiv

/-- The two-step span of a wrap is at least the integer square root of `p_{n+2}`. -/
lemma wrap_span_ge_sqrt {n : ℕ} (hw : wraps n) :
    Nat.sqrt (primeN (n + 2)) ≤ primeN (n + 2) - primeN n := by
  have h := wrap_span_sq_ge hw
  set p := primeN (n + 2)
  set s := p - primeN n
  have hp : p ≤ s * s := by
    simpa [p, s, Nat.pow_two] using h
  have hlt : Nat.sqrt p < s + 1 := by
    rw [Nat.sqrt_lt]
    nlinarith
  omega

lemma two_le_gap {n : ℕ} (hn : 2 ≤ n) : 2 ≤ gap n := by
  have hpos : 0 < gap n := gap_pos (by omega)
  have he : 2 ∣ gap n := gap_even hn
  omega

lemma two_step_eq_gaps {n : ℕ} (hn : 1 ≤ n) :
    primeN (n + 2) - primeN n = gap n + gap (n + 1) :=
  two_step_sub hn

/-- Crude bound: each two-step span is at most `p_{N+2}`. -/
lemma two_step_sum_le {N : ℕ} :
    ∑ n ∈ Icc 1 N, (primeN (n + 2) - primeN n) ≤ N * primeN (N + 2) := by
  have hle : ∀ n ∈ Icc 1 N, primeN (n + 2) - primeN n ≤ primeN (N + 2) := by
    intro n hn
    simp only [mem_Icc] at hn
    have h1 : primeN (n + 2) ≤ primeN (N + 2) :=
      primeN_le (by omega) (by omega)
    have h2 : primeN n ≤ primeN (n + 2) :=
      (primeN_lt (by omega) (by omega)).le
    omega
  calc
    ∑ n ∈ Icc 1 N, (primeN (n + 2) - primeN n) ≤
        ∑ n ∈ Icc 1 N, primeN (N + 2) :=
      Finset.sum_le_sum hle
    _ = (Icc 1 N).card * primeN (N + 2) := sum_const _
    _ = N * primeN (N + 2) := by simp [Nat.card_Icc]

/-- Pigeonhole: some fibre is at least `s.card / k` when the image has size `≤ k`. -/
lemma pigeon_count {s : Finset ℕ} (f : ℕ → ℕ) {k : ℕ}
    (hk : (s.image f).card ≤ k) :
    ∃ v, k * (s.filter (fun n => f n = v)).card ≥ s.card := by
  classical
  by_cases hne : s.Nonempty
  · obtain ⟨v, hv, hmax⟩ :=
      exists_max_image (s.image f) (fun v => (s.filter (fun n => f n = v)).card)
        (image_nonempty.mpr hne)
    refine ⟨v, ?_⟩
    have hsum :
        s.card = ∑ t ∈ s.image f, (s.filter (fun n => f n = t)).card :=
      Finset.card_eq_sum_card_fiberwise (s := s) (f := f) (t := s.image f)
        (by intro x hx; exact mem_image_of_mem f hx)
    have hle :
        ∑ t ∈ s.image f, (s.filter (fun n => f n = t)).card ≤
          (s.image f).card * (s.filter (fun n => f n = v)).card := by
      refine Finset.sum_le_card_nsmul _ _ _ ?_
      intro t ht
      exact hmax t ht
    have hmul :
        (s.image f).card * (s.filter (fun n => f n = v)).card ≤
          k * (s.filter (fun n => f n = v)).card :=
      Nat.mul_le_mul_right _ hk
    exact hsum ▸ le_trans hle hmul
  · refine ⟨0, ?_⟩
    have : s.card = 0 := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hne
    omega

/-- Sharp two-step telescoping: `∑_{n=1}^N (p_{n+2}-p_n) = p_{N+1}+p_{N+2}-5`. -/
lemma two_step_sum_exact : ∀ N, 1 ≤ N →
    ∑ n ∈ Icc 1 N, (primeN (n + 2) - primeN n) =
      primeN (N + 1) + primeN (N + 2) - 5 := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hN
    rcases N with _ | N
    · exact (Nat.not_succ_le_zero 0 hN).elim
    · rcases N with _ | N
      · -- N = 1
        simp only [Icc_self, sum_singleton]
        rw [primeN_one, primeN_two, primeN_three]
      · -- N = N+2 ≥ 2, apply IH at N+1
        have hIH : 1 ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le _)
        have hs : N + 1 < N + 1 + 1 := Nat.lt_succ_self _
        have ih' := ih (N + 1) hs hIH
        have hunion :
            Icc 1 (N + 1 + 1) = insert (N + 1 + 1) (Icc 1 (N + 1)) := by
          ext k; simp [mem_insert, mem_Icc]; omega
        have hnotin : N + 1 + 1 ∉ Icc 1 (N + 1) := by
          simp [mem_Icc]
        rw [hunion, sum_insert hnotin, ih']
        set pK := primeN (N + 2)
        set pK1 := primeN (N + 3)
        set pK2 := primeN (N + 4)
        have hpK_le : pK ≤ pK2 := by
          simpa [pK, pK2] using
            primeN_le (by omega : 1 ≤ N + 2) (by omega : N + 2 ≤ N + 4)
        have hpK3 : 3 ≤ pK := by
          simpa [pK] using three_le_primeN (by omega : 2 ≤ N + 2)
        have hpK2 : 2 ≤ pK := le_trans (by decide : 2 ≤ 3) hpK3
        have hpK1 : 2 ≤ pK1 := by
          simpa [pK1] using two_le_primeN (by omega : 1 ≤ N + 3)
        have hpK22 : 2 ≤ pK2 := by
          simpa [pK2] using two_le_primeN (by omega : 1 ≤ N + 4)
        have h5 : 5 ≤ pK + pK1 := by omega
        -- `ih'` says sum(Icc 1 (N+1)) = p_{N+2} + p_{N+3} - 5 = pK + pK1 - 5
        -- added term is p_{N+3} - p_{N+1}? No: at n = N+2, term is p_{N+4} - p_{N+2} = pK2 - pK
        -- Wait n = N+1+1 = N+2, term p_{N+4}-p_{N+2} = pK2 - pK
        -- IH: p_{N+2}+p_{N+3}-5 = pK+pK1-5
        -- total = pK+pK1-5 + (pK2-pK) = pK1+pK2-5
        -- RHS: p_{(N+2)+1} + p_{(N+2)+2} - 5 = p_{N+3}+p_{N+4}-5 = pK1+pK2-5
        have ih_rw : primeN (N + 1 + 1) + primeN (N + 1 + 2) - 5 = pK + pK1 - 5 := by
          simp [pK, pK1]
        have add_rw : primeN (N + 1 + 1 + 2) - primeN (N + 1 + 1) = pK2 - pK := by
          simp [pK, pK2]
        have rhs_rw : primeN (N + 1 + 1 + 1) + primeN (N + 1 + 1 + 2) - 5 =
            pK1 + pK2 - 5 := by
          simp [pK1, pK2]
        rw [ih_rw, add_rw, rhs_rw]
        omega

lemma two_step_sum_exact' {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, (primeN (n + 2) - primeN n) =
      primeN (N + 1) + primeN (N + 2) - 5 :=
  two_step_sum_exact N hN

/-- Wraps in `[N₁, N]` are bounded using `span ≥ √p_{N₁}`. -/
lemma wraps_Icc_mul_sqrt_le {N1 N : ℕ} (hN1 : 1 ≤ N1) (hN : N1 ≤ N) :
    ((Icc N1 N).filter wraps).card * Nat.sqrt (primeN N1) ≤
      primeN (N + 1) + primeN (N + 2) := by
  classical
  have hspan : ∀ n ∈ (Icc N1 N).filter wraps,
      Nat.sqrt (primeN N1) ≤ primeN (n + 2) - primeN n := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    have hw : wraps n := hn.2
    have hge : primeN N1 ≤ primeN (n + 2) :=
      primeN_le hN1 (by omega)
    have := wrap_span_ge_sqrt hw
    exact le_trans (Nat.sqrt_le_sqrt hge) this
  have hsum_le :
      ((Icc N1 N).filter wraps).card * Nat.sqrt (primeN N1) ≤
        ∑ n ∈ (Icc N1 N).filter wraps, (primeN (n + 2) - primeN n) := by
    exact Finset.card_nsmul_le_sum _ _ _ hspan
  have hsub :
      ∑ n ∈ (Icc N1 N).filter wraps, (primeN (n + 2) - primeN n) ≤
        ∑ n ∈ Icc 1 N, (primeN (n + 2) - primeN n) := by
    refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
    intro n hn
    simp only [mem_filter, mem_Icc] at hn ⊢
    exact ⟨by omega, hn.1.2⟩
  have hexact := two_step_sum_exact N (le_trans hN1 hN)
  have : primeN (N + 1) + primeN (N + 2) - 5 ≤ primeN (N + 1) + primeN (N + 2) :=
    Nat.sub_le _ _
  omega

lemma wraps_card_le_add {N1 N : ℕ} (hN1 : 1 ≤ N1) (hN : N1 ≤ N)
    (hs : 0 < Nat.sqrt (primeN N1)) :
    ((Icc N1 N).filter wraps).card ≤
      (primeN (N + 1) + primeN (N + 2)) / Nat.sqrt (primeN N1) :=
  (Nat.le_div_iff_mul_le hs).mpr (wraps_Icc_mul_sqrt_le hN1 hN)

lemma wraps_total_le {N1 N : ℕ} (hN1 : 1 ≤ N1) (hN : N1 ≤ N)
    (hs : 0 < Nat.sqrt (primeN N1)) :
    ((Icc 1 N).filter wraps).card ≤
      N1 + (primeN (N + 1) + primeN (N + 2)) / Nat.sqrt (primeN N1) := by
  classical
  have hsplit :
      (Icc 1 N).filter wraps ⊆
        (Icc 1 N1).filter wraps ∪ (Icc N1 N).filter wraps := by
    intro n hn
    simp only [mem_union, mem_filter, mem_Icc] at hn ⊢
    rcases le_total n N1 with h | h
    · exact Or.inl ⟨⟨hn.1.1, h⟩, hn.2⟩
    · exact Or.inr ⟨⟨h, hn.1.2⟩, hn.2⟩
  have hcard := card_le_card hsplit
  have hun := card_union_le ((Icc 1 N1).filter wraps) ((Icc N1 N).filter wraps)
  have hlo : ((Icc 1 N1).filter wraps).card ≤ N1 := by
    have : ((Icc 1 N1).filter wraps).card ≤ (Icc 1 N1).card := card_filter_le _ _
    simpa [Nat.card_Icc] using this
  have hhi := wraps_card_le_add hN1 hN hs
  omega

lemma four_dvd_a_of_ge_two_nowrap {n : ℕ} (hn : 2 ≤ n) (h : ¬ wraps n) :
    4 ∣ a n :=
  four_dvd_a_of_not_wrap hn h

/-- If `4 ∤ v` then every occurrence of `v` is a wrap (or the `n = 1` term). -/
lemma occurrence_wrap_of_not_four_dvd {x v n : ℕ}
    (hn : n ∈ Icc 1 x) (ha : a n = v) (h4 : ¬ 4 ∣ v) :
    n = 1 ∨ wraps n := by
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  rcases eq_or_ne n 1 with rfl | hne
  · exact Or.inl rfl
  · have hn2' : 2 ≤ n := by
      have : 1 ≤ n := hn1
      omega
    by_cases hw : wraps n
    · exact Or.inr hw
    · have : 4 ∣ a n := four_dvd_a_of_not_wrap hn2' hw
      exact False.elim (h4 (by simpa [ha] using this))

lemma count_not_four_dvd_le_wraps {x v : ℕ} (h4 : ¬ 4 ∣ v) :
    count_a x v ≤
      ((Icc 1 x).filter (fun n => n = 1 ∨ wraps n)).card := by
  classical
  rw [count_a_eq_Icc]
  refine card_le_card ?_
  intro n hn
  simp only [mem_filter, mem_Icc] at hn ⊢
  exact ⟨hn.1, occurrence_wrap_of_not_four_dvd (mem_Icc.mpr hn.1) hn.2 h4⟩

lemma four_dvd_gapProd_of_ge_two {n : ℕ} (hn : 2 ≤ n) : 4 ∣ gapProd n :=
  four_dvd_gapProd hn

lemma four_dvd_of_nowrap_eq {n v : ℕ} (hn : 2 ≤ n)
    (h : a n = v) (hw : ¬ wraps n) : 4 ∣ v := by
  have : 4 ∣ a n := four_dvd_a_of_not_wrap hn hw
  simpa [h] using this

/-- If `v` is not a multiple of 4 then it can only arise at `n = 1` or at wraps. -/
lemma count_a_not_four_le_succ_wraps {x v : ℕ} (h4 : ¬ 4 ∣ v) :
    count_a x v ≤ ((Icc 1 x).filter (fun n => n = 1 ∨ wraps n)).card :=
  count_not_four_dvd_le_wraps h4

lemma wraps_subset_span_ge_sqrt {N : ℕ} :
    (Icc 1 N).filter wraps ⊆
      (Icc 1 N).filter (fun n => Nat.sqrt (primeN (n + 2)) ≤ primeN (n + 2) - primeN n) := by
  intro n hn
  simp only [mem_filter, mem_Icc] at hn ⊢
  exact ⟨hn.1, wrap_span_ge_sqrt hn.2⟩

/-- Gap product pairs for a general unreduced value `4 * t`. -/
lemma gapProd_eq_four_mul {n t : ℕ} (hn : 2 ≤ n) (h : gapProd n = 4 * t) :
    ∃ b c : ℕ, 0 < b ∧ 0 < c ∧ gap n = 2 * b ∧ gap (n + 1) = 2 * c ∧
      c * (b + c) = t := by
  obtain ⟨b, c, hbpos, hcpos, hgb, hgc, hgp⟩ := gapProd_four_mul hn
  refine ⟨b, c, hbpos, hcpos, hgb, hgc, ?_⟩
  have : 4 * c * (b + c) = 4 * t := by
    rw [← hgp, h]
  have h4pos : (4 : ℕ) ≠ 0 := by decide
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) (by
    rw [mul_assoc] at this
    exact this)

/- ### Main conjecture -/

/-- No modular wrap-around occurs after the last known wrap `n = 61`.
This is a strong prime-gap statement (`(g₁+g₂)g₂ < p_{n+2}`), still open
in general, though verified computationally to enormous height. -/
lemma no_wraps_after_sixty_one {n : ℕ} (hn : 61 < n) : ¬ wraps n := by
  -- The range 62 ≤ n ≤ 81 is settled by direct computation.
  by_cases h81 : n ≤ 81
  · have h62 : 62 ≤ n := by omega
    interval_cases n
    · exact not_wraps_62
    · exact not_wraps_63
    · exact not_wraps_64
    · exact not_wraps_65
    · exact not_wraps_66
    · exact not_wraps_67
    · exact not_wraps_68
    · exact not_wraps_69
    · exact not_wraps_70
    · exact not_wraps_71
    · exact not_wraps_72
    · exact not_wraps_73
    · exact not_wraps_74
    · exact not_wraps_75
    · exact not_wraps_76
    · exact not_wraps_77
    · exact not_wraps_78
    · exact not_wraps_79
    · exact not_wraps_80
    · exact not_wraps_81
  · -- Second gap 2 is impossible for n ≥ 3. Larger second gaps remain open.
    have hn3 : 3 ≤ n := by omega
    by_cases hg2 : gap (n + 1) = 2
    · exact not_wrap_of_second_gap_two hn3 hg2
    · -- For n > 81 this is a strong prime-gap statement, still open.
      sorry

/-- The 13 known wrap/one values, for rewriting. -/
lemma known_wrap_a_values :
    a 1 = 1 ∧ a 2 = 1 ∧ a 3 = 2 ∧ a 5 = 7 ∧ a 7 = 1 ∧ a 8 = 2 ∧
    a 10 = 11 ∧ a 14 = 7 ∧ a 15 = 13 ∧ a 23 = 15 ∧ a 29 = 125 ∧
    a 46 = 65 ∧ a 61 = 29 :=
  ⟨a_one, a_two, a_three, a_five, a_seven, a_eight, a_ten, a_fourteen,
   a_fifteen, a_twenty_three, a_twenty_nine, a_forty_six, a_sixty_one⟩

/-- Among the 13 known wraps (and `n = 1`), no single value occurs 6 times. -/
lemma count_known_wraps_lt_six (v : ℕ) :
    (({1, 2, 3, 5, 7, 8, 10, 14, 15, 23, 29, 46, 61} : Finset ℕ).filter
      (fun n => a n = v)).card ≤ 3 := by
  obtain ⟨h1, h2, h3, h5, h7, h8, h10, h14, h15, h23, h29, h46, h61⟩ :=
    known_wrap_a_values
  have hsub :
      ({1, 2, 3, 5, 7, 8, 10, 14, 15, 23, 29, 46, 61} : Finset ℕ).filter
        (fun n => a n = v) ⊆
      if v = 1 then {1, 2, 7}
      else if v = 2 then {3, 8}
      else if v = 7 then {5, 14}
      else if v = 11 then {10}
      else if v = 13 then {15}
      else if v = 15 then {23}
      else if v = 125 then {29}
      else if v = 65 then {46}
      else if v = 29 then {61}
      else (∅ : Finset ℕ) := by
    intro n hn
    simp only [mem_filter] at hn
    obtain ⟨hn, ha⟩ := hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [h1] at ha; subst ha; simp
    · simp [h2] at ha; subst ha; simp
    · simp [h3] at ha; subst ha; simp
    · simp [h5] at ha; subst ha; simp
    · simp [h7] at ha; subst ha; simp
    · simp [h8] at ha; subst ha; simp
    · simp [h10] at ha; subst ha; simp
    · simp [h14] at ha; subst ha; simp
    · simp [h15] at ha; subst ha; simp
    · simp [h23] at ha; subst ha; simp
    · simp [h29] at ha; subst ha; simp
    · simp [h46] at ha; subst ha; simp
    · simp [h61] at ha; subst ha; simp
  have hle := card_le_card hsub
  split_ifs at hle <;> exact le_trans hle (by decide)

/-- If every occurrence of `v₀` is at `n = 1` or a wrap, then `v₀` cannot be a
mode for `x ≥ 81`: there are no wraps after 61, and the 13 known wraps
repeat no single value six times. -/
lemma wrap_only_not_mode {x v₀ : ℕ} (hx : 81 ≤ x)
    (hv : is_most_frequent x v₀)
    (hocc : ∀ n, n ∈ Icc 1 x → a n = v₀ → n = 1 ∨ wraps n) : False := by
  have hcnt : 6 ≤ count_a x v₀ := le_trans (count_a_six_le hx) (hv 120)
  have hsub : ((Icc 1 x).filter (fun n => a n = v₀)) ⊆
      ({1, 2, 3, 5, 7, 8, 10, 14, 15, 23, 29, 46, 61} : Finset ℕ) := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨hn1, hnx⟩, ha⟩ := hn
    have hor : n = 1 ∨ wraps n := hocc n (mem_Icc.mpr ⟨hn1, hnx⟩) ha
    have hn61 : n ≤ 61 := by
      by_contra hgt
      have : 61 < n := Nat.lt_of_not_ge hgt
      rcases hor with rfl | hw
      · omega
      · exact no_wraps_after_sixty_one this hw
    rcases hor with rfl | hw
    · simp
    · exact (wraps_iff_le_sixty_one hn1 hn61).mp hw
  have hle : count_a x v₀ ≤
      (({1, 2, 3, 5, 7, 8, 10, 14, 15, 23, 29, 46, 61} : Finset ℕ).filter
        (fun n => a n = v₀)).card := by
    rw [count_a_eq_Icc]
    refine card_le_card ?_
    intro n hn
    have hn' := hsub hn
    simp only [mem_filter] at hn ⊢
    exact ⟨hn', hn.2⟩
  have hle' := le_trans hle (count_known_wraps_lt_six v₀)
  exact absurd hle' (not_le.mpr (lt_of_lt_of_le (by decide : (3:ℕ) < 6) hcnt))

/-- A value not divisible by 4 can only arise at `n = 1` or at wraps. -/
lemma not_four_dvd_not_mode {x v₀ : ℕ} (hx : 81 ≤ x)
    (hv : is_most_frequent x v₀) (h4 : ¬ 4 ∣ v₀) : False :=
  wrap_only_not_mode hx hv fun _ hn ha =>
    occurrence_wrap_of_not_four_dvd hn ha h4

/-- Any mode at `x ≥ 81` occurs at least as often as the six explicit `120`s. -/
lemma mode_count_ge_six {x v₀ : ℕ} (hx : 81 ≤ x)
    (hv : is_most_frequent x v₀) : 6 ≤ count_a x v₀ :=
  le_trans (count_a_six_le hx) (hv 120)

/-- A nowrap occurrence of a non-multiple of 3, after `n = 2`, has
    `3 ∣ gap n` and `3 ∤ gap (n+1)`. -/
lemma missing_three_nowrap_pattern {n : ℕ} (hn : 2 < n)
    (hw : ¬ wraps n) (h3 : ¬ 3 ∣ a n) :
    3 ∣ gap n ∧ ¬ 3 ∣ gap (n + 1) := by
  have hgp : a n = gapProd n := nowrap_gapProd_eq (by omega) hw
  have : ¬ 3 ∣ gapProd n := by simpa [hgp] using h3
  exact missing_three_gap_pattern hn this

/-- After `n = 2`, a nowrap value not divisible by 3 is necessarily `≡ 1 [MOD 3]`. -/
lemma missing_three_nowrap_mod {n : ℕ} (hn : 2 < n)
    (hw : ¬ wraps n) (h3 : ¬ 3 ∣ a n) : a n % 3 = 1 := by
  have ⟨hg1, hg2⟩ := missing_three_nowrap_pattern hn hw h3
  have hgp : a n = gapProd n := nowrap_gapProd_eq (by omega) hw
  have hsum : (gap n + gap (n + 1)) % 3 = gap (n + 1) % 3 := by
    have : gap n % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hg1
    rw [Nat.add_mod, this]
    simp
  have hsq : gapProd n % 3 = (gap (n + 1) % 3) * (gap (n + 1) % 3) % 3 := by
    unfold gapProd
    rw [Nat.mul_mod, hsum]
  have : a n % 3 = (gap (n + 1) % 3) ^ 2 % 3 := by
    rw [hgp, hsq, pow_two]
  have hg2r := mod_three_eq_one_or_two hg2
  rcases hg2r with h | h
  · rw [this, h]; decide
  · rw [this, h]; decide

/-- A value `≡ 2 [MOD 3]` (hence not divisible by 3) can only arise at known
    wrap indices, once late wraps are excluded. -/
lemma missing_three_two_mod_three_not_mode {x v₀ : ℕ} (hx : 81 ≤ x)
    (hv : is_most_frequent x v₀) (hmod : v₀ % 3 = 2) : False := by
  have h120 : 6 ≤ count_a x 120 := count_a_six_le hx
  have hcnt : 6 ≤ count_a x v₀ := le_trans h120 (hv 120)
  have h3 : ¬ 3 ∣ v₀ := by
    intro h
    have : v₀ % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
    omega
  have hsub : ((Icc 1 x).filter (fun n => a n = v₀)) ⊆
      ({1, 2, 3, 5, 7, 8, 10, 14, 15, 23, 29, 46, 61} : Finset ℕ) := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨hn1, hnx⟩, ha⟩ := hn
    have hnv : a n % 3 = 2 := by simp [ha, hmod]
    rcases eq_or_ne n 1 with rfl | hn1ne
    · simp [a_one] at hnv
    rcases eq_or_ne n 2 with rfl | hn2ne
    · simp [a_two] at hnv
    have hn2 : 2 < n := by omega
    by_cases hw : wraps n
    · have hn61 : n ≤ 61 := by
        by_contra hgt
        exact no_wraps_after_sixty_one (Nat.lt_of_not_ge hgt) hw
      exact (wraps_iff_le_sixty_one (by omega) hn61).mp hw
    · have : a n % 3 = 1 := missing_three_nowrap_mod hn2 hw (by simpa [ha] using h3)
      omega
  have hle : count_a x v₀ ≤
      (({1, 2, 3, 5, 7, 8, 10, 14, 15, 23, 29, 46, 61} : Finset ℕ).filter
        (fun n => a n = v₀)).card := by
    rw [count_a_eq_Icc]
    refine card_le_card ?_
    intro n hn
    have hn' := hsub hn
    simp only [mem_filter] at hn ⊢
    exact ⟨hn', hn.2⟩
  have hle' := le_trans hle (count_known_wraps_lt_six v₀)
  exact absurd hle' (not_le.mpr (lt_of_lt_of_le (by decide : (3:ℕ) < 6) hcnt))

/--
Conjecture: for x > 10^9, the most frequent value in a(n), n=1...x, has form 120*k.
We interpret "n=0...x" from the OEIS entry as $n \in \{1, \dots, x\}$ for the active terms.
-/
theorem oeis_182126_conjecture_0 :
  ∀ x : ℕ,
    x > 10^9 →
    ∀ v₀ : ℕ,
      is_most_frequent x v₀ →
      120 ∣ v₀ := by
  intro x hx v₀ hv
  have hx81 : 81 ≤ x :=
    le_trans (le_of_lt eighty_one_lt_ten_pow_nine) hx.le
  by_cases hdiv : 120 ∣ v₀
  · exact hdiv
  · exfalso
    have hfactors : ¬ (8 ∣ v₀ ∧ 3 ∣ v₀ ∧ 5 ∣ v₀) :=
      mt hundred_twenty_dvd_iff.mpr hdiv
    by_cases h4 : 4 ∣ v₀
    · by_cases h8 : 8 ∣ v₀
      · by_cases h3 : 3 ∣ v₀
        · have h5 : ¬ 5 ∣ v₀ := fun h5 => hfactors ⟨h8, h3, h5⟩
          -- Missing 5: the family 24, 48, 72, 96, 144, 288, 504, 2016, …
          exact False.elim (by
            sorry)
        · -- Missing 3. The residue `v₀ ≡ 2 [MOD 3]` is covering-obstructed.
          have hmod : v₀ % 3 = 1 ∨ v₀ % 3 = 2 := mod_three_eq_one_or_two h3
          rcases hmod with h1 | h2
          · -- `v₀ ≡ 1 [MOD 3]`: admissible family 16, 40, 64, 160, …
            exact False.elim (by
              sorry)
          · exact missing_three_two_mod_three_not_mode hx81 hv h2
      · -- Missing 8. If also `v₀ ≡ 2 [MOD 3]` the covering obstruction applies.
        by_cases h3' : 3 ∣ v₀
        · -- `3 ∣ v₀` but `8 ∤ v₀`: family 12, 36, 60, 84, …
          exact False.elim (by
            sorry)
        · have hmod : v₀ % 3 = 1 ∨ v₀ % 3 = 2 := mod_three_eq_one_or_two h3'
          rcases hmod with h1 | h2
          · -- `v₀ ≡ 4 [MOD 8]` and `≡ 1 [MOD 3]`: family 4, 28, 52, 76, …
            -- `4` itself has no nowrap representation (`gapProd ≥ 8`).
            by_cases hv4 : v₀ = 4
            · subst hv4
              refine wrap_only_not_mode hx81 hv ?_
              intro n hn ha
              have hn2 : n = 1 ∨ 2 ≤ n := by
                have : 1 ≤ n := (mem_Icc.mp hn).1
                omega
              rcases hn2 with rfl | hn2
              · simp [a_one] at ha
              · by_cases hw : wraps n
                · exact Or.inr hw
                · have : 8 ≤ a n := nowrap_a_ge_eight hn2 hw
                  omega
            · exact False.elim (by
                sorry)
          · exact missing_three_two_mod_three_not_mode hx81 hv h2
    · exact not_four_dvd_not_mode hx81 hv h4
