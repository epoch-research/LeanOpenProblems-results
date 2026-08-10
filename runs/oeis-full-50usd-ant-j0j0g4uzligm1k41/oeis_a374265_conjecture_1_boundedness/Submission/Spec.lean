import FormalConjectures.Util.ProblemImports

open Nat Finset

-- The function that removes all '0' digits from a number
def remove_zeros (n : ℕ) : ℕ :=
  -- Nat.digits returns the list of digits in reverse order.
  let digits := (Nat.digits 10 n).filter (fun d => d ≠ 0)
  -- Nat.ofDigits interprets the list from most significant digit first if the base is 10
  ofDigits 10 digits

/--
The set of all possible values $f(n)$ resulting from a sequence of choices
where $f(0)=1$ and $f(i) = \operatorname{OpNoz}_i(i \cdot f(i-1))$,
with $\operatorname{OpNoz}_i(x)$ being either $x$ or $remove\_zeros(x)$.
We use `biUnion` for the union of sets.
-/
def reachable_zeroless_factorials : ℕ → Finset ℕ
  | 0 => {1}
  | n + 1 =>
    let prev_set := reachable_zeroless_factorials n
    prev_set.biUnion fun m =>
      let prod := (n + 1) * m
      {prod, remove_zeros prod}

-- The set of reachable values is always nonempty.
lemma reachable_nonempty (n : ℕ) : (reachable_zeroless_factorials n).Nonempty := by
  induction n with
  | zero => exact Finset.singleton_nonempty 1
  | succ n ih =>
    rcases ih with ⟨m, hm⟩ -- Get a guaranteed element m from the previous set
    let prod := (n + 1) * m
    -- We show that `prod` is an element of the current set using `mem_biUnion`.
    -- prod is in {prod, ...} and m is in the previous set, so prod is in the overall union.
    exact ⟨prod, Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_insert_self prod _⟩⟩

/--
A374265: Minimized zeroless factorials.
$a(n)$ is the smallest $f(n)$ such that $f(0) = 1$ and for $i > 0$,
$f(i) = \operatorname{OpNoz}_i(i \cdot f(i-1))$, where $\operatorname{OpNoz}_i$
is a function that either removes zeros or keeps the value unchanged.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (reachable_zeroless_factorials n).min' (reachable_nonempty n)

/-!
We disprove the boundedness conjecture: the sequence `a` is **unbounded**.

Key idea. Define the (base 10) digit sum `D n := (Nat.digits 10 n).sum`.

* `remove_zeros` preserves the digit sum (it only deletes `0` digits), hence every
  value reachable at step `n` has the same digit sum as `n * (value at step n-1)`.
* Every positive multiple of `10^k - 1` (the repunit `99…9`) has digit sum `≥ 9 k`,
  because the only positive multiple below `10^k` is `10^k - 1` itself, and digit sum
  is subadditive.
* Taking `n = 10^k - 1`, every reachable value `v` satisfies `D v ≥ 9 k`, hence
  `v ≥ 10^{k-1}`.  Therefore `a (10^k - 1) ≥ 10^{k-1} → ∞`, so `a` is unbounded.
-/

/-- Base-10 digit sum. -/
private def D (n : ℕ) : ℕ := (Nat.digits 10 n).sum

private lemma D_zero : D 0 = 0 := by simp [D]

/-- Deleting `0`-digits does not change the (list) sum. -/
private lemma sum_filter_ne_zero (l : List ℕ) :
    (l.filter (fun d => d ≠ 0)).sum = l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases h : a = 0
    · subst h
      rw [List.filter_cons_of_neg (by simp), ih, List.sum_cons, Nat.zero_add]
    · rw [List.filter_cons_of_pos (by simpa using h), List.sum_cons, List.sum_cons, ih]

/-- `remove_zeros` preserves the digit sum. -/
private lemma D_remove (x : ℕ) : D (remove_zeros x) = D x := by
  unfold D remove_zeros
  have w1 : ∀ l ∈ (Nat.digits 10 x).filter (fun d => d ≠ 0), l < 10 := by
    intro l hl
    exact Nat.digits_lt_base (by norm_num) (List.mem_of_mem_filter hl)
  have w2 : ∀ h : (Nat.digits 10 x).filter (fun d => d ≠ 0) ≠ [],
      ((Nat.digits 10 x).filter (fun d => d ≠ 0)).getLast h ≠ 0 := by
    intro hne
    have hmem := List.getLast_mem hne
    rw [List.mem_filter] at hmem
    simpa using hmem.2
  rw [Nat.digits_ofDigits 10 (by norm_num) _ w1 w2]
  exact sum_filter_ne_zero _

/-- For `x ≠ 0`, the digit sum is at least `1`. -/
private lemma one_le_D (x : ℕ) (hx : x ≠ 0) : 1 ≤ D x := by
  unfold D
  have hne : Nat.digits 10 x ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hx
  have hgl : (Nat.digits 10 x).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 10 hx
  have hmem := List.getLast_mem hne
  have hle : (Nat.digits 10 x).getLast hne ≤ (Nat.digits 10 x).sum :=
    List.single_le_sum (by intro y _; exact Nat.zero_le y) _ hmem
  omega

/-- `remove_zeros` of a nonzero number is nonzero. -/
private lemma remove_ne_zero (x : ℕ) (hx : x ≠ 0) : remove_zeros x ≠ 0 := by
  intro h
  have h1 := one_le_D x hx
  have h2 := D_remove x
  rw [h] at h2
  rw [D_zero] at h2
  omega

/-- Every reachable value is positive. -/
private lemma reachable_pos :
    ∀ n, ∀ m ∈ reachable_zeroless_factorials n, 0 < m := by
  intro n
  induction n with
  | zero =>
    intro m hm
    simp only [reachable_zeroless_factorials, Finset.mem_singleton] at hm
    omega
  | succ n ih =>
    intro v hv
    have hunf : reachable_zeroless_factorials (n + 1) =
        (reachable_zeroless_factorials n).biUnion
          (fun m => {(n + 1) * m, remove_zeros ((n + 1) * m)}) := rfl
    rw [hunf] at hv
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hv
    obtain ⟨m, hm, hv⟩ := hv
    have hmpos := ih m hm
    rcases hv with rfl | rfl
    · positivity
    · have hne : (n + 1) * m ≠ 0 := by positivity
      exact Nat.pos_of_ne_zero (remove_ne_zero _ hne)

/-- Subadditivity of the digit sum: `D (a + b) ≤ D a + D b`. -/
private lemma D_add_le : ∀ N a b, a + b = N → D N ≤ D a + D b := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro a b hab
    rcases Nat.eq_zero_or_pos a with ha0 | ha
    · subst ha0; simp_all [D]
    rcases Nat.eq_zero_or_pos b with hb0 | hb
    · subst hb0; simp_all [D]
    have hN : 0 < N := by omega
    have hDN : D N = N % 10 + D (N / 10) := by
      unfold D; rw [Nat.digits_def' (by norm_num) hN]; simp
    have hDa : D a = a % 10 + D (a / 10) := by
      unfold D; rw [Nat.digits_def' (by norm_num) ha]; simp
    have hDb : D b = b % 10 + D (b / 10) := by
      unfold D; rw [Nat.digits_def' (by norm_num) hb]; simp
    set c := (a % 10 + b % 10) / 10 with hc
    have hNdiv : N / 10 = a / 10 + (b / 10 + c) := by subst hab; omega
    have hNmod : N % 10 + c ≤ a % 10 + b % 10 := by subst hab; omega
    have hlt1 : N / 10 < N := Nat.div_lt_self hN (by norm_num)
    have e1 : D (N / 10) ≤ D (a / 10) + D (b / 10 + c) :=
      IH (N / 10) hlt1 (a / 10) (b / 10 + c) hNdiv.symm
    have hcle : c ≤ 1 := by omega
    have hlt2 : b / 10 + c < N := by
      have : b / 10 ≤ b := Nat.div_le_self b 10
      omega
    have e2 : D (b / 10 + c) ≤ D (b / 10) + D c := IH (b / 10 + c) hlt2 (b / 10) c rfl
    have hDc : D c ≤ c := Nat.digit_sum_le 10 c
    rw [hDN, hDa, hDb]
    omega

/-- The repunit `10^k - 1` has digits `[9, 9, …, 9]` (`k` nines). -/
private lemma digits_repunit (k : ℕ) :
    Nat.digits 10 (10 ^ k - 1) = List.replicate k 9 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have h1 : 10 ^ (k + 1) - 1 = 9 + 10 * (10 ^ k - 1) := by
      have h2 : 10 ^ (k + 1) = 10 * 10 ^ k := by ring
      omega
    rw [h1, Nat.digits_add 10 (by norm_num) 9 (10 ^ k - 1) (by norm_num) (by left; norm_num), ih,
      List.replicate_succ]

private lemma D_repunit (k : ℕ) : D (10 ^ k - 1) = 9 * k := by
  unfold D
  rw [digits_repunit, List.sum_replicate]
  simp [Nat.mul_comm]

private lemma len_repunit (k : ℕ) : (Nat.digits 10 (10 ^ k - 1)).length = k := by
  rw [digits_repunit, List.length_replicate]

/-- The digit sum is at most `9` times the number of digits. -/
private lemma D_le (n : ℕ) : D n ≤ 9 * (Nat.digits 10 n).length := by
  unfold D
  have hb : ∀ x ∈ Nat.digits 10 n, x ≤ 9 := by
    intro x hx
    have := Nat.digits_lt_base (by norm_num) hx
    omega
  calc (Nat.digits 10 n).sum ≤ (Nat.digits 10 n).length • 9 :=
        List.sum_le_card_nsmul _ 9 hb
    _ = 9 * (Nat.digits 10 n).length := by rw [smul_eq_mul]; ring

/-- Splitting off the lowest `k` (base-10) digits adds the digit sums. -/
private lemma D_split (k q r : ℕ) (hq : 0 < q) (hr : r < 10 ^ k) :
    D (10 ^ k * q + r) = D q + D r := by
  have hlen : (Nat.digits 10 r).length ≤ k := by
    have hxle : r ≤ 10 ^ k - 1 := by omega
    calc (Nat.digits 10 r).length
        ≤ (Nat.digits 10 (10 ^ k - 1)).length := Nat.le_digits_len_le 10 r _ hxle
      _ = k := len_repunit k
  have key := Nat.digits_append_zeroes_append_digits (b := 10) (n := r) (m := q)
    (k := k - (Nat.digits 10 r).length) (by norm_num) hq
  rw [Nat.add_sub_cancel' hlen] at key
  have hval : r + 10 ^ k * q = 10 ^ k * q + r := by ring
  rw [hval] at key
  unfold D
  rw [← key]
  simp [List.sum_append, List.sum_replicate]
  ring

/-- Every positive multiple of `10^k - 1` has digit sum at least `9 k`. -/
private lemma digitSum_multiple_ge (k : ℕ) (hk : 1 ≤ k) :
    ∀ M, 0 < M → (10 ^ k - 1) ∣ M → 9 * k ≤ D M := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M IH =>
    intro hMpos hdvd
    have hP : 10 ≤ 10 ^ k := by
      calc (10 : ℕ) = 10 ^ 1 := by ring
        _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    set m := 10 ^ k - 1 with hm
    have hmval : 10 ^ k = m + 1 := by omega
    have hm1 : 1 ≤ m := by omega
    by_cases hsmall : M < 10 ^ k
    · -- only positive multiple below `10^k` is `m = 10^k - 1` itself
      obtain ⟨t, ht⟩ := hdvd
      have ht0 : t ≠ 0 := by rintro rfl; simp [ht] at hMpos
      have ht1 : t = 1 := by
        by_contra htne
        have ht2 : 2 ≤ t := by omega
        have hbig : m * 2 ≤ m * t := Nat.mul_le_mul (le_refl m) ht2
        omega
      have hDM : D M = 9 * k := by rw [ht, ht1, Nat.mul_one, hm, D_repunit]
      omega
    · -- `M ≥ 10^k`: fold the top digits down
      push_neg at hsmall
      set q := M / 10 ^ k with hqdef
      set r := M % 10 ^ k with hrdef
      have hrlt : r < 10 ^ k := Nat.mod_lt _ (by positivity)
      have hMqr : M = 10 ^ k * q + r := (Nat.div_add_mod M (10 ^ k)).symm
      have hqpos : 0 < q := by
        rw [hqdef]; exact Nat.div_pos hsmall (by positivity)
      have hmq : 0 < m * q := Nat.mul_pos hm1 hqpos
      have hexp : 10 ^ k * q = m * q + q := by rw [hmval]; ring
      -- `M = m*q + (q + r)`
      have hcong : M = m * q + (q + r) := by omega
      have hsplit : D M = D q + D r := by rw [hMqr]; exact D_split k q r hqpos hrlt
      have hMdvd : m ∣ (q + r) := by
        have hd : m ∣ (m * q + (q + r)) := by rw [← hcong]; exact hdvd
        exact (Nat.dvd_add_right (Dvd.intro q rfl)).mp hd
      have hMpos' : 0 < q + r := by omega
      have hlt : q + r < M := by omega
      have hM' : 9 * k ≤ D (q + r) := IH (q + r) hlt hMpos' hMdvd
      have hsub : D (q + r) ≤ D q + D r := D_add_le (q + r) q r rfl
      omega

/-- If `D x ≥ 9 k` then `x ≥ 10^{k-1}`. -/
private lemma big_of_D (k : ℕ) (hk : 1 ≤ k) (x : ℕ) (h : 9 * k ≤ D x) :
    10 ^ (k - 1) ≤ x := by
  by_contra hlt
  push_neg at hlt
  have hxle : x ≤ 10 ^ (k - 1) - 1 := by omega
  have hlen : (Nat.digits 10 x).length ≤ k - 1 :=
    calc (Nat.digits 10 x).length
        ≤ (Nat.digits 10 (10 ^ (k - 1) - 1)).length := Nat.le_digits_len_le 10 x _ hxle
      _ = k - 1 := len_repunit (k - 1)
  have hDle := D_le x
  omega

/-- Every value reachable at step `10^k - 1` has digit sum at least `9 k`. -/
private lemma reachable_D_ge (k : ℕ) (hk : 1 ≤ k) :
    ∀ v ∈ reachable_zeroless_factorials (10 ^ k - 1), 9 * k ≤ D v := by
  intro v hv
  have hNpos : 0 < 10 ^ k - 1 := by
    have : 10 ≤ 10 ^ k := by
      calc (10 : ℕ) = 10 ^ 1 := by ring
        _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  obtain ⟨P, hP⟩ : ∃ P, 10 ^ k - 1 = P + 1 := ⟨10 ^ k - 1 - 1, by omega⟩
  rw [hP] at hv
  have hunf : reachable_zeroless_factorials (P + 1) =
      (reachable_zeroless_factorials P).biUnion
        (fun m => {(P + 1) * m, remove_zeros ((P + 1) * m)}) := rfl
  rw [hunf] at hv
  simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hv
  obtain ⟨u, hu, hv⟩ := hv
  have hupos := reachable_pos P u hu
  have hmult : (P + 1) = 10 ^ k - 1 := hP.symm
  have hdvd : (10 ^ k - 1) ∣ ((P + 1) * u) := by
    rw [hmult]; exact Dvd.intro u rfl
  have hprodpos : 0 < (P + 1) * u := by positivity
  rcases hv with rfl | rfl
  · exact digitSum_multiple_ge k hk ((P + 1) * u) hprodpos hdvd
  · rw [D_remove]
    exact digitSum_multiple_ge k hk ((P + 1) * u) hprodpos hdvd

/-- The key bound: `a (10^k - 1) ≥ 10^{k-1}`. -/
private lemma a_ge (k : ℕ) (hk : 1 ≤ k) : 10 ^ (k - 1) ≤ a (10 ^ k - 1) := by
  apply big_of_D k hk
  have hmem : a (10 ^ k - 1) ∈ reachable_zeroless_factorials (10 ^ k - 1) :=
    Finset.min'_mem _ _
  exact reachable_D_ge k hk _ hmem

/--
Disproof of the OEIS A374265 boundedness conjecture: the sequence `a` is **unbounded**.
-/
theorem oeis_a374265_conjecture_1_boundedness.disproof :
    ¬ ∃ B : ℕ, ∀ n : ℕ, a n ≤ B := by
  rintro ⟨B, hB⟩
  have hk : 1 ≤ B + 1 := by omega
  have h1 : 10 ^ ((B + 1) - 1) ≤ a (10 ^ (B + 1) - 1) := a_ge (B + 1) hk
  have h3 : (B + 1) - 1 = B := by omega
  rw [h3] at h1
  have h2 : a (10 ^ (B + 1) - 1) ≤ B := hB _
  have h4 : B < 10 ^ B := Nat.lt_pow_self (by norm_num)
  omega
