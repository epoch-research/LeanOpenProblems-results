import FormalConjectures.Util.ProblemImports

open Nat Finset List

/--
A067599: Decimal encoding of the prime factorization of $n$: concatenation of prime factors and exponents.
If $n$ has prime factorization $p_1^{e_1} \cdot \ldots \cdot p_r^{e_r}$ with $p_1 < \ldots < p_r$,
then its decimal encoding is $p_1 e_1 \ldots p_r e_r$.
-/
noncomputable def a067599 (n : ℕ) : ℕ :=
  if n ≤ 1 then
    0 -- Sequence conventionally starts at $n=2$.
  else
    -- Helper function to get digits in most-significant-first order.
    let to_digits (k : ℕ) : List ℕ := (Nat.digits 10 k).reverse

    -- 1. Get the distinct prime factors as a sorted list.
    -- `n.factorization.support` is a Finset, and we sort it to get $p_1 < p_2 < \ldots$.
    -- The result of Finset.sort is a List ℕ.
    let sorted_primes : List ℕ := n.factorization.support.sort (· ≤ ·)

    -- 2. Build the list of all concatenated digits by iterating over the sorted primes.
    -- We fold over the list of primes, appending the digits of p and e to the accumulator.
    let all_digits : List ℕ := sorted_primes.foldr
      (fun p acc =>
        let e : ℕ := n.factorization p
        (to_digits p) ++ (to_digits e) ++ acc) []

    -- 3. Convert the list of digits (most-significant-first) back to a number.
    Nat.ofDigits 10 all_digits.reverse

lemma list_rev_helper (A B C : List ℕ) : (A ++ B ++ C).reverse = (C.reverse ++ B.reverse) ++ A.reverse := by
  simp only [List.reverse_append]
  rw [List.append_assoc]

lemma a067599_eq_of_sort (n : ℕ) (h : ¬ n ≤ 1) (q : ℕ) (qs : List ℕ) (h_sp : n.factorization.support.sort (· ≤ ·) = q :: qs) :
    a067599 n = ofDigits 10 (((digits 10 q).reverse ++ (digits 10 (n.factorization q)).reverse) ++ List.foldr (fun p acc => (digits 10 p).reverse ++ (digits 10 (n.factorization p)).reverse ++ acc) [] qs).reverse := by
  unfold a067599
  rw [if_neg h]
  dsimp only
  rw [h_sp]
  rfl

lemma ofDigits_lt_pow (b : ℕ) (hb : b > 1) (L : List ℕ) (hL : ∀ d ∈ L, d < b) : ofDigits b L < b^(L.length) := by
  induction L with
  | nil =>
    simp
  | cons d ds ih =>
    simp [ofDigits]
    have hd_lt : d < b := hL d (by simp)
    have h_all : ∀ d ∈ ds, d < b := fun x hx => hL x (by simp [hx])
    have h_ih := ih h_all
    have h1 : ofDigits b ds + 1 ≤ b^(ds.length) := h_ih
    have h2 : b * (ofDigits b ds + 1) ≤ b * b^(ds.length) := Nat.mul_le_mul_left b h1
    rw [Nat.mul_add, Nat.mul_one] at h2
    rw [mul_comm b (b^(ds.length))] at h2
    rw [← pow_succ] at h2
    omega

lemma sorted_primes_ne_nil (n : ℕ) (hn : 2 ≤ n) : n.factorization.support.sort (· ≤ ·) ≠ [] := by
  have h_ne : n ≠ 1 := by omega
  obtain ⟨p1, hp1_prime, hp1_dvd⟩ := exists_prime_and_dvd h_ne
  have hn0 : n ≠ 0 := by omega
  have hp1_mem : p1 ∈ n.factorization.support := by
    change p1 ∈ n.primeFactors
    rw [mem_primeFactors]
    exact ⟨hp1_prime, hp1_dvd, hn0⟩
  intro hc
  have hp1_mem_sort : p1 ∈ n.factorization.support.sort (· ≤ ·) := by
    rw [Finset.mem_sort]
    exact hp1_mem
  rw [hc] at hp1_mem_sort
  cases hp1_mem_sort

lemma a067599_ge_20 (n : ℕ) (hn : 2 ≤ n) : a067599 n ≥ 20 := by
  have h1 : ¬ n ≤ 1 := by omega
  have h_ne : n ≠ 1 := by omega
  obtain ⟨p1, hp1_prime, hp1_dvd⟩ := exists_prime_and_dvd h_ne
  have hn0 : n ≠ 0 := by omega
  have hp1_mem : p1 ∈ n.factorization.support := by
    change p1 ∈ n.primeFactors
    rw [mem_primeFactors]
    exact ⟨hp1_prime, hp1_dvd, hn0⟩
  have h_sp_ne : n.factorization.support.sort (· ≤ ·) ≠ [] := by
    intro hc
    have hp1_mem_sort : p1 ∈ n.factorization.support.sort (· ≤ ·) := by
      rw [Finset.mem_sort]
      exact hp1_mem
    rw [hc] at hp1_mem_sort
    cases hp1_mem_sort
  rcases List.exists_cons_of_ne_nil h_sp_ne with ⟨q, qs, h_sp⟩
  have hq_mem_sort : q ∈ n.factorization.support.sort (· ≤ ·) := by
    rw [h_sp]
    simp
  have hq_mem : q ∈ n.factorization.support := by
    rw [Finset.mem_sort] at hq_mem_sort
    exact hq_mem_sort
  have hq_prime : Nat.Prime q := by
    change q ∈ n.primeFactors at hq_mem
    rw [mem_primeFactors] at hq_mem
    exact hq_mem.1
  have hq_fac_ne_zero : n.factorization q ≠ 0 := by
    rwa [Finsupp.mem_support_iff] at hq_mem

  rw [a067599_eq_of_sort n h1 q qs h_sp]

  let A := (digits 10 q).reverse
  let B := (digits 10 (n.factorization q)).reverse
  let C := List.foldr (fun p acc => (digits 10 p).reverse ++ (digits 10 (n.factorization p)).reverse ++ acc) [] qs

  change ofDigits 10 ((A ++ B) ++ C).reverse ≥ 20

  have h_rev := list_rev_helper A B C
  rw [h_rev]
  dsimp only [A, B]
  simp only [List.reverse_reverse]

  rw [ofDigits_append]
  rw [ofDigits_digits]

  have h_len : (C.reverse ++ digits 10 (n.factorization q)).length ≥ 1 := by
    rw [List.length_append]
    have h_dig_len : (digits 10 (n.factorization q)).length ≥ 1 := by
      rw [digits_len 10 (n.factorization q) (by omega) hq_fac_ne_zero]
      omega
    omega

  have h_pow_ge : 10 ^ (C.reverse ++ digits 10 (n.factorization q)).length ≥ 10 := by
    have h_pow := Nat.pow_le_pow_right (by omega : 10 > 0) h_len
    exact h_pow

  have hq_ge : q ≥ 2 := hq_prime.two_le
  have h_mul : 20 ≤ 10 ^ (C.reverse ++ digits 10 (n.factorization q)).length * q := Nat.mul_le_mul h_pow_ge hq_ge
  omega

lemma sorted_primes_prime (n : ℕ) (hp : n.Prime) : n.factorization.support.sort (· ≤ ·) = [n] := by
  have h_support : n.factorization.support = {n} := by
    rw [support_factorization]
    exact hp.primeFactors
  rw [h_support]
  exact Finset.sort_singleton (· ≤ ·) n

lemma factorization_prime_self (n : ℕ) (hp : n.Prime) : n.factorization n = 1 := by
  simp [Nat.Prime.factorization hp]

lemma a067599_prime (n : ℕ) (hp : n.Prime) : a067599 n = 10 * n + 1 := by
  have h1 : ¬ n ≤ 1 := by have := hp.two_le; omega
  have h_sp := sorted_primes_prime n hp
  rw [a067599_eq_of_sort n h1 n [] h_sp]
  have h_fac := factorization_prime_self n hp
  rw [h_fac]
  dsimp only [List.foldr]
  have hd1 : digits 10 1 = [1] := by apply digits_of_lt 10 1 <;> decide
  rw [hd1]
  simp only [List.reverse_singleton, List.append_assoc]
  rw [List.append_nil]
  rw [List.reverse_append]
  simp only [List.reverse_reverse, List.reverse_singleton]
  change ofDigits 10 (1 :: digits 10 n) = 10 * n + 1
  rw [ofDigits_cons]
  rw [ofDigits_digits]
  omega

lemma a067599_prime_ne_self (n : ℕ) (hp : n.Prime) : a067599 n ≠ n := by
  intro h
  have h_eq := a067599_prime n hp
  rw [h_eq] at h
  omega

lemma a067599_prime_pow (n : ℕ) (h : ¬ n ≤ 1) (q : ℕ) (h_sp : n.factorization.support.sort (· ≤ ·) = [q]) :
    a067599 n = n.factorization q + q * 10^((digits 10 (n.factorization q)).length) := by
  rw [a067599_eq_of_sort n h q [] h_sp]
  dsimp only [List.foldr]
  rw [List.append_nil]
  rw [List.reverse_append]
  simp only [List.reverse_reverse]
  rw [ofDigits_append]
  rw [ofDigits_digits]
  rw [ofDigits_digits]
  ring

lemma pow_length_digits_le_mul (e : ℕ) (he : e > 0) : 10 ^ (digits 10 e).length ≤ 10 * e :=
  Nat.base_pow_length_digits_le 10 e (by decide) (Nat.ne_of_gt he)

lemma digits_ten (e : ℕ) (he : 2 ≤ e) (he10 : e < 10) : digits 10 e = [e] := by
  have he_nz : e ≠ 0 := by omega
  exact digits_of_lt 10 e he_nz he10

lemma pow_ge_mul_self_of_ge2 (q e : ℕ) (hq : q ≥ 2) (he : e ≥ 8) : q^e > (10 * q + 1) * e := by
  induction e, he using Nat.le_induction with
  | base =>
    have hq_pow : q^8 = q^7 * q := by ring
    rw [hq_pow]
    have h1 : q^7 * q ≥ 2^7 * q := Nat.mul_le_mul_right q (Nat.pow_le_pow_left hq 7)
    have h_pow7 : 2^7 = 128 := rfl
    omega
  | succ e he ih =>
    have hq_pow_succ : q^(e+1) = q^e * q := by ring
    have h_rhs : (10 * q + 1) * (e + 1) = (10 * q + 1) * e + 10 * q + 1 := by ring
    rw [hq_pow_succ, h_rhs]
    have h1 : q^e * q ≥ q^e * 2 := Nat.mul_le_mul_left (q^e) hq
    have h2 : q^e * 2 > ((10 * q + 1) * e) * 2 := by omega
    have h3 : ((10 * q + 1) * e) * 2 = (10 * q + 1) * e + (10 * q + 1) * e := by ring
    have h4 : (10 * q + 1) * e ≥ (10 * q + 1) * 8 := Nat.mul_le_mul_left (10 * q + 1) he
    omega

lemma prime_power_ne_self_small (q e : ℕ) (hq : q.Prime) (he : 2 ≤ e) (he7 : e < 8) :
    e + q * 10 ≠ q^e := by
  by_cases hq11 : q < 11
  · interval_cases q
    · have : ¬ Nat.Prime 0 := by decide
      contradiction
    · have : ¬ Nat.Prime 1 := by decide
      contradiction
    all_goals
      interval_cases e <;> decide
  · -- q ≥ 11
    have hq11' : q ≥ 11 := by omega
    have h_pow_ge : q^e ≥ q^2 := by
      have : e ≥ 2 := by omega
      exact Nat.pow_le_pow_right (by omega) this
    have h_q2 : q^2 ≥ 11 * q := by
      rw [sq]
      exact Nat.mul_le_mul_right q hq11'
    have h_gt : q^e > q * 10 + e := by
      have : 11 * q = q * 10 + q := by ring
      omega
    omega

lemma prime_power_ne_self (q e : ℕ) (hq : q.Prime) (he : 2 ≤ e) :
    e + q * 10^(digits 10 e).length ≠ q^e := by
  by_cases he8 : e ≥ 8
  · -- Case e ≥ 8
    have hq2 : q ≥ 2 := hq.two_le
    have h_pow := pow_ge_mul_self_of_ge2 q e hq2 he8
    have he_gt : e > 0 := by
      clear h_pow hq
      omega
    have h_dig_le := pow_length_digits_le_mul e he_gt
    generalize hL : (digits 10 e).length = L at h_dig_le ⊢
    have h_mul_le : q * 10^L ≤ q * (10 * e) := Nat.mul_le_mul_left q h_dig_le
    have h_rhs_le : e + q * 10^L ≤ (10 * q + 1) * e := by
      have h_ring : (10 * q + 1) * e = q * (10 * e) + e := by ring
      rw [h_ring]
      omega
    have h_final : e + q * 10^L < q^e := by
      have h1 : e + q * 10^L ≤ (10 * q + 1) * e := h_rhs_le
      have h2 : (10 * q + 1) * e < q^e := h_pow
      omega
    omega
  · -- Case e < 8
    have he7 : e < 8 := by
      clear hq
      omega
    have he10 : e < 10 := by
      clear hq
      omega
    have h_dig := digits_ten e he he10
    have h_len : (digits 10 e).length = 1 := by rw [h_dig]; rfl
    rw [h_len]
    change e + q * 10 ≠ q^e
    exact prime_power_ne_self_small q e hq he he7

lemma support_eq_singleton_of_sort (n q : ℕ) (h_sp : n.factorization.support.sort (· ≤ ·) = [q]) :
    n.factorization.support = {q} := by
  ext x
  rw [Finset.mem_singleton]
  have h_mem : x ∈ n.factorization.support ↔ x ∈ n.factorization.support.sort (· ≤ ·) := by
    rw [Finset.mem_sort]
  rw [h_mem, h_sp]
  simp

lemma eq_pow_of_sort_eq_singleton (n : ℕ) (hn : n ≠ 0) (q : ℕ) (h_sp : n.factorization.support.sort (· ≤ ·) = [q]) :
    n = q ^ (n.factorization q) := by
  have h_sup := support_eq_singleton_of_sort n q h_sp
  have h_prod := factorization_prod_pow_eq_self hn
  unfold Finsupp.prod at h_prod
  rw [h_sup] at h_prod
  rw [Finset.prod_singleton] at h_prod
  exact h_prod.symm

/-- Is there any solution to a(n) = n? - _Franklin T. Adams-Watters_, Dec 18 2006 -/
lemma foldr_append_one {α β : Type _} (f : α → β → β) (acc : β) (L : List α) (x : α) :
    List.foldr f acc (L ++ [x]) = List.foldr f (f x acc) L := by
  induction L with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.cons_append]
    change f y (List.foldr f acc (ys ++ [x])) = f y (List.foldr f (f x acc) ys)
    rw [ih]

lemma foldr_append_acc (n : ℕ) (acc : List ℕ) (L : List ℕ) :
    List.foldr (fun p acc' => (digits 10 p).reverse ++ (digits 10 (n.factorization p)).reverse ++ acc') acc L =
    List.foldr (fun p acc' => (digits 10 p).reverse ++ (digits 10 (n.factorization p)).reverse ++ acc') [] L ++ acc := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    change (digits 10 x).reverse ++ (digits 10 (n.factorization x)).reverse ++ List.foldr (fun p acc' => (digits 10 p).reverse ++ (digits 10 (n.factorization p)).reverse ++ acc') acc xs =
           ((digits 10 x).reverse ++ (digits 10 (n.factorization x)).reverse ++ List.foldr (fun p acc' => (digits 10 p).reverse ++ (digits 10 (n.factorization p)).reverse ++ acc') [] xs) ++ acc
    rw [ih]
    simp only [List.append_assoc]

lemma list_eq_append_singleton_of_ne_nil {α : Type _} : ∀ (L : List α), L ≠ [] → ∃ (ms : List α) (x : α), L = ms ++ [x]
  | [] => by intro h; contradiction
  | [x] => by
    intro _
    use [], x
    rfl
  | x :: y :: ys => by
    intro _
    have h_ne : y :: ys ≠ [] := by simp
    obtain ⟨ms, z, hz⟩ := list_eq_append_singleton_of_ne_nil (y :: ys) h_ne
    use x :: ms, z
    rw [hz]
    rfl

lemma a067599_composite_split (n : ℕ) (hn : ¬ n ≤ 1) (q : ℕ) (qs : List ℕ) (h_sp : n.factorization.support.sort (· ≤ ·) = q :: qs)
    (ms : List ℕ) (p_r : ℕ) (h_qs_eq : qs = ms ++ [p_r]) :
    let e_r := n.factorization p_r
    let L_er := (digits 10 e_r).length
    let L_pr := (digits 10 p_r).length
    let C := List.foldr (fun p acc => (digits 10 p).reverse ++ (digits 10 (n.factorization p)).reverse ++ acc) [] (q :: ms)
    a067599 n = e_r + p_r * 10^L_er + (ofDigits 10 C.reverse) * 10^(L_er + L_pr) := by
  intro e_r L_er L_pr C
  unfold a067599
  rw [if_neg hn]
  dsimp only
  rw [h_sp]
  rw [h_qs_eq]
  let f := fun p acc => (digits 10 p).reverse ++ (digits 10 (n.factorization p)).reverse ++ acc
  change ofDigits 10 (List.foldr f [] ((q :: ms) ++ [p_r])).reverse = e_r + p_r * 10^L_er + (ofDigits 10 C.reverse) * 10^(L_er + L_pr)
  rw [foldr_append_one f [] (q :: ms) p_r]
  dsimp only [f]
  change ofDigits 10 (List.foldr f ((digits 10 p_r).reverse ++ (digits 10 (n.factorization p_r)).reverse ++ []) (q :: ms)).reverse =
    e_r + p_r * 10^L_er + (ofDigits 10 C.reverse) * 10^(L_er + L_pr)
  rw [List.append_nil]
  rw [foldr_append_acc n ((digits 10 p_r).reverse ++ (digits 10 (n.factorization p_r)).reverse) (q :: ms)]
  change ofDigits 10 (C ++ ((digits 10 p_r).reverse ++ (digits 10 e_r).reverse)).reverse =
    e_r + p_r * 10^L_er + (ofDigits 10 C.reverse) * 10^(L_er + L_pr)
  have h_rev : (C ++ ((digits 10 p_r).reverse ++ (digits 10 e_r).reverse)).reverse =
    (digits 10 e_r ++ digits 10 p_r) ++ C.reverse := by
    simp only [List.reverse_append, List.reverse_reverse]
  rw [h_rev]
  rw [ofDigits_append]
  rw [ofDigits_append]
  rw [ofDigits_digits]
  rw [ofDigits_digits]
  rw [List.length_append]
  ring

lemma foldr_digits_lt_ten (n : ℕ) (L : List ℕ) :
    ∀ d ∈ List.foldr (fun p acc => (digits 10 p).reverse ++ (digits 10 (n.factorization p)).reverse ++ acc) [] L, d < 10 := by
  induction L with
  | nil =>
    intro d hd
    cases hd
  | cons x xs ih =>
    intro d hd
    change d ∈ ((digits 10 x).reverse ++ (digits 10 (n.factorization x)).reverse) ++ List.foldr (fun p acc => (digits 10 p).reverse ++ (digits 10 (n.factorization p)).reverse ++ acc) [] xs at hd
    rcases List.mem_append.mp hd with h | h
    · rcases List.mem_append.mp h with h' | h'
      · rw [List.mem_reverse] at h'
        exact digits_lt_base (by decide) h'
      · rw [List.mem_reverse] at h'
        exact digits_lt_base (by decide) h'
    · exact ih d h

lemma finset_prod_eq_sort_prod (s : Finset ℕ) (f : ℕ → ℕ) :
    s.prod f = ((s.sort (· ≤ ·)).map f).prod := by
  unfold Finset.prod
  have h := sort_eq s (· ≤ ·)
  rw [← h]
  rfl

lemma mul_le_pow_of_ge_two (x e : ℕ) (hx : x ≥ 2) (he : e ≥ 1) : x * e ≤ x^e := by
  have hx0 : 0 < x := by omega
  induction e, he using Nat.le_induction with
  | base =>
    simp
  | succ e he ih =>
    rw [pow_succ]
    have h1 : x * (e + 1) = x * e + x := by ring
    rw [h1]
    have h2 : x^e * x ≥ x^e * 2 := Nat.mul_le_mul_left (x^e) hx
    have h3 : x^e * 2 = x^e + x^e := by ring
    have h4 : x^e ≥ x := by
      have := Nat.pow_le_pow_right hx0 he
      rw [pow_one] at this
      exact this
    have h_trans : x * e + x ≤ x^e + x^e := Nat.add_le_add ih h4
    have h_trans2 : x^e + x^e ≤ x^e * x := by
      rw [← h3]
      exact h2
    exact Nat.le_trans h_trans h_trans2

lemma prod_le_prod_pow (n : ℕ) (L : List ℕ) (h_pos : ∀ p ∈ L, p ≥ 2) (h_fac : ∀ p ∈ L, n.factorization p ≥ 1) :
    (L.map (fun p => p * n.factorization p)).prod ≤ (L.map (fun p => p^(n.factorization p))).prod := by
  induction L with
  | nil =>
    simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons]
    have h_pos_x : x ≥ 2 := h_pos x (by simp)
    have h_fac_x : n.factorization x ≥ 1 := h_fac x (by simp)
    have h_pe_le := mul_le_pow_of_ge_two x (n.factorization x) h_pos_x h_fac_x
    have h_xs_pos : ∀ p ∈ xs, p ≥ 2 := fun p hp => h_pos p (by simp [hp])
    have h_xs_fac : ∀ p ∈ xs, n.factorization p ≥ 1 := fun p hp => h_fac p (by simp [hp])
    have h_ih := ih h_xs_pos h_xs_fac
    exact Nat.mul_le_mul h_pe_le h_ih

lemma foldr_length_bound (n : ℕ) (L : List ℕ) (h_pos : ∀ p ∈ L, p > 0) (h_fac_pos : ∀ p ∈ L, n.factorization p > 0) :
    10^(List.foldr (fun p acc => (digits 10 p).reverse ++ (digits 10 (n.factorization p)).reverse ++ acc) [] L).length ≤
    100^(L.length) * (L.map (fun p => p * n.factorization p)).prod := by
  induction L with
  | nil =>
    simp
  | cons x xs ih =>
    simp only [List.length_cons, pow_succ]
    dsimp [List.foldr]
    have h_len : ((digits 10 x).reverse ++ (digits 10 (n.factorization x)).reverse ++ List.foldr (fun p acc => (digits 10 p).reverse ++ (digits 10 (n.factorization p)).reverse ++ acc) [] xs).length =
      (digits 10 x).length + (digits 10 (n.factorization x)).length + (List.foldr (fun p acc => (digits 10 p).reverse ++ (digits 10 (n.factorization p)).reverse ++ acc) [] xs).length := by
      simp only [List.length_append, List.length_reverse]
    rw [h_len]
    rw [pow_add, pow_add]
    have h_pos_x : x > 0 := h_pos x (by simp)
    have h_fac_pos_x : n.factorization x > 0 := h_fac_pos x (by simp)
    have h1 := pow_length_digits_le_mul x h_pos_x
    have h2 := pow_length_digits_le_mul (n.factorization x) h_fac_pos_x
    have h_xs_pos : ∀ p ∈ xs, p > 0 := fun p hp => h_pos p (by simp [hp])
    have h_xs_fac_pos : ∀ p ∈ xs, n.factorization p > 0 := fun p hp => h_fac_pos p (by simp [hp])
    have h3 := ih h_xs_pos h_xs_fac_pos
    have h4 : 10^(digits 10 x).length * 10^(digits 10 (n.factorization x)).length ≤ 100 * (x * n.factorization x) := by
      calc 10^(digits 10 x).length * 10^(digits 10 (n.factorization x)).length ≤ (10 * x) * (10 * n.factorization x) := Nat.mul_le_mul h1 h2
      _ = 100 * (x * n.factorization x) := by ring
    have h5 : 10^(digits 10 x).length * 10^(digits 10 (n.factorization x)).length * 10^(List.foldr (fun p acc => (digits 10 p).reverse ++ (digits 10 (n.factorization p)).reverse ++ acc) [] xs).length ≤
      (100 * (x * n.factorization x)) * (100^(xs.length) * (xs.map (fun p => p * n.factorization p)).prod) := Nat.mul_le_mul h4 h3
    have h_rearrange : (100 * (x * n.factorization x)) * (100^(xs.length) * (xs.map (fun p => p * n.factorization p)).prod) =
      100^(xs.length + 1) * (x * n.factorization x * (xs.map (fun p => p * n.factorization p)).prod) := by
      ring
    rw [h_rearrange] at h5
    exact h5

lemma sorted_primes_last_ge_strong (q : ℕ) (ms : List ℕ) (p_r : ℕ)
    (h_sorted : List.Pairwise (· ≤ ·) (q :: (ms ++ [p_r])))
    (h_nodup : (q :: (ms ++ [p_r])).Nodup) :
    p_r ≥ q + 1 + ms.length := by
  induction ms generalizing q
  · -- nil
    simp only [List.length_nil]
    have h_rel : q < p_r := by
      rw [List.pairwise_cons] at h_sorted
      have h_le := h_sorted.1 p_r (by simp)
      rw [List.nodup_cons] at h_nodup
      have h_ne := h_nodup.1
      simp at h_ne
      omega
    omega
  · -- cons y ys ih
    rename_i y ys ih
    simp only [List.length_cons]
    have h_sorted' : List.Pairwise (· ≤ ·) (y :: (ys ++ [p_r])) := by
      rw [List.pairwise_cons] at h_sorted
      exact h_sorted.2
    have h_nodup' : (y :: (ys ++ [p_r])).Nodup := by
      rw [List.nodup_cons] at h_nodup
      exact h_nodup.2
    have h_rel : q < y := by
      rw [List.pairwise_cons] at h_sorted
      have h_le := h_sorted.1 y (by simp)
      rw [List.nodup_cons] at h_nodup
      have h_ne : q ≠ y := by
        intro hc
        have : q ∈ y :: ys ++ [p_r] := by
          rw [hc]
          simp
        exact h_nodup.1 this
      omega
    have h_ih := ih y h_sorted' h_nodup'
    omega

lemma sorted_primes_last_ge (q : ℕ) (ms : List ℕ) (p_r : ℕ)
    (h_sorted : List.Pairwise (· ≤ ·) (q :: (ms ++ [p_r])))
    (h_nodup : (q :: (ms ++ [p_r])).Nodup) (hq : q ≥ 2) :
    p_r ≥ ms.length + 3 := by
  have h := sorted_primes_last_ge_strong q ms p_r h_sorted h_nodup
  omega

lemma sq_mod (y m : ℕ) : y^2 % m = (y % m)^2 % m := by
  have h1 : y^2 = y * y := by ring
  have h2 : (y % m)^2 = (y % m) * (y % m) := by ring
  rw [h1, h2]
  exact Nat.mul_mod y y m

set_option maxRecDepth 200000
lemma no_qr_717_lt : ∀ y < 719, y^2 % 719 ≠ 717 := by decide

lemma no_qr_717 (y : ℕ) : y^2 % 719 ≠ 717 := by
  rw [sq_mod]
  apply no_qr_717_lt
  exact Nat.mod_lt _ (by decide)

lemma mod_power_step (a b m : ℕ) (h : a % m = b % m) (n : ℕ) : a^n % m = b^n % m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    have h1 : (a^n * a) % m = ((a^n % m) * (a % m)) % m := Nat.mul_mod _ _ _
    have h2 : (b^n * b) % m = ((b^n % m) * (b % m)) % m := Nat.mul_mod _ _ _
    rw [h1, h2, ih, h]

lemma mod_719_no_sol (L : ℕ) : 10^L % 719 ≠ 717 := by
  intro hc
  have h27_10 : (27^2) % 719 = 10 % 719 := by decide
  have h_qr := mod_power_step (27^2) 10 719 h27_10 L
  have h_pow : (27^2)^L = (27^L)^2 := by
    rw [← pow_mul, mul_comm 2 L, pow_mul]
  rw [h_pow] at h_qr
  rw [← h_qr] at hc
  exact no_qr_717 (27^L) hc


theorem oeis_67599_conjecture_0.disproof : ¬ ∃ n, 2 ≤ n ∧ a067599 n = n := by
  intro ⟨n, hn, h_eq⟩
  have hn20 : n ≥ 20 := by
    have h_ge := a067599_ge_20 n hn
    omega
  have hn1 : ¬ n ≤ 1 := by omega
  by_cases hp : n.Prime
  · exact a067599_prime_ne_self n hp h_eq
  · -- Case composite
    have h_sp_ne := sorted_primes_ne_nil n hn
    rcases List.exists_cons_of_ne_nil h_sp_ne with ⟨q, qs, h_sp⟩
    have hq_mem_sort : q ∈ n.factorization.support.sort (· ≤ ·) := by
      rw [h_sp]
      simp
    have hq_mem : q ∈ n.factorization.support := by
      rw [Finset.mem_sort] at hq_mem_sort
      exact hq_mem_sort
    have hq_prime : Nat.Prime q := by
      change q ∈ n.primeFactors at hq_mem
      rw [mem_primeFactors] at hq_mem
      exact hq_mem.1
    by_cases h_qs : qs = []
    · -- qs is empty: prime power q^e with e ≥ 2
      rw [h_qs] at h_sp
      have h_pow := eq_pow_of_sort_eq_singleton n (by omega) q h_sp
      have h_eq_prime_pow := a067599_prime_pow n hn1 q h_sp
      rw [h_eq] at h_eq_prime_pow
      have he_ge_2 : 2 ≤ n.factorization q := by
        by_contra h_lt
        have h_lt' : n.factorization q ≤ 1 := by omega
        interval_cases h_val : n.factorization q
        · -- factorization q = 0
          have h0 : n.factorization q ≠ 0 := by
            rwa [Finsupp.mem_support_iff] at hq_mem
          rw [h_val] at h0
          contradiction
        · -- factorization q = 1
          have hn_prime : n = q := by rw [h_pow]; ring
          rw [hn_prime] at hp
          contradiction
      nth_rw 1 [h_pow] at h_eq_prime_pow
      exact prime_power_ne_self q (n.factorization q) hq_prime he_ge_2 h_eq_prime_pow.symm
    · -- qs is not empty (r ≥ 2)
      obtain ⟨ms, p_r, h_qs_eq⟩ := list_eq_append_singleton_of_ne_nil qs h_qs
      let e_r := n.factorization p_r
      let L_er := (digits 10 e_r).length
      let L_pr := (digits 10 p_r).length
      let C := List.foldr (fun p acc => (digits 10 p).reverse ++ (digits 10 (n.factorization p)).reverse ++ acc) [] (q :: ms)
      have h_a_eq := a067599_composite_split n hn1 q qs h_sp ms p_r h_qs_eq
      dsimp only at h_a_eq
      rw [h_eq] at h_a_eq
      have hn0 : n ≠ 0 := by omega
      have h_prod := factorization_prod_pow_eq_self hn0
      unfold Finsupp.prod at h_prod
      rw [finset_prod_eq_sort_prod] at h_prod
      rw [h_sp] at h_prod
      rw [h_qs_eq] at h_prod
      rw [← List.cons_append] at h_prod
      rw [List.map_append] at h_prod
      rw [List.prod_append] at h_prod
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h_prod
      let n' := ((q :: ms).map (fun p => p ^ n.factorization p)).prod
      change n' * p_r ^ e_r = n at h_prod
      have h_mem : ∀ p ∈ q :: ms, p ∈ n.factorization.support := by
        intro p hp
        rw [← Finset.mem_sort (· ≤ ·)]
        rw [h_sp]
        rw [h_qs_eq]
        rw [← List.cons_append]
        exact List.mem_append_left [p_r] hp
      have h_pos : ∀ p ∈ q :: ms, p ≥ 2 := by
        intro p hp
        have h_mem' := h_mem p hp
        change p ∈ n.primeFactors at h_mem'
        rw [mem_primeFactors] at h_mem'
        exact h_mem'.1.two_le
      have h_fac : ∀ p ∈ q :: ms, n.factorization p ≥ 1 := by
        intro p hp
        have h_mem' := h_mem p hp
        rw [Finsupp.mem_support_iff] at h_mem'
        omega
      have h_pos_gt0 : ∀ p ∈ q :: ms, p > 0 := fun p hp => by
        have := h_pos p hp
        omega
      have h_fac_pos : ∀ p ∈ q :: ms, n.factorization p > 0 := fun p hp => by
        have := h_fac p hp
        omega
      have h_len_bound := foldr_length_bound n (q :: ms) h_pos_gt0 h_fac_pos
      have h_prod_le := prod_le_prod_pow n (q :: ms) h_pos h_fac
      have h_bound_combined : 10^(C.length) ≤ 100^(ms.length + 1) * n' := by
        calc 10^(C.length) ≤ 100^(ms.length + 1) * ((q :: ms).map (fun p => p * n.factorization p)).prod := h_len_bound
        _ ≤ 100^(ms.length + 1) * n' := Nat.mul_le_mul_left _ h_prod_le
      have hC_digits : ∀ d ∈ C.reverse, d < 10 := by
        intro d hd
        rw [List.mem_reverse] at hd
        exact foldr_digits_lt_ten n (q :: ms) d hd
      have hA_lt_pow := ofDigits_lt_pow 10 (by decide) C.reverse hC_digits
      rw [List.length_reverse] at hA_lt_pow
      have hA_lt : ofDigits 10 C.reverse < 100^(ms.length + 1) * n' := by
        omega
      have hp_r_ge : p_r ≥ ms.length + 3 := by
        have h_sorted_all : List.Pairwise (· ≤ ·) (q :: (ms ++ [p_r])) := by
          rw [← h_qs_eq]
          rw [← h_sp]
          exact Finset.pairwise_sort n.factorization.support (· ≤ ·)
        have h_nodup_all : (q :: (ms ++ [p_r])).Nodup := by
          rw [← h_qs_eq]
          rw [← h_sp]
          exact Finset.sort_nodup n.factorization.support (· ≤ ·)
        have hq_ge : q ≥ 2 := hq_prime.two_le
        exact sorted_primes_last_ge q ms p_r h_sorted_all h_nodup_all hq_ge
      have hp_r_gt0 : p_r > 0 := by omega
      have hp_r_ge2 : p_r ≥ 2 := by omega
      have he_r_gt0 : e_r > 0 := by
        have hp_r_mem : p_r ∈ n.factorization.support := by
          rw [← Finset.mem_sort (· ≤ ·)]
          rw [h_sp]
          rw [h_qs_eq]
          simp
        rw [Finsupp.mem_support_iff] at hp_r_mem
        omega
      have h_rhs_bound : 2 + 10 * 100^(ms.length + 1) * n' ≤ 11 * 100^(ms.length + 1) * n' := by
        have h_pow_ge : 100^(ms.length + 1) ≥ 100 := by
          have := Nat.pow_le_pow_right (by decide : 100 > 0) (by omega : ms.length + 1 ≥ 1)
          exact this
        have h_n'_gt0 : n' > 0 := by
          by_contra hc
          have : n' = 0 := by omega
          rw [this, zero_mul] at h_prod
          omega
        have h_mul_ge : 100^(ms.length + 1) * n' ≥ 100 := by
          calc 100^(ms.length + 1) * n' ≥ 100 * 1 := Nat.mul_le_mul h_pow_ge h_n'_gt0
          _ = 100 := by ring
        rw [mul_assoc, mul_assoc]
        omega
      change n' * p_r ^ (n.factorization p_r) = n at h_prod
      nth_rw 1 [← h_prod] at h_a_eq
      have h_a_eq' : n' * p_r ^ (n.factorization p_r) = (n.factorization p_r + p_r * 10^(digits 10 (n.factorization p_r)).length) + ofDigits 10 C.reverse * 10^((digits 10 (n.factorization p_r)).length + (digits 10 p_r).length) := h_a_eq
      have he_r_lt : n.factorization p_r < 10^(digits 10 (n.factorization p_r)).length := by
        have h_dig_lt : ∀ d ∈ digits 10 (n.factorization p_r), d < 10 := fun d hd => digits_lt_base (by decide) hd
        have h_lt := ofDigits_lt_pow 10 (by decide) (digits 10 (n.factorization p_r)) h_dig_lt
        rw [ofDigits_digits 10 (n.factorization p_r)] at h_lt
        exact h_lt
      have h_term1_lt : n.factorization p_r + p_r * 10^(digits 10 (n.factorization p_r)).length < 2 * p_r * 10^(digits 10 (n.factorization p_r)).length := by
        have h_le_mul : 10^(digits 10 (n.factorization p_r)).length ≤ p_r * 10^(digits 10 (n.factorization p_r)).length := by
          calc 10^(digits 10 (n.factorization p_r)).length = 1 * 10^(digits 10 (n.factorization p_r)).length := by ring
          _ ≤ p_r * 10^(digits 10 (n.factorization p_r)).length := Nat.mul_le_mul_right _ (by omega : 1 ≤ p_r)
        calc n.factorization p_r + p_r * 10^(digits 10 (n.factorization p_r)).length < 10^(digits 10 (n.factorization p_r)).length + p_r * 10^(digits 10 (n.factorization p_r)).length := Nat.add_lt_add_right he_r_lt _
        _ ≤ p_r * 10^(digits 10 (n.factorization p_r)).length + p_r * 10^(digits 10 (n.factorization p_r)).length := Nat.add_le_add_right h_le_mul _
        _ = 2 * p_r * 10^(digits 10 (n.factorization p_r)).length := by ring
      have h_L_pr := pow_length_digits_le_mul p_r hp_r_gt0
      have h_pow_add : 10^((digits 10 (n.factorization p_r)).length + (digits 10 p_r).length) = 10^(digits 10 (n.factorization p_r)).length * 10^(digits 10 p_r).length := by rw [pow_add]
      have h_term2_le : ofDigits 10 C.reverse * 10^((digits 10 (n.factorization p_r)).length + (digits 10 p_r).length) < (100^(ms.length + 1) * n') * 10^(digits 10 (n.factorization p_r)).length * (10 * p_r) := by
        calc ofDigits 10 C.reverse * 10^((digits 10 (n.factorization p_r)).length + (digits 10 p_r).length) = ofDigits 10 C.reverse * 10^(digits 10 (n.factorization p_r)).length * 10^(digits 10 p_r).length := by
               rw [h_pow_add]
               ring
        _ < (100^(ms.length + 1) * n') * 10^(digits 10 (n.factorization p_r)).length * 10^(digits 10 p_r).length := by
               have h_pos_pr : 10^(digits 10 p_r).length > 0 := Nat.pow_pos (by decide : 10 > 0)
               have h_pos_er : 10^(digits 10 (n.factorization p_r)).length > 0 := Nat.pow_pos (by decide : 10 > 0)
               have h_lt_mul : ofDigits 10 C.reverse * 10^(digits 10 (n.factorization p_r)).length < (100^(ms.length + 1) * n') * 10^(digits 10 (n.factorization p_r)).length :=
                 Nat.mul_lt_mul_of_pos_right hA_lt h_pos_er
               exact Nat.mul_lt_mul_of_pos_right h_lt_mul h_pos_pr
        _ ≤ (100^(ms.length + 1) * n') * 10^(digits 10 (n.factorization p_r)).length * (10 * p_r) := Nat.mul_le_mul_left _ h_L_pr
      have h_sum_lt : n' * p_r ^ (n.factorization p_r) < p_r * 10^(digits 10 (n.factorization p_r)).length * (2 + 10 * 100^(ms.length + 1) * n') := by
        calc n' * p_r ^ (n.factorization p_r) = (n.factorization p_r + p_r * 10^(digits 10 (n.factorization p_r)).length) + ofDigits 10 C.reverse * 10^((digits 10 (n.factorization p_r)).length + (digits 10 p_r).length) := h_a_eq'
        _ < 2 * p_r * 10^(digits 10 (n.factorization p_r)).length + (100^(ms.length + 1) * n') * 10^(digits 10 (n.factorization p_r)).length * (10 * p_r) := Nat.add_lt_add h_term1_lt h_term2_le
        _ = p_r * 10^(digits 10 (n.factorization p_r)).length * (2 + 10 * 100^(ms.length + 1) * n') := by ring
      have h_pow_split : p_r^(n.factorization p_r) = p_r^(n.factorization p_r - 1) * p_r := by
        have h_eq : n.factorization p_r = n.factorization p_r - 1 + 1 := (Nat.sub_add_cancel he_r_gt0).symm
        nth_rw 1 [h_eq]
        rw [pow_add, pow_one]
      have h_div_pr : n' * p_r^(n.factorization p_r - 1) < 10^(digits 10 (n.factorization p_r)).length * (2 + 10 * 100^(ms.length + 1) * n') := by
        have h_lhs : n' * p_r ^ (n.factorization p_r) = (n' * p_r^(n.factorization p_r - 1)) * p_r := by
          rw [h_pow_split]
          ring
        have h_rhs : p_r * 10^(digits 10 (n.factorization p_r)).length * (2 + 10 * 100^(ms.length + 1) * n') = (10^(digits 10 (n.factorization p_r)).length * (2 + 10 * 100^(ms.length + 1) * n')) * p_r := by ring
        rw [h_lhs, h_rhs] at h_sum_lt
        exact Nat.lt_of_mul_lt_mul_right h_sum_lt
      have h_L_er := pow_length_digits_le_mul (n.factorization p_r) he_r_gt0
      have h_bound_final : 10^(digits 10 (n.factorization p_r)).length * (2 + 10 * 100^(ms.length + 1) * n') ≤ 110 * 100^(ms.length + 1) * n' * n.factorization p_r := by
        calc 10^(digits 10 (n.factorization p_r)).length * (2 + 10 * 100^(ms.length + 1) * n') ≤ (10 * n.factorization p_r) * (2 + 10 * 100^(ms.length + 1) * n') := Nat.mul_le_mul_right _ h_L_er
        _ ≤ (10 * n.factorization p_r) * (11 * 100^(ms.length + 1) * n') := Nat.mul_le_mul_left _ h_rhs_bound
        _ = 110 * 100^(ms.length + 1) * n' * n.factorization p_r := by ring
      have h_bound_n' : n' * p_r^(n.factorization p_r - 1) < (110 * 100^(ms.length + 1) * n.factorization p_r) * n' := by
        calc n' * p_r^(n.factorization p_r - 1) < 10^(digits 10 (n.factorization p_r)).length * (2 + 10 * 100^(ms.length + 1) * n') := h_div_pr
        _ ≤ 110 * 100^(ms.length + 1) * n' * n.factorization p_r := h_bound_final
        _ = (110 * 100^(ms.length + 1) * n.factorization p_r) * n' := by ring
      rw [mul_comm] at h_bound_n'
      have h_n'_gt0 : n' > 0 := by
        by_contra hc
        have : n' = 0 := by omega
        rw [this, zero_mul] at h_prod
        omega
      have h_pr_er_bound : p_r^(n.factorization p_r - 1) < 110 * 100^(ms.length + 1) * n.factorization p_r := Nat.lt_of_mul_lt_mul_right h_bound_n'
      by_cases he_r_eq1 : n.factorization p_r = 1
      · -- Case e_r = 1
        have h_rewritten : n' * p_r = 1 + 10 * p_r + 10 * ofDigits 10 C.reverse * 10^L_pr := by
          rw [he_r_eq1] at h_a_eq'
          rw [pow_one] at h_a_eq'
          have h_len_1 : (digits 10 1).length = 1 := by
            have hd1 : digits 10 1 = [1] := by apply digits_of_lt 10 1 <;> decide
            rw [hd1]
            rfl
          rw [h_len_1] at h_a_eq'
          rw [pow_one] at h_a_eq'
          rw [pow_add] at h_a_eq'
          rw [pow_one] at h_a_eq'
          calc n' * p_r = 1 + p_r * 10 + ofDigits 10 C.reverse * (10 * 10^L_pr) := h_a_eq'
          _ = 1 + 10 * p_r + 10 * ofDigits 10 C.reverse * 10^L_pr := by ring
        by_cases hq2 : q = 2
        · have h_dvd_n' : 2 ∣ n' := by
            change 2 ∣ ((q :: ms).map (fun p => p ^ n.factorization p)).prod
            rw [hq2]
            simp only [List.map_cons, List.prod_cons]
            have h_fac_q := h_fac 2 (by rw [← hq2]; exact List.Mem.head ms)
            have h_pow_split : 2 ^ n.factorization 2 = 2 * 2^(n.factorization 2 - 1) := by
              have h_eq : n.factorization 2 = n.factorization 2 - 1 + 1 := (Nat.sub_add_cancel h_fac_q).symm
              nth_rw 1 [h_eq]
              rw [pow_add, pow_one, mul_comm]
            rw [h_pow_split]
            use 2^(n.factorization 2 - 1) * (List.map (fun p => p ^ n.factorization p) ms).prod
            ring
          have h_even_lhs : 2 ∣ n' * p_r := dvd_mul_of_dvd_left h_dvd_n' p_r
          have h_odd_rhs : ¬ 2 ∣ 1 + 10 * p_r + 10 * ofDigits 10 C.reverse * 10^L_pr := by
            intro hd
            have h_eq : 1 + 10 * p_r + 10 * ofDigits 10 C.reverse * 10^L_pr = 2 * (5 * p_r + 5 * ofDigits 10 C.reverse * 10^L_pr) + 1 := by ring
            rw [h_eq] at hd
            have h_dvd_one : 2 ∣ 1 := (Nat.dvd_add_right (by omega)).mp hd
            omega
          rw [h_rewritten] at h_even_lhs
          contradiction
        · -- q ≠ 2
          have hq_ge3 : q ≥ 3 := by
            have hq_ge2 : q ≥ 2 := hq_prime.two_le
            omega
          have hp_r_lt : p_r < 10^L_pr := by
            have h_dig_lt : ∀ d ∈ digits 10 p_r, d < 10 := fun d hd => digits_lt_base (by decide) hd
            have h_lt := ofDigits_lt_pow 10 (by decide) (digits 10 p_r) h_dig_lt
            rw [ofDigits_digits 10 p_r] at h_lt
            exact h_lt
          have h_ge_step : 10 * ofDigits 10 C.reverse * 10^L_pr ≥ 10 * ofDigits 10 C.reverse * (p_r + 1) := Nat.mul_le_mul_left _ hp_r_lt
          have h_sum_ge : n' * p_r ≥ (10 * ofDigits 10 C.reverse + 10) * p_r + 10 * ofDigits 10 C.reverse + 1 := by
            calc n' * p_r = 1 + 10 * p_r + 10 * ofDigits 10 C.reverse * 10^L_pr := h_rewritten
            _ ≥ 1 + 10 * p_r + 10 * ofDigits 10 C.reverse * (p_r + 1) := by omega
            _ = (10 * ofDigits 10 C.reverse + 10) * p_r + 10 * ofDigits 10 C.reverse + 1 := by ring
          have h_sum_gt : n' * p_r > (10 * ofDigits 10 C.reverse + 10) * p_r := by omega
          have hn'_gt : n' > 10 * ofDigits 10 C.reverse + 10 := Nat.lt_of_mul_lt_mul_right h_sum_gt
          have hn'_ge : n' ≥ 10 * ofDigits 10 C.reverse + 11 := by omega

          have hn'_le : n' ≤ 100 * ofDigits 10 C.reverse + 10 := by
            have h_le_step : 10 * ofDigits 10 C.reverse * 10^L_pr ≤ 10 * ofDigits 10 C.reverse * (10 * p_r) := Nat.mul_le_mul_left _ h_L_pr
            have h_sum_le : n' * p_r ≤ 100 * ofDigits 10 C.reverse * p_r + 10 * p_r + 1 := by
              calc n' * p_r = 1 + 10 * p_r + 10 * ofDigits 10 C.reverse * 10^L_pr := h_rewritten
              _ ≤ 1 + 10 * p_r + 10 * ofDigits 10 C.reverse * (10 * p_r) := by omega
              _ = 100 * ofDigits 10 C.reverse * p_r + 10 * p_r + 1 := by ring
            have h_sum_lt : n' * p_r < 100 * ofDigits 10 C.reverse * p_r + 11 * p_r := by
              have : 10 * p_r + 1 < 11 * p_r := by omega
              omega
            have h_ring_back : 100 * ofDigits 10 C.reverse * p_r + 11 * p_r = (100 * ofDigits 10 C.reverse + 11) * p_r := by ring
            rw [h_ring_back] at h_sum_lt
            exact Nat.le_of_lt_add_one (Nat.lt_of_mul_lt_mul_right h_sum_lt)
          have h_sub : (n' - 10) * p_r = 1 + 10 * ofDigits 10 C.reverse * 10^L_pr := by
            have h1 : n' * p_r = (n' - 10) * p_r + 10 * p_r := by
              rw [Nat.sub_mul]
              omega
            rw [h1] at h_rewritten
            omega
          have hdvd_pr : p_r ∣ 1 + 10 * ofDigits 10 C.reverse * 10^L_pr := by
            use n' - 10
            rw [← h_sub]
            exact mul_comm _ _
          sorry
      · sorry
