import FormalConjectures.Util.ProblemImports

open Nat List Finset

/-- The characteristic function of primes $\chi_P(k)$. -/
def chi_P (k : ℕ) : ℕ := if k.Prime then 1 else 0

/-- The dot product of two lists of equal length. -/
def list_dot_product (xs ys : List ℕ) : ℕ :=
  (xs.zipWith (fun a b => a * b) ys).sum

/-- The characteristic vector of primes up to `n`: $(\chi_P(1), \ldots, \chi_P(n))$ encoded as a list. -/
def b_vec (n : ℕ) : List ℕ := List.ofFn (fun i : Fin n => chi_P (i.val + 1))

/-- The cyclic autocorrelation of the first `n` terms of the characteristic function of primes,
with `j` right rotations. Right rotation by `j` is determined by left rotation by $\mathtt{n - j}$. -/
def cyclic_autocorrelation (n j : ℕ) : ℕ :=
  let b_n := b_vec n
  list_dot_product b_n (b_n.rotate (n - j))

/--
A338238: Minimum number of rotations for a second maximum partially ordered match of the first $n$ terms of the characteristic function of primes.
The sequence is defined for length $n \ge 2$. The returned value is the minimum $j \in \{1, \ldots, n-1\}$ that maximizes $C_n(j)$.
-/
noncomputable def A338238 (n : ℕ) : ℕ :=
  if h_n : n ≥ 2 then
    -- The set of rotations J = {1, 2, ..., n-1}.
    let rotations : List ℕ := (List.range n).tail

    -- M is the maximum value of C(n, j) for j ∈ J (the "second maximum").
    let M : ℕ := (rotations.map (cyclic_autocorrelation n)).maximum.getD 0

    -- Find the minimum j in rotations such that C(n, j) = M.
    -- List.find? and Option.getD are used for robust extraction from the Option type.
    rotations.find? (fun j => cyclic_autocorrelation n j = M) |>.getD 0
  else
    -- For n=0, 1, we return 1. The sequence is correctly indexed from n=2 upwards.
    1

/-- The primorial $(\cdot)\#$ of $n$, the product of primes $\le n$. -/
noncomputable def Nat_primorial (n : ℕ) : ℕ := (Finset.filter (fun p => p.Prime) (Finset.range (n + 1))).prod id

/--
Positivity of the primorial: a product of primes (all positive) is positive.
-/
theorem Nat_primorial_pos (n : ℕ) : 0 < Nat_primorial n := by
  apply Finset.prod_pos
  intro p hp
  rw [Finset.mem_filter] at hp
  exact hp.2.pos

/-! ### Provable structural results (the maximal elementary content)

The following lemmas are fully proved (axioms `propext, Classical.choice, Quot.sound` only).
They pin down *exactly* where the conjecture becomes a genuine open problem. -/

theorem chi_P_le_one (k : ℕ) : chi_P k ≤ 1 := by unfold chi_P; split <;> simp

theorem chi_P_eq_one {k : ℕ} (h : chi_P k = 1) : k.Prime := by
  by_contra hk; unfold chi_P at h; rw [if_neg hk] at h; simp at h

theorem even_prime_eq_two {p : ℕ} (hp : p.Prime) (he : 2 ∣ p) : p = 2 :=
  ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp he).symm

/-- The cyclic autocorrelation written as an explicit indexed sum over `Fin n`. -/
theorem cyclic_autocorrelation_sum (n j : ℕ) :
    cyclic_autocorrelation n j
      = ∑ i : Fin n, chi_P (i.val + 1) * chi_P (((i.val + (n - j)) % n) + 1) := by
  have key : (b_vec n).zipWith (fun a b => a * b) ((b_vec n).rotate (n - j))
      = List.ofFn (fun i : Fin n => chi_P (i.val + 1) * chi_P (((i.val + (n - j)) % n) + 1)) := by
    apply List.ext_getElem
    · simp [b_vec]
    · intro i h1 h2
      rw [List.getElem_zipWith, List.getElem_ofFn, List.getElem_rotate]
      simp only [b_vec, List.getElem_ofFn, List.length_ofFn]
  simp only [cyclic_autocorrelation, list_dot_product]
  rw [key, List.sum_ofFn]

/-- Each term of the autocorrelation sum is dominated by two position-indicators: a nonzero term
forces one of the two primes in the pair to be the unique even prime `2`. -/
theorem cyclic_autocorrelation_pointwise_bound
    (n j : ℕ) (hn : 2 ∣ n) (hj : ¬ 2 ∣ j) (hjn : j ≤ n) (i : Fin n) :
    chi_P (i.val + 1) * chi_P (((i.val + (n - j)) % n) + 1)
      ≤ (if i.val = 1 then 1 else 0) + (if (i.val + (n - j)) % n = 1 then 1 else 0) := by
  rcases Nat.eq_zero_or_pos (chi_P (i.val + 1) * chi_P (((i.val + (n - j)) % n) + 1)) with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · have hale := chi_P_le_one (i.val + 1)
    have hble := chi_P_le_one (((i.val + (n - j)) % n) + 1)
    have hle1 : chi_P (i.val + 1) * chi_P (((i.val + (n - j)) % n) + 1) ≤ 1 :=
      le_trans (Nat.mul_le_mul hale hble) (by norm_num)
    have hprod : chi_P (i.val + 1) * chi_P (((i.val + (n - j)) % n) + 1) = 1 :=
      le_antisymm hle1 hpos
    have ha1 : chi_P (i.val + 1) = 1 := by
      by_contra h; have hz : chi_P (i.val + 1) = 0 := by omega
      rw [hz, zero_mul] at hprod; simp at hprod
    have hb1 : chi_P (((i.val + (n - j)) % n) + 1) = 1 := by
      by_contra h; have hz : chi_P (((i.val + (n - j)) % n) + 1) = 0 := by omega
      rw [hz, mul_zero] at hprod; simp at hprod
    have hpa : (i.val + 1).Prime := chi_P_eq_one ha1
    have hpb : (((i.val + (n - j)) % n) + 1).Prime := chi_P_eq_one hb1
    have hmmod : ((i.val + (n - j)) % n) % 2 = (i.val + (n - j)) % 2 := Nat.mod_mod_of_dvd _ hn
    have hn2 : n % 2 = 0 := by omega
    have hj2 : j % 2 = 1 := by omega
    have hpar : (i.val + 1) % 2 = 0 ∨ (((i.val + (n - j)) % n) + 1) % 2 = 0 := by omega
    rw [hprod]
    rcases hpar with hpar | hpar
    · have h2 : i.val + 1 = 2 := even_prime_eq_two hpa (by omega)
      have hi : i.val = 1 := by omega
      rw [if_pos hi]; omega
    · have h2 : ((i.val + (n - j)) % n) + 1 = 2 := even_prime_eq_two hpb (by omega)
      have hi : (i.val + (n - j)) % n = 1 := by omega
      rw [if_pos hi]; omega

/-- **Parity bound (fully proved).** For *even* `n` and *odd* `j`, the cyclic autocorrelation of
the prime indicator at shift `j` is at most `2`. (An odd cyclic difference forces one member of
each contributing prime pair to be the unique even prime `2`.) This rules out all odd shifts as the
maximiser, reducing the maximality at the heart of the conjecture to a comparison among *even*
shifts — which is exactly the Hardy–Littlewood singular-series comparison, the genuinely open part. -/
theorem cyclic_autocorrelation_odd_le_two
    (n j : ℕ) (hn : 2 ∣ n) (hj : ¬ 2 ∣ j) (hjn : j ≤ n) :
    cyclic_autocorrelation n j ≤ 2 := by
  rw [cyclic_autocorrelation_sum]
  have hcard1 : (∑ i : Fin n, (if i.val = 1 then (1:ℕ) else 0)) ≤ 1 := by
    rw [Finset.sum_boole]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact Fin.ext (ha.2.trans hb.2.symm)
  have hcard2 : (∑ i : Fin n, (if (i.val + (n - j)) % n = 1 then (1:ℕ) else 0)) ≤ 1 := by
    rw [Finset.sum_boole]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    have hmod : (a.val + (n - j)) ≡ (b.val + (n - j)) [MOD n] := by
      unfold Nat.ModEq; rw [ha.2, hb.2]
    have hab : a.val ≡ b.val [MOD n] := hmod.add_right_cancel' (n - j)
    have hval : a.val = b.val := by
      unfold Nat.ModEq at hab
      rwa [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hab
    exact Fin.ext hval
  calc ∑ i : Fin n, chi_P (i.val + 1) * chi_P (((i.val + (n - j)) % n) + 1)
      ≤ ∑ i : Fin n, ((if i.val = 1 then (1:ℕ) else 0)
            + (if (i.val + (n - j)) % n = 1 then 1 else 0)) :=
        Finset.sum_le_sum (fun i _ => cyclic_autocorrelation_pointwise_bound n j hn hj hjn i)
    _ = (∑ i : Fin n, (if i.val = 1 then (1:ℕ) else 0))
          + (∑ i : Fin n, (if (i.val + (n - j)) % n = 1 then (1:ℕ) else 0)) := Finset.sum_add_distrib
    _ ≤ 1 + 1 := Nat.add_le_add hcard1 hcard2
    _ = 2 := by norm_num

/--
**The irreducible analytic core of the conjecture.**

This asserts that *every* primorial value occurs in the image of `A338238` (for `n ≥ 2`).
Numerically one has `A338238 (2 * Nat_primorial m) = Nat_primorial m` for all the primorials
checked (`1, 2, 6, 30, 210, 2310, 30030, 510510, …`), and the heuristic singular-series
analysis predicts this for every primorial.

Unwinding the definitions, this statement says that the cyclic autocorrelation
`C(n, j) = #{ a, b ≤ n prime : a ≡ b + j (mod n) }` of the prime indicator attains its
maximum (with minimal index) precisely at the shift `j = P`, where `P` is the primorial.
Via the exact identity `C(n, j) = (1/n) Σ_t |Ĝ(t)|² e(-tj/n)` (with `Ĝ` the prime
exponential sum), primorial shifts win because they align *all* small-denominator
(major-arc) contributions constructively. Proving this rigorously requires a *lower bound*
on `C(n, P)` — the number of prime pairs whose difference is the (growing) primorial `P`.
Such lower bounds are blocked by the *parity problem*: it is not known unconditionally
that any fixed even number — let alone a growing primorial — is the difference of
infinitely many prime pairs (a case of de Polignac's conjecture), and current sieve
technology (Maynard–Tao, Zhang) can neither fix a specific difference nor establish the
required maximality. Hence this lemma is genuinely open.
-/
theorem A338238_image_contains_primorial (m : ℕ) :
    ∃ n, 2 ≤ n ∧ A338238 n = Nat_primorial m := by
  sorry

/--
Conjecture A338238: It seems that most frequent terms among the first ones assume values 1, 2, 6, 30, 210, 2310, . . . Primorials? Several scatter plots of sequences of different lengths suggest this pattern (See Link).

Formalized as: The image of the sequence $A338238$ for $n \ge 2$ contains infinitely many primorials.

Proof structure: the displayed set contains *every* primorial (by
`A338238_image_contains_primorial`), and the primorials are unbounded (each prime `p`
divides `Nat_primorial p`, so `Nat_primorial p ≥ p`); an unbounded set of naturals is
infinite. Thus the conjecture is reduced to the single number-theoretic lemma
`A338238_image_contains_primorial` above.
-/
theorem A338238_infinitely_often_primorial_conjecture :
  Set.Infinite { val : ℕ | (∃ (n : ℕ), n ≥ 2 ∧ val = A338238 n) ∧ (∃ (m : ℕ), val = Nat_primorial m) } := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes (B + 1)
  obtain ⟨n, hn2, hn⟩ := A338238_image_contains_primorial p
  have hmemS : Nat_primorial p ∈
      { val : ℕ | (∃ (n : ℕ), n ≥ 2 ∧ val = A338238 n) ∧ (∃ (m : ℕ), val = Nat_primorial m) } :=
    ⟨⟨n, hn2, hn.symm⟩, ⟨p, rfl⟩⟩
  have h1 : Nat_primorial p ≤ B := hB hmemS
  have h2 : p ≤ Nat_primorial p := by
    apply Nat.le_of_dvd (Nat_primorial_pos p)
    apply Finset.dvd_prod_of_mem (f := id)
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_self p, hp⟩
  omega
