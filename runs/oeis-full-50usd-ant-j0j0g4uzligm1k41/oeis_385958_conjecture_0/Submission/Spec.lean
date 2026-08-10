import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A helper function to find the largest prime $p$ such that $p-1$ divides $2 \cdot k$.
This is the definition of $a(n)$ given $b(n-1)=k$.
Since $k \ge 1$, $2k \ge 2$, and the set of such primes is non-empty (it always contains $p=2$).
-/
noncomputable def largest_prime_divisor_property (k : ℕ) : ℕ :=
  -- Generate candidates p = d + 1 where d is a divisor of 2k. Filter for primes and find the max.
  let candidates := Finset.image (fun d => d + 1) (2 * k).divisors
  let max_prime := candidates.filter Nat.Prime |> Finset.max
  max_prime.getD 0

/--
A385959: The auxiliary sequence $b(n)$.
$b(0) = 1$.
$b(n) = b(n-1) \cdot \frac{a(n)+1}{a(n)-1}$.
-/
noncomputable def b : ℕ → ℕ
| 0 => 1
| n + 1 =>
  let b_prev := b n;
  let p := largest_prime_divisor_property b_prev;
  -- b(n+1) = b_prev + b_prev * 2 / (p - 1)
  b_prev + b_prev * 2 / (p - 1)

/--
A385958: $a(n)$ is the largest prime $p$ such that $b(n) = b(n-1) \cdot \frac{p+1}{p-1}$ is an integer (A385959), where $b(0) = 1$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n > 0 then
    largest_prime_divisor_property (b (n - 1))
  else 0

/-!
### Structural results towards the conjecture

We isolate the genuinely provable structure of the problem.  Writing
`lpdp := largest_prime_divisor_property`, the value `lpdp k` is the largest prime
`p` with `(p-1) ∣ 2k`.  The main theorem reduces, via the proven *witness lemma*
`lpdp ((q-1)/2) = q`, to the statement that the orbit `b` actually attains, for each
odd prime `q`, a value mapping to `q` (`reaches_each_odd_prime`).
-/

/-- Membership in the candidate set used by `largest_prime_divisor_property`. -/
theorem lpdp_mem_iff (k x : ℕ) (hk : 1 ≤ k) :
    x ∈ (Finset.image (fun d => d + 1) (2 * k).divisors).filter Nat.Prime ↔
      (∃ d, d ∣ (2 * k) ∧ d + 1 = x) ∧ Nat.Prime x := by
  rw [mem_filter, mem_image]
  constructor
  · rintro ⟨⟨d, hd, rfl⟩, hp⟩
    rw [Nat.mem_divisors] at hd; exact ⟨⟨d, hd.1, rfl⟩, hp⟩
  · rintro ⟨⟨d, hd, rfl⟩, hp⟩
    refine ⟨⟨d, ?_, rfl⟩, hp⟩
    rw [Nat.mem_divisors]; exact ⟨hd, by positivity⟩

/-- **Witness lemma.** For every odd prime `q`, the input `k = (q-1)/2` (for which
`2k = q-1`) yields `largest_prime_divisor_property k = q`: indeed `q-1` is the
largest divisor of `q-1`, giving the prime `q`, and no candidate `d+1` can exceed `q`. -/
theorem witness (q : ℕ) (hq : Nat.Prime q) (hodd : Odd q) :
    largest_prime_divisor_property ((q - 1) / 2) = q := by
  have hne : q ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hodd
  have h2 := hq.two_le
  have hq3 : 3 ≤ q := by omega
  have hev : 2 * ((q - 1) / 2) = q - 1 := by obtain ⟨m, hm⟩ := hodd; omega
  set S := (Finset.image (fun d => d + 1) (2 * ((q - 1) / 2)).divisors).filter Nat.Prime
    with hS
  have hmem : ∀ x, x ∈ S ↔ (∃ d, d ∣ (q - 1) ∧ d + 1 = x) ∧ Nat.Prime x := by
    intro x
    rw [hS, mem_filter, mem_image, hev]
    constructor
    · rintro ⟨⟨d, hd, rfl⟩, hp⟩
      rw [Nat.mem_divisors] at hd; exact ⟨⟨d, hd.1, rfl⟩, hp⟩
    · rintro ⟨⟨d, hd, rfl⟩, hp⟩
      refine ⟨⟨d, ?_, rfl⟩, hp⟩
      rw [Nat.mem_divisors]; exact ⟨hd, by omega⟩
  have hqS : q ∈ S := by rw [hmem]; exact ⟨⟨q - 1, dvd_refl _, by omega⟩, hq⟩
  have hub : ∀ x ∈ S, x ≤ q := by
    intro x hx; rw [hmem] at hx
    obtain ⟨⟨d, hd, rfl⟩, _⟩ := hx
    have : d ≤ q - 1 := Nat.le_of_dvd (by omega) hd
    omega
  have hmax : S.max = (q : WithBot ℕ) := by
    apply le_antisymm
    · rw [Finset.max_le_iff]; intro x hx; exact WithBot.coe_le_coe.mpr (hub x hx)
    · exact Finset.le_max hqS
  show (S.max).getD 0 = q
  rw [hmax]; rfl

/-- The candidate set always contains `3` when `k ≥ 1`. -/
theorem three_mem (k : ℕ) (hk : 1 ≤ k) :
    (3 : ℕ) ∈ (Finset.image (fun d => d + 1) (2 * k).divisors).filter Nat.Prime := by
  rw [mem_filter, mem_image]
  refine ⟨⟨2, ?_, rfl⟩, by norm_num⟩
  rw [Nat.mem_divisors]
  exact ⟨⟨k, by ring⟩, by positivity⟩

/-- **Well-definedness / structural specification of `lpdp`.** For `k ≥ 1`,
`largest_prime_divisor_property k` is prime, is `≥ 3`, and `(lpdp k - 1) ∣ 2k`
(so the integer division in the definition of `b` is exact and never divides by zero). -/
theorem lpdp_spec (k : ℕ) (hk : 1 ≤ k) :
    Nat.Prime (largest_prime_divisor_property k) ∧
    (largest_prime_divisor_property k - 1) ∣ (2 * k) ∧
    3 ≤ largest_prime_divisor_property k := by
  set S := (Finset.image (fun d => d + 1) (2 * k).divisors).filter Nat.Prime with hS
  have hne : S.Nonempty := ⟨3, three_mem k hk⟩
  obtain ⟨v, hv⟩ := Finset.max_of_nonempty hne
  have hvmem : v ∈ S := Finset.mem_of_max hv
  have hlp : largest_prime_divisor_property k = v := by
    show (S.max).getD 0 = v
    rw [hv]; rfl
  rw [mem_filter, mem_image] at hvmem
  obtain ⟨⟨d, hd, hdv⟩, hvp⟩ := hvmem
  rw [Nat.mem_divisors] at hd
  refine ⟨by rw [hlp]; exact hvp, ?_, ?_⟩
  · rw [hlp, ← hdv]; simpa using hd.1
  · rw [hlp]
    have h3 : ((3 : ℕ) : WithBot ℕ) ≤ S.max := Finset.le_max (three_mem k hk)
    rw [hv] at h3
    exact WithBot.coe_le_coe.mp h3

/-- The orbit is positive. -/
theorem b_pos : ∀ n, 1 ≤ b n
| 0 => le_refl 1
| n + 1 => by
  have h := b_pos n
  show 1 ≤ b n + b n * 2 / (largest_prime_divisor_property (b n) - 1)
  exact h.trans (Nat.le_add_right _ _)

/-- **The orbit is strictly increasing with multiplicative gap at most `2`:**
`b n < b (n+1) ≤ 2 * b n`.  In particular the orbit has a value in every octave
`[2^k, 2^{k+1})`.  This is the strongest structural handle on the dynamics; it is
nonetheless insufficient to settle the conjecture, since within the octave
`[(q-1)/2, q-1]` the only multiples of `(q-1)/2` are `(q-1)/2` and `q-1` themselves,
so the single orbit value landing there is generically not a witness for `q`. -/
theorem b_step (n : ℕ) : b n < b (n+1) ∧ b (n+1) ≤ 2 * b n := by
  have hbpos := b_pos n
  obtain ⟨_, hdvd, hge3⟩ := lpdp_spec (b n) hbpos
  set p := largest_prime_divisor_property (b n) with hp
  have hp1 : (p - 1) ∣ (2 * b n) := by simpa [Nat.mul_comm] using hdvd
  have hle : p - 1 ≤ 2 * b n := Nat.le_of_dvd (by omega) hp1
  have hq : b n * 2 / (p - 1) = (2 * b n) / (p - 1) := by ring_nf
  have hpos : 1 ≤ (2 * b n) / (p - 1) := by
    apply Nat.one_le_div_iff (by omega) |>.mpr; omega
  have hub : (2 * b n) / (p - 1) ≤ b n := by
    have h1 : (2 * b n) / (p - 1) ≤ (2 * b n) / 2 :=
      Nat.div_le_div_left (by omega) (by omega)
    have h2 : (2 * b n) / 2 = b n := by omega
    omega
  refine ⟨?_, ?_⟩
  · show b n < b n + b n * 2 / (p - 1)
    rw [hq]; omega
  · show b n + b n * 2 / (p - 1) ≤ 2 * b n
    rw [hq]; omega

/-- The reachability statement: the orbit `b` attains, for every odd prime `q`,
a value `b m` with `largest_prime_divisor_property (b m) = q`.

This is exactly the content of the OEIS A385958 conjecture, restated on the orbit.
By the `witness` lemma it suffices, for each `q`, that the orbit reaches some value
`b m` lying in the (nonempty, since it contains `(q-1)/2`) target set
`{ b' | largest_prime_divisor_property b' = q }`.  Establishing this for the actual
chaotic deterministic orbit is the open mathematical core of the problem. -/
theorem reaches_each_odd_prime :
    ∀ q : ℕ, Nat.Prime q → q ≠ 2 →
      ∃ m : ℕ, largest_prime_divisor_property (b m) = q := by
  sorry

/--
Conjecture: Does this sequence contain all odd primes?
Formalization: For every odd prime $p$, there exists $n \in \mathbb{N}^+$ such that $a(n) = p$.
-/
theorem oeis_385958_conjecture_0 : ∀ (p : ℕ), Nat.Prime p → p ≠ 2 → ∃ (n : ℕ+), a n = p := by
  intro p hp hne
  obtain ⟨m, hm⟩ := reaches_each_odd_prime p hp hne
  refine ⟨⟨m + 1, Nat.succ_pos m⟩, ?_⟩
  show a (m + 1) = p
  unfold a
  simp only [Nat.succ_pos, if_true, Nat.add_sub_cancel]
  exact hm
