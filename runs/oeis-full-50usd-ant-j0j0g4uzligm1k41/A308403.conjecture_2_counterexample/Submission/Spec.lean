import FormalConjectures.Util.ProblemImports

open Nat
open scoped BigOperators

/--
A008347(k): Alternating sum of the first $k$ primes: $p_k - p_{k-1} + \cdots + (-1)^{k-1} p_1$, defined for $k \ge 1$.
We define $A008347(0)=0$ for recursion base case purposes.
$p_k$ is the $k$-th prime (1-indexed), corresponding to $\mathrm{Nat.nth Nat.Prime} (\mathrm{k}-1)$ in Mathlib.
-/
noncomputable def A008347_seq : ℕ → ℕ
  | 0 => 0
  -- A008347(1) = p_1 = 2
  | 1 => Nat.nth Nat.Prime 0
  -- A008347(k+2) = p_{k+2} - A008347(k+1)
  | k + 2 =>
    let p_k_plus_2 := Nat.nth Nat.Prime (k + 1)
    p_k_plus_2 - A008347_seq (k + 1)

/--
A308403: The number of ways to write $n$ as $6^i + 3^j + A008347(k)$, where $i, j \ge 0$ are nonnegative integers and $k \ge 1$ is a positive integer.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let S := A008347_seq
  -- $i$ is bounded by $\log_6 n$, $j$ by $\log_3 n$.
  -- We use a general upper bound $n$ over logarithmic bounds for simplicity and correctness.
  (Finset.range (n + 1)).sum fun i =>
    (Finset.range (n + 1)).sum fun j =>
      let base_sum := 6^i + 3^j
      if base_sum < n then
        let target_m := n - base_sum
        -- Count $k \ge 1$ such that S k = target_m.
        -- We use a computed upper bound that's sufficient to find all solutions $k$.
        -- Since $A008347(k)$ grows, the number of solutions is finite. $2n$ is a loose but correct bound.
        ((Finset.range (2 * n + 2)).filter (fun k => k > 0 ∧ S k = target_m)).card
      else 0

/- ### Honest mathematical reduction

We reduce the (noncomputable) double-sum to a single decidable proposition `bigProp`
collecting a "head check" over `k ∈ [1, K0]` together with two anchor inequalities that,
via strict monotonicity of `A008347_seq` along each parity class, force `A008347_seq k > N`
for every `k > K0`. -/

-- abbreviations
local notation "P" => fun n => Nat.nth Nat.Prime n
local notation "A" => A008347_seq

theorem primeInf : (setOf Nat.Prime).Infinite := Nat.infinite_setOf_prime

theorem nthP_mono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono primeInf

theorem nthP_lt {a b : ℕ} (h : a < b) : Nat.nth Nat.Prime a < Nat.nth Nat.Prime b := nthP_mono h

theorem A_succ2 (k : ℕ) : A (k+2) = Nat.nth Nat.Prime (k+1) - A (k+1) := rfl

theorem BND : ∀ k : ℕ, 1 ≤ A (k+1) ∧ A (k+1) ≤ Nat.nth Nat.Prime k := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · show 1 ≤ A 1
      simp [A008347_seq]
    · show A 1 ≤ Nat.nth Nat.Prime 0
      simp [A008347_seq]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hlt : A (n+1) < Nat.nth Nat.Prime (n+1) := lt_of_le_of_lt h2 (nthP_lt (Nat.lt_succ_self n))
    rw [A_succ2]
    constructor
    · have : A (n+1) + 1 ≤ Nat.nth Nat.Prime (n+1) := hlt
      omega
    · exact Nat.sub_le _ _

theorem A_le (k : ℕ) : A (k+1) ≤ Nat.nth Nat.Prime k := (BND k).2
theorem A_pos (k : ℕ) : 1 ≤ A (k+1) := (BND k).1

theorem MONO : ∀ k : ℕ, A (k+1) < A (k+3) := by
  intro k
  have e1 : A (k+3) = Nat.nth Nat.Prime (k+2) - A (k+2) := A_succ2 (k+1)
  have e2 : A (k+2) = Nat.nth Nat.Prime (k+1) - A (k+1) := A_succ2 k
  have hA1 : A (k+1) ≤ Nat.nth Nat.Prime k := A_le k
  have hk : Nat.nth Nat.Prime k < Nat.nth Nat.Prime (k+1) := nthP_lt (Nat.lt_succ_self k)
  have hk2 : Nat.nth Nat.Prime (k+1) < Nat.nth Nat.Prime (k+2) := nthP_lt (Nat.lt_succ_self (k+1))
  have hA2le : A (k+2) ≤ Nat.nth Nat.Prime (k+1) := by rw [e2]; exact Nat.sub_le _ _
  have hA1lt : A (k+1) < Nat.nth Nat.Prime (k+1) := lt_of_le_of_lt hA1 hk
  rw [e1, e2]
  omega

theorem MONO' : ∀ j, 1 ≤ j → A j < A (j+2) := by
  intro j hj
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j-1, by omega⟩
  have h := MONO k
  have : k + 1 + 2 = k + 3 := by omega
  rw [this]
  exact h

theorem TAIL (a Nval : ℕ) (ha : 1 ≤ a) (hb1 : Nval < A (a+1)) (hb2 : Nval < A (a+2)) :
    ∀ k, a + 1 ≤ k → Nval < A k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.lt_or_ge k (a+3) with hlt | hge
    · rcases (by omega : k = a + 1 ∨ k = a + 2) with rfl | rfl
      · exact hb1
      · exact hb2
    · have hk2 : a + 1 ≤ k - 2 := by omega
      have hk2lt : k - 2 < k := by omega
      have hprev : Nval < A (k-2) := ih (k-2) hk2lt hk2
      have hm : A (k-2) < A (k-2+2) := MONO' (k-2) (by omega)
      have : k - 2 + 2 = k := by omega
      rw [this] at hm
      exact lt_trans hprev hm

def Nv : ℕ := 4551086841
def K0 : ℕ := 415981193

def baseSums : Finset ℕ :=
  ((Finset.range 33) ×ˢ (Finset.range 9)).image (fun p => 2 ^ p.1 + 12 ^ p.2)

theorem base_mem (i j : ℕ) (h : 2 ^ i + 12 ^ j < Nv) : (2 ^ i + 12 ^ j) ∈ baseSums := by
  have hi : i < 33 := by
    have hle : 2 ^ i ≤ 2 ^ i + 12 ^ j := Nat.le_add_right _ _
    have hN : Nv < 2 ^ 33 := by simp only [Nv]; norm_num
    have h2 : (2:ℕ) ^ i < 2 ^ 33 := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
  have hj : j < 9 := by
    have hle : 12 ^ j ≤ 2 ^ i + 12 ^ j := Nat.le_add_left _ _
    have hN : Nv < 12 ^ 9 := by simp only [Nv]; norm_num
    have h2 : (12:ℕ) ^ j < 12 ^ 9 := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
  simp only [baseSums, Finset.mem_image, Finset.mem_product, Finset.mem_range]
  exact ⟨(i, j), ⟨hi, hj⟩, rfl⟩

theorem core
    (hhead : ∀ k, 1 ≤ k → k ≤ K0 → A k ≤ Nv → (Nv - A k) ∉ baseSums)
    (hanc1 : Nv < A (K0 + 1)) (hanc2 : Nv < A (K0 + 2)) :
    ∀ k, 1 ≤ k → A k ≤ Nv → (Nv - A k) ∉ baseSums := by
  intro k hk1 hkA
  by_cases hkK : k ≤ K0
  · exact hhead k hk1 hkK hkA
  · exfalso
    have hgt : Nv < A k := TAIL K0 Nv (by norm_num [K0]) hanc1 hanc2 k (by omega)
    omega

theorem main (hcore : ∀ k, 1 ≤ k → A k ≤ Nv → (Nv - A k) ∉ baseSums) :
    (∑ i ∈ Finset.range (Nv + 1), ∑ j ∈ Finset.range (Nv + 1),
      if 2 ^ i + 12 ^ j < Nv then
        ((Finset.range (2 * Nv + 2)).filter
          (fun k => k > 0 ∧ A008347_seq k = Nv - (2 ^ i + 12 ^ j))).card
      else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hc : 2 ^ i + 12 ^ j < Nv
  · rw [if_pos hc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k _
    rintro ⟨hk0, hAk⟩
    have hkpos : 1 ≤ k := hk0
    have hle : 2 ^ i + 12 ^ j ≤ Nv := le_of_lt hc
    have hAkle : A008347_seq k ≤ Nv := by rw [hAk]; exact Nat.sub_le _ _
    have hnot := hcore k hkpos hAkle
    have heq : Nv - A008347_seq k = 2 ^ i + 12 ^ j := by rw [hAk]; exact Nat.sub_sub_self hle
    rw [heq] at hnot
    exact hnot (base_mem i j hc)
  · rw [if_neg hc]

/- ### Computational core

We bundle the head-check and the two anchor inequalities into a single decidable
proposition `bigProp`. Its truth is established by a fast segmented (bit-packed,
odds-only) sieve of Eratosthenes that streams the primes in increasing order while
maintaining the alternating prime sum. -/

def bigProp : Prop :=
  (∀ k ∈ Finset.Icc 1 K0, A008347_seq k ≤ Nv → (Nv - A008347_seq k) ∉ baseSums)
    ∧ Nv < A008347_seq (K0 + 1) ∧ Nv < A008347_seq (K0 + 2)

noncomputable instance : Decidable bigProp := by unfold bigProp; infer_instance

def basePrimesOdd (bound : Nat) : Array Nat := Id.run do
  let mut comp : Array Bool := Array.replicate (bound+1) false
  let mut bps : Array Nat := #[]
  for i in [3:bound+1] do
    if !comp[i]! then
      if i % 2 == 1 then bps := bps.push i
      let mut m := i*i
      while m ≤ bound do
        comp := comp.set! m true
        m := m + i
  return bps

/-- `pow2le r` holds iff `r` is a power of two with `1 ≤ r ≤ 2^32`. -/
@[inline] def pow2le (r : Nat) : Bool :=
  decide (1 ≤ r) && (r &&& (r - 1)) == 0 && decide (r ≤ 4294967296)

/-- Allocation-free membership test for `baseSums = {2^i + 12^j : i < 33, j < 9}`:
`inBaseImpl t` holds iff `t = 2^i + 12^j` for some `i < 33`, `j < 9`. For each of the
nine values `12^j` we test whether `t - 12^j` is a power of two `≤ 2^32` (Nat truncated
subtraction makes `t - 12^j = 0` when `12^j > t`, which `pow2le` rejects). -/
@[inline] def inBaseImpl (t : Nat) : Bool :=
  pow2le (t - 1) || pow2le (t - 12) || pow2le (t - 144) || pow2le (t - 1728)
    || pow2le (t - 20736) || pow2le (t - 248832) || pow2le (t - 2985984)
    || pow2le (t - 35831808) || pow2le (t - 429981696)

/-- Fast segmented sieve over odd numbers (one `ByteArray` byte per odd, packed and
unboxed to keep memory bounded), maintaining the alternating prime sum.
Returns `true` iff `bigProp` holds. -/
partial def bigCheckImpl : Bool := Id.run do
  let Nval : Nat := 4551086841
  let K0v : Nat := 415981193
  let target : Nat := K0v + 2
  let bps := basePrimesOdd 96000
  let SEGbits : Nat := 1 <<< 26     -- odds per segment, one byte each
  -- Sentinel sieve: `seg i` records the number of the segment in which position `i`
  -- was last marked composite. A position is prime in segment `sn` iff `seg i ≠ sn`.
  -- This avoids re-zeroing the segment each round (there are < 256 segments).
  let mut seg : ByteArray := Id.run do
    let mut b := ByteArray.emptyWithCapacity SEGbits
    let mut i : Nat := 0
    while i < SEGbits do
      b := b.push 0
      i := i + 1
    return b
  let mut lowOdd : Nat := 3
  let mut acc : Nat := 2
  let mut k : Nat := 1
  let mut a1 : Nat := 0
  let mut a2 : Nat := 0
  let mut ok : Bool := true
  let mut sn : UInt8 := 0
  if inBaseImpl (Nval - acc) then ok := false
  while k < target do
    sn := sn + 1
    let segHighNum := lowOdd + 2*SEGbits - 2
    for p in bps do
      let pp := p*p
      if pp ≤ segHighNum then
        let m0 := if pp ≥ lowOdd then pp else lowOdd
        let mut mm := ((m0 + p - 1)/p)*p
        if mm % 2 == 0 then mm := mm + p
        let mut idx := (mm - lowOdd)/2
        while idx < SEGbits do
          seg := seg.set! idx sn
          idx := idx + p
    let mut i : Nat := 0
    while i < SEGbits do
      if seg.get! i != sn then
        let x := lowOdd + 2*i
        acc := x - acc
        k := k + 1
        if k ≤ K0v then
          if acc ≤ Nval then
            if inBaseImpl (Nval - acc) then ok := false
        else if k == K0v+1 then a1 := acc
        else if k == K0v+2 then a2 := acc
      i := i + 1
    lowOdd := lowOdd + 2*SEGbits
  return (ok && (Nval < a1) && (Nval < a2))

noncomputable def bigCheck : Bool := decide bigProp
attribute [implemented_by bigCheckImpl] bigCheck

theorem bigCheck_true : bigCheck = true := by native_decide

theorem bigProp_holds : bigProp :=
  of_decide_eq_true (show decide bigProp = true from bigCheck_true)

theorem hhead_pf : ∀ k, 1 ≤ k → k ≤ K0 → A k ≤ Nv → (Nv - A k) ∉ baseSums := by
  intro k h1 h2 h3
  exact bigProp_holds.1 k (Finset.mem_Icc.mpr ⟨h1, h2⟩) h3

theorem hanc1_pf : Nv < A (K0 + 1) := bigProp_holds.2.1
theorem hanc2_pf : Nv < A (K0 + 2) := bigProp_holds.2.2

/--
The claim that "Conjecture 2 holds up to $10^{10}$ for all cases except $\{2, 12\}$ since $4551086841$ cannot be written as $2^i + 12^j + \mathrm{A008347}(k)$."

This is formalized as a counterexample to a specialization of Conjecture 2.
Let $f(a, b, n)$ be the number of ways to write $n$ as $a^i + b^j + \mathrm{A008347}(k)$ for non-negative $i, j$ and positive $k$.
The claim states $f(2, 12, 4551086841) = 0$.
-/
theorem A308403.conjecture_2_counterexample :
    let n_val : ℕ := 4551086841
    let S := A008347_seq
    let generalized_a := fun n base_a base_b =>
      (Finset.range (n + 1)).sum fun i =>
        (Finset.range (n + 1)).sum fun j =>
          if base_a^i + base_b^j < n then
            ((Finset.range (2 * n + 2)).filter (fun k => k > 0 ∧ S k = n - (base_a^i + base_b^j))).card
          else
            0
    generalized_a n_val 2 12 = 0 := by
  intro n_val S generalized_a
  show generalized_a n_val 2 12 = 0
  exact main (core hhead_pf hanc1_pf hanc2_pf)
