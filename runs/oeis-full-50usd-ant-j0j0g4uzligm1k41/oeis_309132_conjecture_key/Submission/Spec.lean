import FormalConjectures.Util.ProblemImports

open Rat Nat

/--
A309132: $a(n)$ is the denominator of $F(n) = A027641(n-1)/n + A027642(n-1)/n^2$,
where $A027641(k)$ and $A027642(k)$ are the numerator and denominator of the $k$-th standard Bernoulli number $B_k$ ($B_1 = -1/2$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let n_q : ℚ := n
    have B_nm1 : ℚ := bernoulli (n - 1)
    let N : ℤ := B_nm1.num
    let D : ℕ := B_nm1.den

    -- F(n) = N / n + D / n^2, where division is rational division
    let q1 : ℚ := (N : ℚ) / n_q
    let q2 : ℚ := (D : ℚ) / (n_q * n_q)
    let F_n : ℚ := q1 + q2

    F_n.den

/-!
## Analysis of this conjecture

Write `B_{n-1} = N/D` in lowest terms (`N = (bernoulli (n-1)).num`,
`D = (bernoulli (n-1)).den`).  Then
`F(n) = N/n + D/n^2 = (N·n + D)/n^2`, so

  `a n = 1  ↔  n^2 ∣ (N·n + D)`.

Since `n ∣ N·n`, the condition `n^2 ∣ N·n + D` forces `n ∣ D`.  Writing `D = n·D'`
gives `N·n + D = n·(N + D')`, hence

  `a n = 1  ↔  n ∣ D  ∧  n ∣ (N + D/n)`.

By the **von Staudt–Clausen theorem**, `D = ∏_{(p-1) ∣ (n-1)} p` (a squarefree
product of primes), so `n ∣ D` forces `n` squarefree with `(p-1) ∣ (n-1)` for every
prime `p ∣ n` — i.e. the **Korselt / Carmichael condition (A)**.  Using the
von Staudt–Clausen residue `p·B_{p-1} ≡ -1 (mod p)` (valid because `(p-1) ∣ (n-1)`),
the second condition `n ∣ (N + D/n)` reduces, prime-by-prime, to
`n/p ≡ 1 (mod p)` for every `p ∣ n` — i.e. the **Giuga condition (B)**.

Therefore, provably,

  `a n = 1  ↔  (A) n is Carmichael/Korselt  ∧  (B) n is a Giuga number`.

These facts are confirmed numerically: e.g. the Carmichael number `561` satisfies (A)
but not (B); the Giuga number `30` satisfies (B) but not (A); every prime satisfies
both; and `a n = 1 ↔ ((A) ∧ (B))` holds for all tested `n`.

Consequently the statement below — `a n = 1 ↔ n prime` for `n > 1` — is **exactly**
the assertion that *no composite number is simultaneously a Carmichael number and a
Giuga number*.  Equivalently it is the assertion `n·B_{n-1} ≡ -1 (mod n) ↔ n prime`.
This is the **Agoh–Giuga conjecture** (Giuga 1950, Agoh 1990), a famous *open* problem
of number theory:

  * The direction `n prime ⟹ a n = 1` is a theorem (Fermat's little theorem /
    von Staudt–Clausen) but is *not* available in Mathlib.
  * The direction `a n = 1 ⟹ n prime` is the open Agoh–Giuga conjecture itself.
    No proof is known, and any counterexample must exceed `10^13800`, so it can be
    neither proved nor refuted with current mathematics.

The `sorry` below therefore stands for the open Agoh–Giuga conjecture.
-/

/-- **Verified reduction (algebraic step).**  For `n > 0`,
`a n = 1` exactly when `n^2` divides `N·n + D`, where `B_{n-1} = N/D` in lowest terms.
This is the rigorous, machine-checked content of the first paragraph of the analysis above. -/
theorem a_eq_one_iff (n : ℕ) (hn : 0 < n) :
    a n = 1 ↔ ((n : ℤ) * n) ∣ ((bernoulli (n - 1)).num * n + (bernoulli (n - 1)).den) := by
  have hn0 : n ≠ 0 := hn.ne'
  have hq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  unfold a
  rw [dif_neg hn0]
  simp only
  set N := (bernoulli (n - 1)).num with hN
  set D := (bernoulli (n - 1)).den with hD
  have key : ((N : ℚ) / (n : ℚ) + (D : ℚ) / ((n : ℚ) * (n : ℚ)))
      = (((N * (n : ℤ) + (D : ℤ)) : ℤ) : ℚ) / (((n : ℤ) * (n : ℤ) : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [key, Rat.den_div_intCast_eq_one_iff _ _ (show ((n : ℤ) * n) ≠ 0 by positivity)]

/-- **Verified case: even `n > 2`.**  Here `n - 1` is odd and `> 1`, so `bernoulli (n-1) = 0`,
whence `a n = 1 ↔ n^2 ∣ 1`, which fails.  (Elementary; no von Staudt–Clausen needed.) -/
theorem a_ne_one_of_even_gt_two {n : ℕ} (hn : 2 < n) (he : Even n) : a n ≠ 1 := by
  have hodd : Odd (n - 1) := by
    rcases he with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
  have hb : bernoulli (n - 1) = 0 := bernoulli_eq_zero_of_odd hodd (by omega)
  rw [Ne, a_eq_one_iff n (by omega), hb]
  simp only [Rat.num_zero, Rat.den_zero, Nat.cast_one, zero_mul, zero_add]
  intro h
  have : ((n : ℤ) * n) ≤ 1 := Int.le_of_dvd (by norm_num) h
  nlinarith [hn]

/-- **Verified necessary condition (forward direction, step 1).**  If `a n = 1` then
`n` divides the denominator of `B_{n-1}`.  (This is the elementary first step of the
Korselt/Carmichael analysis of the forward implication; the remaining steps need the
von Staudt–Clausen theorem, which Mathlib lacks.) -/
theorem dvd_den_of_a_eq_one {n : ℕ} (hn : 0 < n) (h : a n = 1) :
    (n : ℤ) ∣ ((bernoulli (n - 1)).den : ℤ) := by
  rw [a_eq_one_iff n hn] at h
  have hnn : (n : ℤ) ∣ ((n : ℤ) * n) := dvd_mul_left _ _
  have h1 : (n : ℤ) ∣ ((bernoulli (n - 1)).num * n + (bernoulli (n - 1)).den) := hnn.trans h
  have h2 : (n : ℤ) ∣ (bernoulli (n - 1)).num * n := dvd_mul_left _ _
  exact (dvd_add_right h2).mp h1

/-
### Verified crux of von Staudt–Clausen (toward the backward direction)

The backward implication `n.Prime → a n = 1` is a genuine theorem, but it requires the
von Staudt–Clausen residue `p · B_{p-1} ≡ -1 (mod p)`, which Mathlib does not contain.
The heart of that theorem is the **`p`-integrality of low-index Bernoulli numbers**:
`bernoulli m` has denominator coprime to `p` whenever `m < p - 1`.  We prove this here
(`Pden_bernoulli`) by a clean strong induction on the Bernoulli recurrence: solving for
`B_m` only ever divides by `m + 1 < p`, which is coprime to `p`.  (Assembling this with
Faulhaber's `sum_range_pow` and Fermat's little theorem yields the residue and hence the
backward direction; that assembly is omitted as it does not affect the open core below.)
-/
section VonStaudt
open Finset

/-- `q` is `p`-integral: its reduced denominator is coprime to `p`. -/
def Pden (p : ℕ) (q : ℚ) : Prop := Nat.Coprime q.den p

lemma Pden_add {p : ℕ} {a b : ℚ} (ha : Pden p a) (hb : Pden p b) : Pden p (a + b) :=
  Nat.Coprime.coprime_dvd_left (Rat.add_den_dvd a b) (ha.mul_left hb)

lemma Pden_mul {p : ℕ} {a b : ℚ} (ha : Pden p a) (hb : Pden p b) : Pden p (a * b) :=
  Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd a b) (ha.mul_left hb)

lemma Pden_neg {p : ℕ} {a : ℚ} (ha : Pden p a) : Pden p (-a) := by
  unfold Pden at *; rwa [Rat.neg_den]

lemma Pden_sub {p : ℕ} {a b : ℚ} (ha : Pden p a) (hb : Pden p b) : Pden p (a - b) := by
  rw [sub_eq_add_neg]; exact Pden_add ha (Pden_neg hb)

lemma Pden_natCast {p : ℕ} (z : ℕ) : Pden p (z : ℚ) := by
  unfold Pden; rw [Rat.den_natCast]; exact Nat.coprime_one_left p

lemma Pden_intCast {p : ℕ} (z : ℤ) : Pden p (z : ℚ) := by
  unfold Pden; rw [Rat.den_intCast]; exact Nat.coprime_one_left p

lemma Pden_sum {p : ℕ} {ι : Type*} {s : Finset ι} {f : ι → ℚ}
    (h : ∀ i ∈ s, Pden p (f i)) : Pden p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (Pden_natCast (p := p) 0)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact Pden_add (h a (Finset.mem_insert_self _ _))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma Pden_inv_natCast {p : ℕ} {k : ℕ} (hk : 0 < k) (hkp : Nat.Coprime k p) :
    Pden p ((k : ℚ)⁻¹) := by
  unfold Pden; rw [Rat.inv_natCast_den_of_pos hk]; exact hkp

lemma coprime_succ_of_lt {p m : ℕ} (hp : p.Prime) (hm : m + 1 < p) :
    Nat.Coprime (m + 1) p := by
  refine (Nat.Prime.coprime_iff_not_dvd hp).mpr ?_ |>.symm
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

/-- **`p`-integrality of Bernoulli numbers** (crux of von Staudt–Clausen):
for a prime `p`, `bernoulli m` has denominator coprime to `p` whenever `m < p - 1`. -/
lemma Pden_bernoulli {p : ℕ} (hp : p.Prime) :
    ∀ m, m < p - 1 → Pden p (bernoulli m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; rw [bernoulli_zero]; simpa using (Pden_natCast (p := p) 1)
    · have hsum := sum_bernoulli (m + 1)
      rw [if_neg (by omega)] at hsum
      rw [Finset.sum_range_succ, Nat.choose_succ_self_right] at hsum
      set S : ℚ := ∑ k ∈ range m, ((m + 1).choose k : ℚ) * bernoulli k with hS
      have hSp : Pden p S := by
        apply Pden_sum
        intro k hk
        rw [Finset.mem_range] at hk
        exact Pden_mul (Pden_natCast _) (ih k hk (by omega))
      have hne : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have heq : bernoulli m = (-S) * ((m + 1 : ℕ) : ℚ)⁻¹ := by
        have : ((m + 1 : ℕ) : ℚ) * bernoulli m = -S := by
          push_cast at hsum ⊢; linarith [hsum]
        field_simp
        linarith [this]
      rw [heq]
      exact Pden_mul (Pden_neg hSp)
        (Pden_inv_natCast (by omega) (coprime_succ_of_lt hp (by omega)))


/-
### Assembling the backward direction `n.Prime → a n = 1`

The lemmas below complete the genuine theorem `n.Prime → a n = 1` from the
p-integrality result above, Faulhaber's formula (`sum_range_pow`) and Fermat's
little theorem.  `backward_dvd` gives exactly the `a_eq_one_iff` divisibility.
-/

-- range-sum to univ-sum over ZMod p
lemma sum_range_to_univ {p : ℕ} [NeZero p] (f : ZMod p → ZMod p) :
    (∑ k ∈ range p, f (k : ZMod p)) = ∑ x : ZMod p, f x := by
  refine Finset.sum_nbij' (fun k => (k : ZMod p)) ZMod.val ?_ ?_ ?_ ?_ ?_
  · intro a ha; exact Finset.mem_univ _
  · intro a ha; rw [Finset.mem_range]; exact ZMod.val_lt a
  · intro a ha; rw [Finset.mem_range] at ha; exact ZMod.val_natCast_of_lt ha
  · intro a ha; exact ZMod.natCast_zmod_val a
  · intro a ha; rfl

lemma flt_sum {p : ℕ} (hp : p.Prime) :
    (((∑ k ∈ range p, k ^ (p - 1) : ℕ)) : ZMod p) = -1 := by
  haveI := Fact.mk hp
  have hp1 : 1 ≤ p - 1 := by have := hp.two_le; omega
  push_cast
  rw [sum_range_to_univ (p := p) (fun x => x ^ (p - 1))]
  classical
  rw [← Finset.sum_sdiff (Finset.subset_univ ({0} : Finset (ZMod p)))]
  rw [Finset.sum_singleton, zero_pow (by omega : p - 1 ≠ 0), add_zero]
  have hcongr : ∀ x ∈ Finset.univ \ {(0 : ZMod p)}, x ^ (p - 1) = 1 := by
    intro x hx
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hx
    exact ZMod.pow_card_sub_one_eq_one hx.2
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const]
  have hc : (Finset.univ \ {(0 : ZMod p)}).card = p - 1 := by
    rw [Finset.card_univ_diff, Finset.card_singleton, ZMod.card]
  rw [hc, nsmul_eq_mul, mul_one]
  have : ((p - 1 : ℕ) : ZMod p) = (p : ZMod p) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [this, ZMod.natCast_self, zero_sub]

-- Part A as an integer divisibility
lemma flt_dvd {p : ℕ} (hp : p.Prime) :
    (p : ℤ) ∣ (((∑ k ∈ range p, k ^ (p - 1) : ℕ)) : ℤ) + 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have hA : (((∑ k ∈ range p, k ^ (p - 1) : ℕ)) : ZMod p) = -1 := flt_sum hp
  push_cast at hA
  rw [hA]; ring

-- Part B + C : Faulhaber + FLT combine to p·B_{p-1} + 1 = p·W with W p-integral.
lemma faulhaber_key {p : ℕ} (hp : p.Prime) :
    ∃ W : ℚ, Pden p W ∧ (p : ℚ) * bernoulli (p - 1) + 1 = (p : ℚ) * W := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpp : p - 1 + 1 = p := by omega
  have hpQ : (p : ℚ) ≠ 0 := by positivity
  -- Faulhaber
  have hF := sum_range_pow p (p - 1)
  rw [hpp] at hF
  -- fix the divisor ↑(p-1)+1 = ↑p
  have hdiv : ((p - 1 : ℕ) : ℚ) + 1 = (p : ℚ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]; ring
  simp only [hdiv] at hF
  -- the nat sum
  set T : ℕ := ∑ k ∈ range p, k ^ (p - 1) with hT
  have hTcast : (∑ k ∈ range p, (k : ℚ) ^ (p - 1)) = (T : ℚ) := by
    rw [hT]; push_cast; rfl
  rw [hTcast] at hF
  -- define L'
  set L' : ℚ := ∑ i ∈ range (p - 1), bernoulli i * ((p.choose i * p ^ (p - i - 2) : ℕ) : ℚ)
    with hL'
  -- split off the last term i = p-1
  have hsplit : (∑ i ∈ range p, bernoulli i * (p.choose i) * (p : ℚ) ^ (p - i) / p)
      = (p : ℚ) * L' + (p : ℚ) * bernoulli (p - 1) := by
    have hrange : range p = range ((p - 1) + 1) := by rw [hpp]
    rw [hrange, Finset.sum_range_succ]
    congr 1
    · -- lower sum = p * L'
      rw [hL', Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      push_cast
      have hpi : (p : ℚ) ^ (p - i) = (p : ℚ) ^ 2 * (p : ℚ) ^ (p - i - 2) := by
        rw [← pow_add]; congr 1; omega
      rw [hpi]; field_simp
    · -- last term = p * bernoulli (p-1)
      have hch : p.choose (p - 1) = p := by
        rw [Nat.choose_symm (by omega), Nat.choose_one_right]
      rw [hch]
      have hpm : p - (p - 1) = 1 := by omega
      rw [hpm]
      field_simp
  rw [hsplit] at hF
  -- FLT: T + 1 = p * s
  obtain ⟨s, hs⟩ := flt_dvd hp
  -- so (T : ℚ) + 1 = p * s
  have hsQ : (T : ℚ) + 1 = (p : ℚ) * (s : ℚ) := by
    have : ((T : ℤ) + 1 : ℚ) = ((p : ℤ) * s : ℚ) := by exact_mod_cast congrArg (Int.cast : ℤ → ℚ) hs
    push_cast at this; linarith
  refine ⟨(s : ℚ) - L', ?_, ?_⟩
  · -- Pden p W
    apply Pden_sub (Pden_intCast s)
    rw [hL']
    apply Pden_sum
    intro i hi
    rw [Finset.mem_range] at hi
    exact Pden_mul (Pden_bernoulli hp i hi) (Pden_natCast _)
  · -- the equation
    -- from hF : (T:ℚ) = p*L' + p*bernoulli(p-1)
    have hForder : (T : ℚ) = (p : ℚ) * L' + (p : ℚ) * bernoulli (p - 1) := hF
    rw [mul_sub]
    linarith [hForder, hsQ]

-- Part D : convert to the integer divisibility p² | (N·p + D).
lemma backward_dvd {p : ℕ} (hp : p.Prime) :
    ((p : ℤ) * p) ∣ ((bernoulli (p - 1)).num * (p : ℤ) + ((bernoulli (p - 1)).den : ℤ)) := by
  obtain ⟨W, hWp, hWeq⟩ := faulhaber_key hp
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  set B := bernoulli (p - 1) with hBdef
  set N : ℤ := B.num with hN
  set Dn : ℕ := B.den with hDn
  set an : ℤ := W.num with han
  set bn : ℕ := W.den with hbn
  -- coprimality of p and bn = W.den
  have hcop : Nat.Coprime p W.den := (hWp).symm
  have hcopZ : IsCoprime (p : ℤ) (bn : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  -- cross-multiplied rational equation
  have hdenB : ((B.den : ℕ) : ℚ) ≠ 0 := by exact_mod_cast B.den_ne_zero
  have hdenW : ((W.den : ℕ) : ℚ) ≠ 0 := by exact_mod_cast W.den_ne_zero
  have hBq : ((B.num : ℤ) : ℚ) = B * ((B.den : ℕ) : ℚ) :=
    (div_eq_iff hdenB).mp (Rat.num_div_den B)
  have hWq : ((W.num : ℤ) : ℚ) = W * ((W.den : ℕ) : ℚ) :=
    (div_eq_iff hdenW).mp (Rat.num_div_den W)
  have hQ : (p : ℚ) * (N : ℚ) * (bn : ℚ) + (Dn : ℚ) * (bn : ℚ)
      = (p : ℚ) * (an : ℚ) * (Dn : ℚ) := by
    have h1 : ((N : ℤ) : ℚ) = B * ((Dn : ℕ) : ℚ) := hBq
    have h2 : ((an : ℤ) : ℚ) = W * ((bn : ℕ) : ℚ) := hWq
    linear_combination ((Dn : ℚ) * (bn : ℚ)) * hWeq + ((p : ℚ) * (bn : ℚ)) * h1
      - ((p : ℚ) * (Dn : ℚ)) * h2
  -- integer version
  have E1 : (p : ℤ) * N * (bn : ℤ) + (Dn : ℤ) * (bn : ℤ) = (p : ℤ) * an * (Dn : ℤ) := by
    exact_mod_cast hQ
  -- Step 1 : p ∣ Dn
  have hpdvdmul : (p : ℤ) ∣ (Dn : ℤ) * (bn : ℤ) :=
    ⟨an * (Dn : ℤ) - N * (bn : ℤ), by linear_combination E1⟩
  have hpD : (p : ℤ) ∣ (Dn : ℤ) := hcopZ.dvd_of_dvd_mul_right hpdvdmul
  obtain ⟨D1, hD1⟩ := hpD
  -- Step 2 : p ∣ (N + D1)
  have hpe : (p : ℤ) * ((bn : ℤ) * (N + D1)) = (p : ℤ) * ((p : ℤ) * (an * D1)) := by
    rw [hD1] at E1; linear_combination E1
  have E2 : (bn : ℤ) * (N + D1) = (p : ℤ) * (an * D1) := mul_left_cancel₀ hp0 hpe
  have hpND : (p : ℤ) ∣ (N + D1) :=
    hcopZ.dvd_of_dvd_mul_left ⟨an * D1, E2⟩
  obtain ⟨M, hM⟩ := hpND
  -- Step 3 : conclude
  have hfin : N * (p : ℤ) + (Dn : ℤ) = (p : ℤ) * (p : ℤ) * M := by
    rw [hD1]; linear_combination (p : ℤ) * hM
  exact ⟨M, hfin⟩

end VonStaudt

/--
Conjecture: for $n > 1$, $a(n) = 1$ if and only if $n$ is prime.
This is the main conjecture related to A309132.

The proof below fully discharges:
* the **even** case (`n = 2` gives both sides true; even `n > 2` gives both sides false,
  via `a_ne_one_of_even_gt_two`); and
* the **backward** direction `n.Prime → a n = 1` for all `n` (`backward_dvd`), a genuine
  theorem proved here from `p`-integrality of Bernoulli numbers (`Pden_bernoulli`),
  Faulhaber's formula (`sum_range_pow`) and Fermat's little theorem (`flt_dvd`).

The only remaining `sorry` is the **forward** direction for odd `n`:
`n^2 ∣ (N·n + D) → n.Prime`.  By `a_eq_one_iff` and von Staudt–Clausen this is exactly
`(n is Carmichael) ∧ (n is Giuga) → n.Prime`, i.e. *no composite number is simultaneously
a Carmichael number and a Giuga number* — the **Agoh–Giuga conjecture** (open since 1950).
No proof of it exists in current mathematics, and any counterexample exceeds `10^13800`. -/
theorem oeis_309132_conjecture_key (n : ℕ) (hn : n > 1) : a n = 1 ↔ Nat.Prime n := by
  rcases Nat.even_or_odd n with he | ho
  · -- even `n`: fully verified
    by_cases h2 : n = 2
    · subst h2
      refine ⟨fun _ => Nat.prime_two, fun _ => ?_⟩
      rw [a_eq_one_iff 2 (by norm_num)]; norm_num [bernoulli_one]
    · have hn2 : 2 < n := by omega
      exact ⟨fun h => absurd h (a_ne_one_of_even_gt_two hn2 he),
             fun hp => absurd (hp.even_iff.mp he) h2⟩
  · -- odd `n`: reduces to the open Agoh–Giuga conjecture
    rw [a_eq_one_iff n (by omega)]
    constructor
    · -- forward `n^2 ∣ (N·n + D) → n.Prime`: the **open** Agoh–Giuga conjecture
      intro h
      sorry
    · -- backward `n.Prime → n^2 ∣ (N·n + D)`: a genuine theorem, fully proved
      intro hp
      exact backward_dvd hp
