import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A308734: Number of ordered ways to write $n$ as $(2^a \cdot 3^b)^2 + (2^c \cdot 5^d)^2 + x^2 + y^2$,
where $a,b,c,d,x,y$ are nonnegative integers with $x \le y$.

Note: The provided definition uses a computationally convenient, but potentially insufficient, range `M` for the exponents $a, b, c, d$.
A mathematically precise definition would use unbounded natural numbers for $a, b, c, d, x, y$ and count the size of the resulting set.
We proceed with the definition as given in the prompt.
-/
def A308734 (n : ℕ) : ℕ :=
  -- We use a six-fold nested summation over a range $M$.
  let M := Nat.sqrt n + 1

  Finset.sum (range M) fun a =>
  Finset.sum (range M) fun b =>
  Finset.sum (range M) fun c =>
  Finset.sum (range M) fun d =>
  Finset.sum (range M) fun x =>
  Finset.sum (range M) fun y =>
    let term1 := (2^a * 3^b)^2
    let term2 := (2^c * 5^d)^2

    if term1 + term2 + x^2 + y^2 = n ∧ x ≤ y
    then 1
    else 0

/-- The unbounded notion of representability:
`n = (2^a 3^b)^2 + (2^c 5^d)^2 + x^2 + y^2` with `x ≤ y`. -/
def RepA308734 (n : ℕ) : Prop :=
  ∃ a b c d x y : ℕ, (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 + x ^ 2 + y ^ 2 = n ∧ x ≤ y

private lemma prod_le_sqrt {p n : ℕ} (h : p ^ 2 ≤ n) : p ≤ Nat.sqrt n := by
  rw [Nat.le_sqrt]
  calc p * p = p ^ 2 := by ring
  _ ≤ n := h

private lemma sqrt_lt_M {x n : ℕ} (h : x ^ 2 ≤ n) : x < Nat.sqrt n + 1 := by
  have := prod_le_sqrt h
  omega

private lemma factor_le_sqrt_left {f g n : ℕ} (hg : 1 ≤ g) (h : (f * g) ^ 2 ≤ n) :
    f ≤ Nat.sqrt n := by
  have hfg : f * g ≤ Nat.sqrt n := prod_le_sqrt h
  have : f ≤ f * g := Nat.le_mul_of_pos_right _ hg
  omega

private lemma factor_le_sqrt_right {f g n : ℕ} (hf : 1 ≤ f) (h : (f * g) ^ 2 ≤ n) :
    g ≤ Nat.sqrt n := by
  have hfg : f * g ≤ Nat.sqrt n := prod_le_sqrt h
  have : g ≤ f * g := Nat.le_mul_of_pos_left _ hf
  omega

/-- **Faithfulness / range sufficiency.**
Although the note above flags the range `M = Nat.sqrt n + 1` as *potentially* insufficient,
it is in fact always sufficient: every (unbounded) representation of `n` automatically has all
six parameters strictly below `M`. Indeed each squared summand is `≤ n`, so for the base
`2^a·3^b ≤ √n` we get `a < 2^a ≤ 2^a·3^b ≤ √n < M` (and analogously for `b, c, d`, while
`x, y ≤ √n < M`). Hence the bounded count `A308734 n` is positive whenever `RepA308734 n` holds. -/
lemma rep_imp_pos (n : ℕ) (h : RepA308734 n) : 0 < A308734 n := by
  obtain ⟨a, b, c, d, x, y, heq, hxy⟩ := h
  have t1 : (2 ^ a * 3 ^ b) ^ 2 ≤ n := by omega
  have t2 : (2 ^ c * 5 ^ d) ^ 2 ≤ n := by omega
  have tx : x ^ 2 ≤ n := by omega
  have ty : y ^ 2 ≤ n := by omega
  have ha : a < Nat.sqrt n + 1 := by
    have h1 := factor_le_sqrt_left (Nat.one_le_pow b 3 (by norm_num)) t1
    have h2 := a.lt_two_pow_self; omega
  have hb : b < Nat.sqrt n + 1 := by
    have h1 := factor_le_sqrt_right (Nat.one_le_pow a 2 (by norm_num)) t1
    have h2 := b.lt_two_pow_self
    have h3 : 2 ^ b ≤ 3 ^ b := Nat.pow_le_pow_left (by norm_num) b
    omega
  have hc : c < Nat.sqrt n + 1 := by
    have h1 := factor_le_sqrt_left (Nat.one_le_pow d 5 (by norm_num)) t2
    have h2 := c.lt_two_pow_self; omega
  have hd : d < Nat.sqrt n + 1 := by
    have h1 := factor_le_sqrt_right (Nat.one_le_pow c 2 (by norm_num)) t2
    have h2 := d.lt_two_pow_self
    have h3 : 2 ^ d ≤ 5 ^ d := Nat.pow_le_pow_left (by norm_num) d
    omega
  have hx : x < Nat.sqrt n + 1 := sqrt_lt_M tx
  have hy : y < Nat.sqrt n + 1 := sqrt_lt_M ty
  have hmemA : a ∈ range (Nat.sqrt n + 1) := mem_range.mpr ha
  have hmemB : b ∈ range (Nat.sqrt n + 1) := mem_range.mpr hb
  have hmemC : c ∈ range (Nat.sqrt n + 1) := mem_range.mpr hc
  have hmemD : d ∈ range (Nat.sqrt n + 1) := mem_range.mpr hd
  have hmemX : x ∈ range (Nat.sqrt n + 1) := mem_range.mpr hx
  have hmemY : y ∈ range (Nat.sqrt n + 1) := mem_range.mpr hy
  show 0 < A308734 n
  unfold A308734
  simp only
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨a, hmemA, ?_⟩
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨b, hmemB, ?_⟩
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨c, hmemC, ?_⟩
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨d, hmemD, ?_⟩
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨x, hmemX, ?_⟩
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨y, hmemY, ?_⟩
  rw [if_pos ⟨heq, hxy⟩]
  exact one_pos

/-- Representability is closed under multiplication by `4`, since scaling
`(a,b,c,d,x,y) ↦ (a+1, b, c+1, d, 2x, 2y)` keeps both bases inside their semigroups:
`2^{a+1} 3^b ∈ ⟨2,3⟩` and `2^{c+1} 5^d ∈ ⟨2,5⟩`. -/
lemma rep_four_mul (n : ℕ) (h : RepA308734 n) : RepA308734 (4 * n) := by
  obtain ⟨a, b, c, d, x, y, heq, hxy⟩ := h
  refine ⟨a + 1, b, c + 1, d, 2 * x, 2 * y, ?_, by omega⟩
  have e1 : (2 ^ (a + 1) * 3 ^ b) ^ 2 = 4 * (2 ^ a * 3 ^ b) ^ 2 := by ring
  have e2 : (2 ^ (c + 1) * 5 ^ d) ^ 2 = 4 * (2 ^ c * 5 ^ d) ^ 2 := by ring
  rw [e1, e2]; ring_nf; ring_nf at heq; omega

/-- The open mathematical core: every `n > 1` with `4 ∤ n` has an (unbounded) representation.
Together with the `4`-descent (`rep_four_mul`) this is equivalent to the full conjecture.
This is the genuinely open part of Zhi-Wei Sun's conjecture A308734. -/
lemma rep_of_not_four_dvd (n : ℕ) (hn : 1 < n) (h4 : ¬ (4 ∣ n)) : RepA308734 n := by
  sorry

/-- Every `n > 1` admits an unbounded representation, by strong induction:
the `4 ∣ n` case follows from the `4`-descent and the induction hypothesis (base `n = 4`),
and the `4 ∤ n` case is `rep_of_not_four_dvd`. -/
lemma rep_of_one_lt : ∀ n : ℕ, 1 < n → RepA308734 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h4 : 4 ∣ n
    · obtain ⟨m, rfl⟩ := h4
      rcases Nat.lt_or_ge m 2 with hm | hm
      · interval_cases m
        · omega
        · exact ⟨0, 0, 0, 0, 1, 1, by norm_num, by norm_num⟩
      · exact rep_four_mul m (ih m (by omega) (by omega))
    · exact rep_of_not_four_dvd n hn h4

/--
Four-square Conjecture: a(n) > 0 for all n > 1.
This is much stronger than Lagrange's four-square theorem.
(OEIS A308734, Comment C2)

By `rep_imp_pos` (range sufficiency, proved above), this is equivalent to the statement that
every `n > 1` admits an unbounded representation `RepA308734 n`, which is exactly Zhi-Wei Sun's
conjecture.
-/
theorem oeis_a308734_conjecture_0 : ∀ n : ℕ, 1 < n → A308734 n > 0 := by
  intro n hn
  exact rep_imp_pos n (rep_of_one_lt n hn)
