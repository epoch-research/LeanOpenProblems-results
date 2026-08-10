import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators Int

-- Generalized binomial coefficient $\binom{r}{k}$ for $r \in \mathbb{Z}, k \in \mathbb{N}$.
-- We use the definition $\binom{r}{k} = \frac{\prod_{i=0}^{k-1} (r-i)}{k!}$ and rely on
-- the known property that this division results in an integer.
def generalized_choose_int (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else
    (Finset.prod (Finset.range k) fun i => r - (i : ℤ)) / (k.factorial : ℤ)

-- Helper definition for the generalized coefficient formula.
/--
The $k$-th power series coefficient of $c(x)^r$: $\frac{r}{r+k}\binom{r+2k-1}{k}$.
This expression is known to be an integer for all $r \in \mathbb{Z}$.
-/
def generalized_catalan_coefficient (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else
    let num_choose := generalized_choose_int (r + 2 * (k : ℤ) - 1) k
    let denominator : ℤ := r + k
    -- The division is exact because the coefficient is an integer.
    -- We rely on integer division to compute the result.
    (r * num_choose) / denominator

/--
The generalized sequence $a_m(n)$ is the $n$-th order Taylor polynomial (centered at 0) of $c(x)^{m \cdot n}$ evaluated at $x=1$.
$$a_m(n) = \sum_{k=0}^n [x^k] c(x)^{m n}$$
-/
def a_gen (m : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 1
  else
    let r : ℤ := m * (n : ℤ)
    Finset.sum (range (n + 1)) fun k =>
      generalized_catalan_coefficient r k

/--
A333096: The $n$-th order Taylor polynomial (centered at 0) of $c(x)^{4n}$ evaluated at $x=1$, where $c(x) = \frac{1 - \sqrt{1 - 4x}}{2x}$ is the o.g.f. of the sequence of Catalan numbers $A000108$.
The sequence is defined by the formula:
$$a(n) = \sum_{k = 0}^n \frac{4n}{4n+k}\binom{4n+2k-1}{k} \quad \text{for } n \ge 1$$
and $a(0) = 1.$$
The summand is the $k$-th coefficient of the power series $c(x)^{4n}$, which is an integer.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.sum (range (n + 1)) fun k =>
      let m : ℕ := 4 * n
      let numerator : ℕ := m * (m + 2 * k - 1).choose k
      let denominator : ℕ := m + k
      -- Since the combinatorial identity guarantees exact divisibility, Nat division is equivalent to integer division.
      numerator / denominator

/-
Conjecture on OEIS A333096:
More generally, for each integer $m$, we conjecture that the sequence
$a_m(n) := \text{the } n\text{-th order Taylor polynomial of } c(x)^{m \cdot n} \text{ evaluated at } x = 1$
satisfies the supercongruences $a_m(n \cdot p^k) \equiv a_m(n \cdot p^{k-1}) \pmod{p^{3k}}$
for prime $p \ge 5$ and positive integers $n$ and $k$.
-/


/-
Self-contained assembly of the temporary lemmas needed for the direct B-sequence
step.  The root temporary files are copied below rather than imported, since
those files are not lake modules in this project.
-/


/- Copied from BetaYpairTemp.lean, AntiPalindromeTemp.lean, MainDvdTemp.lean because root temp files are not importable as Lean modules in this project. -/

/- copied BetaYpairTemp.lean -/

open scoped BigOperators
open Nat

namespace BetaYpairTemp

/-- The beta coefficient from the derivation. -/
def beta (N l M a : ℕ) : ℤ := if a ≤ M then ((N-l).choose (M-a):ℤ) else 0

/-- The antisymmetric raw difference. -/
def rawdiff (M K i j : ℕ) : ℤ :=
  (M.choose i:ℤ)*(K.choose j:ℤ) - (M.choose j:ℤ)*(K.choose i:ℤ)

/-- A paired summand. -/
def Ypair (N M l i : ℕ) : ℤ :=
  let j := l-i
  (N.choose l:ℤ)*(beta N l M i - beta N l M j)

lemma choose_mul_sub_comm (n a b : ℕ) :
    n.choose a * (n - a).choose b = n.choose b * (n - b).choose a := by
  have h1 := Nat.choose_mul (n := n) (k := a + b) (s := a) (Nat.le_add_right a b)
  have h2 := Nat.choose_mul (n := n) (k := a + b) (s := b) (by omega : b ≤ a + b)
  rw [Nat.add_sub_cancel_left] at h1
  have h2' : n.choose (a + b) * (a + b).choose a =
      n.choose b * (n - b).choose a := by
    calc
      n.choose (a + b) * (a + b).choose a
          = n.choose (a + b) * (a + b).choose b := by rw [Nat.choose_symm_add]
      _ = n.choose b * (n - b).choose ((a + b) - b) := h2
      _ = n.choose b * (n - b).choose a := by rw [Nat.add_sub_cancel_right]
  exact h1.symm.trans h2'

lemma choose_three_count {N M l i j : ℕ} (hMN : M ≤ N) (hil : i ≤ l)
    (hij : j = l - i) (hiM : i ≤ M) :
    N.choose M * M.choose i * (N - M).choose j =
      N.choose l * l.choose i * (N - l).choose (M - i) := by
  have hNM : N - i - (M - i) = N - M := by omega
  have hNl : N - i - j = N - l := by omega
  have hMi_le : M - i ≤ N - i := by omega
  have hleft := Nat.choose_mul (n := N) (k := M) (s := i) hiM
  have hright := Nat.choose_mul (n := N) (k := l) (s := i) hil
  rw [← hij] at hright
  have hcomm := choose_mul_sub_comm (n := N - i) (a := M - i) (b := j)
  rw [hNM, hNl] at hcomm
  calc
    N.choose M * M.choose i * (N - M).choose j
        = (N.choose i * (N - i).choose (M - i)) * (N - M).choose j := by rw [hleft]
    _ = N.choose i * ((N - i).choose (M - i) * (N - M).choose j) := by ring
    _ = N.choose i * ((N - i).choose j * (N - l).choose (M - i)) := by rw [hcomm]
    _ = (N.choose i * (N - i).choose j) * (N - l).choose (M - i) := by ring
    _ = (N.choose l * l.choose i) * (N - l).choose (M - i) := by rw [← hright]
    _ = N.choose l * l.choose i * (N - l).choose (M - i) := by ring

lemma choose_factorial_int {l i j : ℕ} (hil : i ≤ l) (hij : j = l - i) :
    (l.choose i : ℤ) * ((i.factorial * j.factorial : ℕ) : ℤ) = (l.factorial : ℤ) := by
  have hnat : l.choose i * i.factorial * j.factorial = l.factorial := by
    rw [hij]
    exact Nat.choose_mul_factorial_mul_factorial hil
  have hnat' : l.choose i * (i.factorial * j.factorial) = l.factorial := by
    rw [← Nat.mul_assoc, hnat]
  exact_mod_cast hnat'

lemma beta_term_identity (N M l i j : ℕ) (hMN : M ≤ N) (hil : i ≤ l) (hij : j = l - i) :
    (l.factorial:ℤ) * (N.choose l:ℤ) * beta N l M i =
      (N.choose M:ℤ) * (((i.factorial * j.factorial:ℕ):ℤ) * (M.choose i:ℤ) * ((N-M).choose j:ℤ)) := by
  by_cases hiM : i ≤ M
  · have hcount_nat := choose_three_count (N := N) (M := M) (l := l) (i := i) (j := j) hMN hil hij hiM
    have hcount : (N.choose M:ℤ) * (M.choose i:ℤ) * ((N - M).choose j:ℤ) =
        (N.choose l:ℤ) * (l.choose i:ℤ) * ((N - l).choose (M - i):ℤ) := by
      exact_mod_cast hcount_nat
    have hfact := choose_factorial_int (l := l) (i := i) (j := j) hil hij
    simp [beta, hiM]
    calc
      (l.factorial:ℤ) * (N.choose l:ℤ) * ((N - l).choose (M - i):ℤ)
          = ((l.choose i:ℤ) * ((i.factorial * j.factorial:ℕ):ℤ)) * (N.choose l:ℤ) * ((N - l).choose (M - i):ℤ) := by rw [hfact]
      _ = ((i.factorial * j.factorial:ℕ):ℤ) * ((N.choose l:ℤ) * (l.choose i:ℤ) * ((N - l).choose (M - i):ℤ)) := by ring
      _ = ((i.factorial * j.factorial:ℕ):ℤ) * ((N.choose M:ℤ) * (M.choose i:ℤ) * ((N - M).choose j:ℤ)) := by rw [← hcount]
      _ = (N.choose M:ℤ) * (((i.factorial * j.factorial:ℕ):ℤ) * (M.choose i:ℤ) * ((N - M).choose j:ℤ)) := by ring
  · have hMi_zero : M.choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [beta, hiM, hMi_zero]

/-- The requested beta/Ypair identity. -/
theorem beta_Ypair_identity (N M l i j : ℕ) (hMN : M ≤ N) (hil : i ≤ l) (hij : j = l - i) :
    (l.factorial:ℤ) * Ypair N M l i =
      (N.choose M:ℤ) * (((i.factorial * j.factorial:ℕ):ℤ) * rawdiff M (N-M) i j) := by
  have hji_le_l : j ≤ l := by omega
  have hij' : i = l - j := by omega
  have hterm_i := beta_term_identity (N := N) (M := M) (l := l) (i := i) (j := j) hMN hil hij
  have hterm_j := beta_term_identity (N := N) (M := M) (l := l) (i := j) (j := i) hMN hji_le_l hij'
  dsimp [Ypair]
  rw [← hij]
  dsimp [rawdiff]
  calc
    (l.factorial:ℤ) * ((N.choose l:ℤ) * (beta N l M i - beta N l M j))
        = (l.factorial:ℤ) * (N.choose l:ℤ) * beta N l M i -
          (l.factorial:ℤ) * (N.choose l:ℤ) * beta N l M j := by ring
    _ = (N.choose M:ℤ) * (((i.factorial * j.factorial:ℕ):ℤ) * (M.choose i:ℤ) * ((N-M).choose j:ℤ)) -
        (N.choose M:ℤ) * (((j.factorial * i.factorial:ℕ):ℤ) * (M.choose j:ℤ) * ((N-M).choose i:ℤ)) := by
      rw [hterm_i, hterm_j]
    _ = (N.choose M:ℤ) * (((i.factorial * j.factorial:ℕ):ℤ) *
        ((M.choose i:ℤ) * ((N-M).choose j:ℤ) - (M.choose j:ℤ) * ((N-M).choose i:ℤ))) := by
      norm_num [Nat.mul_comm]
      ring



/-- The middle term in an anti-palindromic integer sequence is zero. -/
lemma anti_pal_middle_zero {u : ℕ → ℤ} {l i : ℕ}
    (hanti : ∀ k, k ≤ l → u (l - k) = - u k) (hi : i = l - i) : u i = 0 := by
  have hil : i ≤ l := by omega
  have h := hanti i hil
  rw [← hi] at h
  omega

/-- Pair the coefficient sum by the involution `i ↦ l-i`. -/
theorem coefficient_sum_paired_decomposition (u : ℕ → ℤ) (N M l : ℕ)
    (_hsupp : ∀ i, l < i → u i = 0) (_h0 : u 0 = 0) (_hl : u l = 0)
    (hanti : ∀ i, i ≤ l → u (l - i) = - u i) :
    (Finset.range (l + 1)).sum (fun a => u a * ((N.choose l : ℤ) * beta N l M a)) =
      ((Finset.range (l + 1)).filter (fun i => i < l - i)).sum
        (fun i => u i * Ypair N M l i) := by
  classical
  let C : ℤ := (N.choose l : ℤ)
  let f : ℕ → ℤ := fun a => u a * (C * beta N l M a)
  let s : Finset ℕ := Finset.range (l + 1)
  let I : Finset ℕ := s.filter (fun i => i < l - i)
  let E : Finset ℕ := s.filter (fun i => i = l - i)
  let J : Finset ℕ := s.filter (fun i => l - i < i)
  have hmem_s_le : ∀ {a}, a ∈ s → a ≤ l := by
    intro a ha
    exact Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  have hsplit_not : (s.filter fun i => ¬ i < l - i) = E ∪ J := by
    ext a
    simp only [E, J, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro h
      rcases h with ⟨has, hnotlt⟩
      have hal : a ≤ l := hmem_s_le has
      by_cases heq : a = l - a
      · exact Or.inl ⟨has, heq⟩
      · have hlt : l - a < a := by omega
        exact Or.inr ⟨has, hlt⟩
    · intro h
      rcases h with h | h
      · exact ⟨h.1, by omega⟩
      · exact ⟨h.1, by omega⟩
  have hEJ_disj : Disjoint E J := by
    rw [Finset.disjoint_left]
    intro a haE haJ
    have heq : a = l - a := (Finset.mem_filter.mp haE).2
    have hlt : l - a < a := (Finset.mem_filter.mp haJ).2
    omega
  have hE_zero : E.sum f = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have heq : a = l - a := (Finset.mem_filter.mp ha).2
    have hua : u a = 0 := anti_pal_middle_zero hanti heq
    simp [hua]
  have hJ_to_I : J.sum f = I.sum (fun i => f (l - i)) := by
    refine Finset.sum_bij (fun a _ => l - a) ?_ ?_ ?_ ?_
    · intro a ha
      have has : a ∈ s := (Finset.mem_filter.mp ha).1
      have hlt : l - a < a := (Finset.mem_filter.mp ha).2
      have hal : a ≤ l := hmem_s_le has
      have hcomp_mem : l - a ∈ s := by
        simp [s]
      have hlower : l - a < l - (l - a) := by omega
      exact Finset.mem_filter.mpr ⟨hcomp_mem, hlower⟩
    · intro a₁ ha₁ a₂ ha₂ h
      change l - a₁ = l - a₂ at h
      have h1le : a₁ ≤ l := hmem_s_le (Finset.mem_filter.mp ha₁).1
      have h2le : a₂ ≤ l := hmem_s_le (Finset.mem_filter.mp ha₂).1
      omega
    · intro b hb
      refine ⟨l - b, ?_, ?_⟩
      · have hbs : b ∈ s := (Finset.mem_filter.mp hb).1
        have hbl : b ≤ l := hmem_s_le hbs
        have hb_lt : b < l - b := (Finset.mem_filter.mp hb).2
        have hcomp_mem : l - b ∈ s := by
          simp [s]
        have hupper : l - (l - b) < l - b := by omega
        exact Finset.mem_filter.mpr ⟨hcomp_mem, hupper⟩
      · change l - (l - b) = b
        have hbs : b ∈ s := (Finset.mem_filter.mp hb).1
        have hbl : b ≤ l := hmem_s_le hbs
        omega
    · intro a ha
      change f a = f (l - (l - a))
      have hale : a ≤ l := hmem_s_le (Finset.mem_filter.mp ha).1
      have hll : l - (l - a) = a := by omega
      rw [hll]
  have hnot_sum : (s.filter fun i => ¬ i < l - i).sum f = I.sum (fun i => f (l - i)) := by
    rw [hsplit_not, Finset.sum_union hEJ_disj, hE_zero, zero_add, hJ_to_I]
  have htotal : s.sum f = I.sum (fun i => f i + f (l - i)) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := s) (p := fun i => i < l - i) (f := f)
    change I.sum f + (s.filter fun i => ¬ i < l - i).sum f = s.sum f at hsplit
    rw [← hsplit, hnot_sum]
    rw [Finset.sum_add_distrib]
  have hpair : ∀ i ∈ I, f i + f (l - i) = u i * Ypair N M l i := by
    intro i hi
    have his : i ∈ s := (Finset.mem_filter.mp hi).1
    have hil : i ≤ l := hmem_s_le his
    have hui : u (l - i) = - u i := hanti i hil
    simp [f, C, Ypair, hui]
    ring
  calc
    (Finset.range (l + 1)).sum (fun a => u a * ((N.choose l : ℤ) * beta N l M a))
        = s.sum f := by rfl
    _ = I.sum (fun i => f i + f (l - i)) := htotal
    _ = I.sum (fun i => u i * Ypair N M l i) := by
      exact Finset.sum_congr rfl hpair
    _ = ((Finset.range (l + 1)).filter (fun i => i < l - i)).sum
        (fun i => u i * Ypair N M l i) := by rfl

/-- Same paired decomposition in the requested bounded-sum notation. -/
theorem coefficient_sum_paired_decomposition_bounded (u : ℕ → ℤ) (N M l : ℕ)
    (hsupp : ∀ i, l < i → u i = 0) (h0 : u 0 = 0) (hl : u l = 0)
    (hanti : ∀ i, i ≤ l → u (l - i) = - u i) :
    (∑ a ∈ Finset.range (l + 1), u a * ((N.choose l : ℤ) * beta N l M a)) =
      ∑ i ∈ (Finset.range (l + 1)).filter (fun i => i < l - i), u i * Ypair N M l i := by
  simpa using coefficient_sum_paired_decomposition (u := u) (N := N) (M := M) (l := l)
    hsupp h0 hl hanti

end BetaYpairTemp

/- copied AntiPalindromeTemp.lean -/

open scoped BigOperators
open Finset Polynomial

/-- A coefficient function supported in `range (l+1)` and anti-palindromic about `l`. -/
def AntiPalCoeff (u : ℕ → ℤ) (l : ℕ) : Prop :=
  (∀ i, i ≤ l → u (l - i) = - u i) ∧
  u 0 = 0 ∧
  u l = 0 ∧
  (∀ i, l < i → u i = 0)

/-- The polynomial with coefficients `u 0, ..., u l`.  This is useful before introducing
any Cartier operator. -/
noncomputable def coeffPolynomial (u : ℕ → ℤ) (l : ℕ) : Polynomial ℤ :=
  Finset.sum (Finset.range (l + 1)) fun i => Polynomial.monomial i (u i)

lemma coeff_coeffPolynomial_of_le (u : ℕ → ℤ) {l i : ℕ} (hi : i ≤ l) :
    (coeffPolynomial u l).coeff i = u i := by
  classical
  simp [coeffPolynomial, Polynomial.coeff_monomial, not_lt_of_ge hi]

lemma coeff_coeffPolynomial_of_gt (u : ℕ → ℤ) {l i : ℕ} (hi : l < i) :
    (coeffPolynomial u l).coeff i = 0 := by
  classical
  simp [coeffPolynomial, Polynomial.coeff_monomial, hi]

lemma choose_middle_identity_nat {N M l i : ℕ} (hlM : l ≤ M) (hMN : M ≤ N)
    (hi : i ≤ l) :
    (N - i).choose (l - i) * (N - l).choose (M - i) =
      (N - i).choose (M - i) * (N - M).choose (l - i) := by
  let s : ℕ := (M - i) + (l - i)
  have hle_left : l - i ≤ s := by
    dsimp [s]
    omega
  have hle_right : M - i ≤ s := by
    dsimp [s]
    omega
  have hA := Nat.choose_mul (n := N - i) (k := s) (s := l - i) hle_left
  have hB := Nat.choose_mul (n := N - i) (k := s) (s := M - i) hle_right
  have hsymm : s.choose (l - i) = s.choose (M - i) := by
    rw [← Nat.choose_symm hle_left]
    congr 1
    exact Nat.add_sub_cancel (M - i) (l - i)
  rw [hsymm] at hA
  have hlN : l ≤ N := hlM.trans hMN
  have eA1 : N - i - (l - i) = N - l := by omega
  have eA2 : s - (l - i) = M - i := by dsimp [s]; omega
  have hA' : (N - i).choose s * s.choose (M - i) =
      (N - i).choose (l - i) * (N - l).choose (M - i) := by
    simpa [eA1, eA2] using hA
  have eB1 : N - i - (M - i) = N - M := by omega
  have eB2 : s - (M - i) = l - i := by dsimp [s]; omega
  have hB' : (N - i).choose s * s.choose (M - i) =
      (N - i).choose (M - i) * (N - M).choose (l - i) := by
    simpa [eB1, eB2] using hB
  rw [← hA', ← hB']

/-- Correct termwise binomial pairing identity.  The factor `l.choose i` is essential. -/
lemma choose_pairing_identity_nat {N M l i : ℕ} (hlM : l ≤ M) (hMN : M ≤ N)
    (hi : i ≤ l) :
    N.choose l * (l.choose i * (N - l).choose (M - i)) =
      N.choose M * (M.choose i * (N - M).choose (l - i)) := by
  have hiM : i ≤ M := hi.trans hlM
  have h1 := Nat.choose_mul (n := N) (k := l) (s := i) hi
  have h2 := Nat.choose_mul (n := N) (k := M) (s := i) hiM
  calc
    N.choose l * (l.choose i * (N - l).choose (M - i))
        = (N.choose l * l.choose i) * (N - l).choose (M - i) := by ring
    _ = (N.choose i * (N - i).choose (l - i)) * (N - l).choose (M - i) := by rw [h1]
    _ = N.choose i * ((N - i).choose (l - i) * (N - l).choose (M - i)) := by ring
    _ = N.choose i * ((N - i).choose (M - i) * (N - M).choose (l - i)) := by
          rw [choose_middle_identity_nat hlM hMN hi]
    _ = (N.choose i * (N - i).choose (M - i)) * (N - M).choose (l - i) := by ring
    _ = (N.choose M * M.choose i) * (N - M).choose (l - i) := by rw [← h2]
    _ = N.choose M * (M.choose i * (N - M).choose (l - i)) := by ring

lemma choose_pairing_identity_int {N M l i : ℕ} (hlM : l ≤ M) (hMN : M ≤ N)
    (hi : i ≤ l) :
    (N.choose l : ℤ) * ((l.choose i : ℤ) * ((N - l).choose (M - i) : ℤ)) =
      (N.choose M : ℤ) * ((M.choose i : ℤ) * ((N - M).choose (l - i) : ℤ)) := by
  exact_mod_cast choose_pairing_identity_nat (N := N) (M := M) (l := l) (i := i) hlM hMN hi

/-- A corrected finite-sum version.  Compared with the requested expression, the summand on
 the left contains the necessary factor `l.choose i`. -/
lemma choose_pairing_sum_identity_int (u : ℕ → ℤ) {N M l : ℕ} (hlM : l ≤ M)
    (hMN : M ≤ N) :
    (N.choose l : ℤ) *
        (∑ i ∈ Finset.range (l + 1),
          u i * ((l.choose i : ℤ) * ((N - l).choose (M - i) : ℤ))) =
      (N.choose M : ℤ) *
        (∑ i ∈ Finset.range (l + 1),
          u i * ((M.choose i : ℤ) * ((N - M).choose (l - i) : ℤ))) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hil : i ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  calc
    (N.choose l : ℤ) * (u i * ((l.choose i : ℤ) * ((N - l).choose (M - i) : ℤ)))
        = u i * ((N.choose l : ℤ) * ((l.choose i : ℤ) * ((N - l).choose (M - i) : ℤ))) := by ring
    _ = u i * ((N.choose M : ℤ) * ((M.choose i : ℤ) * ((N - M).choose (l - i) : ℤ))) := by
          rw [choose_pairing_identity_int hlM hMN hil]
    _ = (N.choose M : ℤ) * (u i * ((M.choose i : ℤ) * ((N - M).choose (l - i) : ℤ))) := by ring

/-- The raw anti-palindromic binomial difference that appears after pairing the
`i,j` coefficients. -/
def binomialRawDiff (M K i j : ℕ) : ℤ :=
  (M.choose i : ℤ) * (K.choose j : ℤ) - (M.choose j : ℤ) * (K.choose i : ℤ)

/-- If `p^e` divides each of `M`, `K`, and `K-M`, then `p^(3e)` divides their
product.  This is deliberately separated from the factorial clearing argument below. -/
lemma pow_three_mul_dvd_common_of_each {p e M K : ℕ}
    (hM : p ^ e ∣ M) (hK : p ^ e ∣ K) (hKM : p ^ e ∣ K - M) :
    p ^ (3 * e) ∣ M * K * (K - M) := by
  have hprod : (p ^ e * p ^ e) * p ^ e ∣ (M * K) * (K - M) :=
    mul_dvd_mul (mul_dvd_mul hM hK) hKM
  have hpow : (p ^ e * p ^ e) * p ^ e = p ^ (3 * e) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  simpa [hpow, mul_assoc] using hprod

/-- Generic p-adic bookkeeping lemma for clearing an `l!` denominator.

If `p^(3e)` divides an integer `A`, `A = l! * Y`, and the `p`-adic valuation of
`l!` is at most `l-3`, then multiplying `Y` by `p^l` gains enough powers to be
divisible by `p^(3e+3)`. -/
lemma p_pow_clear_factorial_int {p l e : ℕ} {A Y : ℤ}
    (hp : p.Prime) (hl : 3 ≤ l)
    (hA : (p : ℤ) ^ (3 * e) ∣ A)
    (hY : (l.factorial : ℤ) * Y = A)
    (hfac : l.factorial.factorization p ≤ l - 3) :
    (p : ℤ) ^ (3 * e + 3) ∣ (p : ℤ) ^ l * Y := by
  have hA_nat : p ^ (3 * e) ∣ A.natAbs := by
    exact (Int.natCast_dvd.mp (by simpa using hA))
  have hA_abs : A.natAbs = l.factorial * Y.natAbs := by
    rw [← hY, Int.natAbs_mul]
    simp
  have hdiv_prod : p ^ (3 * e) ∣ l.factorial * Y.natAbs := by
    rwa [hA_abs] at hA_nat
  by_cases hY0 : Y.natAbs = 0
  · have hYz : Y = 0 := Int.natAbs_eq_zero.mp hY0
    simp [hYz]
  · have hlfac0 : l.factorial ≠ 0 := Nat.factorial_ne_zero l
    have hprod0 : l.factorial * Y.natAbs ≠ 0 := mul_ne_zero hlfac0 hY0
    have hlower : 3 * e ≤ (l.factorial * Y.natAbs).factorization p :=
      (hp.pow_dvd_iff_le_factorization hprod0).mp hdiv_prod
    have hprod_fac : (l.factorial * Y.natAbs).factorization p =
        l.factorial.factorization p + Y.natAbs.factorization p := by
      rw [Nat.factorization_mul hlfac0 hY0]
      simp
    have hle_without : 3 * e ≤ (l - 3) + Y.natAbs.factorization p := by
      calc
        3 * e ≤ l.factorial.factorization p + Y.natAbs.factorization p := by
          simpa [hprod_fac] using hlower
        _ ≤ (l - 3) + Y.natAbs.factorization p := by
          exact Nat.add_le_add_right hfac _
    have htarget0 : p ^ l * Y.natAbs ≠ 0 :=
      mul_ne_zero (pow_ne_zero l hp.ne_zero) hY0
    have htarget_fac : (p ^ l * Y.natAbs).factorization p =
        l + Y.natAbs.factorization p := by
      rw [Nat.factorization_mul (pow_ne_zero l hp.ne_zero) hY0]
      simp [Nat.Prime.factorization_self hp]
    have hnat : p ^ (3 * e + 3) ∣ p ^ l * Y.natAbs := by
      apply (hp.pow_dvd_iff_le_factorization htarget0).mpr
      rw [htarget_fac]
      omega
    apply (Int.natCast_dvd).mpr
    have htarget_abs : ((p : ℤ) ^ l * Y).natAbs = p ^ l * Y.natAbs := by
      rw [Int.natAbs_mul]
      simp
    simpa [htarget_abs] using hnat

/-- Reusable specialization for the binomial raw difference.  The hypothesis `hmain`
is exactly the output shape of a lemma such as
`main_dvd_of_all_le`: the common factor `M*K*(K-M)` divides the factorial-scaled
raw difference.  The integer `Y` represents division by `l!`, avoiding any
nonintegral expression such as `p^l / l!`. -/
lemma p_pow_clear_factorial_binomialRawDiff {p l e i j M K chooseNM : ℕ} {Y : ℤ}
    (hp : p.Prime) (_hp5 : 5 ≤ p) (hl : 3 ≤ l)
    (_hij : i + j = l) (_hi : 1 ≤ i) (_hj : 1 ≤ j)
    (hM : p ^ e ∣ M) (hK : p ^ e ∣ K) (hKM : p ^ e ∣ K - M)
    (hmain : ((M * K * (K - M) : ℕ) : ℤ) ∣
      ((i.factorial * j.factorial : ℕ) : ℤ) * binomialRawDiff M K i j)
    (hY : (l.factorial : ℤ) * Y =
      (chooseNM : ℤ) * (((i.factorial * j.factorial : ℕ) : ℤ) * binomialRawDiff M K i j))
    (hfac : l.factorial.factorization p ≤ l - 3) :
    (p : ℤ) ^ (3 * e + 3) ∣ (p : ℤ) ^ l * Y := by
  have hcommon_nat : p ^ (3 * e) ∣ M * K * (K - M) :=
    pow_three_mul_dvd_common_of_each hM hK hKM
  have hcommon_int : (p : ℤ) ^ (3 * e) ∣ ((M * K * (K - M) : ℕ) : ℤ) := by
    exact_mod_cast hcommon_nat
  have hdiff : (p : ℤ) ^ (3 * e) ∣
      ((i.factorial * j.factorial : ℕ) : ℤ) * binomialRawDiff M K i j :=
    hcommon_int.trans hmain
  have hA : (p : ℤ) ^ (3 * e) ∣
      (chooseNM : ℤ) * (((i.factorial * j.factorial : ℕ) : ℤ) * binomialRawDiff M K i j) := by
    exact dvd_mul_of_dvd_right hdiff (chooseNM : ℤ)
  exact p_pow_clear_factorial_int (p := p) (l := l) (e := e)
    (A := (chooseNM : ℤ) * (((i.factorial * j.factorial : ℕ) : ℤ) * binomialRawDiff M K i j))
    (Y := Y) hp hl hA hY hfac

/- copied MainDvdTemp.lean -/

open scoped BigOperators
open Polynomial

namespace MainDvdTemp

noncomputable def tailPoly (r : ℕ) : ℤ[X] :=
  ∏ k ∈ Finset.range (r - 1), (Polynomial.X - Polynomial.C ((k + 1 : ℕ) : ℤ))

lemma tailPoly_eval (r : ℕ) (x : ℤ) :
    (tailPoly r).eval x = ∏ k ∈ Finset.range (r - 1), (x - ((k + 1 : ℕ) : ℤ)) := by
  rw [tailPoly, Polynomial.eval_prod]
  refine Finset.prod_congr rfl ?_
  intro k hk
  simp [Nat.cast_add]

lemma sub_dvd_tailPoly_eval_sub (r : ℕ) (x y : ℤ) :
    x - y ∣ (tailPoly r).eval x - (tailPoly r).eval y := by
  exact Polynomial.sub_dvd_eval_sub x y (tailPoly r)

lemma sub_dvd_tailProd_sub (r : ℕ) (x y : ℤ) :
    x - y ∣
      (∏ k ∈ Finset.range (r - 1), (x - ((k + 1 : ℕ) : ℤ))) -
        (∏ k ∈ Finset.range (r - 1), (y - ((k + 1 : ℕ) : ℤ))) := by
  simpa [tailPoly_eval] using sub_dvd_tailPoly_eval_sub r x y

lemma descFactorial_cast_eq_mul_tailPoly_eval {n r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) :
    (n.descFactorial r : ℤ) = (n : ℤ) * (tailPoly r).eval (n : ℤ) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  rw [Nat.descFactorial_eq_prod_range]
  rw [Finset.prod_range_succ']
  have hprod :
      (((∏ k ∈ Finset.range a, (n - (k + 1) : ℕ)) : ℕ) : ℤ) =
        ∏ k ∈ Finset.range a, ((n : ℤ) - ((k + 1 : ℕ) : ℤ)) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl ?_
    intro k hk
    have hklt : k + 1 ≤ a + 1 := Nat.succ_le_succ (Finset.mem_range.mp hk).le
    have hle : k + 1 ≤ n := hklt.trans hrn
    simpa [Nat.cast_add] using (Nat.cast_sub hle : ((n - (k + 1) : ℕ) : ℤ) = (n : ℤ) - ((k + 1 : ℕ) : ℤ))
  have h0 : ((n - 0 : ℕ) : ℤ) = (n : ℤ) := by simp
  calc
    (((∏ k ∈ Finset.range a, (n - (k + 1))) * (n - 0) : ℕ) : ℤ) =
        (∏ k ∈ Finset.range a, ((n : ℤ) - ((k + 1 : ℕ) : ℤ))) * (n : ℤ) := by
      rw [Nat.cast_mul, hprod, h0]
    _ = (n : ℤ) * (tailPoly (a + 1)).eval (n : ℤ) := by
      rw [tailPoly_eval]
      simp [mul_comm]

lemma descFactorial_skew_dvd {M K i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hiM : i ≤ M) (hiK : i ≤ K) (hjM : j ≤ M) (hjK : j ≤ K) :
    (M : ℤ) * (K : ℤ) * ((K : ℤ) - (M : ℤ)) ∣
      ((M.descFactorial i : ℤ) * (K.descFactorial j : ℤ) -
        (M.descFactorial j : ℤ) * (K.descFactorial i : ℤ)) := by
  let Ti : ℤ := (tailPoly i).eval (M : ℤ)
  let Ui : ℤ := (tailPoly i).eval (K : ℤ)
  let Tj : ℤ := (tailPoly j).eval (M : ℤ)
  let Uj : ℤ := (tailPoly j).eval (K : ℤ)
  have hMi : (M.descFactorial i : ℤ) = (M : ℤ) * Ti := by
    simpa [Ti] using descFactorial_cast_eq_mul_tailPoly_eval (n := M) (r := i) hi hiM
  have hKi : (K.descFactorial i : ℤ) = (K : ℤ) * Ui := by
    simpa [Ui] using descFactorial_cast_eq_mul_tailPoly_eval (n := K) (r := i) hi hiK
  have hMj : (M.descFactorial j : ℤ) = (M : ℤ) * Tj := by
    simpa [Tj] using descFactorial_cast_eq_mul_tailPoly_eval (n := M) (r := j) hj hjM
  have hKj : (K.descFactorial j : ℤ) = (K : ℤ) * Uj := by
    simpa [Uj] using descFactorial_cast_eq_mul_tailPoly_eval (n := K) (r := j) hj hjK
  have hdj : (K : ℤ) - (M : ℤ) ∣ Uj - Tj := by
    simpa [Uj, Tj] using sub_dvd_tailPoly_eval_sub j (K : ℤ) (M : ℤ)
  have hdi : (K : ℤ) - (M : ℤ) ∣ Ui - Ti := by
    simpa [Ui, Ti] using sub_dvd_tailPoly_eval_sub i (K : ℤ) (M : ℤ)
  have hbracket : (K : ℤ) - (M : ℤ) ∣ Ti * Uj - Tj * Ui := by
    have h1 : (K : ℤ) - (M : ℤ) ∣ Ti * (Uj - Tj) := dvd_mul_of_dvd_right hdj Ti
    have h2 : (K : ℤ) - (M : ℤ) ∣ Tj * (Ui - Ti) := dvd_mul_of_dvd_right hdi Tj
    have hsub := dvd_sub h1 h2
    convert hsub using 1 <;> ring
  obtain ⟨q, hq⟩ := hbracket
  refine ⟨q, ?_⟩
  rw [hMi, hKi, hMj, hKj]
  calc
    (M : ℤ) * Ti * ((K : ℤ) * Uj) - (M : ℤ) * Tj * ((K : ℤ) * Ui) =
        (M : ℤ) * (K : ℤ) * (Ti * Uj - Tj * Ui) := by ring
    _ = (M : ℤ) * (K : ℤ) * (((K : ℤ) - (M : ℤ)) * q) := by rw [hq]
    _ = (M : ℤ) * (K : ℤ) * ((K : ℤ) - (M : ℤ)) * q := by ring

lemma factorial_choose_prod_eq_descFactorial_prod (M K i j : ℕ) :
    ((i.factorial * j.factorial : ℤ) *
        (((Nat.choose M i * Nat.choose K j : ℕ) : ℤ) -
          ((Nat.choose M j * Nat.choose K i : ℕ) : ℤ))) =
      ((M.descFactorial i : ℤ) * (K.descFactorial j : ℤ) -
        (M.descFactorial j : ℤ) * (K.descFactorial i : ℤ)) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose M i]
  rw [Nat.descFactorial_eq_factorial_mul_choose K j]
  rw [Nat.descFactorial_eq_factorial_mul_choose M j]
  rw [Nat.descFactorial_eq_factorial_mul_choose K i]
  norm_num [Nat.cast_mul]
  ring

lemma main_dvd_of_all_le {M K i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hiM : i ≤ M) (hiK : i ≤ K) (hjM : j ≤ M) (hjK : j ≤ K) :
    (M : ℤ) * (K : ℤ) * ((K : ℤ) - (M : ℤ)) ∣
      ((i.factorial * j.factorial : ℤ) *
        (((Nat.choose M i * Nat.choose K j : ℕ) : ℤ) -
          ((Nat.choose M j * Nat.choose K i : ℕ) : ℤ))) := by
  rw [factorial_choose_prod_eq_descFactorial_prod]
  exact descFactorial_skew_dvd hi hj hiM hiK hjM hjK

end MainDvdTemp

namespace PairPadicTemp

lemma factorial_factorization_le_sub_three_of_five_le {p l : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hl : 3 ≤ l) :
    l.factorial.factorization p ≤ l - 3 := by
  have hpred : 4 ≤ p - 1 := by omega
  have hfac_le : l.factorial.factorization p ≤ l / (p - 1) :=
    Nat.factorization_factorial_le_div_pred hp l
  have hdiv_le : l / (p - 1) ≤ l / 4 := Nat.div_le_div_left hpred (by omega)
  have hdiv4 : l / 4 ≤ l - 3 := by omega
  exact hfac_le.trans (hdiv_le.trans hdiv4)

lemma main_dvd_binomialRawDiff_of_all_le {M K i j : ℕ}
    (hKMle : M ≤ K) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hiM : i ≤ M) (hiK : i ≤ K) (hjM : j ≤ M) (hjK : j ≤ K) :
    ((M * K * (K - M) : ℕ) : ℤ) ∣
      ((i.factorial * j.factorial : ℕ) : ℤ) * binomialRawDiff M K i j := by
  have hmain := MainDvdTemp.main_dvd_of_all_le (M := M) (K := K) (i := i) (j := j)
    hi hj hiM hiK hjM hjK
  simpa [binomialRawDiff, Nat.cast_mul, Nat.cast_sub hKMle] using hmain

/-- Pair-level p-adic divisibility for `Ypair`, in the case where the paired binomial
indices are positive and bounded by both `M` and `K`.  Here `j = l - i` and `N = M + K`. -/
theorem pair_padic_dvd_Ypair_of_common_dvd {p l e i M K N : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hl : 3 ≤ l)
    (hij_lt : i < l - i) (hN : N = M + K) (hKMle : M ≤ K)
    (hi_pos : 1 ≤ i) (hjM : l - i ≤ M)
    (hM : p ^ e ∣ M) (hK : p ^ e ∣ K) (hKM : p ^ e ∣ K - M) :
    (p : ℤ) ^ (3 * e + 3) ∣ (p : ℤ) ^ l * BetaYpairTemp.Ypair N M l i := by
  let j : ℕ := l - i
  have hMN : M ≤ N := by omega
  have hil : i ≤ l := by omega
  have hij_eq : j = l - i := rfl
  have hij_sum : i + j = l := by dsimp [j]; omega
  have hj_pos : 1 ≤ j := by dsimp [j]; omega
  have hiM : i ≤ M := (le_of_lt hij_lt).trans hjM
  have hiK : i ≤ K := hiM.trans hKMle
  have hjK : j ≤ K := by
    change l - i ≤ K
    exact hjM.trans hKMle
  have hmain : ((M * K * (K - M) : ℕ) : ℤ) ∣
      ((i.factorial * j.factorial : ℕ) : ℤ) * binomialRawDiff M K i j :=
    main_dvd_binomialRawDiff_of_all_le (M := M) (K := K) (i := i) (j := j)
      hKMle hi_pos hj_pos hiM hiK hjM hjK
  have hfac := factorial_factorization_le_sub_three_of_five_le (p := p) (l := l) hp hp5 hl
  have hY : (l.factorial : ℤ) * BetaYpairTemp.Ypair N M l i =
      (N.choose M : ℤ) * (((i.factorial * j.factorial : ℕ) : ℤ) * binomialRawDiff M K i j) := by
    have hbeta := BetaYpairTemp.beta_Ypair_identity (N := N) (M := M) (l := l) (i := i) (j := j)
      hMN hil hij_eq
    have hNK : N - M = K := by omega
    rw [hbeta]
    congr 2
    rw [hNK]
    simp [BetaYpairTemp.rawdiff, binomialRawDiff]
  exact p_pow_clear_factorial_binomialRawDiff (p := p) (l := l) (e := e)
    (i := i) (j := j) (M := M) (K := K) (chooseNM := N.choose M)
    (Y := BetaYpairTemp.Ypair N M l i)
    hp hp5 hl hij_sum hi_pos hj_pos hM hK hKM hmain hY hfac


/-- Same pair-level p-adic divisibility theorem with an explicit paired index `j` and
hypothesis `j = l - i`. -/
theorem pair_padic_dvd_Ypair_of_common_dvd_j {p l e i j M K N : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hl : 3 ≤ l)
    (hij : j = l - i) (hij_lt : i < j) (hN : N = M + K) (hKMle : M ≤ K)
    (hi_pos : 1 ≤ i) (hjM : j ≤ M)
    (hM : p ^ e ∣ M) (hK : p ^ e ∣ K) (hKM : p ^ e ∣ K - M) :
    (p : ℤ) ^ (3 * e + 3) ∣ (p : ℤ) ^ l * BetaYpairTemp.Ypair N M l i := by
  subst j
  exact pair_padic_dvd_Ypair_of_common_dvd (p := p) (l := l) (e := e)
    (i := i) (M := M) (K := K) (N := N)
    hp hp5 hl hij_lt hN hKMle hi_pos hjM hM hK hKM

end PairPadicTemp

/- Coefficient-sum p-adic divisibility after anti-palindromic pairing. -/

open scoped BigOperators
open Nat

namespace CoeffPairPadicTemp

/-- For `T ≥ 2`, the anti-palindromically paired coefficient sum has the same
p-adic divisibility as each paired summand.  The extra hypothesis `l ≤ M` is a
convenient boundedness assumption ensuring every paired index `j = l - i` in the
left half is at most `M`, as required by `PairPadicTemp.pair_padic_dvd_Ypair_of_common_dvd`. -/
theorem coeff_sum_anti_pal_padic_dvd_of_two_le_T
    {p l e M T : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hl : 3 ≤ l)
    (hlM : l ≤ M) (hT : 2 ≤ T) (hM : p ^ e ∣ M)
    (u : ℕ → ℤ)
    (hsupp : ∀ i, l < i → u i = 0) (h0 : u 0 = 0) (hul : u l = 0)
    (hanti : ∀ i, i ≤ l → u (l - i) = - u i) :
    (p : ℤ) ^ (3 * e + 3) ∣ (p : ℤ) ^ l *
      (∑ a ∈ Finset.range (l + 1),
        u a * (((M * T).choose l : ℤ) * BetaYpairTemp.beta (M * T) l M a)) := by
  classical
  let d : ℤ := (p : ℤ) ^ (3 * e + 3)
  let I : Finset ℕ := (Finset.range (l + 1)).filter (fun i => i < l - i)
  let K : ℕ := M * (T - 1)
  let N : ℕ := M * T
  have hN : N = M + K := by
    dsimp [N, K]
    have hTs : T = (T - 1) + 1 := by omega
    nth_rewrite 1 [hTs]
    ring
  have hKMle : M ≤ K := by
    dsimp [K]
    exact Nat.le_mul_of_pos_right M (by omega : 0 < T - 1)
  have hK : p ^ e ∣ K := by
    dsimp [K]
    exact dvd_mul_of_dvd_left hM (T - 1)
  have hKM : p ^ e ∣ K - M := by
    dsimp [K]
    have hsub : M * (T - 1) - M = M * (T - 2) := by
      have hTs : T - 1 = (T - 2) + 1 := by omega
      nth_rewrite 1 [hTs]
      rw [Nat.mul_succ, Nat.add_sub_cancel_right]
    rw [hsub]
    exact dvd_mul_of_dvd_left hM (T - 2)
  have hdecomp :
      (∑ a ∈ Finset.range (l + 1),
        u a * (((M * T).choose l : ℤ) * BetaYpairTemp.beta (M * T) l M a)) =
        ∑ i ∈ I, u i * BetaYpairTemp.Ypair (M * T) M l i := by
    simpa [I, N] using
      (BetaYpairTemp.coefficient_sum_paired_decomposition_bounded
        (u := u) (N := M * T) (M := M) (l := l) hsupp h0 hul hanti)
  rw [hdecomp]
  rw [Finset.mul_sum]
  refine Finset.dvd_sum ?_
  intro i hi
  rw [Finset.mem_filter] at hi
  rcases hi with ⟨hi_range, hij_lt⟩
  have hil : i ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hi_range)
  by_cases hi0 : i = 0
  · subst i
    simp [h0]
  · have hi_pos : 1 ≤ i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hi0)
    have hjM : l - i ≤ M := (Nat.sub_le l i).trans hlM
    have hpair : d ∣ (p : ℤ) ^ l * BetaYpairTemp.Ypair (M * T) M l i := by
      simpa [d, N, K] using
        (PairPadicTemp.pair_padic_dvd_Ypair_of_common_dvd
          (p := p) (l := l) (e := e) (i := i) (M := M) (K := K) (N := N)
          hp hp5 hl hij_lt hN hKMle hi_pos hjM hM hK hKM)
    have hmul : d ∣ u i * ((p : ℤ) ^ l * BetaYpairTemp.Ypair (M * T) M l i) :=
      dvd_mul_of_dvd_right hpair (u i)
    convert hmul using 1 <;> ring


lemma three_mul_add_three_le_pow_add_one_of_five_le {p e : ℕ}
    (hp5 : 5 ≤ p) (he : 0 < e) : 3 * e + 3 ≤ p ^ e + 1 := by
  have hlin_succ : ∀ n : ℕ, 3 * (n + 1) + 3 ≤ 5 ^ (n + 1) + 1 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        have hpos : 1 ≤ 5 ^ (n + 1) := Nat.one_le_pow (n + 1) 5 (by norm_num)
        calc
          3 * (Nat.succ n + 1) + 3 = (3 * (n + 1) + 3) + 3 := by omega
          _ ≤ (5 ^ (n + 1) + 1) + 3 := Nat.add_le_add_right ih 3
          _ ≤ 5 ^ (Nat.succ n + 1) + 1 := by
            rw [show Nat.succ n + 1 = (n + 1) + 1 by omega, pow_succ]
            change 5 ^ (n + 1) + 1 + 3 ≤ 5 ^ (n + 1) * 5 + 1
            nlinarith [hpos]
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he) with ⟨n, rfl⟩
  have h5pow : 5 ^ (n + 1) ≤ p ^ (n + 1) := Nat.pow_le_pow_left hp5 (n + 1)
  exact (hlin_succ n).trans (Nat.add_le_add_right h5pow 1)

lemma pow_add_one_le_of_dvd_pos_lt {p e M l : ℕ}
    (hMpos : 0 < M) (hM : p ^ e ∣ M) (hMl : M < l) : p ^ e + 1 ≤ l := by
  have hpowleM : p ^ e ≤ M := Nat.le_of_dvd hMpos hM
  omega

/-- Version of `coeff_sum_anti_pal_padic_dvd_of_two_le_T` without the boundedness
hypothesis `l ≤ M`.  In the complementary case `M < l`, positivity of `M` plus
`p ^ e ∣ M` forces the target exponent to be at most `l`, so the leading factor
`(p : ℤ) ^ l` alone supplies the required divisibility. -/
theorem coeff_sum_anti_pal_padic_dvd_of_two_le_T_all_l
    {p l e M T : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hl : 3 ≤ l)
    (hT : 2 ≤ T) (hMpos : 0 < M) (hM : p ^ e ∣ M)
    (u : ℕ → ℤ)
    (hsupp : ∀ i, l < i → u i = 0) (h0 : u 0 = 0) (hul : u l = 0)
    (hanti : ∀ i, i ≤ l → u (l - i) = - u i) :
    (p : ℤ) ^ (3 * e + 3) ∣ (p : ℤ) ^ l *
      (∑ a ∈ Finset.range (l + 1),
        u a * (((M * T).choose l : ℤ) * BetaYpairTemp.beta (M * T) l M a)) := by
  by_cases hlM : l ≤ M
  · exact coeff_sum_anti_pal_padic_dvd_of_two_le_T
      (p := p) (l := l) (e := e) (M := M) (T := T)
      hp hp5 hl hlM hT hM u hsupp h0 hul hanti
  · have hMl : M < l := by omega
    have htarget_le_l : 3 * e + 3 ≤ l := by
      by_cases he0 : e = 0
      · subst e
        omega
      · have hepos : 0 < e := Nat.pos_of_ne_zero he0
        have hpow1le : p ^ e + 1 ≤ l :=
          pow_add_one_le_of_dvd_pos_lt (p := p) (e := e) (M := M) (l := l) hMpos hM hMl
        have hbound : 3 * e + 3 ≤ p ^ e + 1 :=
          three_mul_add_three_le_pow_add_one_of_five_le (p := p) (e := e) hp5 hepos
        exact hbound.trans hpow1le
    have hdvd_pow : (p : ℤ) ^ (3 * e + 3) ∣ (p : ℤ) ^ l :=
      pow_dvd_pow (p : ℤ) htarget_le_l
    exact dvd_mul_of_dvd_left hdvd_pow _

/-- The `T ≥ 3` form requested in the prompt, as an immediate corollary of the
slightly stronger `T ≥ 2` theorem above. -/
theorem coeff_sum_anti_pal_padic_dvd_of_three_le_T
    {p l e M T : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hl : 3 ≤ l)
    (hlM : l ≤ M) (hT : 3 ≤ T) (hM : p ^ e ∣ M)
    (u : ℕ → ℤ)
    (hsupp : ∀ i, l < i → u i = 0) (h0 : u 0 = 0) (hul : u l = 0)
    (hanti : ∀ i, i ≤ l → u (l - i) = - u i) :
    (p : ℤ) ^ (3 * e + 3) ∣ (p : ℤ) ^ l *
      (∑ a ∈ Finset.range (l + 1),
        u a * (((M * T).choose l : ℤ) * BetaYpairTemp.beta (M * T) l M a)) := by
  exact coeff_sum_anti_pal_padic_dvd_of_two_le_T
    (p := p) (l := l) (e := e) (M := M) (T := T)
    hp hp5 hl hlM (by omega) hM u hsupp h0 hul hanti

end CoeffPairPadicTemp

open scoped BigOperators
open Polynomial

namespace PolyCoeffPairTemp

/-- Sampling every `p`-th coefficient of an anti-palindromic polynomial gives an
anti-palindromic coefficient sequence on `0, ..., l`. -/
lemma sampled_coeff_anti_pal
    {p l : ℕ} {P : ℤ[X]}
    (hantiP : P.reflect (p * l) = -P) :
    ∀ a, a ≤ l → P.coeff (p * (l - a)) = -P.coeff (p * a) := by
  intro a ha
  have hpa : p * a ≤ p * l := Nat.mul_le_mul_left p ha
  have hcoeff : (P.reflect (p * l)).coeff (p * a) = (-P).coeff (p * a) := by
    simpa using congrArg (fun Q : ℤ[X] => Q.coeff (p * a)) hantiP
  rw [Polynomial.coeff_reflect, Polynomial.revAt_le hpa] at hcoeff
  have hsub : p * l - p * a = p * (l - a) := by
    rw [← Nat.mul_sub_left_distrib]
  simpa [hsub] using hcoeff

/-- The constant sampled coefficient is zero when the polynomial has zero
constant coefficient. -/
lemma sampled_coeff_zero {p : ℕ} {P : ℤ[X]} (h0 : P.coeff 0 = 0) :
    P.coeff (p * 0) = 0 := by
  simpa using h0

/-- The last sampled coefficient is zero for an anti-palindromic polynomial with
zero constant coefficient. -/
lemma sampled_coeff_last_zero
    {p l : ℕ} {P : ℤ[X]}
    (hantiP : P.reflect (p * l) = -P) (h0 : P.coeff 0 = 0) :
    P.coeff (p * l) = 0 := by
  have hcoeff : (P.reflect (p * l)).coeff 0 = (-P).coeff 0 := by
    simpa using congrArg (fun Q : ℤ[X] => Q.coeff 0) hantiP
  rw [Polynomial.coeff_reflect, Polynomial.revAt_zero] at hcoeff
  simpa [h0] using hcoeff

/-- The sampled coefficient sequence is supported in `0, ..., l`, provided the
polynomial has degree at most `p*l` and `p` is positive. -/
lemma sampled_coeff_support
    {p l : ℕ} {P : ℤ[X]} (hp0 : 0 < p) (hdeg : P.natDegree ≤ p * l) :
    ∀ a, l < a → P.coeff (p * a) = 0 := by
  intro a ha
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
  have hlt : p * l < p * a := Nat.mul_lt_mul_of_pos_left ha hp0
  exact hdeg.trans_lt hlt

/-- Bundle of the endpoint, support, and anti-palindromicity facts for the
sampled sequence `a ↦ P.coeff (p*a)`. -/
theorem sampled_coeffs_anti_pal_endpoints_support
    {p l : ℕ} {P : ℤ[X]} (hp0 : 0 < p)
    (hantiP : P.reflect (p * l) = -P) (hdeg : P.natDegree ≤ p * l)
    (h0 : P.coeff 0 = 0) :
    (P.coeff (p * 0) = 0) ∧
    (P.coeff (p * l) = 0) ∧
    (∀ a, l < a → P.coeff (p * a) = 0) ∧
    (∀ a, a ≤ l → P.coeff (p * (l - a)) = -P.coeff (p * a)) := by
  exact ⟨sampled_coeff_zero h0,
    sampled_coeff_last_zero hantiP h0,
    sampled_coeff_support hp0 hdeg,
    sampled_coeff_anti_pal hantiP⟩

/-- Applying the coefficient-pair padic divisibility theorem to coefficients
sampled every `p` from an anti-palindromic polynomial. -/
theorem sampled_coeff_sum_padic_dvd
    {p l e M T : ℕ} (P : ℤ[X]) (hp : p.Prime) (hp5 : 5 ≤ p) (hl : 3 ≤ l)
    (hT : 2 ≤ T) (hMpos : 0 < M) (hM : p ^ e ∣ M)
    (hantiP : P.reflect (p * l) = -P) (hdeg : P.natDegree ≤ p * l)
    (h0 : P.coeff 0 = 0) :
    (p : ℤ) ^ (3 * e + 3) ∣ (p : ℤ) ^ l *
      (∑ a ∈ Finset.range (l + 1),
        P.coeff (p * a) * (((M * T).choose l : ℤ) * BetaYpairTemp.beta (M * T) l M a)) := by
  have hp0 : 0 < p := hp.pos
  rcases sampled_coeffs_anti_pal_endpoints_support
      (p := p) (l := l) (P := P) hp0 hantiP hdeg h0 with
    ⟨hu0, hul, hsupp, hanti⟩
  exact CoeffPairPadicTemp.coeff_sum_anti_pal_padic_dvd_of_two_le_T_all_l
    (p := p) (l := l) (e := e) (M := M) (T := T)
    hp hp5 hl hT hMpos hM (fun a => P.coeff (p * a)) hsupp hu0 hul hanti

end PolyCoeffPairTemp

open Polynomial
open scoped Polynomial BigOperators

namespace ScaledQuotientTemp

noncomputable def D : ℤ[X] := 1 + X + X^2
noncomputable def A : ℤ[X] := 1 - X^2
noncomputable def Rnum (p : ℕ) : ℤ[X] := (1 + X)^p - 1 - X^p

lemma D_dvd_X3_sub_one : D ∣ (X^3 - 1 : ℤ[X]) := by
  use X - 1
  dsimp [D]
  ring

lemma one_add_X_congr : D ∣ ((1 + X : ℤ[X]) - (-X^2)) := by
  use 1
  dsimp [D]
  ring

lemma D_dvd_pow_congr (p : ℕ) : D ∣ ((1+X : ℤ[X])^p - (-X^2)^p) := by
  exact (one_add_X_congr).trans ((Commute.all (1+X : ℤ[X]) (-X^2)).sub_dvd_pow_sub_pow p)

lemma D_dvd_X_pow_sub_X_of_mod_eq_one {n : ℕ} (hn : n % 3 = 1) :
    D ∣ ((X : ℤ[X])^n - X) := by
  have h : ∃ q, n = 3*q + 1 := by
    use n / 3
    omega
  rcases h with ⟨q, rfl⟩
  have hbase : D ∣ ((X^3 : ℤ[X]) - 1) := D_dvd_X3_sub_one
  have hpow : (X^3 : ℤ[X]) - 1 ∣ (X^3)^q - 1 := sub_one_dvd_pow_sub_one (X^3 : ℤ[X]) q
  have hdvd : D ∣ (X^3 : ℤ[X])^q - 1 := hbase.trans hpow
  have hmul : D ∣ (X : ℤ[X]) * ((X^3)^q - 1) := dvd_mul_of_dvd_right hdvd X
  convert hmul using 1
  ring

lemma D_dvd_X_pow_sub_X2_of_mod_eq_two {n : ℕ} (hn : n % 3 = 2) :
    D ∣ ((X : ℤ[X])^n - X^2) := by
  have h : ∃ q, n = 3*q + 2 := by
    use n / 3
    omega
  rcases h with ⟨q, rfl⟩
  have hbase : D ∣ ((X^3 : ℤ[X]) - 1) := D_dvd_X3_sub_one
  have hpow : (X^3 : ℤ[X]) - 1 ∣ (X^3)^q - 1 := sub_one_dvd_pow_sub_one (X^3 : ℤ[X]) q
  have hdvd : D ∣ (X^3 : ℤ[X])^q - 1 := hbase.trans hpow
  have hmul : D ∣ (X^2 : ℤ[X]) * ((X^3)^q - 1) := dvd_mul_of_dvd_right hdvd (X^2 : ℤ[X])
  convert hmul using 1
  ring

lemma D_dvd_numerator_of_mod_one {p : ℕ} (hpodd : Odd p) (hpmod : p % 3 = 1) :
    D ∣ Rnum p := by
  have hmain := D_dvd_pow_congr p
  have hsign : (-X^2 : ℤ[X])^p = - X^(2*p) := by
    rw [neg_pow]
    simp [hpodd.neg_one_pow, pow_mul]
  have hp2mod : (2*p) % 3 = 2 := by omega
  have hxp := D_dvd_X_pow_sub_X_of_mod_eq_one (n:=p) hpmod
  have hx2p := D_dvd_X_pow_sub_X2_of_mod_eq_two (n:=2*p) hp2mod
  have htarget : D ∣ ((- X^(2*p) - 1 - X^p) - (-(X^2) - 1 - X)) := by
    convert dvd_add (dvd_neg.mpr hx2p) (dvd_neg.mpr hxp) using 1 <;> ring
  have hbase : D ∣ (-(X^2 : ℤ[X]) - 1 - X) := by
    use -1
    dsimp [D]
    ring
  have h2 : D ∣ (- X^(2*p) - 1 - X^p : ℤ[X]) := by
    have := dvd_add htarget hbase
    convert this using 1 <;> ring
  have h1 : D ∣ ((1+X : ℤ[X])^p - (-X^2)^p) := hmain
  have hsum := dvd_add h1 h2
  rw [hsign] at hsum
  convert hsum using 1 <;> simp [Rnum] <;> ring

lemma D_dvd_numerator_of_mod_two {p : ℕ} (hpodd : Odd p) (hpmod : p % 3 = 2) :
    D ∣ Rnum p := by
  have hmain := D_dvd_pow_congr p
  have hsign : (-X^2 : ℤ[X])^p = - X^(2*p) := by
    rw [neg_pow]
    simp [hpodd.neg_one_pow, pow_mul]
  have hp2mod : (2*p) % 3 = 1 := by omega
  have hxp := D_dvd_X_pow_sub_X2_of_mod_eq_two (n:=p) hpmod
  have hx2p := D_dvd_X_pow_sub_X_of_mod_eq_one (n:=2*p) hp2mod
  have htarget : D ∣ ((- X^(2*p) - 1 - X^p) - (-X - 1 - X^2)) := by
    convert dvd_add (dvd_neg.mpr hx2p) (dvd_neg.mpr hxp) using 1 <;> ring
  have hbase : D ∣ (-X - 1 - X^2 : ℤ[X]) := by
    use -1
    dsimp [D]
    ring
  have h2 : D ∣ (- X^(2*p) - 1 - X^p : ℤ[X]) := by
    have := dvd_add htarget hbase
    convert this using 1 <;> ring
  have h1 : D ∣ ((1+X : ℤ[X])^p - (-X^2)^p) := hmain
  have hsum := dvd_add h1 h2
  rw [hsign] at hsum
  convert hsum using 1 <;> simp [Rnum] <;> ring

lemma D_dvd_Rnum_of_prime_ge_five {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    D ∣ Rnum p := by
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hpne3 : p % 3 ≠ 0 := by
    intro h0
    have h3dvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    have hpeq3 : p = 3 := (hp.dvd_iff_eq (by norm_num : 3 ≠ 1)).mp h3dvd
    omega
  have hmodlt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
  interval_cases h : p % 3
  · contradiction
  · exact D_dvd_numerator_of_mod_one hpodd h
  · exact D_dvd_numerator_of_mod_two hpodd h


lemma coeff_D_mul_zero (T : ℤ[X]) : (D * T).coeff 0 = T.coeff 0 := by
  simp [D]

lemma test_coeff_D_mul (T : ℤ[X]) (n : ℕ) :
    (D * T).coeff n = T.coeff n + (X*T).coeff n + (X^2*T).coeff n := by
  simp [D, add_mul]


lemma coeff_X_sq_mul_one (T : ℤ[X]) : (X^2 * T).coeff 1 = 0 := by
  rw [coeff_X_pow_mul']
  norm_num

lemma coeff_D_mul_one (T : ℤ[X]) : (D * T).coeff 1 = T.coeff 1 + T.coeff 0 := by
  simp [D, add_mul, coeff_X_sq_mul_one]

lemma coeff_X_sq_mul_add_two (T : ℤ[X]) (n : ℕ) :
    (X^2 * T).coeff (n + 2) = T.coeff n := by
  simpa using (coeff_X_pow_mul (p := T) (n := 2) (d := n))

lemma coeff_D_mul_add_two (T : ℤ[X]) (n : ℕ) :
    (D * T).coeff (n + 2) = T.coeff (n + 2) + T.coeff (n + 1) + T.coeff n := by
  simp [D, add_mul, coeff_X_sq_mul_add_two]

lemma prime_dvd_coeff_Rnum {p n : ℕ} (hp : p.Prime) :
    (p : ℤ) ∣ (Rnum p).coeff n := by
  by_cases hn0 : n = 0
  · subst n
    have h0p : (0 : ℕ) ≠ p := Ne.symm hp.ne_zero
    simp [Rnum, coeff_one_add_X_pow, coeff_one, coeff_X_pow, h0p]
  · by_cases hnp : n = p
    · subst n
      simp [Rnum, coeff_one_add_X_pow, coeff_one, coeff_X_pow, hn0]
    · by_cases hlt : n < p
      · have hpdvd_nat : p ∣ p.choose n := hp.dvd_choose_self hn0 hlt
        have hpdvd_int : (p : ℤ) ∣ (p.choose n : ℤ) := by exact_mod_cast hpdvd_nat
        simpa [Rnum, coeff_one_add_X_pow, coeff_one, coeff_X_pow, hn0, hnp] using hpdvd_int
      · have hp_lt_n : p < n := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hnp)
        simp [Rnum, coeff_one_add_X_pow, coeff_one, coeff_X_pow, Nat.choose_eq_zero_of_lt hp_lt_n, hn0, hnp]

lemma prime_dvd_coeff_of_Rnum_eq_D_mul {p : ℕ} (hp : p.Prime) {T : ℤ[X]}
    (hT : Rnum p = D * T) : ∀ n : ℕ, (p : ℤ) ∣ T.coeff n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hR : (p : ℤ) ∣ (D * T).coeff n := by
        simpa [hT] using (prime_dvd_coeff_Rnum (p := p) (n := n) hp)
      cases n with
      | zero =>
          rw [coeff_D_mul_zero] at hR
          exact hR
      | succ n =>
          cases n with
          | zero =>
              have h0 : (p : ℤ) ∣ T.coeff 0 := ih 0 (by omega)
              have hsum : (p : ℤ) ∣ T.coeff 1 + T.coeff 0 := by
                simpa [coeff_D_mul_one] using hR
              have hsub : (p : ℤ) ∣ (T.coeff 1 + T.coeff 0) - T.coeff 0 := dvd_sub hsum h0
              simpa using hsub
          | succ n =>
              have hn1 : (p : ℤ) ∣ T.coeff (n + 1) := ih (n + 1) (by omega)
              have hn0 : (p : ℤ) ∣ T.coeff n := ih n (by omega)
              have hprev : (p : ℤ) ∣ T.coeff (n + 1) + T.coeff n := dvd_add hn1 hn0
              have hsum : (p : ℤ) ∣ T.coeff (n + 2) + T.coeff (n + 1) + T.coeff n := by
                simpa [coeff_D_mul_add_two] using hR
              have hsub : (p : ℤ) ∣
                  (T.coeff (n + 2) + T.coeff (n + 1) + T.coeff n) -
                    (T.coeff (n + 1) + T.coeff n) := dvd_sub hsum hprev
              simpa [add_assoc, add_comm, add_left_comm] using hsub

noncomputable def coeffDivPoly (p : ℕ) (T : ℤ[X]) : ℤ[X] :=
  ∑ n ∈ T.support, monomial n (T.coeff n / (p : ℤ))

lemma coeff_coeffDivPoly {p : ℕ} (hp0 : (p : ℤ) ≠ 0) {T : ℤ[X]}
    (hdiv : ∀ n : ℕ, (p : ℤ) ∣ T.coeff n) (n : ℕ) :
    (Polynomial.C (p : ℤ) * coeffDivPoly p T).coeff n = T.coeff n := by
  classical
  by_cases hn : n ∈ T.support
  · have hp_dvd : (p : ℤ) ∣ T.coeff n := hdiv n
    simp [coeffDivPoly, hn, coeff_monomial, hp_dvd, Int.mul_ediv_cancel' hp_dvd]
  · have hcoeff0 : T.coeff n = 0 := by
      simpa [mem_support_iff] using hn
    simp [coeffDivPoly, hn, coeff_monomial, hcoeff0]

lemma C_mul_coeffDivPoly_eq {p : ℕ} (hp0 : (p : ℤ) ≠ 0) {T : ℤ[X]}
    (hdiv : ∀ n : ℕ, (p : ℤ) ∣ T.coeff n) :
    Polynomial.C (p : ℤ) * coeffDivPoly p T = T := by
  ext n
  exact coeff_coeffDivPoly hp0 hdiv n

theorem exists_scaled_quotient_of_prime_ge_five {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∃ S : ℤ[X], Rnum p = Polynomial.C (p : ℤ) * D * S := by
  rcases D_dvd_Rnum_of_prime_ge_five hp hp5 with ⟨T, hT⟩
  have hdiv : ∀ n : ℕ, (p : ℤ) ∣ T.coeff n :=
    prime_dvd_coeff_of_Rnum_eq_D_mul hp hT
  let S : ℤ[X] := coeffDivPoly p T
  have hTscaled : Polynomial.C (p : ℤ) * S = T :=
    C_mul_coeffDivPoly_eq (p := p) (T := T) (by exact_mod_cast hp.ne_zero) hdiv
  refine ⟨S, ?_⟩
  calc
    Rnum p = D * T := hT
    _ = D * (Polynomial.C (p : ℤ) * S) := by rw [hTscaled]
    _ = Polynomial.C (p : ℤ) * D * S := by ring


lemma reflect_D_two : (D.reflect 2) = D := by
  ext n
  by_cases hn : n ≤ 2
  · interval_cases n <;> simp [D, coeff_one, coeff_X, coeff_X_pow]
  · have hlt : 2 < n := Nat.lt_of_not_ge hn
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    simp [D, revAt_eq_self_of_lt hlt, coeff_one, coeff_X, coeff_X_pow, hn0, hn1.symm, hn2]

lemma natDegree_D_le_two : D.natDegree ≤ 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  simp [D, coeff_one, coeff_X, coeff_X_pow, hn0, hn1.symm, hn2]

lemma natDegree_D : D.natDegree = 2 := by
  apply le_antisymm natDegree_D_le_two
  exact le_natDegree_of_ne_zero (by simp [D, coeff_one, coeff_X, coeff_X_pow])

lemma leadingCoeff_D : D.leadingCoeff = 1 := by
  rw [leadingCoeff, natDegree_D]
  simp [D, coeff_one, coeff_X, coeff_X_pow]

lemma D_ne_zero : D ≠ 0 := by
  intro h
  have := congrArg (fun P : ℤ[X] => P.coeff 0) h
  simp [D] at this

lemma reflect_one_add_X_pow (p : ℕ) :
    (((1 + X : ℤ[X]) ^ p).reflect p) = (1 + X : ℤ[X]) ^ p := by
  ext k
  by_cases hk : k ≤ p
  · rw [coeff_reflect, revAt_le hk, coeff_one_add_X_pow, coeff_one_add_X_pow]
    norm_cast
    exact Nat.choose_symm hk
  · rw [coeff_reflect, revAt_eq_self_of_lt (Nat.lt_of_not_ge hk)]

lemma reflect_Rnum (p : ℕ) : (Rnum p).reflect p = Rnum p := by
  simp [Rnum, reflect_one_add_X_pow]
  ring

lemma natDegree_Rnum_le (p : ℕ) : (Rnum p).natDegree ≤ p := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hnp : n ≠ p := by omega
  simp [Rnum, coeff_one_add_X_pow, Nat.choose_eq_zero_of_lt hn, coeff_one, coeff_X_pow, hn0, hnp]

lemma natDegree_of_quotient_le {p : ℕ} (hp2 : 2 ≤ p) {S : ℤ[X]}
    (hS : Rnum p = D * S) : S.natDegree ≤ p - 2 := by
  by_cases h0 : S = 0
  · simp [h0]
  have hlead : D.leadingCoeff * S.leadingCoeff ≠ 0 := by
    rw [leadingCoeff_D]
    simpa using (leadingCoeff_ne_zero.mpr h0 : S.leadingCoeff ≠ 0)
  have hmuldeg : (D * S).natDegree = D.natDegree + S.natDegree := natDegree_mul' hlead
  have hDdeg : D.natDegree = 2 := natDegree_D
  have hprodle : (D * S).natDegree ≤ p := by
    simpa [hS] using natDegree_Rnum_le p
  omega

theorem quotient_reflect_eq_of_prime_ge_five {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {S : ℤ[X]} (hS : Rnum p = D * S) :
    S.reflect (p - 2) = S := by
  have hp2 : 2 ≤ p := by omega
  have hSdeg : S.natDegree ≤ p - 2 := natDegree_of_quotient_le hp2 hS
  have hprod_reflect : ((D * S).reflect p) = D * S.reflect (p - 2) := by
    rw [show p = 2 + (p - 2) by omega]
    rw [reflect_mul (F := 2) (G := p - 2) D S natDegree_D_le_two hSdeg, reflect_D_two]
    rw [show 2 + (p - 2) - 2 = p - 2 by omega]
  have hcancel : D * S = D * S.reflect (p - 2) := by
    calc
      D * S = Rnum p := hS.symm
      _ = (Rnum p).reflect p := (reflect_Rnum p).symm
      _ = (D * S).reflect p := by rw [hS]
      _ = D * S.reflect (p - 2) := hprod_reflect
  exact (mul_left_cancel₀ D_ne_zero hcancel).symm


lemma reflect_C_mul (c : ℤ) (S : ℤ[X]) (N : ℕ) :
    (Polynomial.C c * S).reflect N = Polynomial.C c * S.reflect N := by
  ext n
  simp [coeff_reflect]

theorem scaled_quotient_reflect_eq_of_prime_ge_five {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {S : ℤ[X]} (hS : Rnum p = Polynomial.C (p : ℤ) * D * S) :
    S.reflect (p - 2) = S := by
  let c : ℤ[X] := Polynomial.C (p : ℤ)
  have hQ : Rnum p = D * (c * S) := by
    calc
      Rnum p = c * D * S := hS
      _ = D * (c * S) := by ring
  have hpal : (c * S).reflect (p - 2) = c * S :=
    quotient_reflect_eq_of_prime_ge_five hp hp5 hQ
  change (Polynomial.C (p : ℤ) * S).reflect (p - 2) = Polynomial.C (p : ℤ) * S at hpal
  rw [reflect_C_mul] at hpal
  have hc_ne : Polynomial.C (p : ℤ) ≠ (0 : ℤ[X]) := by
    apply C_ne_zero.mpr
    exact_mod_cast hp.ne_zero
  exact mul_left_cancel₀ hc_ne hpal

def PalPoly (f : ℤ[X]) (N : ℕ) : Prop :=
  f.reflect N = f

def AntiPalPoly (f : ℤ[X]) (N : ℕ) : Prop :=
  f.reflect N = -f

lemma reflect_A_two : (A.reflect 2) = -A := by
  ext n
  by_cases hn : n ≤ 2
  · interval_cases n <;> simp [A, coeff_one, coeff_X_pow]
  · have hlt : 2 < n := Nat.lt_of_not_ge hn
    have hn0 : n ≠ 0 := by omega
    have hn2 : n ≠ 2 := by omega
    rw [coeff_reflect, revAt_eq_self_of_lt hlt]
    simp [A, coeff_one, coeff_X_pow, hn0, hn2]

lemma natDegree_A_le_two : A.natDegree ≤ 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn2 : n ≠ 2 := by omega
  simp [A, coeff_one, coeff_X_pow, hn0, hn2]

lemma D_pal : PalPoly D 2 := reflect_D_two

lemma A_antipal : AntiPalPoly A 2 := reflect_A_two

lemma pal_mul {f g : ℤ[X]} {F G : ℕ}
    (hfdeg : f.natDegree ≤ F) (hgdeg : g.natDegree ≤ G)
    (hf : PalPoly f F) (hg : PalPoly g G) :
    PalPoly (f * g) (F + G) := by
  unfold PalPoly at *
  rw [reflect_mul f g hfdeg hgdeg, hf, hg]

lemma antipal_mul_pal {f g : ℤ[X]} {F G : ℕ}
    (hfdeg : f.natDegree ≤ F) (hgdeg : g.natDegree ≤ G)
    (hf : AntiPalPoly f F) (hg : PalPoly g G) :
    AntiPalPoly (f * g) (F + G) := by
  unfold AntiPalPoly PalPoly at *
  rw [reflect_mul f g hfdeg hgdeg, hf, hg]
  ring

lemma pal_pow {f : ℤ[X]} {F : ℕ} (hfdeg : f.natDegree ≤ F) (hf : PalPoly f F) :
    ∀ l, PalPoly (f ^ l) (l * F) := by
  intro l
  induction l with
  | zero =>
      unfold PalPoly
      simp [reflect_one]
  | succ l ih =>
      have hpowdeg : (f ^ l).natDegree ≤ l * F := natDegree_pow_le_of_le l hfdeg
      have hmul := pal_mul (f := f ^ l) (g := f) (F := l * F) (G := F)
        hpowdeg hfdeg ih hf
      simpa [pow_succ, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using hmul

lemma natDegree_of_scaled_quotient_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {S : ℤ[X]}
    (hS : Rnum p = Polynomial.C (p : ℤ) * D * S) :
    S.natDegree ≤ p - 2 := by
  let c : ℤ[X] := Polynomial.C (p : ℤ)
  have hQ : Rnum p = D * (c * S) := by
    calc
      Rnum p = c * D * S := hS
      _ = D * (c * S) := by ring
  have hCSdeg : (c * S).natDegree ≤ p - 2 := natDegree_of_quotient_le (by omega) hQ
  have hc0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  change (Polynomial.C (p : ℤ) * S).natDegree ≤ p - 2 at hCSdeg
  rwa [natDegree_C_mul hc0] at hCSdeg

theorem scaled_P_reflect_eq_neg {p l : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hl : 1 ≤ l)
    {S : ℤ[X]} (hS : Rnum p = Polynomial.C (p : ℤ) * D * S) :
    ((A * D ^ (l - 1) * S ^ l).reflect (p * l)) = -(A * D ^ (l - 1) * S ^ l) := by
  classical
  have hSpal : PalPoly S (p - 2) := scaled_quotient_reflect_eq_of_prime_ge_five hp hp5 hS
  have hSdeg : S.natDegree ≤ p - 2 := natDegree_of_scaled_quotient_le hp hp5 hS
  have hDpow : PalPoly (D ^ (l - 1)) ((l - 1) * 2) :=
    pal_pow natDegree_D_le_two D_pal (l - 1)
  have hSpow : PalPoly (S ^ l) (l * (p - 2)) :=
    pal_pow hSdeg hSpal l
  have hDpowdeg : (D ^ (l - 1)).natDegree ≤ (l - 1) * 2 :=
    natDegree_pow_le_of_le (l - 1) natDegree_D_le_two
  have hSpowdeg : (S ^ l).natDegree ≤ l * (p - 2) :=
    natDegree_pow_le_of_le l hSdeg
  have hpal_prod : PalPoly (D ^ (l - 1) * S ^ l) (((l - 1) * 2) + l * (p - 2)) :=
    pal_mul hDpowdeg hSpowdeg hDpow hSpow
  have hpal_prod_deg : (D ^ (l - 1) * S ^ l).natDegree ≤ ((l - 1) * 2) + l * (p - 2) :=
    natDegree_mul_le_of_le hDpowdeg hSpowdeg
  have hanti := antipal_mul_pal (f := A) (g := D ^ (l - 1) * S ^ l)
    (F := 2) (G := ((l - 1) * 2) + l * (p - 2))
    natDegree_A_le_two hpal_prod_deg A_antipal hpal_prod
  have hdeg : 2 + (((l - 1) * 2) + l * (p - 2)) = p * l := by
    have hl' : l = (l - 1) + 1 := by omega
    have hp' : p = (p - 2) + 2 := by omega
    nlinarith
  simpa [AntiPalPoly, hdeg, mul_assoc] using hanti





end ScaledQuotientTemp
namespace ScaledFreshmanCoeffPadicTemp

/-- Re-export of the beta coefficient under the namespace requested for this temp file. -/
def beta (N l M a : ℕ) : ℤ := BetaYpairTemp.beta N l M a

noncomputable def D : ℤ[X] := 1 + X + X^2
noncomputable def A : ℤ[X] := 1 - X^2
noncomputable def Rnum (p : ℕ) : ℤ[X] := (1 + X)^p - 1 - X^p

lemma D_eq : D = ScaledQuotientTemp.D := rfl
lemma A_eq : A = ScaledQuotientTemp.A := rfl
lemma Rnum_eq (p : ℕ) : Rnum p = ScaledQuotientTemp.Rnum p := rfl

/-- The scaled quotient `S` still has degree at most `p-2`. -/
lemma scaled_S_natDegree_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {S : ℤ[X]}
    (hS : Rnum p = Polynomial.C (p : ℤ) * D * S) :
    S.natDegree ≤ p - 2 := by
  have hS' : ScaledQuotientTemp.Rnum p = Polynomial.C (p : ℤ) * ScaledQuotientTemp.D * S := by
    simpa [Rnum, D, ScaledQuotientTemp.Rnum, ScaledQuotientTemp.D] using hS
  exact ScaledQuotientTemp.natDegree_of_scaled_quotient_le hp hp5 hS'

/-- The scaled quotient `S` has zero constant coefficient. -/
lemma scaled_S_coeff_zero {p : ℕ} (hp : p.Prime) {S : ℤ[X]}
    (hS : Rnum p = Polynomial.C (p : ℤ) * D * S) :
    S.coeff 0 = 0 := by
  have hcoeff : (Rnum p).coeff 0 = (Polynomial.C (p : ℤ) * D * S).coeff 0 := by
    simpa using congrArg (fun P : ℤ[X] => P.coeff 0) hS
  have hR0 : (Rnum p).coeff 0 = 0 := by
    simp [Rnum, Polynomial.coeff_one_add_X_pow, Nat.ne_of_lt hp.pos]
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmul : (p : ℤ) * S.coeff 0 = 0 := by
    simpa [hR0, D, mul_assoc] using hcoeff.symm
  exact mul_left_cancel₀ hpz hmul

/-- Degree bound for the scaled product used in the sampled coefficient theorem. -/
lemma scaled_P_natDegree_le {p l : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hl : 1 ≤ l)
    {S : ℤ[X]} (hS : Rnum p = Polynomial.C (p : ℤ) * D * S) :
    (A * D ^ (l - 1) * S ^ l).natDegree ≤ p * l := by
  have hSdeg : S.natDegree ≤ p - 2 := scaled_S_natDegree_le hp hp5 hS
  have hDpowdeg : (D ^ (l - 1)).natDegree ≤ (l - 1) * 2 := by
    simpa [D, ScaledQuotientTemp.D] using
      (Polynomial.natDegree_pow_le_of_le (l - 1) ScaledQuotientTemp.natDegree_D_le_two)
  have hSpowdeg : (S ^ l).natDegree ≤ l * (p - 2) :=
    Polynomial.natDegree_pow_le_of_le l hSdeg
  have hADdeg : (A * D ^ (l - 1)).natDegree ≤ 2 + ((l - 1) * 2) := by
    exact Polynomial.natDegree_mul_le_of_le
      (by simpa [A, ScaledQuotientTemp.A] using ScaledQuotientTemp.natDegree_A_le_two)
      hDpowdeg
  have hdeg : (A * D ^ (l - 1) * S ^ l).natDegree ≤
      (2 + ((l - 1) * 2)) + l * (p - 2) :=
    Polynomial.natDegree_mul_le_of_le hADdeg hSpowdeg
  have harith : (2 + ((l - 1) * 2)) + l * (p - 2) = p * l := by
    have hp2 : 2 ≤ p := by omega
    have hl' : l = (l - 1) + 1 := by omega
    have hp' : p = (p - 2) + 2 := by omega
    nlinarith
  simpa [harith] using hdeg

/-- The scaled product used in the sampled coefficient theorem has zero constant coefficient. -/
lemma scaled_P_coeff_zero {p l : ℕ} (hp : p.Prime) (hl : 1 ≤ l) {S : ℤ[X]}
    (hS : Rnum p = Polynomial.C (p : ℤ) * D * S) :
    (A * D ^ (l - 1) * S ^ l).coeff 0 = 0 := by
  have hS0 : S.coeff 0 = 0 := scaled_S_coeff_zero hp hS
  have hSpow0 : (S ^ l).coeff 0 = 0 := by
    rcases Nat.exists_eq_add_of_le hl with ⟨k, rfl⟩
    rw [show 1 + k = k + 1 by omega, pow_succ, Polynomial.mul_coeff_zero, hS0, mul_zero]
  rw [Polynomial.mul_coeff_zero, hSpow0, mul_zero]

/-- Corrected scaled synthesis: if `Rnum p = p * D * S`, then the freshman
coefficient sum formed from the scaled quotient satisfies the same p-adic
bound, by the scaled anti-palindromicity theorem and the sampled coefficient
p-adic theorem. -/
theorem scaled_freshman_coeff_padic_dvd
    {p l e M T : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hl : 3 ≤ l)
    (hMpos : 0 < M) (hT : 2 ≤ T) (hM : p^e ∣ M)
    {S : ℤ[X]} (hS : Rnum p = Polynomial.C (p:ℤ) * D * S) :
    (p:ℤ)^(3*e+3) ∣ (p:ℤ)^l *
      ∑ a ∈ Finset.range (l + 1), (A * D ^ (l - 1) * S ^ l).coeff (p * a) *
        (((M * T).choose l : ℤ) * beta (M * T) l M a) := by
  have hS' : ScaledQuotientTemp.Rnum p = Polynomial.C (p : ℤ) * ScaledQuotientTemp.D * S := by
    simpa [Rnum, D, ScaledQuotientTemp.Rnum, ScaledQuotientTemp.D] using hS
  have hanti : (ScaledQuotientTemp.A * ScaledQuotientTemp.D ^ (l - 1) * S ^ l).reflect (p * l) =
      -(ScaledQuotientTemp.A * ScaledQuotientTemp.D ^ (l - 1) * S ^ l) :=
    ScaledQuotientTemp.scaled_P_reflect_eq_neg hp hp5 (by omega : 1 ≤ l) hS'
  have hanti' : (A * D ^ (l - 1) * S ^ l).reflect (p * l) =
      -(A * D ^ (l - 1) * S ^ l) := by
    simpa [A, D, ScaledQuotientTemp.A, ScaledQuotientTemp.D] using hanti
  have hdeg : (A * D ^ (l - 1) * S ^ l).natDegree ≤ p * l :=
    scaled_P_natDegree_le hp hp5 (by omega : 1 ≤ l) hS
  have h0 : (A * D ^ (l - 1) * S ^ l).coeff 0 = 0 :=
    scaled_P_coeff_zero hp (by omega : 1 ≤ l) hS
  simpa [beta] using
    (PolyCoeffPairTemp.sampled_coeff_sum_padic_dvd
      (p := p) (l := l) (e := e) (M := M) (T := T)
      (P := A * D ^ (l - 1) * S ^ l)
      hp hp5 hl hT hMpos hM hanti' hdeg h0)

end ScaledFreshmanCoeffPadicTemp

/- copied DirectBseqCongruenceTemp2.lean -/

open scoped BigOperators
open Nat Finset BigOperators Int Polynomial
open Polynomial
open scoped Polynomial

/-- The target B-sequence coefficient pattern. -/
def hCoeff (i : ℕ) : ℤ := if i = 0 then 1 else if 3 ∣ i then 2 else -1

/-- The target B-sequence form. -/
def Bseq (s : ℤ) (N : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (N + 1), hCoeff i * Ring.choose (s * (N : ℤ)) (N - i)

namespace DirectBseqCongruenceTemp2

/-- The beta coefficient from the coefficient extraction of the freshman correction terms. -/
def beta (N l M a : ℕ) : ℤ := if a ≤ M then ((N - l).choose (M - a) : ℤ) else 0

noncomputable def D : ℤ[X] := 1 + X + X^2
noncomputable def A : ℤ[X] := 1 - X^2
noncomputable def Rnum (p : ℕ) : ℤ[X] := (1 + X)^p - 1 - X^p

/-- For primes `p ≥ 5`, prime scaling preserves the `hCoeff` pattern. -/
theorem hCoeff_mul_prime_left_eq {p a : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    hCoeff (p * a) = hCoeff a := by
  by_cases ha : a = 0
  · subst ha
    simp [hCoeff]
  · have hpa0 : p * a ≠ 0 := by
      exact Nat.mul_ne_zero (Nat.ne_of_gt hp.pos) ha
    have h3p_not : ¬ 3 ∣ p := by
      intro h3p
      have hpeq3 : p = 3 := (hp.dvd_iff_eq (by norm_num : (3 : ℕ) ≠ 1)).mp h3p
      omega
    have hiff : (3 ∣ p * a) ↔ (3 ∣ a) := by
      constructor
      · intro h
        rcases (Nat.prime_three.dvd_mul.mp h) with h3p | h3a
        · exact (h3p_not h3p).elim
        · exact h3a
      · intro h3a
        exact dvd_mul_of_dvd_right h3a p
    simp [hCoeff, ha, hpa0, hiff]

/-- Right-sided version of `hCoeff_mul_prime_left_eq`. -/
theorem hCoeff_mul_prime_right_eq {p a : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    hCoeff (a * p) = hCoeff a := by
  rw [Nat.mul_comm]
  exact hCoeff_mul_prime_left_eq (p := p) (a := a) hp hp5


/-- The polynomial-level scaled freshman contribution to the sampled coefficient formula for
`Bseq (T : ℤ) (p*M)`.  This is intentionally before the further `D`-cancellation
that rewrites positive `l` terms using `A * D^(l-1) * S^l`. -/
noncomputable def CorrScaledPoly (p M T l : ℕ) (S : ℤ[X]) : ℤ :=
  ∑ i ∈ Finset.range (p * M + 1), hCoeff i *
    (((Polynomial.C (p : ℤ)) * D * S) ^ l *
      (1 + X ^ p : ℤ[X]) ^ (M * T - l) *
        Polynomial.C ((M * T).choose l : ℤ)).coeff (p * M - i)

/-- The unscaled correction coefficient appearing after the formal cancellation of the
`hCoeff` generating series against one factor of `D`. -/
noncomputable def CorrUnscaled (p M T l : ℕ) (S : ℤ[X]) : ℤ :=
  ∑ a ∈ Finset.range (l + 1),
    (A * D ^ (l - 1) * S ^ l).coeff (p * a) *
      (((M * T).choose l : ℤ) * beta (M * T) l M a)

/-- The scaled correction coefficient. -/
noncomputable def CorrScaled (p M T l : ℕ) (S : ℤ[X]) : ℤ :=
  (p : ℤ) ^ l * CorrUnscaled p M T l S

/-- One freshman step under a scaled quotient hypothesis. -/
theorem freshman_step_scaled (p : ℕ) {S : ℤ[X]}
    (hS : Rnum p = (Polynomial.C (p : ℤ)) * D * S) :
    (1 + X : ℤ[X]) ^ p = 1 + X ^ p + (Polynomial.C (p : ℤ)) * D * S := by
  have h : (1 + X : ℤ[X]) ^ p - 1 - X ^ p = (Polynomial.C (p : ℤ)) * D * S := by
    simpa [Rnum] using hS
  rw [← h]
  ring

/-- Full binomial expansion from the scaled quotient. -/
theorem freshman_full_expansion_scaled (p M T : ℕ) {S : ℤ[X]}
    (hS : Rnum p = (Polynomial.C (p : ℤ)) * D * S) :
    (1 + X : ℤ[X]) ^ (p * (M * T)) =
      ∑ l ∈ Finset.range (M * T + 1),
        ((Polynomial.C (p : ℤ)) * D * S) ^ l *
          (1 + X ^ p : ℤ[X]) ^ (M * T - l) *
            Polynomial.C ((M * T).choose l : ℤ) := by
  calc
    (1 + X : ℤ[X]) ^ (p * (M * T)) = ((1 + X : ℤ[X]) ^ p) ^ (M * T) := by
      rw [pow_mul]
    _ = ((Polynomial.C (p : ℤ)) * D * S + (1 + X ^ p : ℤ[X])) ^ (M * T) := by
      rw [freshman_step_scaled (p := p) (S := S) hS]
      ring
    _ = ∑ l ∈ Finset.range (M * T + 1),
        ((Polynomial.C (p : ℤ)) * D * S) ^ l *
          (1 + X ^ p : ℤ[X]) ^ (M * T - l) *
            Polynomial.C ((M * T).choose l : ℤ) := by
      simpa using add_pow ((Polynomial.C (p : ℤ)) * D * S) (1 + X ^ p : ℤ[X]) (M * T)

lemma int_nat_cast_mul_Bseq_arg (p M T : ℕ) :
    (T : ℤ) * ((p * M : ℕ) : ℤ) = ((p * (M * T) : ℕ) : ℤ) := by
  norm_num [Nat.cast_mul]
  ring

lemma Bseq_choose_as_coeff_scaled (p M T i : ℕ) :
    Ring.choose ((T : ℤ) * ((p * M : ℕ) : ℤ)) (p * M - i) =
      ((1 + X : ℤ[X]) ^ (p * (M * T))).coeff (p * M - i) := by
  rw [int_nat_cast_mul_Bseq_arg]
  rw [Ring.choose_natCast]
  simp [Polynomial.coeff_one_add_X_pow]

lemma coeff_finset_sum {α : Type*} (s : Finset α) (f : α → ℤ[X]) (n : ℕ) :
    (∑ x ∈ s, f x).coeff n = ∑ x ∈ s, (f x).coeff n := by
  exact map_sum (Polynomial.lcoeff ℤ n) f s


/-- Fallback coefficient expansion: the scaled freshman expansion gives `Bseq (T:ℤ) (p*M)`
as a finite sum of the polynomial-level scaled correction contributions.  This is the
coefficient-extraction stage preceding the additional cancellation that identifies the
positive `l` terms with `CorrScaled`. -/
theorem Bseq_nat_scaled_poly_expansion (p M T : ℕ) {S : ℤ[X]}
    (hS : Rnum p = (Polynomial.C (p : ℤ)) * D * S) :
    Bseq (T : ℤ) (p * M) =
      ∑ l ∈ Finset.range (M * T + 1), CorrScaledPoly p M T l S := by
  classical
  unfold Bseq CorrScaledPoly
  simp_rw [Bseq_choose_as_coeff_scaled (p := p) (M := M) (T := T)]
  rw [freshman_full_expansion_scaled (p := p) (M := M) (T := T) (S := S) hS]
  simp_rw [coeff_finset_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Difference form of the fallback coefficient expansion. -/
theorem Bseq_nat_scaled_poly_difference (p M T : ℕ) {S : ℤ[X]}
    (hS : Rnum p = (Polynomial.C (p : ℤ)) * D * S) :
    Bseq (T : ℤ) (p * M) - Bseq (T : ℤ) M =
      (∑ l ∈ Finset.range (M * T + 1), CorrScaledPoly p M T l S) - Bseq (T : ℤ) M := by
  rw [Bseq_nat_scaled_poly_expansion (p := p) (M := M) (T := T) (S := S) hS]

end DirectBseqCongruenceTemp2

/- copied CorrZeroTemp.lean in a namespace -/
namespace CorrZeroAssembled

open scoped BigOperators
open Nat Finset BigOperators Int Polynomial
open Polynomial
open scoped Polynomial

/-- The target B-sequence coefficient pattern. -/
def hCoeff (i : ℕ) : ℤ := if i = 0 then 1 else if 3 ∣ i then 2 else -1

/-- The target B-sequence form. -/
def Bseq (s : ℤ) (N : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (N + 1), hCoeff i * Ring.choose (s * (N : ℤ)) (N - i)

/-- The beta coefficient from the coefficient extraction of the freshman correction terms. -/
def beta (N l M a : ℕ) : ℤ := if a ≤ M then ((N - l).choose (M - a) : ℤ) else 0

noncomputable def D : ℤ[X] := 1 + X + X^2

/-- The polynomial-level scaled freshman contribution to the sampled coefficient formula. -/
noncomputable def CorrScaledPoly (p M T l : ℕ) (S : ℤ[X]) : ℤ :=
  ∑ i ∈ Finset.range (p * M + 1), hCoeff i *
    ((((Polynomial.C (p : ℤ)) * D * S) ^ l *
      (1 + X ^ p : ℤ[X]) ^ (M * T - l) *
        Polynomial.C ((M * T).choose l : ℤ)).coeff (p * M - i))

/-- For primes `p ≥ 5`, prime scaling preserves the `hCoeff` pattern. -/
theorem hCoeff_mul_prime_left_eq {p a : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    hCoeff (p * a) = hCoeff a := by
  by_cases ha : a = 0
  · subst ha
    simp [hCoeff]
  · have hpa0 : p * a ≠ 0 := by
      exact Nat.mul_ne_zero (Nat.ne_of_gt hp.pos) ha
    have h3p_not : ¬ 3 ∣ p := by
      intro h3p
      have hpeq3 : p = 3 := (hp.dvd_iff_eq (by norm_num : (3 : ℕ) ≠ 1)).mp h3p
      omega
    have hiff : (3 ∣ p * a) ↔ (3 ∣ a) := by
      constructor
      · intro h
        rcases (Nat.prime_three.dvd_mul.mp h) with h3p | h3a
        · exact (h3p_not h3p).elim
        · exact h3a
      · intro h3a
        exact dvd_mul_of_dvd_right h3a p
    simp [hCoeff, ha, hpa0, hiff]

/-- Right-sided version of `hCoeff_mul_prime_left_eq`. -/
theorem hCoeff_mul_prime_right_eq {p a : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    hCoeff (a * p) = hCoeff a := by
  rw [Nat.mul_comm]
  exact hCoeff_mul_prime_left_eq (p := p) (a := a) hp hp5

/-- The finite polynomial whose coefficients are the `hCoeff` pattern up to degree `N`. -/
noncomputable def hPoly (N : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range (N + 1), Polynomial.C (hCoeff i) * X ^ i

lemma hPoly_coeff (N k : ℕ) : (hPoly N).coeff k = if k ≤ N then hCoeff k else 0 := by
  classical
  rw [hPoly]
  change Polynomial.lcoeff ℤ k (∑ i ∈ Finset.range (N + 1), Polynomial.C (hCoeff i) * X ^ i) = _
  rw [map_sum]
  by_cases hk : k ≤ N
  · rw [if_pos hk]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b hb hbk
      simp [Polynomial.coeff_X_pow, (Ne.symm hbk)]
    · intro hnot
      exfalso
      exact hnot (by simpa using Nat.lt_succ_of_le hk)
  · rw [if_neg hk]
    rw [Finset.sum_eq_zero]
    intro b hb
    have hbk : b ≠ k := by
      intro h
      subst h
      exact hk (Nat.le_of_lt_succ (by simpa using hb))
    simp [Polynomial.coeff_X_pow, (Ne.symm hbk)]

lemma one_add_X_pow_p_eq_expand (p n : ℕ) :
    (1 + X ^ p : ℤ[X]) ^ n = Polynomial.expand ℤ p ((1 + X : ℤ[X]) ^ n) := by
  rw [map_pow]
  simp

lemma contract_hPoly_scaled (p M : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Polynomial.contract p (hPoly (p * M)) = hPoly M := by
  classical
  ext k
  have hpne : p ≠ 0 := Nat.ne_of_gt hp.pos
  rw [Polynomial.coeff_contract hpne]
  rw [hPoly_coeff, hPoly_coeff]
  by_cases hk : k ≤ M
  · rw [if_pos hk]
    have hkp : k * p ≤ p * M := by
      rw [Nat.mul_comm k p]
      exact Nat.mul_le_mul_left p hk
    rw [if_pos hkp]
    exact hCoeff_mul_prime_right_eq (p := p) (a := k) hp hp5
  · rw [if_neg hk]
    have hnot : ¬ k * p ≤ p * M := by
      intro hle
      have hle' : k ≤ M := by
        rw [Nat.mul_comm k p] at hle
        exact Nat.le_of_mul_le_mul_left hle hp.pos
      exact hk hle'
    rw [if_neg hnot]

lemma Bseq_choose_as_coeff (M T i : ℕ) :
    Ring.choose ((T : ℤ) * (M : ℤ)) (M - i) =
      ((1 + X : ℤ[X]) ^ (M * T)).coeff (M - i) := by
  have harg : (T : ℤ) * (M : ℤ) = ((M * T : ℕ) : ℤ) := by
    norm_num [Nat.cast_mul]
    ring
  rw [harg]
  rw [Ring.choose_natCast]
  simp [Polynomial.coeff_one_add_X_pow]

lemma Bseq_eq_hPoly_mul_coeff (M T : ℕ) :
    Bseq (T : ℤ) M = (hPoly M * (1 + X : ℤ[X]) ^ (M * T)).coeff M := by
  classical
  unfold Bseq
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i hi
  have hiM : i ≤ M := Nat.le_of_lt_succ (by simpa using hi)
  rw [hPoly_coeff]
  rw [if_pos hiM]
  rw [Bseq_choose_as_coeff (M := M) (T := T) (i := i)]

lemma CorrScaledPoly_zero_eq_hPoly_mul_coeff (p M T : ℕ) (S : ℤ[X]) :
    CorrScaledPoly p M T 0 S =
      (hPoly (p * M) * (1 + X ^ p : ℤ[X]) ^ (M * T)).coeff (p * M) := by
  classical
  unfold CorrScaledPoly
  simp
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i hi
  have hiM : i ≤ p * M := Nat.le_of_lt_succ (by simpa using hi)
  rw [hPoly_coeff]
  rw [if_pos hiM]

/-- For the zero-th freshman term, the scaled correction polynomial is exactly `Bseq` at the
unscaled index.  The polynomial is `(1 + X^p)^(M*T)` and is independent of `S`. -/
theorem CorrScaledPoly_zero_eq_Bseq (p M T : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (S : ℤ[X]) :
    CorrScaledPoly p M T 0 S = Bseq (T : ℤ) M := by
  classical
  have hpne : p ≠ 0 := Nat.ne_of_gt hp.pos
  calc
    CorrScaledPoly p M T 0 S
        = (hPoly (p * M) * (1 + X ^ p : ℤ[X]) ^ (M * T)).coeff (p * M) :=
          CorrScaledPoly_zero_eq_hPoly_mul_coeff p M T S
    _ = (Polynomial.contract p
            (hPoly (p * M) * (1 + X ^ p : ℤ[X]) ^ (M * T))).coeff M := by
          rw [Nat.mul_comm p M]
          rw [Polynomial.coeff_contract hpne]
    _ = (Polynomial.contract p
            (hPoly (p * M) * Polynomial.expand ℤ p ((1 + X : ℤ[X]) ^ (M * T)))).coeff M := by
          rw [← one_add_X_pow_p_eq_expand (p := p) (n := M * T)]
    _ = (Polynomial.contract p (hPoly (p * M)) * (1 + X : ℤ[X]) ^ (M * T)).coeff M := by
          rw [Polynomial.contract_mul_expand hpne]
    _ = (hPoly M * (1 + X : ℤ[X]) ^ (M * T)).coeff M := by
          rw [contract_hPoly_scaled (p := p) (M := M) hp hp5]
    _ = Bseq (T : ℤ) M := by
          rw [← Bseq_eq_hPoly_mul_coeff (M := M) (T := T)]


end CorrZeroAssembled

/- copied CorrBridgeTemp.lean -/

open Polynomial Finset
open scoped Polynomial BigOperators

namespace CorrBridgeTemp

/-- The target B-sequence coefficient pattern. -/
def hCoeff (i : ℕ) : ℤ := if i = 0 then 1 else if 3 ∣ i then 2 else -1

/-- The beta coefficient from the coefficient extraction. -/
def beta (N l M a : ℕ) : ℤ := if a ≤ M then ((N - l).choose (M - a) : ℤ) else 0

noncomputable def D : ℤ[X] := 1 + X + X^2
noncomputable def A : ℤ[X] := 1 - X^2

/-- The polynomial-level scaled freshman contribution. -/
noncomputable def CorrScaledPoly (p M T l : ℕ) (S : ℤ[X]) : ℤ :=
  ∑ i ∈ Finset.range (p * M + 1), hCoeff i *
    (((Polynomial.C (p : ℤ)) * D * S) ^ l *
      (1 + X ^ p : ℤ[X]) ^ (M * T - l) *
        Polynomial.C ((M * T).choose l : ℤ)).coeff (p * M - i)

/-- The unscaled correction coefficient. -/
noncomputable def CorrUnscaled (p M T l : ℕ) (S : ℤ[X]) : ℤ :=
  ∑ a ∈ Finset.range (l + 1),
    (A * D ^ (l - 1) * S ^ l).coeff (p * a) *
      (((M * T).choose l : ℤ) * beta (M * T) l M a)

/-- The scaled correction coefficient. -/
noncomputable def CorrScaled (p M T l : ℕ) (S : ℤ[X]) : ℤ :=
  (p : ℤ) ^ l * CorrUnscaled p M T l S

noncomputable def hPoly (N : ℕ) : ℤ[X] :=
  ∑ i∈Finset.range (N+1), Polynomial.C (hCoeff i) * X^i

lemma hCoeff_rec (n : ℕ) : hCoeff (n+3) + hCoeff (n+2) + hCoeff (n+1) = 0 := by
  have hlt : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  interval_cases h : n % 3 <;>
    simp [hCoeff, Nat.dvd_iff_mod_eq_zero] <;> omega

lemma D_coeff (n : ℕ) : D.coeff n = if n ≤ 2 then 1 else 0 := by
  dsimp [D]
  simp [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  split <;> omega

lemma A_coeff (n : ℕ) : A.coeff n = if n = 0 then 1 else if n = 2 then -1 else 0 := by
  dsimp [A]
  simp [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_pow]
  split <;> omega

lemma hPoly_coeff (N k : ℕ) : (hPoly N).coeff k = if k ≤ N then hCoeff k else 0 := by
  classical
  rw [hPoly]
  change Polynomial.lcoeff ℤ k (∑ i∈Finset.range (N+1), Polynomial.C (hCoeff i) * X^i) = _
  rw [map_sum]
  by_cases hk : k ≤ N
  · rw [if_pos hk]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b hb hbk
      simp [Polynomial.coeff_X_pow, (Ne.symm hbk)]
    · intro hnot
      exfalso
      exact hnot (by simpa using Nat.lt_succ_of_le hk)
  · rw [if_neg hk]
    rw [Finset.sum_eq_zero]
    intro b hb
    have hbk : b ≠ k := by
      intro h
      subst h
      exact hk (Nat.le_of_lt_succ (by simpa using hb))
    simp [Polynomial.coeff_X_pow, (Ne.symm hbk)]

lemma hPoly_coeff_of_le {N k : ℕ} (hk : k ≤ N) : (hPoly N).coeff k = hCoeff k := by
  simp [hPoly_coeff, hk]

lemma hCoeff_D_sum (n : ℕ) :
    (∑ i∈Finset.range (n+1), hCoeff i * D.coeff (n-i)) = A.coeff n := by
  by_cases hn : n < 3
  · interval_cases n <;> norm_num [Finset.sum_range_succ, hCoeff, D_coeff, A_coeff]
  · have hn3 : 3 ≤ n := by omega
    let f : ℕ → ℤ := fun i => hCoeff i * D.coeff (n-i)
    have hsplit : (∑ i∈Finset.range (n+1), f i) =
        (∑ i∈Finset.range (n-2), f i) + f (n-2) + f (n-1) + f n := by
      calc
        (∑ i∈Finset.range (n+1), f i) = (∑ i∈Finset.range n, f i) + f n := by
          rw [Finset.sum_range_succ]
        _ = ((∑ i∈Finset.range (n-1), f i) + f (n-1)) + f n := by
          rw [show n = (n-1) + 1 by omega, Finset.sum_range_succ]
          simp
        _ = (((∑ i∈Finset.range (n-2), f i) + f (n-2)) + f (n-1)) + f n := by
          rw [show n - 1 = (n-2) + 1 by omega, Finset.sum_range_succ]
        _ = (∑ i∈Finset.range (n-2), f i) + f (n-2) + f (n-1) + f n := by
          abel
    have hz : (∑ i∈Finset.range (n-2), f i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi_lt : i < n - 2 := by simpa using hi
      have hfalse : ¬ n ≤ 2 + i := by omega
      simp [f, D_coeff, hfalse]
    have hrec := hCoeff_rec (n-3)
    have hA : A.coeff n = 0 := by simp [A_coeff]; omega
    rw [show (∑ i∈Finset.range (n+1), hCoeff i * D.coeff (n-i)) = ∑ i∈Finset.range (n+1), f i by rfl]
    rw [hsplit, hz, hA]
    simp [f, D_coeff, show n ≤ 2 + (n - 2) by omega, show n ≤ 2 + (n - 1) by omega]
    have hrec' : hCoeff n + hCoeff (n - 1) + hCoeff (n - 2) = 0 := by
      have h0 : n - 3 + 3 = n := by omega
      have h1 : n - 3 + 2 = n - 1 := by omega
      have h2 : n - 3 + 1 = n - 2 := by omega
      simpa [h0, h1, h2] using hrec
    simpa [add_comm, add_left_comm, add_assoc] using hrec'

lemma hPoly_mul_D_coeff (N k : ℕ) (hk : k ≤ N) : (hPoly N * D).coeff k = A.coeff k := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    (∑ x ∈ Finset.range (k + 1), (hPoly N).coeff x * D.coeff (k - x))
        = ∑ x ∈ Finset.range (k + 1), hCoeff x * D.coeff (k - x) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxk : x ≤ k := Nat.le_of_lt_succ (by simpa using hx)
          rw [hPoly_coeff_of_le (le_trans hxk hk)]
    _ = A.coeff k := hCoeff_D_sum k

/-- Convolution of the `hCoeff` pattern with one factor of `D`. -/
theorem hCoeff_D_convolution (R : ℤ[X]) (N : ℕ) :
    (∑ i∈Finset.range (N+1), hCoeff i * (D*R).coeff (N-i)) = (A*R).coeff N := by
  calc
    (∑ i∈Finset.range (N+1), hCoeff i * (D*R).coeff (N-i))
        = (hPoly N * (D*R)).coeff N := by
          rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
          apply Finset.sum_congr rfl
          intro i hi
          have hiN : i ≤ N := Nat.le_of_lt_succ (by simpa using hi)
          rw [hPoly_coeff_of_le hiN]
    _ = ((hPoly N * D) * R).coeff N := by rw [mul_assoc]
    _ = (A*R).coeff N := by
          rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
          apply Finset.sum_congr rfl
          intro x hx
          have hxsum : x.1 + x.2 = N := Finset.mem_antidiagonal.mp hx
          have hxN : x.1 ≤ N := by omega
          rw [hPoly_mul_D_coeff N x.1 hxN]

lemma one_add_X_pow_p_eq_expand (p n : ℕ) :
    (1 + X ^ p : ℤ[X]) ^ n = Polynomial.expand ℤ p ((1 + X : ℤ[X]) ^ n) := by
  rw [map_pow]
  simp

lemma coeff_contract_mul_one_add_pow_eq_sum (p M n l : ℕ) (hp : p ≠ 0) (P : ℤ[X])
    (hdeg : P.natDegree ≤ p * l) :
    (Polynomial.contract p P * (1 + X : ℤ[X]) ^ n).coeff M =
      ∑ a ∈ Finset.range (l + 1), P.coeff (p * a) * beta n 0 M a := by
  classical
  let G : ℤ[X] := Polynomial.contract p P
  let f : ℕ → ℤ := fun a => G.coeff a * (if a ≤ M then ((n.choose (M - a) : ℤ)) else 0)
  have hleft : (G * (1 + X : ℤ[X]) ^ n).coeff M = ∑ a ∈ Finset.range (M + 1), f a := by
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro a ha
    have haM : a ≤ M := Nat.le_of_lt_succ (by simpa using ha)
    simp [f, haM, Polynomial.coeff_one_add_X_pow]
  have hzero_gt_l : ∀ a, l < a → G.coeff a = 0 := by
    intro a hla
    rw [show G.coeff a = P.coeff (a * p) by simpa [G] using Polynomial.coeff_contract hp P a]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    calc
      P.natDegree ≤ p * l := hdeg
      _ < p * a := Nat.mul_lt_mul_of_pos_left hla (Nat.pos_of_ne_zero hp)
      _ = a * p := Nat.mul_comm p a
  let B := Finset.range (Nat.max M l + 1)
  have hleftB : (∑ a ∈ Finset.range (M + 1), f a) = ∑ a ∈ B, f a := by
    apply Finset.sum_subset
    · intro x hx
      simp only [B, Finset.mem_range] at hx ⊢
      exact Nat.lt_succ_of_le (le_trans (Nat.le_of_lt_succ hx) (Nat.le_max_left M l))
    · intro a haB haM
      have hnot : ¬ a ≤ M := by
        intro h; exact haM (by simpa using Nat.lt_succ_of_le h)
      simp [f, hnot]
  have hrightB : (∑ a ∈ Finset.range (l + 1), f a) = ∑ a ∈ B, f a := by
    apply Finset.sum_subset
    · intro x hx
      simp only [B, Finset.mem_range] at hx ⊢
      exact Nat.lt_succ_of_le (le_trans (Nat.le_of_lt_succ hx) (Nat.le_max_right M l))
    · intro a haB hal
      have hla : l < a := Nat.lt_of_not_ge (by intro h; exact hal (by simpa using Nat.lt_succ_of_le h))
      simp [f, hzero_gt_l a hla]
  calc
    (G * (1 + X : ℤ[X]) ^ n).coeff M = ∑ a ∈ Finset.range (M + 1), f a := hleft
    _ = ∑ a ∈ Finset.range (l + 1), f a := by rw [hleftB, hrightB]
    _ = ∑ a ∈ Finset.range (l + 1), P.coeff (p * a) * beta n 0 M a := by
      apply Finset.sum_congr rfl
      intro a ha
      dsimp [f, G]
      rw [Polynomial.coeff_contract hp P a]
      rw [Nat.mul_comm a p]
      simp [beta]

lemma coeff_mul_one_add_X_pow_p_eq_sum (p M n l : ℕ) (hp : p ≠ 0) (P : ℤ[X])
    (hdeg : P.natDegree ≤ p * l) :
    (P * (1 + X ^ p : ℤ[X]) ^ n).coeff (p * M) =
      ∑ a ∈ Finset.range (l + 1), P.coeff (p * a) * beta n 0 M a := by
  have hcontract := coeff_contract_mul_one_add_pow_eq_sum p M n l hp P hdeg
  rw [← hcontract]
  rw [Nat.mul_comm p M]
  rw [← Polynomial.coeff_contract hp (P * (1 + X ^ p : ℤ[X]) ^ n) M]
  rw [one_add_X_pow_p_eq_expand]
  rw [Polynomial.contract_mul_expand hp]

/-- Bridge from the polynomial-level scaled correction to the closed scaled correction.
The degree hypothesis is exactly what permits truncating the coefficient sum to `range (l+1)`. -/
theorem CorrScaledPoly_eq_CorrScaled (p M T l : ℕ) (hl : 1 ≤ l) (S : ℤ[X])
    (hdeg : (A * D ^ (l - 1) * S ^ l).natDegree ≤ p * l) :
    CorrScaledPoly p M T l S = CorrScaled p M T l S := by
  classical
  by_cases hp0 : p = 0
  · subst p
    have hl0 : l ≠ 0 := by omega
    unfold CorrScaledPoly CorrScaled CorrUnscaled
    simp [zero_pow hl0]
  · let n := M * T - l
    let c : ℤ := ((M * T).choose l : ℤ)
    let P : ℤ[X] := A * D ^ (l - 1) * S ^ l
    let R : ℤ[X] := D ^ (l - 1) * S ^ l * (1 + X ^ p : ℤ[X]) ^ n * Polynomial.C c
    have hterm : ∀ i, ((((Polynomial.C (p : ℤ)) * D * S) ^ l *
          (1 + X ^ p : ℤ[X]) ^ n * Polynomial.C c).coeff (p * M - i)) =
        (p : ℤ) ^ l * (D * R).coeff (p * M - i) := by
      intro i
      have hpoly : ((Polynomial.C (p : ℤ)) * D * S) ^ l *
          (1 + X ^ p : ℤ[X]) ^ n * Polynomial.C c =
          Polynomial.C ((p : ℤ)^l) * (D * R) := by
        dsimp [R]
        rw [mul_pow, mul_pow]
        have hD : D ^ l = D * D ^ (l - 1) := by
          conv_lhs => rw [show l = (l - 1) + 1 by omega, pow_succ]
          ring
        rw [hD]
        simp
        ring_nf
      rw [hpoly]
      rw [Polynomial.coeff_C_mul]
    have hconvScaled : CorrScaledPoly p M T l S = (p : ℤ)^l * (A * R).coeff (p * M) := by
      unfold CorrScaledPoly
      simp_rw [show M * T - l = n by rfl]
      simp_rw [show ((M * T).choose l : ℤ) = c by rfl]
      simp_rw [hterm]
      calc
        (∑ i ∈ Finset.range (p * M + 1), hCoeff i * ((p : ℤ) ^ l * (D * R).coeff (p * M - i)))
            = (p : ℤ)^l * ∑ i ∈ Finset.range (p * M + 1), hCoeff i * (D * R).coeff (p * M - i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = (p : ℤ)^l * (A * R).coeff (p * M) := by
              rw [hCoeff_D_convolution R (p*M)]
    have hAR : (A * R).coeff (p * M) = c * (P * (1 + X ^ p : ℤ[X]) ^ n).coeff (p * M) := by
      dsimp [R, P]
      have hpoly : A * (D ^ (l - 1) * S ^ l * (1 + X ^ p : ℤ[X]) ^ n * Polynomial.C c) =
          Polynomial.C c * ((A * D ^ (l - 1) * S ^ l) * (1 + X ^ p : ℤ[X]) ^ n) := by
        ring
      rw [hpoly]
      simp
    have hp : p ≠ 0 := hp0
    have hcoeff := coeff_mul_one_add_X_pow_p_eq_sum p M n l hp P hdeg
    calc
      CorrScaledPoly p M T l S = (p : ℤ)^l * (A * R).coeff (p * M) := hconvScaled
      _ = (p : ℤ)^l * (c * (P * (1 + X ^ p : ℤ[X]) ^ n).coeff (p * M)) := by rw [hAR]
      _ = (p : ℤ)^l * (∑ a ∈ Finset.range (l + 1), P.coeff (p * a) * (c * beta n 0 M a)) := by
        rw [hcoeff]
        rw [Finset.mul_sum]
        apply congrArg ((HMul.hMul ((p : ℤ)^l)))
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = CorrScaled p M T l S := by
        unfold CorrScaled CorrUnscaled
        dsimp [P, c, n]
        apply congrArg ((HMul.hMul ((p : ℤ)^l)))
        apply Finset.sum_congr rfl
        intro a ha
        simp [beta]

end CorrBridgeTemp

/- copied DirectBseqCongruenceTemp.lean in a namespace for low-l lemmas -/
namespace LowAssembled

open scoped BigOperators
open Nat Finset BigOperators Int Polynomial
open Polynomial
open scoped Polynomial

/-- The target B-sequence coefficient pattern. -/
def hCoeff (i : ℕ) : ℤ := if i = 0 then 1 else if 3 ∣ i then 2 else -1

/-- The target B-sequence form. -/
def Bseq (s : ℤ) (N : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (N + 1), hCoeff i * Ring.choose (s * (N : ℤ)) (N - i)

namespace DirectBseqCongruenceTemp

/-- The beta coefficient from the coefficient extraction of the freshman correction terms. -/
def beta (N l M a : ℕ) : ℤ := if a ≤ M then ((N - l).choose (M - a) : ℤ) else 0

noncomputable def D : ℤ[X] := 1 + X + X^2
noncomputable def A : ℤ[X] := 1 - X^2
noncomputable def Rnum (p : ℕ) : ℤ[X] := (1 + X)^p - 1 - X^p

/-- For primes `p ≥ 5`, prime scaling preserves the `hCoeff` pattern, since such a
prime is not divisible by `3`.  This is the coefficient fact needed for the `l = 0`
term in the freshman expansion. -/
theorem hCoeff_mul_prime_left_eq {p a : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    hCoeff (p * a) = hCoeff a := by
  by_cases ha : a = 0
  · subst ha
    simp [hCoeff]
  · have hpa0 : p * a ≠ 0 := by
      exact Nat.mul_ne_zero (Nat.ne_of_gt hp.pos) ha
    have h3p_not : ¬ 3 ∣ p := by
      intro h3p
      have hpeq3 : p = 3 := (hp.dvd_iff_eq (by norm_num : (3 : ℕ) ≠ 1)).mp h3p
      omega
    have hiff : (3 ∣ p * a) ↔ (3 ∣ a) := by
      constructor
      · intro h
        rcases (Nat.prime_three.dvd_mul.mp h) with h3p | h3a
        · exact (h3p_not h3p).elim
        · exact h3a
      · intro h3a
        exact dvd_mul_of_dvd_right h3a p
    simp [hCoeff, ha, hpa0, hiff]

/-- Right-sided version of `hCoeff_mul_prime_left_eq`. -/
theorem hCoeff_mul_prime_right_eq {p a : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    hCoeff (a * p) = hCoeff a := by
  rw [Nat.mul_comm]
  exact hCoeff_mul_prime_left_eq (p := p) (a := a) hp hp5

lemma D_dvd_X3_sub_one : D ∣ (X^3 - 1 : ℤ[X]) := by
  use X - 1
  dsimp [D]
  ring

lemma one_add_X_congr : D ∣ ((1 + X : ℤ[X]) - (-X^2)) := by
  use 1
  dsimp [D]
  ring

lemma D_dvd_pow_congr (p : ℕ) : D ∣ ((1 + X : ℤ[X])^p - (-X^2)^p) := by
  exact (one_add_X_congr).trans ((Commute.all (1 + X : ℤ[X]) (-X^2)).sub_dvd_pow_sub_pow p)

lemma D_dvd_X_pow_sub_X_of_mod_eq_one {n : ℕ} (hn : n % 3 = 1) :
    D ∣ ((X : ℤ[X])^n - X) := by
  have h : ∃ q, n = 3 * q + 1 := by
    use n / 3
    omega
  rcases h with ⟨q, rfl⟩
  have hbase : D ∣ ((X^3 : ℤ[X]) - 1) := D_dvd_X3_sub_one
  have hpow : (X^3 : ℤ[X]) - 1 ∣ (X^3)^q - 1 := sub_one_dvd_pow_sub_one (X^3 : ℤ[X]) q
  have hdvd : D ∣ (X^3 : ℤ[X])^q - 1 := hbase.trans hpow
  have hmul : D ∣ (X : ℤ[X]) * ((X^3)^q - 1) := dvd_mul_of_dvd_right hdvd X
  convert hmul using 1
  ring

lemma D_dvd_X_pow_sub_X2_of_mod_eq_two {n : ℕ} (hn : n % 3 = 2) :
    D ∣ ((X : ℤ[X])^n - X^2) := by
  have h : ∃ q, n = 3 * q + 2 := by
    use n / 3
    omega
  rcases h with ⟨q, rfl⟩
  have hbase : D ∣ ((X^3 : ℤ[X]) - 1) := D_dvd_X3_sub_one
  have hpow : (X^3 : ℤ[X]) - 1 ∣ (X^3)^q - 1 := sub_one_dvd_pow_sub_one (X^3 : ℤ[X]) q
  have hdvd : D ∣ (X^3 : ℤ[X])^q - 1 := hbase.trans hpow
  have hmul : D ∣ (X^2 : ℤ[X]) * ((X^3)^q - 1) := dvd_mul_of_dvd_right hdvd (X^2 : ℤ[X])
  convert hmul using 1
  ring

lemma D_dvd_numerator_of_mod_one {p : ℕ} (hpodd : Odd p) (hpmod : p % 3 = 1) :
    D ∣ ((1 + X : ℤ[X])^p - 1 - X^p) := by
  have hmain := D_dvd_pow_congr p
  have hsign : (-X^2 : ℤ[X])^p = - X^(2 * p) := by
    rw [neg_pow]
    simp [hpodd.neg_one_pow, pow_mul]
  have hp2mod : (2 * p) % 3 = 2 := by omega
  have hxp := D_dvd_X_pow_sub_X_of_mod_eq_one (n := p) hpmod
  have hx2p := D_dvd_X_pow_sub_X2_of_mod_eq_two (n := 2 * p) hp2mod
  have htarget : D ∣ ((- X^(2 * p) - 1 - X^p) - (-(X^2) - 1 - X)) := by
    convert dvd_add (dvd_neg.mpr hx2p) (dvd_neg.mpr hxp) using 1; ring
  have hbase : D ∣ (-(X^2 : ℤ[X]) - 1 - X) := by
    use -1
    dsimp [D]
    ring
  have h2 : D ∣ (- X^(2 * p) - 1 - X^p : ℤ[X]) := by
    have := dvd_add htarget hbase
    convert this using 1; ring
  have h1 : D ∣ ((1 + X : ℤ[X])^p - (-X^2)^p) := hmain
  have hsum := dvd_add h1 h2
  rw [hsign] at hsum
  convert hsum using 1; ring

lemma D_dvd_numerator_of_mod_two {p : ℕ} (hpodd : Odd p) (hpmod : p % 3 = 2) :
    D ∣ ((1 + X : ℤ[X])^p - 1 - X^p) := by
  have hmain := D_dvd_pow_congr p
  have hsign : (-X^2 : ℤ[X])^p = - X^(2 * p) := by
    rw [neg_pow]
    simp [hpodd.neg_one_pow, pow_mul]
  have hp2mod : (2 * p) % 3 = 1 := by omega
  have hxp := D_dvd_X_pow_sub_X2_of_mod_eq_two (n := p) hpmod
  have hx2p := D_dvd_X_pow_sub_X_of_mod_eq_one (n := 2 * p) hp2mod
  have htarget : D ∣ ((- X^(2 * p) - 1 - X^p) - (-X - 1 - X^2)) := by
    convert dvd_add (dvd_neg.mpr hx2p) (dvd_neg.mpr hxp) using 1; ring
  have hbase : D ∣ (-X - 1 - X^2 : ℤ[X]) := by
    use -1
    dsimp [D]
    ring
  have h2 : D ∣ (- X^(2 * p) - 1 - X^p : ℤ[X]) := by
    have := dvd_add htarget hbase
    convert this using 1; ring
  have h1 : D ∣ ((1 + X : ℤ[X])^p - (-X^2)^p) := hmain
  have hsum := dvd_add h1 h2
  rw [hsign] at hsum
  convert hsum using 1; ring

/-- The freshman numerator `Rnum p = (1+X)^p - 1 - X^p` is divisible by
`D = 1 + X + X^2` for every prime `p ≥ 5`. -/
theorem D_dvd_Rnum_of_prime_ge_five {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    D ∣ Rnum p := by
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hpne3 : p % 3 ≠ 0 := by
    intro h0
    have h3dvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    have hpeq3 : p = 3 := (hp.dvd_iff_eq (by norm_num : (3 : ℕ) ≠ 1)).mp h3dvd
    omega
  have hmodlt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
  interval_cases h : p % 3
  · contradiction
  · simpa [Rnum] using D_dvd_numerator_of_mod_one hpodd h
  · simpa [Rnum] using D_dvd_numerator_of_mod_two hpodd h

/-- For primes `p ≥ 5`, choose a quotient `S` with `Rnum p = D*S`. -/
theorem exists_S_Rnum_eq_D_mul {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∃ S : ℤ[X], Rnum p = D * S := by
  simpa [dvd_def] using D_dvd_Rnum_of_prime_ge_five (p := p) hp hp5

/-- The unscaled correction coefficient.  This is the expression obtained from the
hypothesis `Rnum p = D*S`; there is **no** factor `(p : ℤ)^l`. -/
noncomputable def CorrUnscaled (p M T l : ℕ) (S : ℤ[X]) : ℤ :=
  ∑ a ∈ Finset.range (l + 1),
    (A * D ^ (l - 1) * S ^ l).coeff (p * a) *
      (((M * T).choose l : ℤ) * beta (M * T) l M a)

/-- The scaled correction coefficient.  This is the expression with the factor
`(p : ℤ)^l`; it corresponds to the scaled quotient hypothesis
`Rnum p = (Polynomial.C (p : ℤ)) * D * S`, not to `Rnum p = D*S`. -/
noncomputable def CorrScaled (p M T l : ℕ) (S : ℤ[X]) : ℤ :=
  (p : ℤ) ^ l * CorrUnscaled p M T l S

/-- If `S` is the unscaled quotient `Rnum p = D*S`, then the freshman identity is
`(1+X)^p = 1 + X^p + D*S`.  This is the source of correction terms with no
extra factor `(p : ℤ)^l`. -/
theorem freshman_step_unscaled {p : ℕ} {S : ℤ[X]} (hS : Rnum p = D * S) :
    (1 + X : ℤ[X]) ^ p = 1 + X ^ p + D * S := by
  have h : (1 + X : ℤ[X]) ^ p - 1 - X ^ p = D * S := by
    simpa [Rnum] using hS
  rw [← h]
  ring

/-- If `S` is the scaled quotient `Rnum p = p*D*S`, then the freshman identity is
`(1+X)^p = 1 + X^p + p*D*S`.  This is the source of the factors `(p : ℤ)^l`
in the correction expansion. -/
theorem freshman_step_scaled {p : ℕ} {S : ℤ[X]}
    (hS : Rnum p = (Polynomial.C (p : ℤ)) * D * S) :
    (1 + X : ℤ[X]) ^ p = 1 + X ^ p + (Polynomial.C (p : ℤ)) * D * S := by
  have h : (1 + X : ℤ[X]) ^ p - 1 - X ^ p = (Polynomial.C (p : ℤ)) * D * S := by
    simpa [Rnum] using hS
  rw [← h]
  ring

/-- Full binomial expansion from the unscaled quotient.  The `l`th freshman
correction polynomial contains `(D*S)^l`, hence no standalone factor `p^l`. -/
theorem freshman_full_expansion_unscaled (p M T : ℕ) {S : ℤ[X]}
    (hS : Rnum p = D * S) :
    (1 + X : ℤ[X]) ^ (p * (M * T)) =
      ∑ l ∈ Finset.range (M * T + 1),
        (D * S) ^ l * (1 + X ^ p : ℤ[X]) ^ (M * T - l) *
          Polynomial.C ((M * T).choose l : ℤ) := by
  let N := M * T
  calc
    (1 + X : ℤ[X]) ^ (p * (M * T)) = ((1 + X : ℤ[X]) ^ p) ^ (M * T) := by
      rw [pow_mul]
    _ = (D * S + (1 + X ^ p : ℤ[X])) ^ (M * T) := by
      rw [freshman_step_unscaled (p := p) (S := S) hS]
      ring
    _ = ∑ l ∈ Finset.range (M * T + 1),
        (D * S) ^ l * (1 + X ^ p : ℤ[X]) ^ (M * T - l) *
          Polynomial.C ((M * T).choose l : ℤ) := by
      simpa using add_pow (D * S) (1 + X ^ p : ℤ[X]) (M * T)

/-- Full binomial expansion from the scaled quotient.  The `l`th freshman
correction polynomial contains `((p : ℤ[X])*D*S)^l`; this is where the factor
`(p : ℤ)^l` in `CorrScaled` comes from after taking coefficients. -/
theorem freshman_full_expansion_scaled (p M T : ℕ) {S : ℤ[X]}
    (hS : Rnum p = (Polynomial.C (p : ℤ)) * D * S) :
    (1 + X : ℤ[X]) ^ (p * (M * T)) =
      ∑ l ∈ Finset.range (M * T + 1),
        ((Polynomial.C (p : ℤ)) * D * S) ^ l *
          (1 + X ^ p : ℤ[X]) ^ (M * T - l) *
            Polynomial.C ((M * T).choose l : ℤ) := by
  calc
    (1 + X : ℤ[X]) ^ (p * (M * T)) = ((1 + X : ℤ[X]) ^ p) ^ (M * T) := by
      rw [pow_mul]
    _ = ((Polynomial.C (p : ℤ)) * D * S + (1 + X ^ p : ℤ[X])) ^ (M * T) := by
      rw [freshman_step_scaled (p := p) (S := S) hS]
      ring
    _ = ∑ l ∈ Finset.range (M * T + 1),
        ((Polynomial.C (p : ℤ)) * D * S) ^ l *
          (1 + X ^ p : ℤ[X]) ^ (M * T - l) *
            Polynomial.C ((M * T).choose l : ℤ) := by
      simpa using add_pow ((Polynomial.C (p : ℤ)) * D * S) (1 + X ^ p : ℤ[X]) (M * T)

/-- Pulling the scalar `(p : ℤ)^l` out of the scaled `l`th correction polynomial.
This algebraic normalization is the formal reason that `CorrScaled` is the right
coefficient expression under `Rnum p = p*D*S`. -/
theorem scaled_correction_factor (p l : ℕ) (S : ℤ[X]) :
    ((Polynomial.C (p : ℤ)) * D * S) ^ l =
      Polynomial.C ((p : ℤ) ^ l) * (D ^ l * S ^ l) := by
  rw [mul_pow, mul_pow]
  simp
  ring


/-- Sampling every `p`-th coefficient of an anti-palindromic polynomial gives an
anti-palindromic coefficient sequence on `0, ..., l`. -/
lemma sampled_coeff_anti_pal {p l : ℕ} {P : ℤ[X]}
    (hantiP : P.reflect (p * l) = -P) :
    ∀ a, a ≤ l → P.coeff (p * (l - a)) = -P.coeff (p * a) := by
  intro a ha
  have hpa : p * a ≤ p * l := Nat.mul_le_mul_left p ha
  have hcoeff : (P.reflect (p * l)).coeff (p * a) = (-P).coeff (p * a) := by
    simpa using congrArg (fun Q : ℤ[X] => Q.coeff (p * a)) hantiP
  rw [Polynomial.coeff_reflect, Polynomial.revAt_le hpa] at hcoeff
  have hsub : p * l - p * a = p * (l - a) := by rw [← Nat.mul_sub_left_distrib]
  simpa [hsub] using hcoeff

/-- The last sampled coefficient is zero for an anti-palindromic polynomial with zero
constant coefficient. -/
lemma sampled_coeff_last_zero {p l : ℕ} {P : ℤ[X]}
    (hantiP : P.reflect (p * l) = -P) (h0 : P.coeff 0 = 0) :
    P.coeff (p * l) = 0 := by
  have hcoeff : (P.reflect (p * l)).coeff 0 = (-P).coeff 0 := by
    simpa using congrArg (fun Q : ℤ[X] => Q.coeff 0) hantiP
  rw [Polynomial.coeff_reflect, Polynomial.revAt_zero] at hcoeff
  simpa [h0] using hcoeff

/-- A purely formal low-degree anti-palindromic endpoint lemma: if `P` is
anti-palindromic about degree `p*1` and has zero constant coefficient, then every
weighted sampled sum over `a=0,1` vanishes. -/
theorem sampled_coeff_weighted_sum_l_one_eq_zero {p : ℕ} {P : ℤ[X]} (w : ℕ → ℤ)
    (hantiP : P.reflect (p * 1) = -P) (h0 : P.coeff 0 = 0) :
    (∑ a ∈ Finset.range (1 + 1), P.coeff (p * a) * w a) = 0 := by
  have h0s : P.coeff (p * 0) = 0 := by simpa using h0
  have h1s : P.coeff (p * 1) = 0 := by
    simpa using sampled_coeff_last_zero (p := p) (l := 1) (P := P) hantiP h0
  apply Finset.sum_eq_zero
  intro a ha
  have ha_lt : a < 2 := by simpa using Finset.mem_range.mp ha
  have hcases : a = 0 ∨ a = 1 := by omega
  rcases hcases with rfl | rfl
  · rw [h0s]
    simp
  · rw [h1s]
    simp

/-- A purely formal low-degree anti-palindromic endpoint lemma: if `P` is
anti-palindromic about degree `p*2` and has zero constant coefficient, then every
weighted sampled sum over `a=0,1,2` vanishes.  The middle sampled coefficient is
zero because it is equal to its own negative. -/
theorem sampled_coeff_weighted_sum_l_two_eq_zero {p : ℕ} {P : ℤ[X]} (w : ℕ → ℤ)
    (hantiP : P.reflect (p * 2) = -P) (h0 : P.coeff 0 = 0) :
    (∑ a ∈ Finset.range (2 + 1), P.coeff (p * a) * w a) = 0 := by
  have h0s : P.coeff (p * 0) = 0 := by simpa using h0
  have h2s : P.coeff (p * 2) = 0 := by
    simpa using sampled_coeff_last_zero (p := p) (l := 2) (P := P) hantiP h0
  have hmid_sym : P.coeff (p * (2 - 1)) = -P.coeff (p * 1) :=
    sampled_coeff_anti_pal (p := p) (l := 2) (P := P) hantiP 1 (by norm_num)
  have h1s_self : P.coeff (p * 1) = -P.coeff (p * 1) := by
    simpa using hmid_sym
  have h1s : P.coeff (p * 1) = 0 := by omega
  apply Finset.sum_eq_zero
  intro a ha
  have ha_lt : a < 3 := by simpa using Finset.mem_range.mp ha
  have hcases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · rw [h0s]
    simp
  · rw [h1s]
    simp
  · rw [h2s]
    simp

/-- The `l = 1` freshman correction coefficient sum is exactly zero, assuming the
standard anti-palindromicity and zero-constant facts for
`P = A * D^(l-1) * S^l`. -/
theorem freshman_coeff_l_one_sum_eq_zero_of_antipal {p M T : ℕ} {S : ℤ[X]}
    (hanti : ((A * D ^ (1 - 1) * S ^ 1).reflect (p * 1)) = -(A * D ^ (1 - 1) * S ^ 1))
    (h0 : (A * D ^ (1 - 1) * S ^ 1).coeff 0 = 0) :
    (∑ a ∈ Finset.range (1 + 1),
        (A * D ^ (1 - 1) * S ^ 1).coeff (p * a) *
          (((M * T).choose 1 : ℤ) * beta (M * T) 1 M a)) = 0 := by
  exact sampled_coeff_weighted_sum_l_one_eq_zero
    (p := p) (P := A * D ^ (1 - 1) * S ^ 1)
    (fun a => (((M * T).choose 1 : ℤ) * beta (M * T) 1 M a)) hanti h0

/-- The `l = 2` freshman correction coefficient sum is exactly zero, assuming the
standard anti-palindromicity and zero-constant facts for
`P = A * D^(l-1) * S^l`. -/
theorem freshman_coeff_l_two_sum_eq_zero_of_antipal {p M T : ℕ} {S : ℤ[X]}
    (hanti : ((A * D ^ (2 - 1) * S ^ 2).reflect (p * 2)) = -(A * D ^ (2 - 1) * S ^ 2))
    (h0 : (A * D ^ (2 - 1) * S ^ 2).coeff 0 = 0) :
    (∑ a ∈ Finset.range (2 + 1),
        (A * D ^ (2 - 1) * S ^ 2).coeff (p * a) *
          (((M * T).choose 2 : ℤ) * beta (M * T) 2 M a)) = 0 := by
  exact sampled_coeff_weighted_sum_l_two_eq_zero
    (p := p) (P := A * D ^ (2 - 1) * S ^ 2)
    (fun a => (((M * T).choose 2 : ℤ) * beta (M * T) 2 M a)) hanti h0

/-- Divisibility form of the vanishing `l = 1` freshman correction term. -/
theorem freshman_coeff_l_one_term_dvd_of_antipal {p e M T : ℕ} {S : ℤ[X]}
    (hanti : ((A * D ^ (1 - 1) * S ^ 1).reflect (p * 1)) = -(A * D ^ (1 - 1) * S ^ 1))
    (h0 : (A * D ^ (1 - 1) * S ^ 1).coeff 0 = 0) :
    (p : ℤ) ^ (3 * e + 3) ∣ (p : ℤ) ^ 1 *
      (∑ a ∈ Finset.range (1 + 1),
        (A * D ^ (1 - 1) * S ^ 1).coeff (p * a) *
          (((M * T).choose 1 : ℤ) * beta (M * T) 1 M a)) := by
  rw [freshman_coeff_l_one_sum_eq_zero_of_antipal (p := p) (M := M) (T := T) (S := S) hanti h0]
  simp

/-- Divisibility form of the vanishing `l = 2` freshman correction term. -/
theorem freshman_coeff_l_two_term_dvd_of_antipal {p e M T : ℕ} {S : ℤ[X]}
    (hanti : ((A * D ^ (2 - 1) * S ^ 2).reflect (p * 2)) = -(A * D ^ (2 - 1) * S ^ 2))
    (h0 : (A * D ^ (2 - 1) * S ^ 2).coeff 0 = 0) :
    (p : ℤ) ^ (3 * e + 3) ∣ (p : ℤ) ^ 2 *
      (∑ a ∈ Finset.range (2 + 1),
        (A * D ^ (2 - 1) * S ^ 2).coeff (p * a) *
          (((M * T).choose 2 : ℤ) * beta (M * T) 2 M a)) := by
  rw [freshman_coeff_l_two_sum_eq_zero_of_antipal (p := p) (M := M) (T := T) (S := S) hanti h0]
  simp

end DirectBseqCongruenceTemp

end LowAssembled

open scoped BigOperators
open Polynomial Finset
open scoped Polynomial

namespace DirectStepAssembledTemp

private lemma sum_erase_zero_sub_singleton_dvd {α : Type*} [DecidableEq α]
    (s : Finset α) (z : α) (f : α → ℤ) {d : ℤ}
    (hz : z ∈ s) (hdiv : ∀ x ∈ s.erase z, d ∣ f x) :
    d ∣ (∑ x ∈ s, f x) - f z := by
  classical
  have hsum : (∑ x ∈ s, f x) = f z + ∑ x ∈ s.erase z, f x := by
    rw [← Finset.sum_insert (s := s.erase z) (a := z)]
    · congr
      exact (Finset.insert_erase hz).symm
    · simp
  rw [hsum]
  simp only [add_sub_cancel_left]
  exact Finset.dvd_sum (fun x hx => hdiv x hx)

private lemma direct_corr_zero_eq (p M T : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (S : ℤ[X]) :
    DirectBseqCongruenceTemp2.CorrScaledPoly p M T 0 S = Bseq (T : ℤ) M := by
  simpa [DirectBseqCongruenceTemp2.CorrScaledPoly, CorrZeroAssembled.CorrScaledPoly,
    DirectBseqCongruenceTemp2.D, CorrZeroAssembled.D,
    hCoeff, CorrZeroAssembled.hCoeff, Bseq, CorrZeroAssembled.Bseq] using
    (CorrZeroAssembled.CorrScaledPoly_zero_eq_Bseq p M T hp hp5 S)

private lemma direct_bridge_eq (p M T l : ℕ) (hl : 1 ≤ l) (S : ℤ[X])
    (hdeg : (CorrBridgeTemp.A * CorrBridgeTemp.D ^ (l - 1) * S ^ l).natDegree ≤ p * l) :
    DirectBseqCongruenceTemp2.CorrScaledPoly p M T l S =
      DirectBseqCongruenceTemp2.CorrScaled p M T l S := by
  have h := CorrBridgeTemp.CorrScaledPoly_eq_CorrScaled p M T l hl S hdeg
  simpa [DirectBseqCongruenceTemp2.CorrScaledPoly, DirectBseqCongruenceTemp2.CorrScaled,
    DirectBseqCongruenceTemp2.CorrUnscaled, DirectBseqCongruenceTemp2.D,
    DirectBseqCongruenceTemp2.A, DirectBseqCongruenceTemp2.beta,
    CorrBridgeTemp.CorrScaledPoly, CorrBridgeTemp.CorrScaled, CorrBridgeTemp.CorrUnscaled,
    CorrBridgeTemp.D, CorrBridgeTemp.A, CorrBridgeTemp.beta,
    hCoeff, CorrBridgeTemp.hCoeff] using h

private lemma direct_scaled_term_dvd
    {p e M T l : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hlpos : 1 ≤ l)
    (hMpos : 0 < M) (hT : 2 ≤ T) (hM : p^e ∣ M)
    {S : ℤ[X]} (hS : DirectBseqCongruenceTemp2.Rnum p = Polynomial.C (p : ℤ) * DirectBseqCongruenceTemp2.D * S) :
    (p : ℤ)^(3*e+3) ∣ DirectBseqCongruenceTemp2.CorrScaled p M T l S := by
  have hS_scaled : ScaledFreshmanCoeffPadicTemp.Rnum p =
      Polynomial.C (p : ℤ) * ScaledFreshmanCoeffPadicTemp.D * S := by
    simpa [DirectBseqCongruenceTemp2.Rnum, DirectBseqCongruenceTemp2.D,
      ScaledFreshmanCoeffPadicTemp.Rnum, ScaledFreshmanCoeffPadicTemp.D] using hS
  have hS_quot : ScaledQuotientTemp.Rnum p =
      Polynomial.C (p : ℤ) * ScaledQuotientTemp.D * S := by
    simpa [ScaledFreshmanCoeffPadicTemp.Rnum, ScaledFreshmanCoeffPadicTemp.D,
      ScaledQuotientTemp.Rnum, ScaledQuotientTemp.D] using hS_scaled
  by_cases hl1 : l = 1
  · subst l
    have hantiQ : (ScaledQuotientTemp.A * ScaledQuotientTemp.D ^ (1 - 1) * S ^ 1).reflect (p * 1) =
        -(ScaledQuotientTemp.A * ScaledQuotientTemp.D ^ (1 - 1) * S ^ 1) :=
      ScaledQuotientTemp.scaled_P_reflect_eq_neg hp hp5 (by norm_num) hS_quot
    have hanti : (LowAssembled.DirectBseqCongruenceTemp.A *
          LowAssembled.DirectBseqCongruenceTemp.D ^ (1 - 1) * S ^ 1).reflect (p * 1) =
        -(LowAssembled.DirectBseqCongruenceTemp.A *
          LowAssembled.DirectBseqCongruenceTemp.D ^ (1 - 1) * S ^ 1) := by
      simpa [LowAssembled.DirectBseqCongruenceTemp.A, LowAssembled.DirectBseqCongruenceTemp.D,
        ScaledQuotientTemp.A, ScaledQuotientTemp.D] using hantiQ
    have h0S : (ScaledFreshmanCoeffPadicTemp.A * ScaledFreshmanCoeffPadicTemp.D ^ (1 - 1) * S ^ 1).coeff 0 = 0 :=
      ScaledFreshmanCoeffPadicTemp.scaled_P_coeff_zero hp (by norm_num) hS_scaled
    have h0 : (LowAssembled.DirectBseqCongruenceTemp.A *
          LowAssembled.DirectBseqCongruenceTemp.D ^ (1 - 1) * S ^ 1).coeff 0 = 0 := by
      simpa [LowAssembled.DirectBseqCongruenceTemp.A, LowAssembled.DirectBseqCongruenceTemp.D,
        ScaledFreshmanCoeffPadicTemp.A, ScaledFreshmanCoeffPadicTemp.D] using h0S
    have hlow := LowAssembled.DirectBseqCongruenceTemp.freshman_coeff_l_one_term_dvd_of_antipal
      (p := p) (e := e) (M := M) (T := T) (S := S) hanti h0
    simpa [DirectBseqCongruenceTemp2.CorrScaled, DirectBseqCongruenceTemp2.CorrUnscaled,
      DirectBseqCongruenceTemp2.A, DirectBseqCongruenceTemp2.D, DirectBseqCongruenceTemp2.beta,
      LowAssembled.DirectBseqCongruenceTemp.A, LowAssembled.DirectBseqCongruenceTemp.D,
      LowAssembled.DirectBseqCongruenceTemp.beta] using hlow
  · by_cases hl2 : l = 2
    · subst l
      have hantiQ : (ScaledQuotientTemp.A * ScaledQuotientTemp.D ^ (2 - 1) * S ^ 2).reflect (p * 2) =
          -(ScaledQuotientTemp.A * ScaledQuotientTemp.D ^ (2 - 1) * S ^ 2) :=
        ScaledQuotientTemp.scaled_P_reflect_eq_neg hp hp5 (by norm_num) hS_quot
      have hanti : (LowAssembled.DirectBseqCongruenceTemp.A *
            LowAssembled.DirectBseqCongruenceTemp.D ^ (2 - 1) * S ^ 2).reflect (p * 2) =
          -(LowAssembled.DirectBseqCongruenceTemp.A *
            LowAssembled.DirectBseqCongruenceTemp.D ^ (2 - 1) * S ^ 2) := by
        simpa [LowAssembled.DirectBseqCongruenceTemp.A, LowAssembled.DirectBseqCongruenceTemp.D,
          ScaledQuotientTemp.A, ScaledQuotientTemp.D] using hantiQ
      have h0S : (ScaledFreshmanCoeffPadicTemp.A * ScaledFreshmanCoeffPadicTemp.D ^ (2 - 1) * S ^ 2).coeff 0 = 0 :=
        ScaledFreshmanCoeffPadicTemp.scaled_P_coeff_zero hp (by norm_num) hS_scaled
      have h0 : (LowAssembled.DirectBseqCongruenceTemp.A *
            LowAssembled.DirectBseqCongruenceTemp.D ^ (2 - 1) * S ^ 2).coeff 0 = 0 := by
        simpa [LowAssembled.DirectBseqCongruenceTemp.A, LowAssembled.DirectBseqCongruenceTemp.D,
          ScaledFreshmanCoeffPadicTemp.A, ScaledFreshmanCoeffPadicTemp.D] using h0S
      have hlow := LowAssembled.DirectBseqCongruenceTemp.freshman_coeff_l_two_term_dvd_of_antipal
        (p := p) (e := e) (M := M) (T := T) (S := S) hanti h0
      simpa [DirectBseqCongruenceTemp2.CorrScaled, DirectBseqCongruenceTemp2.CorrUnscaled,
        DirectBseqCongruenceTemp2.A, DirectBseqCongruenceTemp2.D, DirectBseqCongruenceTemp2.beta,
        LowAssembled.DirectBseqCongruenceTemp.A, LowAssembled.DirectBseqCongruenceTemp.D,
        LowAssembled.DirectBseqCongruenceTemp.beta] using hlow
    · have hl3 : 3 ≤ l := by omega
      have hpadic := ScaledFreshmanCoeffPadicTemp.scaled_freshman_coeff_padic_dvd
        (p := p) (l := l) (e := e) (M := M) (T := T)
        hp hp5 hl3 hMpos hT hM (S := S) hS_scaled
      simpa [DirectBseqCongruenceTemp2.CorrScaled, DirectBseqCongruenceTemp2.CorrUnscaled,
        DirectBseqCongruenceTemp2.A, DirectBseqCongruenceTemp2.D, DirectBseqCongruenceTemp2.beta,
        ScaledFreshmanCoeffPadicTemp.A, ScaledFreshmanCoeffPadicTemp.D,
        ScaledFreshmanCoeffPadicTemp.beta, BetaYpairTemp.beta] using hpadic

private lemma direct_scaled_poly_term_dvd
    {p e M T l : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hlpos : 1 ≤ l)
    (hMpos : 0 < M) (hT : 2 ≤ T) (hM : p^e ∣ M)
    {S : ℤ[X]} (hS : DirectBseqCongruenceTemp2.Rnum p = Polynomial.C (p : ℤ) * DirectBseqCongruenceTemp2.D * S) :
    (p : ℤ)^(3*e+3) ∣ DirectBseqCongruenceTemp2.CorrScaledPoly p M T l S := by
  have hS_scaled : ScaledFreshmanCoeffPadicTemp.Rnum p =
      Polynomial.C (p : ℤ) * ScaledFreshmanCoeffPadicTemp.D * S := by
    simpa [DirectBseqCongruenceTemp2.Rnum, DirectBseqCongruenceTemp2.D,
      ScaledFreshmanCoeffPadicTemp.Rnum, ScaledFreshmanCoeffPadicTemp.D] using hS
  have hdegS := ScaledFreshmanCoeffPadicTemp.scaled_P_natDegree_le
    (p := p) (l := l) hp hp5 hlpos (S := S) hS_scaled
  have hdegB : (CorrBridgeTemp.A * CorrBridgeTemp.D ^ (l - 1) * S ^ l).natDegree ≤ p * l := by
    simpa [CorrBridgeTemp.A, CorrBridgeTemp.D,
      ScaledFreshmanCoeffPadicTemp.A, ScaledFreshmanCoeffPadicTemp.D] using hdegS
  rw [direct_bridge_eq p M T l hlpos S hdegB]
  exact direct_scaled_term_dvd hp hp5 hlpos hMpos hT hM hS

/-- Direct assembled B-sequence step, proved for the nontrivial range `2 ≤ T`. -/
theorem Bseq_nat_step_dvd
    {p e M T : ℕ} (hp : p.Prime) (hp5 : 5≤p) (hT : 2≤T)
    (hMpos : 0<M) (hM : p^e ∣ M) :
    (p:ℤ)^(3*e+3) ∣ Bseq (T:ℤ) (p*M) - Bseq (T:ℤ) M := by
  classical
  rcases ScaledQuotientTemp.exists_scaled_quotient_of_prime_ge_five hp hp5 with ⟨S, hSquot⟩
  have hS : DirectBseqCongruenceTemp2.Rnum p =
      Polynomial.C (p : ℤ) * DirectBseqCongruenceTemp2.D * S := by
    simpa [DirectBseqCongruenceTemp2.Rnum, DirectBseqCongruenceTemp2.D,
      ScaledQuotientTemp.Rnum, ScaledQuotientTemp.D] using hSquot
  let F : ℕ → ℤ := fun l => DirectBseqCongruenceTemp2.CorrScaledPoly p M T l S
  have hexp : Bseq (T : ℤ) (p * M) = ∑ l ∈ Finset.range (M * T + 1), F l := by
    simpa [F] using DirectBseqCongruenceTemp2.Bseq_nat_scaled_poly_expansion
      (p := p) (M := M) (T := T) (S := S) hS
  have hzero : F 0 = Bseq (T : ℤ) M := by
    simpa [F] using direct_corr_zero_eq p M T hp hp5 S
  rw [hexp, ← hzero]
  apply sum_erase_zero_sub_singleton_dvd (s := Finset.range (M * T + 1)) (z := 0) (f := F)
  · simp
  · intro l hl
    have hlmem : l ∈ Finset.range (M * T + 1) := by
      exact (Finset.mem_erase.mp hl).2
    have hlne : l ≠ 0 := by
      exact (Finset.mem_erase.mp hl).1
    have hlpos : 1 ≤ l := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hlne)
    exact direct_scaled_poly_term_dvd hp hp5 hlpos hMpos hT hM hS


end DirectStepAssembledTemp

/-- Global-name wrapper for the assembled direct B-sequence step, in the proven `2 ≤ T` range. -/
theorem Bseq_nat_step_dvd
    {p e M T : ℕ} (hp : p.Prime) (hp5 : 5≤p) (hT : 2≤T)
    (hMpos : 0<M) (hM : p^e ∣ M) :
    (p:ℤ)^(3*e+3) ∣ Bseq (T:ℤ) (p*M) - Bseq (T:ℤ) M :=
  DirectStepAssembledTemp.Bseq_nat_step_dvd hp hp5 hT hMpos hM



/- Small-`T` exact steps and the finite-difference `Cseq` step. -/

lemma Bseq_zero_eq_hCoeff (N : ℕ) : Bseq (0 : ℤ) N = hCoeff N := by
  classical
  unfold Bseq
  rw [Finset.sum_eq_single N]
  · simp
  · intro b hb hbN
    have hb_le : b ≤ N := Nat.le_of_lt_succ (by simpa using hb)
    have hpos : 0 < N - b := Nat.sub_pos_of_lt (lt_of_le_of_ne hb_le hbN)
    have hchoose : Ring.choose (0 : ℤ) (N - b) = 0 := by
      exact Ring.choose_zero_pos ℤ hpos
    simp [hchoose]
  · intro hnot
    exfalso
    exact hnot (by simp)

/-- The `s=0` small-`T` step is exact. -/
theorem Bseq_zero_step_eq (p M : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Bseq (0:ℤ) (p*M) = Bseq (0:ℤ) M := by
  rw [Bseq_zero_eq_hCoeff, Bseq_zero_eq_hCoeff]
  exact DirectBseqCongruenceTemp2.hCoeff_mul_prime_left_eq (p := p) (a := M) hp hp5

/-- Binomial transform of the shifted `hCoeff` sequence. -/
def B1shift (k N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (N + 1), hCoeff (j + k) * (Nat.choose N j : ℤ)

lemma Bseq_one_eq_B1shift_zero (N : ℕ) : Bseq (1 : ℤ) N = B1shift 0 N := by
  classical
  unfold Bseq B1shift
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : i ≤ N := Nat.le_of_lt_succ (by simpa using hi)
  have harg : (1 : ℤ) * (N : ℤ) = (N : ℤ) := by ring
  rw [harg, Ring.choose_natCast]
  have hsymm : Nat.choose N (N - i) = Nat.choose N i := Nat.choose_symm hiN
  rw [hsymm]
  simp

lemma hCoeff_rec (n : ℕ) : hCoeff (n+3) + hCoeff (n+2) + hCoeff (n+1) = 0 := by
  have hlt : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  interval_cases h : n % 3 <;>
    simp [hCoeff, Nat.dvd_iff_mod_eq_zero] <;> omega

lemma hCoeff_pair_sum (j : ℕ) :
    hCoeff (j + 1) + hCoeff (j + 2) = - hCoeff j - if j = 0 then 1 else 0 := by
  by_cases hj : j = 0
  · subst hj
    norm_num [hCoeff]
  · have hrec := hCoeff_rec (j - 1)
    have h0 : j - 1 + 3 = j + 2 := by omega
    have h1 : j - 1 + 2 = j + 1 := by omega
    have h2 : j - 1 + 1 = j := by omega
    have hsum : hCoeff (j + 2) + hCoeff (j + 1) + hCoeff j = 0 := by
      simpa [h0, h1, h2] using hrec
    rw [if_neg hj]
    omega

lemma B1shift_pair_sum (N : ℕ) :
    B1shift 1 N + B1shift 2 N = - B1shift 0 N - 1 := by
  classical
  unfold B1shift
  rw [← Finset.sum_add_distrib]
  calc
    (∑ x ∈ Finset.range (N + 1),
        (hCoeff (x + 1) * (Nat.choose N x : ℤ) +
          hCoeff (x + 2) * (Nat.choose N x : ℤ)))
        = ∑ x ∈ Finset.range (N + 1),
            (hCoeff (x + 1) + hCoeff (x + 2)) * (Nat.choose N x : ℤ) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
    _ = ∑ x ∈ Finset.range (N + 1),
          (- hCoeff x - if x = 0 then 1 else 0) * (Nat.choose N x : ℤ) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hCoeff_pair_sum x]
    _ = ∑ x ∈ Finset.range (N + 1),
          (- hCoeff x * (Nat.choose N x : ℤ) -
            (if x = 0 then 1 else 0 : ℤ) * (Nat.choose N x : ℤ)) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
    _ = (∑ x ∈ Finset.range (N + 1), - hCoeff x * (Nat.choose N x : ℤ)) - 1 := by
            rw [Finset.sum_sub_distrib]
            have hone : (∑ x ∈ Finset.range (N + 1),
                (if x = 0 then 1 else 0 : ℤ) * (Nat.choose N x : ℤ)) = 1 := by
              rw [Finset.sum_eq_single 0]
              · simp
              · intro b hb hb0
                simp [if_neg hb0]
              · intro hnot
                exfalso
                exact hnot (by simp)
            rw [hone]
    _ = - (∑ x ∈ Finset.range (N + 1), hCoeff x * (Nat.choose N x : ℤ)) - 1 := by
            congr 1
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro x hx
            ring

lemma B1shift_succ (k N : ℕ) : B1shift k (N + 1) = B1shift k N + B1shift (k + 1) N := by
  classical
  unfold B1shift
  have h := Finset.sum_choose_succ_mul (R := ℤ) (fun i _ => hCoeff (i + k)) N
  simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using h

lemma B1shift_zero_rec (N : ℕ) :
    B1shift 0 (N + 2) = B1shift 0 (N + 1) - B1shift 0 N - 1 := by
  calc
    B1shift 0 (N + 2) = B1shift 0 (N + 1) + B1shift 1 (N + 1) := by
      simpa using B1shift_succ 0 (N + 1)
    _ = B1shift 0 (N + 1) + (B1shift 1 N + B1shift 2 N) := by
      rw [B1shift_succ 1 N]
    _ = B1shift 0 (N + 1) - B1shift 0 N - 1 := by
      rw [B1shift_pair_sum N]
      ring

lemma B1shift_zero_period_six (N : ℕ) : B1shift 0 (N + 6) = B1shift 0 N := by
  have h2 := B1shift_zero_rec N
  have h3 := B1shift_zero_rec (N + 1)
  have h4 := B1shift_zero_rec (N + 2)
  have h5 := B1shift_zero_rec (N + 3)
  have h6 := B1shift_zero_rec (N + 4)
  rw [show N + 6 = N + 4 + 2 by omega]
  rw [h6, h5, h4, h3, h2]
  ring

lemma B1shift_zero_add_six_mul (N k : ℕ) : B1shift 0 (N + 6 * k) = B1shift 0 N := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc]
      calc
        B1shift 0 (N + 6 * k + 6) = B1shift 0 (N + 6 * k) := B1shift_zero_period_six _
        _ = B1shift 0 N := ih

lemma B1shift_zero_mod_eq (N : ℕ) : B1shift 0 N = B1shift 0 (N % 6) := by
  have h := B1shift_zero_add_six_mul (N % 6) (N / 6)
  have hN : N % 6 + 6 * (N / 6) = N := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div N 6)
  calc
    B1shift 0 N = B1shift 0 (N % 6 + 6 * (N / 6)) := by rw [hN]
    _ = B1shift 0 (N % 6) := h

lemma B1shift_zero_mul_prime_eq (p M : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    B1shift 0 (p * M) = B1shift 0 M := by
  have hp2mod : p % 2 ≠ 0 := by
    intro h
    have h2dvd : 2 ∣ p := Nat.dvd_of_mod_eq_zero h
    have hp_eq_two : p = 2 := (hp.dvd_iff_eq (by norm_num : (2 : ℕ) ≠ 1)).mp h2dvd
    omega
  have hp3mod : p % 3 ≠ 0 := by
    intro h
    have h3dvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have hp_eq_three : p = 3 := (hp.dvd_iff_eq (by norm_num : (3 : ℕ) ≠ 1)).mp h3dvd
    omega
  have hpmod : p % 6 = 1 ∨ p % 6 = 5 := by
    omega
  have hmulmod : (p * M) % 6 = ((p % 6) * (M % 6)) % 6 := by
    exact Nat.mul_mod p M 6
  rw [B1shift_zero_mod_eq (p * M), B1shift_zero_mod_eq M, hmulmod]
  rcases hpmod with hpmod | hpmod <;>
    rw [hpmod] <;>
    have hMlt : M % 6 < 6 := Nat.mod_lt M (by norm_num) <;>
    interval_cases hM : M % 6 <;>
    norm_num [B1shift, hCoeff, Finset.sum_range_succ, Nat.choose]

/-- The `s=1` small-`T` step is exact. -/
theorem Bseq_one_step_eq (p M : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Bseq (1:ℤ) (p*M) = Bseq (1:ℤ) M := by
  rw [Bseq_one_eq_B1shift_zero, Bseq_one_eq_B1shift_zero]
  exact B1shift_zero_mul_prime_eq p M hp hp5

/-- Explicit finite-difference coefficient at the origin. -/
def newtonCoeff (f : ℤ → ℤ) (r : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (r + 1),
    (-1 : ℤ) ^ (r - j) * (Nat.choose r j : ℤ) * f (j : ℤ)

/-- The finite-difference coefficients for `Bseq`. -/
def Cseq (r N : ℕ) : ℤ := newtonCoeff (fun s : ℤ => Bseq s N) r

/-- The finite-difference coefficients inherit the prime step congruence termwise. -/
theorem Cseq_step_dvd {p e M r : ℕ} (hp:p.Prime) (hp5:5≤p)
    (hMpos:0<M) (hM:p^e ∣ M) :
  (p:ℤ)^(3*e+3) ∣ Cseq r (p*M) - Cseq r M := by
  classical
  unfold Cseq newtonCoeff
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro j hj
  rw [← mul_sub]
  apply Int.dvd_mul_of_dvd_right
  by_cases hj0 : j = 0
  · subst hj0
    have hdiv : (p:ℤ)^(3*e+3) ∣ Bseq (0:ℤ) (p*M) - Bseq (0:ℤ) M := by
      rw [Bseq_zero_step_eq p M hp hp5]
      simp
    simpa using hdiv
  · by_cases hj1 : j = 1
    · subst hj1
      have hdiv : (p:ℤ)^(3*e+3) ∣ Bseq (1:ℤ) (p*M) - Bseq (1:ℤ) M := by
        rw [Bseq_one_step_eq p M hp hp5]
        simp
      simpa using hdiv
    · have hT : 2 ≤ j := by omega
      exact Bseq_nat_step_dvd (p := p) (e := e) (M := M) (T := j) hp hp5 hT hMpos hM


/- Newton expansion and all-integer B-sequence step. -/

open Nat Finset BigOperators Int Polynomial
open scoped fwdDiff

lemma fwdDiff_eq_zero_const (f : ℤ → ℤ) (h : fwdDiff (1 : ℤ) f = 0) (s : ℤ) :
    f s = f 0 := by
  refine Int.inductionOn' s 0 ?base ?succ ?pred
  · rfl
  · intro k hk ih
    have hk0 : f (k + 1) - f k = 0 := by
      simpa [fwdDiff, Pi.zero_apply] using congrFun h k
    exact (sub_eq_zero.mp hk0).trans ih
  · intro k hk ih
    have hk0 : f ((k - 1) + 1) - f (k - 1) = 0 := by
      simpa [fwdDiff, Pi.zero_apply] using congrFun h (k - 1)
    have hprev : f k = f (k - 1) := by
      simpa using sub_eq_zero.mp hk0
    exact hprev.symm.trans ih

lemma fwdDiff_iter_succ_as_iter_fwdDiff (f : ℤ → ℤ) (r : ℕ) :
    (fwdDiff (1 : ℤ))^[r + 1] f = (fwdDiff (1 : ℤ))^[r] (fwdDiff (1 : ℤ) f) := by
  rw [Function.iterate_succ_apply]

lemma fwdDiff_choose_int_succ (r : ℕ) :
    fwdDiff (1 : ℤ) (fun s : ℤ => Ring.choose s (r + 1)) =
      fun s : ℤ => Ring.choose s r := by
  ext s
  simp [fwdDiff, Ring.choose_succ_succ]

lemma fwdDiff_newtonTerm_zero :
    fwdDiff (1 : ℤ) (fun s : ℤ => Ring.choose s 0 * (0 : ℤ)) = 0 := by
  ext s
  simp [fwdDiff]

lemma fwdDiff_choose_mul_const (r : ℕ) (c : ℤ) :
    fwdDiff (1 : ℤ) (fun s : ℤ => Ring.choose s (r + 1) * c) =
      fun s : ℤ => Ring.choose s r * c := by
  ext s
  simp [fwdDiff, Ring.choose_succ_succ]
  ring

lemma fwdDiff_newton_sum_succ (f : ℤ → ℤ) (N : ℕ) :
    fwdDiff (1 : ℤ)
      (fun s : ℤ => ∑ r ∈ Finset.range (N + 2),
        Ring.choose s r * ((fwdDiff (1 : ℤ))^[r] f 0))
    = fun s : ℤ => ∑ r ∈ Finset.range (N + 1),
        Ring.choose s r * ((fwdDiff (1 : ℤ))^[r] (fwdDiff (1 : ℤ) f) 0) := by
  ext s
  dsimp [fwdDiff]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ']
  simp only [Ring.choose_zero_right, Function.iterate_zero_apply]
  simp only [sub_self]
  rw [add_zero]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Ring.choose_succ_succ]
  rw [fwdDiff_iter_succ_as_iter_fwdDiff]
  ring

/-- Abstract Newton expansion for functions on `ℤ` whose `(N+1)`st forward difference is zero. -/
theorem newton_series_of_fwdDiff_iter_eq_zero (f : ℤ → ℤ) (N : ℕ)
    (hzero : (fwdDiff (1 : ℤ))^[N + 1] f = 0) (s : ℤ) :
    f s = ∑ r ∈ Finset.range (N + 1),
      Ring.choose s r * ((fwdDiff (1 : ℤ))^[r] f 0) := by
  induction N generalizing f s with
  | zero =>
      have hconst : f s = f 0 := fwdDiff_eq_zero_const f (by simpa using hzero) s
      rw [hconst]
      simp
  | succ N IH =>
      let g : ℤ → ℤ := fwdDiff (1 : ℤ) f
      have hgzero : (fwdDiff (1 : ℤ))^[N + 1] g = 0 := by
        have h' : (fwdDiff (1 : ℤ))^[N + 1] (fwdDiff (1 : ℤ) f) = 0 := by
          rw [← fwdDiff_iter_succ_as_iter_fwdDiff f (N + 1)]
          simpa [Nat.add_assoc] using hzero
        simpa [g] using h'
      let P : ℤ → ℤ := fun s : ℤ => ∑ r ∈ Finset.range (N + 2),
        Ring.choose s r * ((fwdDiff (1 : ℤ))^[r] f 0)
      have hdiff : fwdDiff (1 : ℤ) (fun x : ℤ => f x - P x) = 0 := by
        ext x
        have hP : fwdDiff (1 : ℤ) P x = g x := by
          rw [show fwdDiff (1 : ℤ) P =
              (fun s : ℤ => ∑ r ∈ Finset.range (N + 1),
                Ring.choose s r * ((fwdDiff (1 : ℤ))^[r] g 0)) by
            dsimp [P, g]
            exact fwdDiff_newton_sum_succ f N]
          exact (IH g hgzero x).symm
        dsimp [fwdDiff, P, g] at hP ⊢
        calc
          f (x + 1) - (∑ r ∈ Finset.range (N + 2), Ring.choose (x + 1) r * (fwdDiff (1 : ℤ))^[r] f 0) -
              (f x - (∑ r ∈ Finset.range (N + 2), Ring.choose x r * (fwdDiff (1 : ℤ))^[r] f 0))
              = (f (x + 1) - f x) -
                ((∑ r ∈ Finset.range (N + 2), Ring.choose (x + 1) r * (fwdDiff (1 : ℤ))^[r] f 0) -
                  (∑ r ∈ Finset.range (N + 2), Ring.choose x r * (fwdDiff (1 : ℤ))^[r] f 0)) := by ring
          _ = 0 := by
              rw [hP]
              ring
      have hconst := fwdDiff_eq_zero_const (fun x : ℤ => f x - P x) hdiff s
      have h0 : P 0 = f 0 := by
        dsimp [P]
        rw [Finset.sum_range_succ']
        simp
      change f s = P s
      have hs0 : f s - P s = 0 := by
        simpa [h0] using hconst
      exact sub_eq_zero.mp hs0

lemma fwdDiff_iter_eq_newtonCoeff (f : ℤ → ℤ) (r : ℕ) :
    (fwdDiff (1 : ℤ))^[r] f 0 = newtonCoeff f r := by
  rw [fwdDiff_iter_eq_sum_shift]
  simp [newtonCoeff, mul_assoc]

/-- Abstract Newton expansion with the coefficients written as the usual alternating finite sum. -/
theorem newton_series_of_fwdDiff_iter_eq_zero_explicit (f : ℤ → ℤ) (N : ℕ)
    (hzero : (fwdDiff (1 : ℤ))^[N + 1] f = 0) (s : ℤ) :
    f s = ∑ r ∈ Finset.range (N + 1), Ring.choose s r * newtonCoeff f r := by
  simpa [fwdDiff_iter_eq_newtonCoeff] using
    newton_series_of_fwdDiff_iter_eq_zero f N hzero s

/-- Conditional Newton expansion for `Bseq`. -/
theorem Bseq_newton_of_fwdDiff_iter_eq_zero (N : ℕ)
    (hzero : (fwdDiff (1 : ℤ))^[N + 1] (fun s : ℤ => Bseq s N) = 0) (s : ℤ) :
    Bseq s N = ∑ r ∈ Finset.range (N + 1), Ring.choose s r * Cseq r N := by
  simpa [Cseq] using
    newton_series_of_fwdDiff_iter_eq_zero_explicit (fun s : ℤ => Bseq s N) N hzero s

/-- A rational polynomial representing `Bseq · N`. -/
noncomputable def BseqPoly (N : ℕ) : ℚ[X] :=
  ∑ i ∈ Finset.range (N + 1),
    Polynomial.C (hCoeff i : ℚ) *
      (Polynomial.C (((N - i).factorial : ℚ)⁻¹) *
        ((descPochhammer ℚ (N - i)).comp (Polynomial.C (N : ℚ) * Polynomial.X)))

lemma descPochhammer_int_smeval_rat (k : ℕ) (q : ℚ) :
    (descPochhammer ℤ k).smeval q = (descPochhammer ℚ k).eval q := by
  rw [← descPochhammer_map (Int.castRingHom ℚ), Polynomial.eval_map]
  have hhom : (Int.castRingHom ℚ) = RingHom.smulOneHom := by
    ext z
    simp
  rw [hhom, Polynomial.eval₂_smulOneHom_eq_smeval]

lemma choose_scale_eval (s : ℤ) (N i : ℕ) :
    ((Ring.choose (s * (N : ℤ)) (N - i) : ℤ) : ℚ)
      = (Polynomial.C (((N - i).factorial : ℚ)⁻¹) *
          ((descPochhammer ℚ (N - i)).comp (Polynomial.C (N : ℚ) * Polynomial.X))).eval (s : ℚ) := by
  change (Int.castRingHom ℚ) (Ring.choose (s * (N : ℤ)) (N - i)) = _
  rw [Ring.map_choose (Int.castRingHom ℚ)]
  rw [Ring.choose_eq_smul]
  rw [RingHom.map_mul]
  change ((N - i).factorial : ℚ)⁻¹ • (descPochhammer ℤ (N - i)).smeval
      ((s : ℚ) * (N : ℚ)) = _
  rw [descPochhammer_int_smeval_rat]
  simp
  ring_nf
  exact Or.inl trivial

lemma Bseq_cast_eq_eval (s : ℤ) (N : ℕ) :
    (Bseq s N : ℚ) = (BseqPoly N).eval (s : ℚ) := by
  unfold Bseq BseqPoly
  change (Int.castRingHom ℚ)
      (∑ i ∈ Finset.range (N + 1), hCoeff i * Ring.choose (s * (N : ℤ)) (N - i)) = _
  rw [map_sum, Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul]
  change (hCoeff i : ℚ) * ((Ring.choose (s * (N : ℤ)) (N - i) : ℤ) : ℚ) = _
  rw [choose_scale_eval]
  simp [Polynomial.eval_mul]

lemma BseqPoly_natDegree_lt (N : ℕ) : (BseqPoly N).natDegree < N + 1 := by
  have hle : (BseqPoly N).natDegree ≤ N := by
    unfold BseqPoly
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    have hik : N - i ≤ N := Nat.sub_le N i
    apply (Polynomial.natDegree_C_mul_le (hCoeff i : ℚ) _).trans
    apply (Polynomial.natDegree_C_mul_le (((N - i).factorial : ℚ)⁻¹) _).trans
    calc
      ((descPochhammer ℚ (N - i)).comp (Polynomial.C (N : ℚ) * Polynomial.X)).natDegree
          ≤ (descPochhammer ℚ (N - i)).natDegree *
              (Polynomial.C (N : ℚ) * Polynomial.X).natDegree :=
            Polynomial.natDegree_comp_le
      _ = (N - i) * (Polynomial.C (N : ℚ) * Polynomial.X).natDegree := by simp
      _ ≤ (N - i) * 1 := by
            exact Nat.mul_le_mul_left (N - i) (by
              simpa using (Polynomial.natDegree_C_mul_X_pow_le (N : ℚ) 1))
      _ ≤ N := by simp [hik]
  exact Nat.lt_succ_of_le hle

lemma intCast_fwdDiff_iter (f : ℤ → ℤ) (n : ℕ) (s : ℤ) :
    (((fwdDiff (1 : ℤ))^[n] f s : ℤ) : ℚ) =
      ((fwdDiff (1 : ℤ))^[n] (fun x : ℤ => (f x : ℚ)) s) := by
  induction n generalizing f with
  | zero => simp
  | succ n IH =>
      simp only [Function.iterate_succ_apply]
      rw [IH]
      have hfun : (fun x : ℤ => ((fwdDiff (1 : ℤ) f x : ℤ) : ℚ)) =
          fwdDiff (1 : ℤ) (fun x : ℤ => (f x : ℚ)) := by
        ext x
        simp [fwdDiff]
      rw [hfun]

lemma fwdDiff_int_restrict_rat (F : ℚ → ℚ) (n : ℕ) (s : ℤ) :
    ((fwdDiff (1 : ℤ))^[n] (fun z : ℤ => F (z : ℚ)) s) =
      ((fwdDiff (1 : ℚ))^[n] F (s : ℚ)) := by
  induction n generalizing F with
  | zero => simp
  | succ n IH =>
      simp only [Function.iterate_succ_apply]
      have hfun : fwdDiff (1 : ℤ) (fun z : ℤ => F (z : ℚ)) =
          (fun z : ℤ => fwdDiff (1 : ℚ) F (z : ℚ)) := by
        ext z
        simp [fwdDiff, Int.cast_add]
      rw [hfun]
      exact IH (fwdDiff (1 : ℚ) F)

/-- The `(N+1)`st forward difference of `Bseq · N` vanishes. -/
theorem Bseq_fwdDiff_iter_zero (N : ℕ) :
    (fwdDiff (1 : ℤ))^[N + 1] (fun s : ℤ => Bseq s N) = 0 := by
  ext s
  have hcast : ((((fwdDiff (1 : ℤ))^[N + 1] (fun s : ℤ => Bseq s N)) s : ℤ) : ℚ) = 0 := by
    rw [intCast_fwdDiff_iter]
    have hfun : (fun x : ℤ => (Bseq x N : ℚ)) =
        fun x : ℤ => (BseqPoly N).eval (x : ℚ) := by
      ext x
      exact Bseq_cast_eq_eval x N
    rw [hfun]
    rw [show (fun x : ℤ => (BseqPoly N).eval (x : ℚ)) =
        (fun z : ℤ => (fun q : ℚ => (BseqPoly N).eval q) (z : ℚ)) by rfl]
    rw [fwdDiff_int_restrict_rat (fun q : ℚ => (BseqPoly N).eval q) (N + 1) s]
    have hzeroQ : (fwdDiff (1 : ℚ))^[N + 1] (BseqPoly N).eval = 0 :=
      Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (BseqPoly_natDegree_lt N)
    simpa using congrFun hzeroQ (s : ℚ)
  exact_mod_cast hcast

/-- Newton expansion for `Bseq` with its finite-difference coefficients. -/
theorem Bseq_newton (s : ℤ) (N : ℕ) :
    Bseq s N = ∑ r ∈ Finset.range (N + 1), Ring.choose s r * Cseq r N := by
  exact Bseq_newton_of_fwdDiff_iter_eq_zero N (Bseq_fwdDiff_iter_zero N) s

lemma fwdDiff_iter_eq_zero_of_le {f : ℤ → ℤ} {m r : ℕ}
    (hzero : (fwdDiff (1 : ℤ))^[m] f = 0) (hmr : m ≤ r) :
    (fwdDiff (1 : ℤ))^[r] f = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmr
  have hziter : ∀ k : ℕ, (fwdDiff (1 : ℤ))^[k] (0 : ℤ → ℤ) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k IH =>
        rw [Function.iterate_succ_apply']
        rw [IH]
        ext x
        simp [fwdDiff]
  rw [Nat.add_comm]
  rw [Function.iterate_add_apply]
  rw [hzero]
  exact hziter k

/-- Newton coefficients of `Bseq · N` vanish above degree `N`. -/
theorem Cseq_eq_zero_of_lt {r N : ℕ} (hNr : N < r) : Cseq r N = 0 := by
  unfold Cseq
  rw [← fwdDiff_iter_eq_newtonCoeff]
  have hzero := fwdDiff_iter_eq_zero_of_le (f := fun s : ℤ => Bseq s N)
    (m := N + 1) (r := r) (Bseq_fwdDiff_iter_zero N) (Nat.succ_le_of_lt hNr)
  simpa using congrFun hzero 0

/-- Newton expansion for `Bseq · N`, extended to any larger finite range. -/
theorem Bseq_newton_le (s : ℤ) {N K : ℕ} (hNK : N ≤ K) :
    Bseq s N = ∑ r ∈ Finset.range (K + 1), Ring.choose s r * Cseq r N := by
  rw [Bseq_newton s N]
  refine Finset.sum_subset ?hsub ?hzero
  · intro r hr
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hr)) hNK))
  · intro r hrK hrN
    have hNr : N < r := by
      exact Nat.lt_of_not_ge (by
        intro hrle
        exact hrN (Finset.mem_range.mpr (Nat.lt_succ_of_le hrle)))
    simp [Cseq_eq_zero_of_lt hNr]

/-- The prime-step B-sequence congruence for every integer argument. -/
theorem Bseq_step_dvd_all_int {p e M : ℕ} (hp:p.Prime) (hp5:5≤p)
    (hMpos:0<M) (hM:p^e ∣ M) (s:ℤ) :
  (p:ℤ)^(3*e+3) ∣ Bseq s (p*M) - Bseq s M := by
  classical
  have hp1 : 1 ≤ p := by omega
  have hMle : M ≤ p * M := by
    simpa [one_mul] using Nat.mul_le_mul_right M hp1
  rw [Bseq_newton s (p * M), Bseq_newton_le s hMle]
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro r hr
  rw [← mul_sub]
  apply Int.dvd_mul_of_dvd_right
  exact Cseq_step_dvd (p := p) (e := e) (M := M) (r := r) hp hp5 hMpos hM



open Nat Finset BigOperators Int Polynomial

lemma hCoeff_add_three (i : ℕ) (hi : i ≠ 0) : hCoeff (i + 3) = hCoeff i := by
  simp [hCoeff, hi]

lemma hCoeff_triple (t : ℕ) :
    hCoeff (t + 2) + hCoeff (t + 1) + hCoeff t = (if t = 0 then (-1 : ℤ) else 0) := by
  induction t using Nat.strong_induction_on with
  | h n IH =>
      by_cases hn : n < 4
      · interval_cases n <;> norm_num [hCoeff]
      · have hlt : n - 3 < n := by omega
        have hnon : n - 3 ≠ 0 := by omega
        have h₁ : hCoeff (n + 2) = hCoeff ((n - 3) + 2) := by
          rw [show n + 2 = ((n - 3) + 2) + 3 by omega]
          exact hCoeff_add_three ((n - 3) + 2) (by omega)
        have h₂ : hCoeff (n + 1) = hCoeff ((n - 3) + 1) := by
          rw [show n + 1 = ((n - 3) + 1) + 3 by omega]
          exact hCoeff_add_three ((n - 3) + 1) (by omega)
        have h₃ : hCoeff n = hCoeff (n - 3) := by
          rw [show n = (n - 3) + 3 by omega]
          exact hCoeff_add_three (n - 3) hnon
        rw [h₁, h₂, h₃]
        simpa [show n ≠ 0 by omega, hnon] using IH (n - 3) hlt

lemma choose_add_two_succ_succ (x : ℤ) (j : ℕ) :
    Ring.choose (x + 2) (j + 2) =
      Ring.choose x (j + 2) + 2 * Ring.choose x (j + 1) + Ring.choose x j := by
  rw [show x + 2 = (x + 1) + 1 by ring]
  rw [Ring.choose_succ_succ (x + 1) (j + 1)]
  rw [Ring.choose_succ_succ x j, Ring.choose_succ_succ x (j + 1)]
  ring

lemma choose_add_two_one (x : ℤ) :
    Ring.choose (x + 2) 1 = Ring.choose x 1 + 2 := by
  rw [Ring.choose_one_right, Ring.choose_one_right]

lemma binomial_sum_reflect (r : ℤ) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), hCoeff i * Ring.choose r (N - i)) =
      ∑ j ∈ Finset.range (N + 1), hCoeff (N - j) * Ring.choose r j := by
  rw [← Finset.sum_range_reflect (fun j => hCoeff (N - j) * Ring.choose r j) (N + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  congr 2
  omega

theorem hCoeff_identity_zero (r : ℤ) :
  (∑ k ∈ Finset.range (0 + 1),
      (Ring.choose (r + 2 * (k : ℤ) - 1) k -
        if k = 0 then 0 else Ring.choose (r + 2 * (k : ℤ) - 1) (k - 1)))
  =
  ∑ i ∈ Finset.range (0 + 1),
      hCoeff i * Ring.choose (r + 2 * (0 : ℤ)) (0 - i) := by
  norm_num [hCoeff]

theorem hCoeff_identity_one (r : ℤ) :
  (∑ k ∈ Finset.range (1 + 1),
      (Ring.choose (r + 2 * (k : ℤ) - 1) k -
        if k = 0 then 0 else Ring.choose (r + 2 * (k : ℤ) - 1) (k - 1)))
  =
  ∑ i ∈ Finset.range (1 + 1),
      hCoeff i * Ring.choose (r + 2 * (1 : ℤ)) (1 - i) := by
  simp [Finset.sum_range_succ, hCoeff]
  ring_nf


/-- Reflected right-hand side of the `hCoeff` binomial convolution. -/
def rhsRef (x : ℤ) (N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (N + 1), hCoeff (N - j) * Ring.choose x j

lemma rhsRef_add_two_expand (x : ℤ) (N : ℕ) :
    rhsRef (x + 2) (N + 1) =
      (∑ j ∈ Finset.range (N + 2), hCoeff (N + 1 - j) * Ring.choose x j) +
        2 * (∑ j ∈ Finset.range (N + 1), hCoeff (N - j) * Ring.choose x j) +
          (∑ j ∈ Finset.range N, hCoeff (N - 1 - j) * Ring.choose x j) := by
  rw [rhsRef]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  rw [Finset.sum_range_succ']
  simp only [add_assoc]
  have hsum :
      (∑ k ∈ Finset.range N,
          hCoeff (N + 1 - (k + 2)) * Ring.choose (x + 2) (k + 2)) =
        (∑ k ∈ Finset.range N,
          hCoeff (N - 1 - k) *
            (Ring.choose x (k + 2) + 2 * Ring.choose x (k + 1) + Ring.choose x k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < N := Finset.mem_range.mp hk
    have hsub : N + 1 - (k + 2) = N - 1 - k := by omega
    rw [hsub, choose_add_two_succ_succ]
  rw [hsum]
  rw [Finset.sum_range_succ']
  have hAtail :
      (∑ k ∈ Finset.range N, hCoeff (N + 1 - (k + 1 + 1)) * Ring.choose x (k + 1 + 1)) =
        (∑ k ∈ Finset.range N, hCoeff (N - 1 - k) * Ring.choose x (k + 2)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < N := Finset.mem_range.mp hk
    have hsub : N + 1 - (k + 1 + 1) = N - 1 - k := by omega
    rw [hsub]
  rw [hAtail]
  rw [choose_add_two_one, Ring.choose_zero_right]
  rw [Finset.sum_range_succ']
  have hBtail :
      (∑ k ∈ Finset.range N, hCoeff (N - (k + 1)) * Ring.choose x (k + 1)) =
        (∑ k ∈ Finset.range N, hCoeff (N - 1 - k) * Ring.choose x (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < N := Finset.mem_range.mp hk
    have hsub : N - (k + 1) = N - 1 - k := by omega
    rw [hsub]
  rw [hBtail]
  have hNm1 : N + 1 - 1 = N := by omega
  have hNp0 : N + 1 - 0 = N + 1 := by omega
  have hN0 : N - 0 = N := by omega
  rw [hNm1, hNp0, hN0]
  rw [Ring.choose_zero_right, Ring.choose_one_right]
  have hdist :
      (∑ k ∈ Finset.range N,
        hCoeff (N - 1 - k) * (Ring.choose x (k + 2) + 2 * Ring.choose x (k + 1) + Ring.choose x k)) =
      (∑ k ∈ Finset.range N,
        (hCoeff (N - 1 - k) * Ring.choose x (k + 2) +
          hCoeff (N - 1 - k) * Ring.choose x (k + 1) * 2 +
          hCoeff (N - 1 - k) * Ring.choose x k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hdist]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  -- Now all three right-hand sums have the same tail index `k < N`.
  ring_nf

lemma rhsRef_step (x : ℤ) (N : ℕ) :
    rhsRef (x + 2) (N + 1) - rhsRef x N =
      Ring.choose x (N + 1) - (if N = 0 then 0 else Ring.choose x (N - 1)) := by
  rw [rhsRef_add_two_expand]
  rw [rhsRef]
  by_cases hN : N = 0
  · subst hN
    norm_num [Finset.sum_range_succ, hCoeff, Ring.choose_zero_right, Ring.choose_one_right]
    ring
  · have htail :
        (∑ j ∈ Finset.range N,
            (hCoeff (N + 1 - j) + hCoeff (N - j) + hCoeff (N - 1 - j)) *
              Ring.choose x j) =
          - Ring.choose x (N - 1) := by
      have hlast : N - 1 ∈ Finset.range N := by
        exact Finset.mem_range.mpr (by omega)
      rw [Finset.sum_eq_single (N - 1)]
      · have hsub0 : N + 1 - (N - 1) = 2 := by omega
        have hsub1 : N - (N - 1) = 1 := by omega
        simp [hsub0, hsub1, hCoeff_triple]
      · intro j hj hjne
        have hjlt : j < N := Finset.mem_range.mp hj
        have hjne' : j ≠ N - 1 := by simpa [eq_comm] using hjne
        have htne : N - 1 - j ≠ 0 := by omega
        have hsub0 : N + 1 - j = (N - 1 - j) + 2 := by omega
        have hsub1 : N - j = (N - 1 - j) + 1 := by omega
        rw [hsub0, hsub1]
        simp [hCoeff_triple, htne]
      · intro hnot
        exact (hnot hlast).elim
    have hsplit1 :
        (∑ j ∈ Finset.range (N + 2), hCoeff (N + 1 - j) * Ring.choose x j) =
          (∑ j ∈ Finset.range N, hCoeff (N + 1 - j) * Ring.choose x j) +
            hCoeff 1 * Ring.choose x N + hCoeff 0 * Ring.choose x (N + 1) := by
      rw [show N + 2 = N + 1 + 1 by omega]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      have hN1 : N + 1 - N = 1 := by omega
      simp [hN1]
    have hsplit2 :
        (∑ j ∈ Finset.range (N + 1), hCoeff (N - j) * Ring.choose x j) =
          (∑ j ∈ Finset.range N, hCoeff (N - j) * Ring.choose x j) +
            hCoeff 0 * Ring.choose x N := by
      rw [Finset.sum_range_succ]
      simp
    rw [hsplit1, hsplit2]
    have hABC :
        (∑ j ∈ Finset.range N, hCoeff (N + 1 - j) * Ring.choose x j) +
          (∑ j ∈ Finset.range N, hCoeff (N - j) * Ring.choose x j) +
          (∑ j ∈ Finset.range N, hCoeff (N - 1 - j) * Ring.choose x j) =
        (∑ j ∈ Finset.range N,
          (hCoeff (N + 1 - j) + hCoeff (N - j) + hCoeff (N - 1 - j)) *
            Ring.choose x j) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    calc
      (∑ j ∈ Finset.range N, hCoeff (N + 1 - j) * Ring.choose x j) +
              hCoeff 1 * Ring.choose x N + hCoeff 0 * Ring.choose x (N + 1) +
            2 * ((∑ j ∈ Finset.range N, hCoeff (N - j) * Ring.choose x j) +
              hCoeff 0 * Ring.choose x N) +
          (∑ j ∈ Finset.range N, hCoeff (N - 1 - j) * Ring.choose x j) -
            ((∑ j ∈ Finset.range N, hCoeff (N - j) * Ring.choose x j) +
              hCoeff 0 * Ring.choose x N)
          = ((∑ j ∈ Finset.range N, hCoeff (N + 1 - j) * Ring.choose x j) +
              (∑ j ∈ Finset.range N, hCoeff (N - j) * Ring.choose x j) +
              (∑ j ∈ Finset.range N, hCoeff (N - 1 - j) * Ring.choose x j)) +
              (hCoeff 1 + hCoeff 0) * Ring.choose x N +
                hCoeff 0 * Ring.choose x (N + 1) := by ring
      _ = - Ring.choose x (N - 1) + Ring.choose x (N + 1) := by
            rw [hABC, htail]
            simp [hCoeff]
      _ = Ring.choose x (N + 1) - (if N = 0 then 0 else Ring.choose x (N - 1)) := by
            simp [hN]
            ring

lemma choose_pascal_sub_step (r : ℤ) (N : ℕ) :
    Ring.choose (r + 2 * ((N + 1 : ℕ) : ℤ) - 1) (N + 1) -
        Ring.choose (r + 2 * ((N + 1 : ℕ) : ℤ) - 1) N =
      Ring.choose (r + 2 * (N : ℤ)) (N + 1) -
        (if N = 0 then 0 else Ring.choose (r + 2 * (N : ℤ)) (N - 1)) := by
  have hx : r + 2 * ((N + 1 : ℕ) : ℤ) - 1 = r + 2 * (N : ℤ) + 1 := by omega
  rw [hx]
  cases N with
  | zero =>
      simp
  | succ n =>
      rw [if_neg (Nat.succ_ne_zero n)]
      rw [Ring.choose_succ_succ (r + 2 * ((n + 1 : ℕ) : ℤ)) n]
      rw [Ring.choose_succ_succ (r + 2 * ((n + 1 : ℕ) : ℤ)) (n + 1)]
      simp
      ring

theorem hCoeff_identity (r : ℤ) (N : ℕ) :
  (∑ k ∈ Finset.range (N + 1),
      (Ring.choose (r + 2 * (k : ℤ) - 1) k -
        if k = 0 then 0 else Ring.choose (r + 2 * (k : ℤ) - 1) (k - 1)))
  =
  ∑ i ∈ Finset.range (N + 1), hCoeff i * Ring.choose (r + 2 * (N : ℤ)) (N - i) := by
  induction N with
  | zero =>
      norm_num [hCoeff]
  | succ N IH =>
      rw [binomial_sum_reflect]
      change (∑ k ∈ Finset.range (N + 1 + 1),
          (Ring.choose (r + 2 * (k : ℤ) - 1) k -
            if k = 0 then 0 else Ring.choose (r + 2 * (k : ℤ) - 1) (k - 1))) =
        rhsRef (r + 2 * ((N + 1 : ℕ) : ℤ)) (N + 1)
      have IHref :
          (∑ k ∈ Finset.range (N + 1),
              (Ring.choose (r + 2 * (k : ℤ) - 1) k -
                if k = 0 then 0 else Ring.choose (r + 2 * (k : ℤ) - 1) (k - 1))) =
            rhsRef (r + 2 * (N : ℤ)) N := by
        rw [IH, binomial_sum_reflect]
        rfl
      rw [Finset.sum_range_succ]
      rw [IHref]
      rw [show r + 2 * ((N + 1 : ℕ) : ℤ) = r + 2 * (N : ℤ) + 2 by omega]
      rw [if_neg (Nat.succ_ne_zero N), Nat.succ_sub_one]
      rw [show r + 2 * (N : ℤ) + 2 - 1 = r + 2 * ((N + 1 : ℕ) : ℤ) - 1 by omega]
      rw [choose_pascal_sub_step]
      rw [← rhsRef_step (r + 2 * (N : ℤ)) N]
      ring



lemma descPochhammer_smeval_int_eq_prod_range (r : ℤ) : ∀ k : ℕ,
    (descPochhammer ℤ k).smeval r = ∏ i ∈ Finset.range k, (r - (i : ℤ))
  | 0 => by simp
  | k + 1 => by
      rw [descPochhammer_succ_right, Polynomial.smeval_mul,
        descPochhammer_smeval_int_eq_prod_range r k, Finset.prod_range_succ]
      congr 1
      simp [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast]

theorem generalized_choose_int_eq_ring_choose (r : ℤ) (k : ℕ) :
    generalized_choose_int r k = Ring.choose r k := by
  by_cases hk : k = 0
  · subst hk
    simp [generalized_choose_int]
  · rw [generalized_choose_int, if_neg hk]
    apply Int.ediv_eq_of_eq_mul_right
    · exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k) : (k.factorial : ℤ) ≠ 0)
    · rw [← descPochhammer_smeval_int_eq_prod_range r k]
      rw [Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]

lemma ring_choose_mul_succ (r : ℤ) (t : ℕ) :
    ((t + 1 : ℕ) : ℤ) * Ring.choose r (t + 1) =
      Ring.choose r t * (r - (t : ℤ)) := by
  have h := Ring.choose_smul_choose (R := ℤ) (r := r) (n := t + 1) (k := t) (Nat.le_succ t)
  have hsub : t + 1 - t = 1 := by omega
  rw [hsub, Ring.choose_one_right] at h
  rw [← h]
  simp

lemma ring_choose_mul_self_sub (r : ℤ) (k : ℕ) (hk : k ≠ 0) :
    (k : ℤ) * Ring.choose r k = Ring.choose r (k - 1) * (r - ((k - 1 : ℕ) : ℤ)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simpa using ring_choose_mul_succ r t

lemma catalan_choose_sub_mul_identity (r : ℤ) (k : ℕ) (hk : k ≠ 0) :
    r * Ring.choose (r + 2 * (k : ℤ) - 1) k =
      (r + k) *
        (Ring.choose (r + 2 * (k : ℤ) - 1) k -
          Ring.choose (r + 2 * (k : ℤ) - 1) (k - 1)) := by
  let R : ℤ := r + 2 * (k : ℤ) - 1
  have hrec : (k : ℤ) * Ring.choose R k = Ring.choose R (k - 1) * (r + k) := by
    have h := ring_choose_mul_self_sub R k hk
    have hR : R - ((k - 1 : ℕ) : ℤ) = r + k := by
      omega
    simpa [hR, mul_comm, mul_left_comm, mul_assoc] using h
  calc
    r * Ring.choose R k
        = (r + k) * Ring.choose R k - (k : ℤ) * Ring.choose R k := by ring
    _ = (r + k) * Ring.choose R k - Ring.choose R (k - 1) * (r + k) := by rw [hrec]
    _ = (r + k) * (Ring.choose R k - Ring.choose R (k - 1)) := by ring

theorem generalized_catalan_coefficient_eq_choose_sub (r : ℤ) (k : ℕ)
    (hk : k ≠ 0) (hden : r + k ≠ 0) :
    generalized_catalan_coefficient r k =
      Ring.choose (r + 2 * (k : ℤ) - 1) k -
        Ring.choose (r + 2 * (k : ℤ) - 1) (k - 1) := by
  rw [generalized_catalan_coefficient, if_neg hk, generalized_choose_int_eq_ring_choose]
  apply Int.ediv_eq_of_eq_mul_right hden
  exact catalan_choose_sub_mul_identity r k hk

theorem denom_ne_zero {m : ℤ} {n k : ℕ} (hm : m ≠ -1) (hk : k ≠ 0) (hkle : k ≤ n) :
    m * (n : ℤ) + (k : ℤ) ≠ 0 := by
  intro h
  by_cases hnonneg : 0 ≤ m
  · have hmn_nonneg : 0 ≤ m * (n : ℤ) := mul_nonneg hnonneg (Int.natCast_nonneg n)
    have hk_nonneg : 0 ≤ (k : ℤ) := Int.natCast_nonneg k
    have hk_zero : (k : ℤ) = 0 := by nlinarith
    exact hk (Int.ofNat_eq_zero.mp hk_zero)
  · have hmle : m ≤ -2 := by omega
    by_cases hn : n = 0
    · have : k = 0 := by omega
      exact hk this
    · have hnpos : 0 < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hkeq : (k : ℤ) = (-m) * (n : ℤ) := by nlinarith
      have htwom : (2 : ℤ) ≤ -m := by omega
      have h2nle : (2 : ℤ) * (n : ℤ) ≤ (-m) * (n : ℤ) := by
        exact mul_le_mul_of_nonneg_right htwom (le_of_lt hnpos)
      have hkle' : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hkle
      nlinarith

theorem generalized_catalan_coefficient_eq_choose_sub_for_a_gen {m : ℤ} {n k : ℕ}
    (hm : m ≠ -1) (hk : k ≠ 0) (hkle : k ≤ n) :
    generalized_catalan_coefficient (m * (n : ℤ)) k =
      Ring.choose (m * (n : ℤ) + 2 * (k : ℤ) - 1) k -
        Ring.choose (m * (n : ℤ) + 2 * (k : ℤ) - 1) (k - 1) := by
  exact generalized_catalan_coefficient_eq_choose_sub (m * (n : ℤ)) k hk
    (denom_ne_zero (m := m) (n := n) (k := k) hm hk hkle)

theorem generalized_catalan_coefficient_zero (r : ℤ) :
    generalized_catalan_coefficient r 0 = 1 := by
  simp [generalized_catalan_coefficient]

theorem a_gen_eq_choose_sub_sum_of_ne_neg_one (m : ℤ) (n : ℕ) (hm : m ≠ -1) :
    a_gen m n =
      if n = 0 then 1 else
        ∑ k ∈ Finset.range (n + 1),
          if k = 0 then 1 else
            Ring.choose (m * (n : ℤ) + 2 * (k : ℤ) - 1) k -
              Ring.choose (m * (n : ℤ) + 2 * (k : ℤ) - 1) (k - 1) := by
  by_cases hn : n = 0
  · subst hn
    simp [a_gen]
  · rw [a_gen, if_neg hn, if_neg hn]
    apply Finset.sum_congr rfl
    intro k hk_mem
    by_cases hk0 : k = 0
    · subst hk0
      simp [generalized_catalan_coefficient]
    · rw [if_neg hk0]
      have hkle : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_mem)
      exact generalized_catalan_coefficient_eq_choose_sub_for_a_gen
        (m := m) (n := n) (k := k) hm hk0 hkle


theorem a_gen_eq_Bseq_of_ne_neg_one (m : ℤ) {N : ℕ} (hN : 0 < N) (hm : m ≠ -1) :
    a_gen m N = Bseq (m + 2) N := by
  calc
    a_gen m N
        = ∑ k ∈ Finset.range (N + 1),
            if k = 0 then 1 else
              Ring.choose (m * (N : ℤ) + 2 * (k : ℤ) - 1) k -
                Ring.choose (m * (N : ℤ) + 2 * (k : ℤ) - 1) (k - 1) := by
            rw [a_gen_eq_choose_sub_sum_of_ne_neg_one m N hm]
            rw [if_neg (Nat.ne_of_gt hN)]
    _ = ∑ k ∈ Finset.range (N + 1),
          (Ring.choose (m * (N : ℤ) + 2 * (k : ℤ) - 1) k -
            if k = 0 then 0 else
              Ring.choose (m * (N : ℤ) + 2 * (k : ℤ) - 1) (k - 1)) := by
            apply Finset.sum_congr rfl
            intro k hk
            by_cases hk0 : k = 0
            · simp [hk0]
            · simp [hk0]
    _ = ∑ i ∈ Finset.range (N + 1),
          hCoeff i * Ring.choose (m * (N : ℤ) + 2 * (N : ℤ)) (N - i) := by
            exact hCoeff_identity (m * (N : ℤ)) N
    _ = Bseq (m + 2) N := by
            rw [Bseq]
            apply Finset.sum_congr rfl
            intro i hi
            congr 2
            ring


theorem a_gen_neg_one_eq_Bseq_add_one {N : ℕ} (hN : 0 < N) :
    a_gen (-1) N = Bseq 1 N + 1 := by
  let r : ℤ := (-1 : ℤ) * (N : ℤ)
  let g : ℕ → ℤ := fun k =>
    Ring.choose (r + 2 * (k : ℤ) - 1) k -
      if k = 0 then 0 else Ring.choose (r + 2 * (k : ℤ) - 1) (k - 1)
  have hcoeff_before : ∀ k ∈ Finset.range N,
      generalized_catalan_coefficient r k = g k := by
    intro k hk_mem
    have hklt : k < N := Finset.mem_range.mp hk_mem
    by_cases hk0 : k = 0
    · subst hk0
      simp [g, generalized_catalan_coefficient]
    · have hden : r + (k : ℤ) ≠ 0 := by
        dsimp [r]
        omega
      rw [generalized_catalan_coefficient_eq_choose_sub r k hk0 hden]
      simp [g, hk0]
  have hlast_coeff : generalized_catalan_coefficient r N = 0 := by
    have hNne : N ≠ 0 := Nat.ne_of_gt hN
    rw [generalized_catalan_coefficient, if_neg hNne]
    have hden : r + (N : ℤ) = 0 := by
      dsimp [r]
      ring
    simp [hden]
  have ha : a_gen (-1) N = ∑ k ∈ Finset.range N, g k := by
    rw [a_gen, if_neg (Nat.ne_of_gt hN)]
    change (∑ k ∈ Finset.range (N + 1), generalized_catalan_coefficient r k) =
      ∑ k ∈ Finset.range N, g k
    rw [Finset.sum_range_succ]
    rw [hlast_coeff, add_zero]
    apply Finset.sum_congr rfl
    exact hcoeff_before
  have hgN : g N = -1 := by
    have hNne : N ≠ 0 := Nat.ne_of_gt hN
    have hrN : r + 2 * (N : ℤ) - 1 = ((N - 1 : ℕ) : ℤ) := by
      dsimp [r]
      omega
    have hltpred : N - 1 < N := by omega
    dsimp [g]
    rw [if_neg hNne, hrN]
    rw [Ring.choose_natCast, Ring.choose_natCast]
    rw [Nat.choose_eq_zero_of_lt hltpred, Nat.choose_self]
    norm_num
  calc
    a_gen (-1) N = ∑ k ∈ Finset.range N, g k := ha
    _ = (∑ k ∈ Finset.range (N + 1), g k) + 1 := by
      rw [Finset.sum_range_succ, hgN]
      ring
    _ = (∑ i ∈ Finset.range (N + 1), hCoeff i * Ring.choose (r + 2 * (N : ℤ)) (N - i)) + 1 := by
      rw [show (∑ k ∈ Finset.range (N + 1), g k) =
          ∑ i ∈ Finset.range (N + 1), hCoeff i * Ring.choose (r + 2 * (N : ℤ)) (N - i) by
        dsimp [g]
        exact hCoeff_identity r N]
    _ = Bseq 1 N + 1 := by
      congr 1
      rw [Bseq]
      apply Finset.sum_congr rfl
      intro i hi
      congr 2
      dsimp [r]
      ring



theorem oeis_333096_supercongruence_conjecture (m : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    a_gen m (n * p ^ k) ≡ a_gen m (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
  let M : ℕ := n * p ^ (k - 1)
  have hMpos : 0 < M := by
    dsimp [M]
    exact Nat.mul_pos hn (pow_pos hp.pos _)
  have hp5' : 5 ≤ p := hp5
  have hstep_dvd : (p : ℤ) ^ (3 * (k - 1) + 3) ∣ Bseq (m + 2) (p * M) - Bseq (m + 2) M := by
    have hdiv : p ^ (k - 1) ∣ M := by
      dsimp [M]
      exact dvd_mul_left (p ^ (k - 1)) n
    exact Bseq_step_dvd_all_int (p := p) (e := k - 1) (M := M) hp hp5' hMpos hdiv (m + 2)
  have hexp : 3 * (k - 1) + 3 = 3 * k := by omega
  have hNhi : n * p ^ k = p * M := by
    dsimp [M]
    have hkpos : 1 ≤ k := hk
    have hpow : p ^ k = p * p ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [pow_succ']
    rw [hpow]
    ac_rfl
  have hNlo : n * p ^ (k - 1) = M := by rfl
  by_cases hm : m = -1
  · subst hm
    have hhi_pos : 0 < n * p ^ k := Nat.mul_pos hn (pow_pos hp.pos _)
    have hlo_pos : 0 < n * p ^ (k - 1) := Nat.mul_pos hn (pow_pos hp.pos _)
    have hhi := a_gen_neg_one_eq_Bseq_add_one (N := n * p ^ k) hhi_pos
    have hlo := a_gen_neg_one_eq_Bseq_add_one (N := n * p ^ (k - 1)) hlo_pos
    rw [hhi, hlo]
    rw [hNhi, hNlo]
    rw [Int.modEq_iff_dvd]
    rw [hexp] at hstep_dvd
    have hstep1 : (p : ℤ) ^ (3 * k) ∣ Bseq 1 M - Bseq 1 (p * M) := by
      have hneg : (p : ℤ) ^ (3 * k) ∣ -(Bseq 1 (p * M) - Bseq 1 M) := dvd_neg.mpr (by simpa using hstep_dvd)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hstep1
  · have hhi_pos : 0 < n * p ^ k := Nat.mul_pos hn (pow_pos hp.pos _)
    have hlo_pos : 0 < n * p ^ (k - 1) := Nat.mul_pos hn (pow_pos hp.pos _)
    have hhi := a_gen_eq_Bseq_of_ne_neg_one m (N := n * p ^ k) hhi_pos hm
    have hlo := a_gen_eq_Bseq_of_ne_neg_one m (N := n * p ^ (k - 1)) hlo_pos hm
    rw [hhi, hlo]
    rw [hNhi, hNlo]
    rw [Int.modEq_iff_dvd]
    rw [hexp] at hstep_dvd
    have hstepm : (p : ℤ) ^ (3 * k) ∣ Bseq (m + 2) M - Bseq (m + 2) (p * M) := by
      have hneg : (p : ℤ) ^ (3 * k) ∣ -(Bseq (m + 2) (p * M) - Bseq (m + 2) M) := dvd_neg.mpr (by simpa using hstep_dvd)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
    simpa [sub_eq_add_neg] using hstepm
