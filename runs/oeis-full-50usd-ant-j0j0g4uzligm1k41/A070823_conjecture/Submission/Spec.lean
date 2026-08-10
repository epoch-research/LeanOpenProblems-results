import FormalConjectures.Util.ProblemImports

open Nat Int

/--
Helper function to calculate the number of decimal digits of $n$. For $n=0$, it returns $1$,
which is necessary for the correct concatenation behavior observed in the sequence examples.
We use the mathematical definition $\lfloor \log_{10} n \rfloor + 1$.
-/
def num_digits_base_10 (n : ℕ) : ℕ :=
  if n = 0 then 1 else (Nat.log 10 n) + 1

/-- Concatenates $x$ followed by $y$ in base 10: $x \cdot 10^{\text{num\_digits}(y)} + y$. -/
def concatenate (x y : ℕ) : ℕ :=
  x * (10 ^ (num_digits_base_10 y)) + y

/--
A070823: $a(1)=0, a(2)=1, a(n+2)=|concatenate(a(n+1),a(n))-concatenate(a(n),a(n+1))|$.
The sequence is 1-indexed.
-/
noncomputable def A070823 : ℕ → ℕ
| 0 => 0 -- Auxiliary value for total function on ℕ
| 1 => 0
| 2 => 1
| n + 3 => -- Covers indices $k \ge 4$. The terms used are $a(n+2)$ and $a(n+1)$, which are smaller indices.
  let anp1 := A070823 (n + 2) -- This corresponds to $a(k-1)$
  let an := A070823 (n + 1)   -- This corresponds to $a(k-2)$

  let cat1 := concatenate anp1 an
  let cat2 := concatenate an anp1

  -- Absolute difference: |cat1 - cat2|
  (ofNat cat1 - ofNat cat2).natAbs

/-
Conjecture: $a(n) \equiv 0 \pmod 3$ if $n>2$. Also, $a(n)$ is always of the form $2^a \cdot 3^b \cdot b'$ where $b'$ is a squarefree number.

This conjecture is FALSE: while $a(n)$ is always divisible by $9$ (hence by $3$) for $n > 2$,
the representation $a(n) = 2^a \cdot 3^b \cdot b'$ with $b'$ squarefree fails for $n = 20$, because
$a(20)$ is divisible by $13^2$. Since $13$ is coprime to $6$, any such representation would force
$13^2 \mid b'$, contradicting squarefreeness of $b'$.
-/
set_option maxRecDepth 10000 in
theorem A070823_conjecture.disproof : ¬ (∀ n : ℕ, 2 < n →
    (A070823 n ≡ 0 [MOD 3]) ∧
    (∃ a b b' : ℕ, A070823 n = 2^a * 3^b * b' ∧ Squarefree b')) := by
  intro h
  obtain ⟨-, a, b, b', heq, hsf⟩ := h 20 (by norm_num)
  have hdvd : 13 * 13 ∣ A070823 20 := by decide
  rw [heq] at hdvd
  have c2 : Nat.Coprime (13 * 13) 2 := by decide
  have c3 : Nat.Coprime (13 * 13) 3 := by decide
  have cop : Nat.Coprime (13 * 13) (2 ^ a * 3 ^ b) :=
    (c2.pow_right a).mul_right (c3.pow_right b)
  have hb' : 13 * 13 ∣ b' := cop.dvd_of_dvd_mul_left hdvd
  have : (13 : ℕ) = 1 := Nat.isUnit_iff.mp (hsf 13 hb')
  exact absurd this (by decide)

