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

/--
Conjecture: $a(n) \equiv 0 \pmod 3$ if $n>2$. Also, $a(n)$ is always of the form $2^a \cdot 3^b \cdot b'$ where $b'$ is a squarefree number.
-/
theorem A070823_conjecture : ∀ n : ℕ, 2 < n →
    (A070823 n ≡ 0 [MOD 3]) ∧
    (∃ a b b' : ℕ, A070823 n = 2^a * 3^b * b' ∧ Squarefree b') := by sorry


lemma dvd_of_169 (a b b' : ℕ) (h : 169 ∣ 2^a * 3^b * b') : 13^2 ∣ b' := by
  have hc : Coprime 169 (2^a * 3^b) := by
    apply Coprime.mul_right
    · exact (Coprime.pow_right a (by decide))
    · exact (Coprime.pow_right b (by decide))
  exact hc.dvd_of_dvd_mul_left h

set_option exponentiation.threshold 100000
set_option maxRecDepth 1000000

theorem A070823_conjecture.disproof : ¬ (type_of% @A070823_conjecture) := by
  intro h
  have h20 := h 20 (by decide)
  obtain ⟨_, a, b, b', habb', hsq⟩ := h20
  have h1 : A070823 20 % 169 = 0 := by rfl
  have h2 : 169 ∣ A070823 20 := Nat.dvd_of_mod_eq_zero h1
  have h3 : 169 ∣ 2^a * 3^b * b' := by rw [← habb']; exact h2
  have h4 : 13^2 ∣ b' := dvd_of_169 a b b' h3
  have h5 : IsUnit 13 := hsq 13 h4
  rw [Nat.isUnit_iff] at h5
  contradiction
