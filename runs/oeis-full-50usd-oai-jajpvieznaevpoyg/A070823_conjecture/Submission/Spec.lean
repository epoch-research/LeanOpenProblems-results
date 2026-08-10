import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 20000
set_option exponentiation.threshold 5000
set_option maxHeartbeats 1000000


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
theorem A070823_conjecture.disproof : ¬ (∀ n : ℕ, 2 < n →
    (A070823 n ≡ 0 [MOD 3]) ∧
    (∃ a b b' : ℕ, A070823 n = 2^a * 3^b * b' ∧ Squarefree b')) := by
  intro h
  have h20 := h 20 (by norm_num)
  rcases h20.2 with ⟨a, b, b', hEq, hsq⟩
  have hA : 169 ∣ A070823 20 := by
    decide
  rw [hEq] at hA
  have hc2 : Nat.Coprime 169 (2^a) := by
    exact (by norm_num : Nat.Coprime 169 2).pow_right a
  have hc3 : Nat.Coprime 169 (3^b) := by
    exact (by norm_num : Nat.Coprime 169 3).pow_right b
  have hc : Nat.Coprime 169 (2^a * 3^b) := hc2.mul_right hc3
  have hd : 169 ∣ b' := (hc.dvd_mul_left).1 hA
  have hd' : 13 * 13 ∣ b' := by
    simpa using hd
  have hu : IsUnit (13 : ℕ) := hsq 13 hd'
  norm_num at hu
