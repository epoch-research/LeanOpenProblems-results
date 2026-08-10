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

set_option exponentiation.threshold 200000
set_option maxRecDepth 1000000

/--
Conjecture: $a(n) \equiv 0 \pmod 3$ if $n>2$. Also, $a(n)$ is always of the form $2^a \cdot 3^b \cdot b'$ where $b'$ is a squarefree number.
-/
theorem A070823_conjecture.disproof : ¬ (∀ n : ℕ, 2 < n →
    (A070823 n ≡ 0 [MOD 3]) ∧
    (∃ a b b' : ℕ, A070823 n = 2^a * 3^b * b' ∧ Squarefree b')) := by
  intro h
  have h20_lt : 2 < 20 := by decide
  have h20 := h 20 h20_lt
  rcases h20 with ⟨_, ⟨a, b, b', h_eq, h_sq⟩⟩
  have h_mod169 : A070823 20 % 169 = 0 := by rfl
  have h_dvd169 : 169 ∣ A070823 20 := dvd_of_mod_eq_zero h_mod169
  rw [h_eq] at h_dvd169
  have h169 : 169 = 13^2 := by rfl
  rw [h169] at h_dvd169
  have h13_prime : Nat.Prime 13 := by decide
  have h13_not_dvd_2 : ¬ 13 ∣ 2 := by decide
  have h13_not_dvd_3 : ¬ 13 ∣ 3 := by decide
  have h13_coprime_2 : Nat.Coprime 13 2 := h13_prime.coprime_iff_not_dvd.mpr h13_not_dvd_2
  have h13_coprime_3 : Nat.Coprime 13 3 := h13_prime.coprime_iff_not_dvd.mpr h13_not_dvd_3
  have h13_coprime_2a : Nat.Coprime 13 (2^a) := h13_coprime_2.pow_right a
  have h13_coprime_3b : Nat.Coprime 13 (3^b) := h13_coprime_3.pow_right b
  have h13_coprime_mul : Nat.Coprime 13 (2^a * 3^b) := h13_coprime_2a.mul_right h13_coprime_3b
  have h169_coprime : Nat.Coprime (13^2) (2^a * 3^b) := h13_coprime_mul.pow_left 2
  have h_dvd_b' : (13^2) ∣ b' := h169_coprime.dvd_of_dvd_mul_left h_dvd169
  have h_unit13 : IsUnit 13 := h_sq 13 h_dvd_b'
  rw [Nat.isUnit_iff] at h_unit13
  contradiction

