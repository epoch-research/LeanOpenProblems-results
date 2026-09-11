import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A219055: Number of ways to write $n = p+q(3-(-1)^n)/2$ with $p>q$ and $p, q, p-6, q+6$ all prime.
-/
def A219055 (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter (fun q : ℕ =>
    -- c = 1 + n % 2. The condition p > q is equivalent to (c + 1) * q < n.
    ((1 + n % 2) + 1) * q < n ∧

    -- Primality conditions for q and derived terms
    q.Prime ∧
    (q + 6).Prime ∧

    -- Primality conditions for p = n - c * q and p - 6
    (n - (1 + n % 2) * q).Prime ∧        -- p must be prime
    (n - (1 + n % 2) * q - 6).Prime      -- p - 6 must be prime
  ) (Finset.range n)

-- Formal definition of Goldbach's Conjecture
def goldbach_conjecture : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q

-- Formal definition of Lemoine's Conjecture (or Levy's Conjecture)
def lemoine_conjecture : Prop :=
  ∀ n : ℕ, 7 ≤ n → Odd n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + 2 * q

-- Formalization of the conjecture that there are infinitely many cousin primes (p, p+6)
def six_prime_gap_conjecture : Prop :=
  Set.Infinite {p : ℕ | p.Prime ∧ (p + 6).Prime}

/--
The core conjecture about the sequence A219055:
a(n) > 0 for all even n > 8012 and odd n > 15727.
-/
def a219055_core_conjecture : Prop :=
  ∀ n : ℕ,
    (Even n ∧ 8012 < n) ∨ (Odd n ∧ 15727 < n)
      → A219055 n > 0

namespace A219055Aux

/-! ### Kernel-friendly verified primality testing and finite checks -/

/-- Trial division by odd `d, d+2, ...` while `d * d ≤ n`; returns `false` when fuel runs out
(so soundness never depends on the fuel). -/
def isPrimeAux (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | d, fuel+1 => if n < d * d then true else if n % d = 0 then false else isPrimeAux n (d+2) fuel

def isPrimeB (n : ℕ) : Bool := 2 ≤ n && (n = 2 || (n % 2 = 1 && isPrimeAux n 3 n))

def searchFrom (p : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => false
  | s, fuel+1 => p s || searchFrom p (s+1) fuel

def forallBelow (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | k+1 => p k && forallBelow p k

def goldB (n : ℕ) : Bool :=
  searchFrom (fun q => (q ≤ n : Bool) && isPrimeB q && isPrimeB (n - q)) 0 n

def lemB (n : ℕ) : Bool :=
  searchFrom (fun q => (2 * q ≤ n : Bool) && isPrimeB q && isPrimeB (n - 2 * q)) 0 n

theorem isPrimeAux_sound (n : ℕ) : ∀ (d fuel : ℕ), d % 2 = 1 → isPrimeAux n d fuel = true →
    ∀ m, d ≤ m → m * m ≤ n → m % 2 = 1 → ¬ m ∣ n := by
  intro d fuel
  induction fuel generalizing d with
  | zero => simp [isPrimeAux]
  | succ fuel ih =>
    intro hd h m hdm hmm hm hdvd
    simp only [isPrimeAux] at h
    split_ifs at h with h1 h2
    · have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · rcases Nat.eq_or_lt_of_le hdm with rfl | hlt
      · exact h2 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact ih (d+2) (by omega) h m (by omega) hmm hm hdvd

theorem isPrimeB_sound (n : ℕ) (h : isPrimeB n = true) : n.Prime := by
  simp only [isPrimeB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨h2, rfl | ⟨hodd, h⟩⟩
  · exact Nat.prime_two
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm hle => fun hdvd => ?_⟩
  have hmm := Nat.le_sqrt.mp hle
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨k, hk⟩ := he
    have : 2 ∣ n := Dvd.dvd.trans ⟨k, by omega⟩ hdvd
    omega
  · obtain ⟨k, hk⟩ := ho
    exact isPrimeAux_sound n 3 n rfl h m (by omega) hmm (by omega) hdvd

theorem searchFrom_sound (p : ℕ → Bool) : ∀ s fuel, searchFrom p s fuel = true → ∃ q, p q = true := by
  intro s fuel
  induction fuel generalizing s with
  | zero => simp [searchFrom]
  | succ fuel ih =>
    intro h
    simp only [searchFrom, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨s, h⟩
    · exact ih (s+1) h

theorem forallBelow_sound (p : ℕ → Bool) : ∀ k, forallBelow p k = true → ∀ n < k, p n = true := by
  intro k
  induction k with
  | zero => intro _ n hn; omega
  | succ k ih =>
    intro h n hn
    simp only [forallBelow, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
    · exact ih h.2 n hn
    · exact h.1

theorem goldB_sound (n : ℕ) (h : goldB n = true) : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q := by
  obtain ⟨q, hq⟩ := searchFrom_sound _ _ _ h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  exact ⟨n - q, q, isPrimeB_sound _ hq.2, isPrimeB_sound _ hq.1.2, by omega⟩

theorem lemB_sound (n : ℕ) (h : lemB n = true) : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + 2 * q := by
  obtain ⟨q, hq⟩ := searchFrom_sound _ _ _ h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  exact ⟨n - 2 * q, q, isPrimeB_sound _ hq.2, isPrimeB_sound _ hq.1.2, by omega⟩

theorem goldAll :
    forallBelow (fun n => (n < 4 : Bool) || (n % 2 = 1 : Bool) || goldB n) 8013 = true := by
  decide +kernel

theorem lemAll :
    forallBelow (fun n => (n < 7 : Bool) || (n % 2 = 0 : Bool) || lemB n) 15728 = true := by
  decide +kernel

theorem goldbach_small (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 8012) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q := by
  have := forallBelow_sound _ _ goldAll n (by omega)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with (h | h) | h
  · omega
  · obtain ⟨k, hk⟩ := he; omega
  · exact goldB_sound n h

theorem lemoine_small (n : ℕ) (h7 : 7 ≤ n) (hn : n ≤ 15727) (ho : Odd n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + 2 * q := by
  have := forallBelow_sound _ _ lemAll n (by omega)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with (h | h) | h
  · omega
  · obtain ⟨k, hk⟩ := ho; omega
  · exact lemB_sound n h

theorem A219055_pos {n : ℕ} (h : A219055 n > 0) :
    ∃ q, ((1 + n % 2) + 1) * q < n ∧ q.Prime ∧ (q + 6).Prime ∧
      (n - (1 + n % 2) * q).Prime ∧ (n - (1 + n % 2) * q - 6).Prime := by
  unfold A219055 at h
  obtain ⟨q, hq⟩ := Finset.card_pos.mp h
  simp only [Finset.mem_filter, Finset.mem_range] at hq
  exact ⟨q, hq.2⟩

end A219055Aux

/--
A219055, Conjecture 1: The core conjecture for A219055 implies Goldbach's conjecture,
Lemoine's conjecture and the conjecture that there are infinitely many primes p with p+6 also prime.
-/
theorem oeis_219055_conjecture_1 :
    a219055_core_conjecture → goldbach_conjecture ∧ lemoine_conjecture ∧ six_prime_gap_conjecture := by
  intro h
  refine ⟨?_, ?_, ?_⟩
  · intro n h4 he
    by_cases hn : n ≤ 8012
    · exact A219055Aux.goldbach_small n h4 hn he
    · obtain ⟨q, hq1, hq2, -, hq4, -⟩ := A219055Aux.A219055_pos (h n (Or.inl ⟨he, by omega⟩))
      have h2 : n % 2 = 0 := Nat.even_iff.mp he
      rw [h2] at hq1 hq4
      norm_num at hq1 hq4
      exact ⟨n - q, q, hq4, hq2, by omega⟩
  · intro n h7 ho
    by_cases hn : n ≤ 15727
    · exact A219055Aux.lemoine_small n h7 hn ho
    · obtain ⟨q, hq1, hq2, -, hq4, -⟩ := A219055Aux.A219055_pos (h n (Or.inr ⟨ho, by omega⟩))
      have h2 : n % 2 = 1 := Nat.odd_iff.mp ho
      rw [h2] at hq1 hq4
      norm_num at hq1 hq4
      exact ⟨n - 2 * q, q, hq4, hq2, by omega⟩
  · apply Set.infinite_of_forall_exists_gt
    intro a
    have he : Even (2 * a + 8014) := ⟨a + 4007, by omega⟩
    obtain ⟨q, hq1, -, -, hq4, hq5⟩ :=
      A219055Aux.A219055_pos (h (2 * a + 8014) (Or.inl ⟨he, by omega⟩))
    have h2 : (2 * a + 8014) % 2 = 0 := Nat.even_iff.mp he
    rw [h2] at hq1 hq4 hq5
    norm_num at hq1 hq4 hq5
    refine ⟨2 * a + 8014 - q - 6, ⟨hq5, ?_⟩, ?_⟩
    · have := hq5.two_le
      have : 2 * a + 8014 - q - 6 + 6 = 2 * a + 8014 - q := by omega
      rw [this]; exact hq4
    · omega

theorem oeis_219055_conjecture_1.disproof : ¬ (type_of% @oeis_219055_conjecture_1) := sorry
