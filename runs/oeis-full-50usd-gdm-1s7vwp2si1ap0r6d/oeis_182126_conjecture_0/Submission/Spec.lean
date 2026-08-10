import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat
open Finset

/--
A182126: $a(n) = \text{prime}(n) \cdot \text{prime}(n+1) \bmod \text{prime}(n+2)$.
The function $\text{prime}(k)$ is the $k$-th prime number, with $\text{prime}(1)=2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let p_n := fun k : ℕ => (Nat.nth Nat.Prime (k - 1))
  if n = 0 then 0 -- Handle the 0 case for the otherwise 1-indexed sequence
  else (p_n n * p_n (n + 1)) % p_n (n + 2)

/--
Let $C(v, x)$ be the number of times $v$ appears in the sequence $a(1), a(2), \ldots, a(x)$.
$C(v, x) = |\{ n \in \{1, \dots, x\} : a(n) = v \}|$.
-/
noncomputable def count_a (x v : ℕ) : ℕ :=
  -- The index set is {1, 2, ..., x}. We use range (x+1) which is {0, ..., x} and filter by 1 ≤ n.
  ((range (x + 1)).filter fun n => 1 ≤ n ∧ a n = v).card

/--
A value $v₀$ is a most frequent value in $a(1), \ldots, a(x)$ if its count is greater
than or equal to the count of every other value $v$.
-/
def is_most_frequent (x v₀ : ℕ) : Prop :=
  ∀ v : ℕ, count_a x v₀ ≥ count_a x v

theorem nth_prime_32 : nth Nat.Prime 32 = 137 := by
  have h : nth Nat.Prime (count Nat.Prime 137) = 137 := nth_count (by decide : Nat.Prime 137)
  have hc : count Nat.Prime 137 = 32 := rfl
  rwa [hc] at h

theorem nth_prime_33 : nth Nat.Prime 33 = 139 := by
  have h : nth Nat.Prime (count Nat.Prime 139) = 139 := nth_count (by decide : Nat.Prime 139)
  have hc : count Nat.Prime 139 = 33 := rfl
  rwa [hc] at h

theorem nth_prime_34 : nth Nat.Prime 34 = 149 := by
  have h : nth Nat.Prime (count Nat.Prime 149) = 149 := nth_count (by decide : Nat.Prime 149)
  have hc : count Nat.Prime 149 = 34 := rfl
  rwa [hc] at h

theorem a_33 : a 33 = 120 := by
  unfold a
  simp only
  rw [nth_prime_32, nth_prime_33, nth_prime_34]
  rfl

theorem count_a_120_pos (x : ℕ) (hx : x > 10^9) : count_a x 120 ≥ 1 := by
  unfold count_a
  have h_33_mem : 33 ∈ (range (x + 1)).filter (fun n => 1 ≤ n ∧ a n = 120) := by
    rw [mem_filter]
    refine ⟨?_, ?_⟩
    · rw [mem_range]
      omega
    · exact ⟨by decide, a_33⟩
  have h_nonempty : ((range (x + 1)).filter (fun n => 1 ≤ n ∧ a n = 120)).Nonempty := ⟨33, h_33_mem⟩
  exact card_pos.mpr h_nonempty

/--
Conjecture: for x > 10^9, the most frequent value in a(n), n=1...x, has form 120*k.
We interpret "n=0...x" from the OEIS entry as $n \in \{1, \dots, x\}$ for the active terms.
-/
theorem oeis_182126_conjecture_0 :
  ∀ x : ℕ,
    x > 10^9 →
    ∀ v₀ : ℕ,
      is_most_frequent x v₀ →
      120 ∣ v₀ := by
  intro x hx v₀ hv
  by_cases h : 120 ∣ v₀
  · exact h
  · have h120 : count_a x 120 ≥ 1 := count_a_120_pos x hx
    have h_mf : count_a x v₀ ≥ count_a x 120 := hv 120
    have h_pos : count_a x v₀ ≥ 1 := by omega
    have h_unfolded : count_a x v₀ = ((range (x + 1)).filter fun n => 1 ≤ n ∧ a n = v₀).card := rfl
    have h_pos' : ((range (x + 1)).filter fun n => 1 ≤ n ∧ a n = v₀).card > 0 := by
      change 1 ≤ count_a x v₀ at h_pos
      rw [h_unfolded] at h_pos
      omega
    have h_nonempty : ((range (x + 1)).filter fun n => 1 ≤ n ∧ a n = v₀).Nonempty := card_pos.mp h_pos'
    let n := Classical.choose h_nonempty
    have h_mem := Classical.choose_spec h_nonempty
    rw [mem_filter] at h_mem
    have h_a_n : a n = v₀ := h_mem.2.2
    sorry
