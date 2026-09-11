import FormalConjectures.Util.ProblemImports

open Nat

/--
A383327: $a(n)$ is the number of occurrences of $n$ in A049802.
A049802(m) is the sum of $(m \bmod 2^k)$ for $k=1, \dots, \lfloor \log_2 m \rfloor$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- Define the auxiliary sequence A049802 locally.
    let A049802_val (m : ℕ) : ℕ :=
      let r := Nat.log 2 m
      -- Sum over k=1 to r. We use index i in {0, ..., r-1} such that k = i+1.
      (Finset.range r).sum (fun i => m % (2 ^ (i + 1)))

    -- Since $A049802(m) = n$ implies $m < 2^{n+1}$, we use $B = 2^{n+1}$ as a sufficient search bound.
    let B : ℕ := 2 ^ (n + 1)
    Finset.card (Finset.filter (fun m => A049802_val m = n) (Finset.range B))

/--
Conjecture based on OEIS A383327 comment:
From a combinatorial perspective, the tuple of summands (x_1, ..., x_t) mentioned above can be seen as a set of t counters, where the j-th counter cycles through 0 to 2^j-1. The natural question 'which m in A049802 appear k times?' becomes a question about how this cycling condition restricts the number of tuples which sum to m. For example, for n <= 100, when n = 1, 3, 5, 9, 15, 23, 35, 63, 65, and 67 there is only one m such that the tuple of summands sums to n (a trivial tuple consisting of n 1s, trivial because there is such a tuple for every n >= 1, i.e. for every m = 2^n+1).
This is a precise statement about the set of values $n$ for which $a(n) = 1$ among $n \le 100$.
-/
def A049802_val' (m : ℕ) : ℕ :=
  let r := Nat.log 2 m
  (Finset.range r).sum (fun i => m % (2 ^ (i + 1)))

lemma p_147 : A049802_val' 147 = 67 := by rfl
lemma p_2055 : A049802_val' 2055 = 67 := by rfl
lemma p_32773 : A049802_val' 32773 = 67 := by rfl

lemma h_147 : 147 ∈ Finset.range (2^68) := by
  rw [Finset.mem_range]
  decide
lemma h_2055 : 2055 ∈ Finset.range (2^68) := by
  rw [Finset.mem_range]
  decide
lemma h_32773 : 32773 ∈ Finset.range (2^68) := by
  rw [Finset.mem_range]
  decide

lemma card_F_ge_3 : Finset.card (Finset.filter (fun m => A049802_val' m = 67) (Finset.range (2^68))) ≥ 3 := by
  let F := Finset.filter (fun m => A049802_val' m = 67) (Finset.range (2^68))
  have mem1 : 147 ∈ F := by
    rw [Finset.mem_filter]
    exact ⟨h_147, p_147⟩
  have mem2 : 2055 ∈ F := by
    rw [Finset.mem_filter]
    exact ⟨h_2055, p_2055⟩
  have mem3 : 32773 ∈ F := by
    rw [Finset.mem_filter]
    exact ⟨h_32773, p_32773⟩
  let S : Finset ℕ := {147, 2055, 32773}
  have sub : S ⊆ F := by
    intro x hx
    change x ∈ {147, 2055, 32773} at hx
    simp_all only [Finset.mem_insert, Finset.mem_singleton]
    rcases hx with rfl | rfl | rfl
    · exact mem1
    · exact mem2
    · exact mem3
  have cS : Finset.card S = 3 := by rfl
  have h_le := Finset.card_le_card sub
  rw [cS] at h_le
  exact h_le

lemma a_67_neq_1 : a 67 ≠ 1 := by
  have ha : a 67 = Finset.card (Finset.filter (fun m => A049802_val' m = 67) (Finset.range (2^68))) := by
    rw [a]
    simp [A049802_val']
  rw [ha]
  have h := card_F_ge_3
  omega

theorem oeis_383327_conjecture_0 :
  let S : Finset ℕ := {1, 3, 5, 9, 15, 23, 35, 63, 65, 67}
  ∀ n : ℕ, n ∈ S → a n = 1 :=
by sorry

theorem oeis_383327_conjecture_0.disproof : ¬ (type_of% @oeis_383327_conjecture_0) := by
  intro h
  have h67 : 67 ∈ ({1, 3, 5, 9, 15, 23, 35, 63, 65, 67} : Finset ℕ) := by decide
  have h67_1 := h 67 h67
  have hneq := a_67_neq_1
  exact hneq h67_1
