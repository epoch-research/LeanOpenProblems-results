import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

noncomputable def a : ℕ → ℕ :=
fun n =>
  have p_n := fun k => Nat.nth Nat.Prime (k - 1);
  if n = 0 then 0 else p_n n * p_n (n + 1) % p_n (n + 2)

noncomputable def count_a : ℕ → ℕ → ℕ :=
fun x v => {n ∈ Finset.range (x + 1) | 1 ≤ n ∧ a n = v}.card

def is_most_frequent (x v₀ : ℕ) : Prop :=
  ∀ v : ℕ, count_a x v ≤ count_a x v₀

theorem nth_32 : Nat.nth Nat.Prime 32 = 137 := by
  have h1 : Nat.Prime 137 := by decide
  have h2 : Nat.count Nat.Prime 137 = 32 := by decide
  have h3 := Nat.nth_count h1
  rw [h2] at h3
  exact h3

theorem nth_33 : Nat.nth Nat.Prime 33 = 139 := by
  have h1 : Nat.Prime 139 := by decide
  have h2 : Nat.count Nat.Prime 139 = 33 := by decide
  have h3 := Nat.nth_count h1
  rw [h2] at h3
  exact h3

theorem nth_34 : Nat.nth Nat.Prime 34 = 149 := by
  have h1 : Nat.Prime 149 := by decide
  have h2 : Nat.count Nat.Prime 149 = 34 := by decide
  have h3 := Nat.nth_count h1
  rw [h2] at h3
  exact h3

theorem a_33_eq_120 : a 33 = 120 := by
  unfold a
  have h : 33 ≠ 0 := by decide
  rw [if_neg h]
  dsimp only
  rw [nth_32, nth_33, nth_34]

theorem count_a_120_pos (x : ℕ) (hx : x > 10^9) : count_a x 120 ≥ 1 := by
  unfold count_a
  have h33 : 33 ∈ Finset.filter (fun n => 1 ≤ n ∧ a n = 120) (Finset.range (x + 1)) := by
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_range]
      have hx2 : x ≥ 33 := by omega
      omega
    · constructor
      · decide
      · exact a_33_eq_120
  have h_card := Finset.card_pos.mpr ⟨33, h33⟩
  omega

theorem oeis_182126_conjecture_0 : ∀ x > 10 ^ 9, ∀ (v₀ : ℕ), is_most_frequent x v₀ → 120 ∣ v₀ := by
  intro x hx v₀ hf
  have h_pos : count_a x 120 ≥ 1 := count_a_120_pos x hx
  have h_freq : count_a x 120 ≤ count_a x v₀ := hf 120
  have h_v0_pos : count_a x v₀ ≥ 1 := by omega
  unfold count_a at h_v0_pos
  have h_nonempty : Finset.Nonempty (Finset.filter (fun n => 1 ≤ n ∧ a n = v₀) (Finset.range (x + 1))) := by
    rwa [Finset.card_pos] at h_v0_pos
  rcases h_nonempty with ⟨n, hn⟩
  rw [Finset.mem_filter] at hn
  have hn_a : a n = v₀ := hn.2.2
  sorry

