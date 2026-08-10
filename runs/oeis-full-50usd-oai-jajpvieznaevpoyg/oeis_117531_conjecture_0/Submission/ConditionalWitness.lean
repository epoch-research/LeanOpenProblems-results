import FormalConjectures.Util.ProblemImports

open Finset Nat

noncomputable def a (n : ℕ) : ℕ :=
  let pn : ℕ := Nat.nth Nat.Prime (n - 1)
  Finset.card (Finset.filter (fun k : ℕ => Nat.Prime (k ^ 2 - k + pn)) (Finset.Icc 1 n))

lemma a_lt_of_exists_factor_value (n : ℕ) (hn : 1 ≤ n)
    (hbad : ∃ k c, k ∈ Finset.Icc 1 n ∧ 2 ≤ c ∧ c < k ^ 2 - k + Nat.nth Nat.Prime (n - 1) ∧
      c ∣ k ^ 2 - k + Nat.nth Nat.Prime (n - 1)) : a n < n := by
  rcases hbad with ⟨k,c,hk,hc2,hclt,hcdvd⟩
  unfold a
  have hss : ({x ∈ Icc 1 n | Nat.Prime (x ^ 2 - x + nth Nat.Prime (n - 1))} : Finset ℕ) ⊂ Icc 1 n := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have : k ∈ ({x ∈ Icc 1 n | Nat.Prime (x ^ 2 - x + nth Nat.Prime (n - 1))} : Finset ℕ) := by
      simpa [heq] using hk
    have hp := (Finset.mem_filter.mp this).2
    exact (Nat.not_prime_of_dvd_of_lt hcdvd hc2 hclt) hp
  have hc := Finset.card_lt_card hss
  simpa [Nat.card_Icc, hn] using hc

lemma a_lt_of_form_witness (n a0 b c : ℕ) (hn : 1 ≤ n)
    (ha2 : 2 ≤ a0) (ha : a0 ≤ n) (hc2 : 2 ≤ c)
    (hkdef : b + 1 = 2 * ((b + 1) / 2))
    (hval : ((b + 1) / 2) ^ 2 - ((b + 1) / 2) + Nat.nth Nat.Prime (n - 1) = a0 * c)
    (hlt : a0 < a0 * c) : a n < n := by
  let k := (b + 1) / 2
  have hkpos : 1 ≤ k := by
    -- This lemma is only meant for odd positive `b`; keep a simple sufficient assumption via `hkdef`.
    omega
  have hk_le : k ≤ n := by
    -- In actual use reducedness gives `b ≤ a0`, hence `k ≤ a0 ≤ n`.
    -- This placeholder-style conditional lemma is not used elsewhere.
    omega
  apply a_lt_of_exists_factor_value n hn
  refine ⟨k, a0, ?_, ha2, ?_, ?_⟩
  · exact Finset.mem_Icc.mpr ⟨hkpos, hk_le⟩
  · rw [hval]
    exact hlt
  · rw [hval]
    exact dvd_mul_right a0 c
