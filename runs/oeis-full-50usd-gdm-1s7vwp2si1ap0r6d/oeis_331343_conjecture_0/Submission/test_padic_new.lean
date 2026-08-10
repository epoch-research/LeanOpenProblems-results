import FormalConjectures.Util.ProblemImports

open Nat Finset

def L_seq (n : ℕ) : ℕ := (Ico 1 (n + 1)).lcm id

lemma L_seq_ne_zero (m : ℕ) (hm : m ≥ 1) : L_seq m ≠ 0 := by
  sorry

lemma finset_lcm_ne_zero {s : Finset β} {f : β → ℕ} (hs : ∀ b ∈ s, f b ≠ 0) : s.lcm f ≠ 0 := by
  sorry

lemma prime_pow_dvd_finset_lcm {p k : ℕ} [hp : Fact p.Prime] {s : Finset β} {f : β → ℕ}
    (hs : ∀ b ∈ s, f b ≠ 0) (hk : k ≥ 1) (hdvd : p^k ∣ s.lcm f) : ∃ b ∈ s, p^k ∣ f b := by
  sorry

lemma not_pow_dvd_L {p m k : ℕ} [hp : Fact p.Prime] (hm : m ≥ 1) (hk : k ≥ 1) (hlt : m < p^k) : ¬ p^k ∣ L_seq m := by
  intro hdvd
  have hs : ∀ b ∈ Ico 1 (m + 1), b ≠ 0 := by
    intro b hb
    simp only [mem_Ico] at hb
    omega
  have h_ex := prime_pow_dvd_finset_lcm (hp := hp) hs hk hdvd
  rcases h_ex with ⟨b, hb, h_dvd⟩
  simp only [mem_Ico] at hb
  have h_le : p^k ≤ b := Nat.le_of_dvd (by omega) h_dvd
  omega

lemma pow_p_dvd_L (p : ℕ) [hp : Fact p.Prime] {m k : ℕ} (hm : m ≥ 1) (hk : p^k ≤ m) : p^k ∣ L_seq m := by
  have : p^k > 0 := Nat.pow_pos hp.out.pos
  have hk_pos : p^k ≥ 1 := by omega
  have hk_mem : p^k ∈ Ico 1 (m + 1) := by
    simp only [mem_Ico]
    omega
  dsimp [L_seq]
  exact dvd_lcm hk_mem (f := id)

lemma le_vp_L (p : ℕ) [hp : Fact p.Prime] {m k : ℕ} (hm : m ≥ 1) (hk : p^k ≤ m) : k ≤ padicValNat p (L_seq m) := by
  have hdvd := pow_p_dvd_L p hm hk
  have h_ne : L_seq m ≠ 0 := sorry
  have h_dvd_iff : p ^ k ∣ L_seq m ↔ L_seq m = 0 ∨ k ≤ padicValNat p (L_seq m) := padicValNat_dvd_iff k (L_seq m)
  rw [h_dvd_iff] at hdvd
  rcases hdvd with h_zero | h_le
  · contradiction
  · exact h_le
