import FormalConjectures.Util.ProblemImports

open Nat Int Finset

namespace A361714

/-- The signed inner sum (before taking natAbs). -/
noncomputable def Q (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n,
    (-1 : ℤ) ^ (n + k + 1) * (n.choose k : ℤ) * ((Nat.choose (n + k - 1) k : ℤ) ^ 2)

noncomputable def a (n : ℕ) : ℕ := (Q n).natAbs

/-- The summand as a function, for odd n the sign `(-1)^(n+k+1)` becomes `(-1)^k`. -/
noncomputable def fterm (n k : ℕ) : ℤ :=
  (-1 : ℤ) ^ k * (n.choose k : ℤ) * ((Nat.choose (n + k - 1) k : ℤ) ^ 2)

/-- For odd `n`, `Q n = ∑ fterm n k`. -/
lemma Q_eq_sum_fterm {n : ℕ} (hn : Odd n) :
    Q n = ∑ k ∈ Finset.range n, fterm n k := by
  unfold Q fterm
  apply Finset.sum_congr rfl
  intro k _
  have : (-1 : ℤ) ^ (n + k + 1) = (-1 : ℤ) ^ k := by
    obtain ⟨m, hm⟩ := hn
    subst hm
    rw [show 2 * m + 1 + k + 1 = 2*(m+1) + k by ring, pow_add, pow_mul]
    norm_num
  rw [this]

/-- Split a sum over `range (p*M)` into non-multiples of `p` and the reindexed multiples. -/
lemma sum_split_mult {p M : ℕ} (hp : 0 < p) (g : ℕ → ℤ) :
    ∑ k ∈ Finset.range (p * M), g k
      = (∑ k ∈ (Finset.range (p * M)).filter (fun k => ¬ p ∣ k), g k)
        + ∑ i ∈ Finset.range M, g (p * i) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (p * M)) (fun k => ¬ p ∣ k) g]
  congr 1
  refine Finset.sum_nbij' (fun k => k / p) (fun i => p * i) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, not_not] at hk
    simp only [Finset.mem_range]
    obtain ⟨c, rfl⟩ := hk.2
    rw [Nat.mul_div_cancel_left c hp]
    exact lt_of_mul_lt_mul_left hk.1 (Nat.zero_le p)
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_filter, Finset.mem_range, not_not]
    exact ⟨mul_lt_mul_of_pos_left hi hp, Dvd.intro i rfl⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, not_not] at hk
    obtain ⟨c, rfl⟩ := hk.2
    simp only [Nat.mul_div_cancel_left c hp]
  · intro i hi
    simp only [Nat.mul_div_cancel_left i hp]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, not_not] at hk
    obtain ⟨c, rfl⟩ := hk.2
    simp only [Nat.mul_div_cancel_left c hp]

/-- **Core supercongruence 1** (non-multiples of `p` vanish):
`∑_{p ∤ k} fterm(p^r, k) ≡ 0 (mod p^{3r+3})`. -/
lemma SL1_dvd {p r : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hr : 2 ≤ r) :
    (p ^ (3 * r + 3) : ℤ) ∣
      ∑ k ∈ (Finset.range (p ^ r)).filter (fun k => ¬ p ∣ k), fterm (p ^ r) k := by
  sorry

/-- **Core supercongruence 2** (multiples of `p` descend to level `r-1`):
`∑_i (fterm(p^r, p·i) - fterm(p^{r-1}, i)) ≡ 0 (mod p^{3r+3})`. -/
lemma SL2_dvd {p r : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hr : 2 ≤ r) :
    (p ^ (3 * r + 3) : ℤ) ∣
      ∑ i ∈ Finset.range (p ^ (r - 1)), (fterm (p ^ r) (p * i) - fterm (p ^ (r - 1)) i) := by
  sorry

/-- Positivity of the signed sum at odd arguments. -/
lemma Q_pos {n : ℕ} (hn : Odd n) : 0 < Q n := by
  sorry

/-- The exact telescoping identity `Q(p^r) - Q(p^{r-1}) = SL1 + SL2`. -/
lemma Q_diff_eq {p r : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hr : 2 ≤ r) :
    Q (p ^ r) - Q (p ^ (r - 1))
      = (∑ k ∈ (Finset.range (p ^ r)).filter (fun k => ¬ p ∣ k), fterm (p ^ r) k)
        + ∑ i ∈ Finset.range (p ^ (r - 1)), (fterm (p ^ r) (p * i) - fterm (p ^ (r - 1)) i) := by
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hRodd : Odd (p ^ r) := hpodd.pow
  have hR1odd : Odd (p ^ (r - 1)) := hpodd.pow
  have hpr : p ^ r = p * p ^ (r - 1) := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega]
    rw [pow_succ]; ring
  rw [Q_eq_sum_fterm hRodd, Q_eq_sum_fterm hR1odd]
  rw [hpr]
  rw [sum_split_mult (by omega : 0 < p) (fterm (p * p ^ (r - 1)))]
  rw [← hpr]
  rw [Finset.sum_sub_distrib]
  ring

theorem main {p r : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hr : 2 ≤ r) :
    (a (p ^ r) : ℤ) ≡ (a (p ^ (r - 1)) : ℤ) [ZMOD (p ^ (3 * r + 3) : ℤ)] := by
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hRodd : Odd (p ^ r) := hpodd.pow
  have hR1odd : Odd (p ^ (r - 1)) := hpodd.pow
  have e1 : ((a (p ^ r) : ℤ)) = Q (p ^ r) := by
    show ((Q (p ^ r)).natAbs : ℤ) = Q (p ^ r)
    rw [← Int.abs_eq_natAbs]; exact abs_of_pos (Q_pos hRodd)
  have e2 : ((a (p ^ (r - 1)) : ℤ)) = Q (p ^ (r - 1)) := by
    show ((Q (p ^ (r - 1))).natAbs : ℤ) = Q (p ^ (r - 1))
    rw [← Int.abs_eq_natAbs]; exact abs_of_pos (Q_pos hR1odd)
  rw [e1, e2]
  rw [Int.modEq_iff_dvd]
  have key := Q_diff_eq hp hp7 hr
  have hdvd : (p ^ (3 * r + 3) : ℤ) ∣ (Q (p ^ r) - Q (p ^ (r - 1))) := by
    rw [key]; exact dvd_add (SL1_dvd hp hp7 hr) (SL2_dvd hp hp7 hr)
  have : Q (p ^ (r - 1)) - Q (p ^ r) = -(Q (p ^ r) - Q (p ^ (r - 1))) := by ring
  rw [this]
  exact dvd_neg.mpr hdvd

end A361714
