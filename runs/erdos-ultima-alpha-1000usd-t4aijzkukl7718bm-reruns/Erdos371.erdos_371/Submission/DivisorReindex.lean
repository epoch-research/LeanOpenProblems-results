import FormalConjecturesUtil

/-! A finite divisor-sum reindexing, independent of any asymptotic assertion. -/

namespace Erdos371DivisorReindex

lemma divisors_eq_filter_Icc {m N : ℕ} (hm : m ∈ Finset.Icc 1 N) :
    m.divisors = (Finset.Icc 1 N).filter (fun d => d ∣ m) := by
  have hmI := Finset.mem_Icc.mp hm
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hd, _⟩
    have hdpos := Nat.pos_of_dvd_of_pos hd (by omega : 0 < m)
    have hdle := Nat.le_of_dvd (by omega : 0 < m) hd
    exact ⟨⟨by omega, by omega⟩, hd⟩
  · rintro ⟨_, hd⟩
    exact ⟨hd, by omega⟩

lemma sum_multiples {d N : ℕ} (hd : 0 < d) (f : ℕ → ℤ) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m => d ∣ m), f m) =
      ∑ k ∈ Finset.Icc 1 (N / d), f (k * d) := by
  symm
  apply Finset.sum_bij (fun k _ => k * d)
  · intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    have hkbound := (Nat.le_div_iff_mul_le hd).mp hkN
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, hkbound⟩, dvd_mul_left d k⟩
    exact Nat.mul_pos (by omega) hd
  · intro k hk l hl he
    exact Nat.eq_of_mul_eq_mul_right hd he
  · intro m hm
    obtain ⟨hmI, hdm⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hmI
    have he : m / d * d = m := Nat.div_mul_cancel hdm
    have hkp : 0 < m / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdm) hd
    refine ⟨m / d, Finset.mem_Icc.mpr ⟨hkp, Nat.div_le_div_right hmN⟩, he⟩
  · intro k hk
    rfl

lemma sum_divisors_reindex (N : ℕ) (f : ℕ → ℕ → ℤ) :
    (∑ m ∈ Finset.Icc 1 N, ∑ d ∈ m.divisors, f d m) =
      ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 (N / d), f d (k * d) := by
  have he : (∑ m ∈ Finset.Icc 1 N, ∑ d ∈ m.divisors, f d m) =
      ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, if d ∣ m then f d m else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [divisors_eq_filter_Icc hm, Finset.sum_filter]
  rw [he, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter]
  exact sum_multiples (by have := (Finset.mem_Icc.mp hd).1; omega) (f d)

end Erdos371DivisorReindex

#print axioms Erdos371DivisorReindex.sum_divisors_reindex
