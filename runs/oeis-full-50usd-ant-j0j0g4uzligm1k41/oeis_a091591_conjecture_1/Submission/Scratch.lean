import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option maxHeartbeats 1000000 in
lemma small (n : ℕ) (h0 : 0 < n) (h122 : n ≤ 122) :
    ∃ p, Nat.Prime p ∧ n^2 < p ∧ p < (n+1)^2 := by
  interval_cases n
  · exact ⟨2, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨17, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨29, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨37, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨53, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨67, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨83, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨101, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨127, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨149, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨173, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨197, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨227, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨257, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨293, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨331, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨367, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨401, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨443, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨487, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨541, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨577, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨631, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨677, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨733, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨787, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨853, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨907, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨967, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1031, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1091, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1163, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1229, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1297, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1373, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1447, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1523, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1601, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1693, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1777, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1861, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1949, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2027, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2129, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2213, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2309, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2411, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2503, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2609, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2707, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2819, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2917, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3037, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3137, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3251, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3371, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3491, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3607, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3727, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3847, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3989, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4099, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4229, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4357, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4493, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4637, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4783, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4903, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5051, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5189, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5333, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5477, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5639, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5779, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5939, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6089, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6247, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6421, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6563, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6733, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6899, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7057, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7229, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7411, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7573, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7753, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7927, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨8101, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨8287, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨8467, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨8663, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨8837, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨9029, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨9221, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨9413, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨9613, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨9803, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨10007, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨10211, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨10427, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨10613, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨10831, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11027, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11239, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11467, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11677, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11887, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨12101, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨12323, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨12547, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨12781, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13001, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13229, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13457, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13691, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13931, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨14173, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨14401, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨14653, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨14887, by norm_num, by norm_num, by norm_num⟩

def a (n : ℕ) : ℕ :=
  let lower_p_start : ℕ := n ^ 2 + 1
  let max_p_value : ℕ := (n + 1) ^ 2 - 3
  Finset.card $ Finset.filter
    (fun p => p.Prime ∧ (p + 2).Prime)
    (Finset.Icc lower_p_start max_p_value)

theorem oeis_a091591_conjecture_1 :
  (∀ n : ℕ, n > 122 → a n > 0) → (∀ n : ℕ, n > 0 → ∃ p, p.Prime ∧ n^2 < p ∧ p < (n+1)^2) := by
  intro H n hn
  by_cases hgt : n > 122
  · have hpos := H n hgt
    simp only [a, gt_iff_lt, Finset.card_pos, Finset.filter_nonempty_iff,
      Finset.mem_Icc] at hpos
    obtain ⟨p, ⟨hlo, hhi⟩, hprime, _⟩ := hpos
    have ht : 3 ≤ (n+1)^2 := by nlinarith
    exact ⟨p, hprime, by omega, by omega⟩
  · exact small n hn (by omega)

#print axioms oeis_a091591_conjecture_1
