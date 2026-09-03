import FormalConjecturesUtil

/-!
A finite, exact prime-pair interval cover related to Erdős 972.
This auxiliary result does not prove infinitude and does not settle the conjecture.
-/

namespace FiniteCover972

def primeSet (α : ℝ) : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ Nat.Prime ⌊(α * p)⌋₊}

private lemma advance {α : ℝ} {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hn : p ∉ primeSet α)
    (hlo : (q : ℝ) ≤ α * p) : (q : ℝ) + 1 ≤ α * p := by
  by_contra h
  have hf : ⌊(α * p)⌋₊ = q :=
    (Nat.floor_eq_iff ((Nat.cast_nonneg q).trans hlo)).mpr
      ⟨hlo, lt_of_not_ge h⟩
  apply hn
  exact ⟨hp, hf.symm ▸ hq⟩

/-- Every slope in this closed interval has a prime-pair witness between 101 and 313. -/
theorem exists_prime_pair_100_313 {α : ℝ}
    (hlo : (6 : ℝ) / 5 ≤ α) (hhi : α ≤ (3 : ℝ) / 2) :
    ∃ p : ℕ, 100 < p ∧ p ≤ 313 ∧ p ∈ primeSet α := by
  by_contra hn
  push_neg at hn
  have h1 : (158 : ℝ) ≤ α * 131 := by
    have hh := advance (p := 131) (q := 157) (by norm_num) (by norm_num)
      (hn 131 (by norm_num) (by norm_num)) (by norm_num; linarith only [hlo])
    norm_num at hh
    exact hh
  have h2 : (132 : ℝ) ≤ α * 109 := by
    have hh := advance (p := 109) (q := 131) (by norm_num) (by norm_num)
      (hn 109 (by norm_num) (by norm_num)) (by norm_num; linarith only [h1])
    norm_num at hh
    exact hh
  have h3 : (198 : ℝ) ≤ α * 163 := by
    have hh := advance (p := 163) (q := 197) (by norm_num) (by norm_num)
      (hn 163 (by norm_num) (by norm_num)) (by norm_num; linarith only [h2])
    norm_num at hh
    exact hh
  have h4 : (138 : ℝ) ≤ α * 113 := by
    have hh := advance (p := 113) (q := 137) (by norm_num) (by norm_num)
      (hn 113 (by norm_num) (by norm_num)) (by norm_num; linarith only [h3])
    norm_num at hh
    exact hh
  have h5 : (200 : ℝ) ≤ α * 163 := by
    have hh := advance (p := 163) (q := 199) (by norm_num) (by norm_num)
      (hn 163 (by norm_num) (by norm_num)) (by norm_num; linarith only [h4])
    norm_num at hh
    exact hh
  have h6 : (132 : ℝ) ≤ α * 107 := by
    have hh := advance (p := 107) (q := 131) (by norm_num) (by norm_num)
      (hn 107 (by norm_num) (by norm_num)) (by norm_num; linarith only [h5])
    norm_num at hh
    exact hh
  have h7 : (128 : ℝ) ≤ α * 103 := by
    have hh := advance (p := 103) (q := 127) (by norm_num) (by norm_num)
      (hn 103 (by norm_num) (by norm_num)) (by norm_num; linarith only [h6])
    norm_num at hh
    exact hh
  have h8 : (278 : ℝ) ≤ α * 223 := by
    have hh := advance (p := 223) (q := 277) (by norm_num) (by norm_num)
      (hn 223 (by norm_num) (by norm_num)) (by norm_num; linarith only [h7])
    norm_num at hh
    exact hh
  have h9 : (164 : ℝ) ≤ α * 131 := by
    have hh := advance (p := 131) (q := 163) (by norm_num) (by norm_num)
      (hn 131 (by norm_num) (by norm_num)) (by norm_num; linarith only [h8])
    norm_num at hh
    exact hh
  have h10 : (240 : ℝ) ≤ α * 191 := by
    have hh := advance (p := 191) (q := 239) (by norm_num) (by norm_num)
      (hn 191 (by norm_num) (by norm_num)) (by norm_num; linarith only [h9])
    norm_num at hh
    exact hh
  have h11 : (198 : ℝ) ≤ α * 157 := by
    have hh := advance (p := 157) (q := 197) (by norm_num) (by norm_num)
      (hn 157 (by norm_num) (by norm_num)) (by norm_num; linarith only [h10])
    norm_num at hh
    exact hh
  have h12 : (128 : ℝ) ≤ α * 101 := by
    have hh := advance (p := 101) (q := 127) (by norm_num) (by norm_num)
      (hn 101 (by norm_num) (by norm_num)) (by norm_num; linarith only [h11])
    norm_num at hh
    exact hh
  have h13 : (192 : ℝ) ≤ α * 151 := by
    have hh := advance (p := 151) (q := 191) (by norm_num) (by norm_num)
      (hn 151 (by norm_num) (by norm_num)) (by norm_num; linarith only [h12])
    norm_num at hh
    exact hh
  have h14 : (200 : ℝ) ≤ α * 157 := by
    have hh := advance (p := 157) (q := 199) (by norm_num) (by norm_num)
      (hn 157 (by norm_num) (by norm_num)) (by norm_num; linarith only [h13])
    norm_num at hh
    exact hh
  have h15 : (132 : ℝ) ≤ α * 103 := by
    have hh := advance (p := 103) (q := 131) (by norm_num) (by norm_num)
      (hn 103 (by norm_num) (by norm_num)) (by norm_num; linarith only [h14])
    norm_num at hh
    exact hh
  have h16 : (138 : ℝ) ≤ α * 107 := by
    have hh := advance (p := 107) (q := 137) (by norm_num) (by norm_num)
      (hn 107 (by norm_num) (by norm_num)) (by norm_num; linarith only [h15])
    norm_num at hh
    exact hh
  have h17 : (180 : ℝ) ≤ α * 139 := by
    have hh := advance (p := 139) (q := 179) (by norm_num) (by norm_num)
      (hn 139 (by norm_num) (by norm_num)) (by norm_num; linarith only [h16])
    norm_num at hh
    exact hh
  have h18 : (212 : ℝ) ≤ α * 163 := by
    have hh := advance (p := 163) (q := 211) (by norm_num) (by norm_num)
      (hn 163 (by norm_num) (by norm_num)) (by norm_num; linarith only [h17])
    norm_num at hh
    exact hh
  have h19 : (140 : ℝ) ≤ α * 107 := by
    have hh := advance (p := 107) (q := 139) (by norm_num) (by norm_num)
      (hn 107 (by norm_num) (by norm_num)) (by norm_num; linarith only [h18])
    norm_num at hh
    exact hh
  have h20 : (180 : ℝ) ≤ α * 137 := by
    have hh := advance (p := 137) (q := 179) (by norm_num) (by norm_num)
      (hn 137 (by norm_num) (by norm_num)) (by norm_num; linarith only [h19])
    norm_num at hh
    exact hh
  have h21 : (228 : ℝ) ≤ α * 173 := by
    have hh := advance (p := 173) (q := 227) (by norm_num) (by norm_num)
      (hn 173 (by norm_num) (by norm_num)) (by norm_num; linarith only [h20])
    norm_num at hh
    exact hh
  have h22 : (200 : ℝ) ≤ α * 151 := by
    have hh := advance (p := 151) (q := 199) (by norm_num) (by norm_num)
      (hn 151 (by norm_num) (by norm_num)) (by norm_num; linarith only [h21])
    norm_num at hh
    exact hh
  have h23 : (230 : ℝ) ≤ α * 173 := by
    have hh := advance (p := 173) (q := 229) (by norm_num) (by norm_num)
      (hn 173 (by norm_num) (by norm_num)) (by norm_num; linarith only [h22])
    norm_num at hh
    exact hh
  have h24 : (390 : ℝ) ≤ α * 293 := by
    have hh := advance (p := 293) (q := 389) (by norm_num) (by norm_num)
      (hn 293 (by norm_num) (by norm_num)) (by norm_num; linarith only [h23])
    norm_num at hh
    exact hh
  have h25 : (138 : ℝ) ≤ α * 103 := by
    have hh := advance (p := 103) (q := 137) (by norm_num) (by norm_num)
      (hn 103 (by norm_num) (by norm_num)) (by norm_num; linarith only [h24])
    norm_num at hh
    exact hh
  have h26 : (152 : ℝ) ≤ α * 113 := by
    have hh := advance (p := 113) (q := 151) (by norm_num) (by norm_num)
      (hn 113 (by norm_num) (by norm_num)) (by norm_num; linarith only [h25])
    norm_num at hh
    exact hh
  have h27 : (212 : ℝ) ≤ α * 157 := by
    have hh := advance (p := 157) (q := 211) (by norm_num) (by norm_num)
      (hn 157 (by norm_num) (by norm_num)) (by norm_num; linarith only [h26])
    norm_num at hh
    exact hh
  have h28 : (140 : ℝ) ≤ α * 103 := by
    have hh := advance (p := 103) (q := 139) (by norm_num) (by norm_num)
      (hn 103 (by norm_num) (by norm_num)) (by norm_num; linarith only [h27])
    norm_num at hh
    exact hh
  have h29 : (138 : ℝ) ≤ α * 101 := by
    have hh := advance (p := 101) (q := 137) (by norm_num) (by norm_num)
      (hn 101 (by norm_num) (by norm_num)) (by norm_num; linarith only [h28])
    norm_num at hh
    exact hh
  have h30 : (270 : ℝ) ≤ α * 197 := by
    have hh := advance (p := 197) (q := 269) (by norm_num) (by norm_num)
      (hn 197 (by norm_num) (by norm_num)) (by norm_num; linarith only [h29])
    norm_num at hh
    exact hh
  have h31 : (150 : ℝ) ≤ α * 109 := by
    have hh := advance (p := 109) (q := 149) (by norm_num) (by norm_num)
      (hn 109 (by norm_num) (by norm_num)) (by norm_num; linarith only [h30])
    norm_num at hh
    exact hh
  have h32 : (192 : ℝ) ≤ α * 139 := by
    have hh := advance (p := 139) (q := 191) (by norm_num) (by norm_num)
      (hn 139 (by norm_num) (by norm_num)) (by norm_num; linarith only [h31])
    norm_num at hh
    exact hh
  have h33 : (140 : ℝ) ≤ α * 101 := by
    have hh := advance (p := 101) (q := 139) (by norm_num) (by norm_num)
      (hn 101 (by norm_num) (by norm_num)) (by norm_num; linarith only [h32])
    norm_num at hh
    exact hh
  have h34 : (152 : ℝ) ≤ α * 109 := by
    have hh := advance (p := 109) (q := 151) (by norm_num) (by norm_num)
      (hn 109 (by norm_num) (by norm_num)) (by norm_num; linarith only [h33])
    norm_num at hh
    exact hh
  have h35 : (150 : ℝ) ≤ α * 107 := by
    have hh := advance (p := 107) (q := 149) (by norm_num) (by norm_num)
      (hn 107 (by norm_num) (by norm_num)) (by norm_num; linarith only [h34])
    norm_num at hh
    exact hh
  have h36 : (212 : ℝ) ≤ α * 151 := by
    have hh := advance (p := 151) (q := 211) (by norm_num) (by norm_num)
      (hn 151 (by norm_num) (by norm_num)) (by norm_num; linarith only [h35])
    norm_num at hh
    exact hh
  have h37 : (314 : ℝ) ≤ α * 223 := by
    have hh := advance (p := 223) (q := 313) (by norm_num) (by norm_num)
      (hn 223 (by norm_num) (by norm_num)) (by norm_num; linarith only [h36])
    norm_num at hh
    exact hh
  have h38 : (278 : ℝ) ≤ α * 197 := by
    have hh := advance (p := 197) (q := 277) (by norm_num) (by norm_num)
      (hn 197 (by norm_num) (by norm_num)) (by norm_num; linarith only [h37])
    norm_num at hh
    exact hh
  have h39 : (180 : ℝ) ≤ α * 127 := by
    have hh := advance (p := 127) (q := 179) (by norm_num) (by norm_num)
      (hn 127 (by norm_num) (by norm_num)) (by norm_num; linarith only [h38])
    norm_num at hh
    exact hh
  have h40 : (198 : ℝ) ≤ α * 139 := by
    have hh := advance (p := 139) (q := 197) (by norm_num) (by norm_num)
      (hn 139 (by norm_num) (by norm_num)) (by norm_num; linarith only [h39])
    norm_num at hh
    exact hh
  have h41 : (444 : ℝ) ≤ α * 311 := by
    have hh := advance (p := 311) (q := 443) (by norm_num) (by norm_num)
      (hn 311 (by norm_num) (by norm_num)) (by norm_num; linarith only [h40])
    norm_num at hh
    exact hh
  have h42 : (182 : ℝ) ≤ α * 127 := by
    have hh := advance (p := 127) (q := 181) (by norm_num) (by norm_num)
      (hn 127 (by norm_num) (by norm_num)) (by norm_num; linarith only [h41])
    norm_num at hh
    exact hh
  have h43 : (200 : ℝ) ≤ α * 139 := by
    have hh := advance (p := 139) (q := 199) (by norm_num) (by norm_num)
      (hn 139 (by norm_num) (by norm_num)) (by norm_num; linarith only [h42])
    norm_num at hh
    exact hh
  have h44 : (198 : ℝ) ≤ α * 137 := by
    have hh := advance (p := 137) (q := 197) (by norm_num) (by norm_num)
      (hn 137 (by norm_num) (by norm_num)) (by norm_num; linarith only [h43])
    norm_num at hh
    exact hh
  have h45 : (164 : ℝ) ≤ α * 113 := by
    have hh := advance (p := 113) (q := 163) (by norm_num) (by norm_num)
      (hn 113 (by norm_num) (by norm_num)) (by norm_num; linarith only [h44])
    norm_num at hh
    exact hh
  have h46 : (252 : ℝ) ≤ α * 173 := by
    have hh := advance (p := 173) (q := 251) (by norm_num) (by norm_num)
      (hn 173 (by norm_num) (by norm_num)) (by norm_num; linarith only [h45])
    norm_num at hh
    exact hh
  have h47 : (282 : ℝ) ≤ α * 193 := by
    have hh := advance (p := 193) (q := 281) (by norm_num) (by norm_num)
      (hn 193 (by norm_num) (by norm_num)) (by norm_num; linarith only [h46])
    norm_num at hh
    exact hh
  have h48 : (192 : ℝ) ≤ α * 131 := by
    have hh := advance (p := 131) (q := 191) (by norm_num) (by norm_num)
      (hn 131 (by norm_num) (by norm_num)) (by norm_num; linarith only [h47])
    norm_num at hh
    exact hh
  have h49 : (354 : ℝ) ≤ α * 241 := by
    have hh := advance (p := 241) (q := 353) (by norm_num) (by norm_num)
      (hn 241 (by norm_num) (by norm_num)) (by norm_num; linarith only [h48])
    norm_num at hh
    exact hh
  have h50 : (158 : ℝ) ≤ α * 107 := by
    have hh := advance (p := 107) (q := 157) (by norm_num) (by norm_num)
      (hn 107 (by norm_num) (by norm_num)) (by norm_num; linarith only [h49])
    norm_num at hh
    exact hh
  have h51 : (150 : ℝ) ≤ α * 101 := by
    have hh := advance (p := 101) (q := 149) (by norm_num) (by norm_num)
      (hn 101 (by norm_num) (by norm_num)) (by norm_num; linarith only [h50])
    norm_num at hh
    exact hh
  have h52 : (234 : ℝ) ≤ α * 157 := by
    have hh := advance (p := 157) (q := 233) (by norm_num) (by norm_num)
      (hn 157 (by norm_num) (by norm_num)) (by norm_num; linarith only [h51])
    norm_num at hh
    exact hh
  have h53 : (384 : ℝ) ≤ α * 257 := by
    have hh := advance (p := 257) (q := 383) (by norm_num) (by norm_num)
      (hn 257 (by norm_num) (by norm_num)) (by norm_num; linarith only [h52])
    norm_num at hh
    exact hh
  have h54 : (468 : ℝ) ≤ α * 313 := by
    have hh := advance (p := 313) (q := 467) (by norm_num) (by norm_num)
      (hn 313 (by norm_num) (by norm_num)) (by norm_num; linarith only [h53])
    norm_num at hh
    exact hh
  have h55 : (152 : ℝ) ≤ α * 101 := by
    have hh := advance (p := 101) (q := 151) (by norm_num) (by norm_num)
      (hn 101 (by norm_num) (by norm_num)) (by norm_num; linarith only [h54])
    norm_num at hh
    exact hh
  linarith only [h55, hhi]

#print axioms exists_prime_pair_100_313

end FiniteCover972
