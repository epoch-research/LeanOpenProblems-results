import Submission.Reductions

/-!
# Local arithmetic structure of cube-Sidon sets

These are unconditional local building blocks, not a proof of the positive-density
statement in `Submission.Spec` (which is not imported). Repeated summands and the
root zero are allowed unless a theorem explicitly says otherwise.

The sum and the sum of cubes determine an unordered pair. For a cube-Sidon set,
insertion witnesses sharing a positive root coincide, and a fixed negative root
determines the positive unordered pair.

The congruence `n ^ 3 ≡ n (mod 6)` gives the conservative local bound
`L ^ 2 ≤ 12 * M` for cube-Sidonicity of `[M, M + L]`. In particular, if
`100 ≤ M` and `L ^ 2 ≤ M`, adjoining any one natural root preserves Sidonicity.
No global forbidden-root estimate or density claim is assumed or proved.
-/

namespace Erdos1206

/-- The sum and the sum of cubes determine an unordered pair of natural roots. -/
theorem unordered_pair_eq_of_sum_eq_of_cube_sum_eq {a b c d : ℕ}
    (hsum : a + b = c + d) (hcube : a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  by_cases hz : a + b = 0
  · left
    omega
  have hs : (a : ℤ) + b = c + d := by exact_mod_cast hsum
  have hc : (a : ℤ) ^ 3 + b ^ 3 = c ^ 3 + d ^ 3 := by exact_mod_cast hcube
  have hm : (3 * ((a : ℤ) + b)) * ((a : ℤ) * b) =
      (3 * ((a : ℤ) + b)) * ((c : ℤ) * d) := by
    have hm' : (3 * ((a : ℤ) + b)) * ((a : ℤ) * b) =
        (3 * ((c : ℤ) + d)) * ((c : ℤ) * d) := by
      nlinarith only [hc, congrArg (fun x : ℤ => x ^ 3) hs]
    rwa [← hs] at hm'
  have hp : (a : ℤ) * b = c * d :=
    mul_left_cancel₀ (by exact_mod_cast (show 3 * (a + b) ≠ 0 by omega)) hm
  have hf : ((a : ℤ) - c) * ((a : ℤ) - d) = 0 := by
    nlinarith [congrArg (fun x : ℤ => (a : ℤ) * x) hs]
  rcases mul_eq_zero.mp hf with h | h
  · have hac : a = c := by exact_mod_cast (sub_eq_zero.mp h)
    exact Or.inl ⟨hac, by omega⟩
  · have had : a = d := by exact_mod_cast (sub_eq_zero.mp h)
    exact Or.inr ⟨had, by omega⟩

/-- In an outside-root insertion witness, the negative old root is different
from both positive old roots. No Sidon hypothesis is needed for cancellation. -/
theorem insertion_witness_negative_ne {A : Finset ℕ} {n a b c : ℕ}
    (hn : n ∉ A) (hb : b ∈ A) (hc : c ∈ A)
    (h : n ^ 3 + a ^ 3 = b ^ 3 + c ^ 3) : a ≠ b ∧ a ≠ c := by
  constructor
  · intro hab
    have hnc : n = c := cube_injective (by change n ^ 3 = c ^ 3; rw [hab] at h; omega)
    exact hn (hnc.symm ▸ hc)
  · intro hac
    have hnb : n = b := cube_injective (by change n ^ 3 = b ^ 3; rw [hac] at h; omega)
    exact hn (hnb.symm ▸ hb)

/-- Two insertion witnesses with a shared positive root are identical, with
the same negative root and the same other positive root. -/
theorem CubeSidon.insertion_witness_shared_positive {A : Finset ℕ}
    (hA : CubeSidon A) {n a b c d e : ℕ} (hn : n ∉ A)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) (he : e ∈ A)
    (h₁ : n ^ 3 + a ^ 3 = b ^ 3 + c ^ 3)
    (h₂ : n ^ 3 + d ^ 3 = b ^ 3 + e ^ 3) : a = d ∧ c = e := by
  have hx : a ^ 3 + e ^ 3 = d ^ 3 + c ^ 3 := by omega
  rcases hA a ha e he d hd c hc hx with ⟨had, hec⟩ | ⟨hac, _⟩
  · exact ⟨had, hec.symm⟩
  · exact ((insertion_witness_negative_ne hn hb hc h₁).2 hac).elim

/-- Fixing the negative root of an insertion witness fixes the positive
unordered pair. The fixed roots need not themselves belong to `A`. -/
theorem CubeSidon.insertion_witness_shared_negative {A : Finset ℕ}
    (hA : CubeSidon A) {n a b c d e : ℕ}
    (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) (he : e ∈ A)
    (h₁ : n ^ 3 + a ^ 3 = b ^ 3 + c ^ 3)
    (h₂ : n ^ 3 + a ^ 3 = d ^ 3 + e ^ 3) :
    (b = d ∧ c = e) ∨ (b = e ∧ c = d) := by
  exact hA b hb c hc d hd e he (by omega)

/-- The repeated-new-root obstruction also has at most one old unordered pair. -/
theorem CubeSidon.double_insertion_witness_unique {A : Finset ℕ}
    (hA : CubeSidon A) {n a b c d : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (h₁ : n ^ 3 + n ^ 3 = a ^ 3 + b ^ 3)
    (h₂ : n ^ 3 + n ^ 3 = c ^ 3 + d ^ 3) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  exact hA a ha b hb c hc d hd (by omega)

/-- Cubing does not change a natural number modulo six. -/
theorem cube_mod_six (n : ℕ) : n ^ 3 % 6 = n % 6 := by
  rw [Nat.pow_mod]
  have hlt : n % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases n % 6 <;> decide

/-- Equal cube sums have congruent root sums modulo six. -/
theorem cube_sum_eq_implies_sum_mod_six {a b c d : ℕ}
    (h : a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3) : (a + b) % 6 = (c + d) % 6 := by
  simpa only [Nat.add_mod, cube_mod_six, Nat.mod_mod] using congrArg (fun n : ℕ => n % 6) h

/-- If the root sums in a cube collision differ, the pair with the smaller
sum has squared gap strictly greater than six times that sum. -/
theorem cube_collision_pair_gap {a b c d : ℕ}
    (hsum : a + b < c + d) (hcube : a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3) :
    6 * ((a : ℤ) + b) < ((a : ℤ) - b) ^ 2 := by
  have hmod := cube_sum_eq_implies_sum_mod_six hcube
  have hsum6 : a + b + 6 ≤ c + d := by omega
  have hs6 : (a : ℤ) + b + 6 ≤ (c : ℤ) + d := by exact_mod_cast hsum6
  have hs0 : (0 : ℤ) ≤ (a : ℤ) + b := by positivity
  have ht0 : (0 : ℤ) ≤ (c : ℤ) + d := by positivity
  have heq : ((a : ℤ) + b) ^ 3 + 3 * ((a : ℤ) + b) * ((a : ℤ) - b) ^ 2 =
      ((c : ℤ) + d) ^ 3 + 3 * ((c : ℤ) + d) * ((c : ℤ) - d) ^ 2 := by
    have hc : (a : ℤ) ^ 3 + b ^ 3 = c ^ 3 + d ^ 3 := by exact_mod_cast hcube
    nlinarith only [hc]
  by_contra h
  have hbound : ((a : ℤ) - b) ^ 2 ≤ 6 * ((a : ℤ) + b) := le_of_not_gt h
  have hp := mul_nonneg hs0 (sub_nonneg.mpr hbound)
  have hq := mul_nonneg ht0 (sq_nonneg ((c : ℤ) - d))
  have hpow : ((a : ℤ) + b + 6) ^ 3 ≤ ((c : ℤ) + d) ^ 3 :=
    pow_le_pow_left₀ (by omega) hs6 3
  nlinarith only [hp, hq, hpow, heq, hs0]

private theorem sq_gap_le_of_mem_Icc {M L a b : ℕ}
    (ha : a ∈ Finset.Icc M (M + L)) (hb : b ∈ Finset.Icc M (M + L)) :
    ((a : ℤ) - b) ^ 2 ≤ (L : ℤ) ^ 2 := by
  simp only [Finset.mem_Icc] at ha hb
  have hleft : (0 : ℤ) ≤ (L : ℤ) - ((a : ℤ) - b) := by omega
  have hright : (0 : ℤ) ≤ (L : ℤ) + ((a : ℤ) - b) := by omega
  nlinarith only [mul_nonneg hleft hright]

/-- An elementary short-interval Sidon bound, with constant twelve. -/
theorem cubeSidon_Icc_of_sq_le_twelve_mul {M L : ℕ} (hLM : L ^ 2 ≤ 12 * M) :
    CubeSidon (Finset.Icc M (M + L)) := by
  intro a ha b hb c hc d hd heq
  apply unordered_pair_eq_of_sum_eq_of_cube_sum_eq ?_ heq
  have hLM' : (L : ℤ) ^ 2 ≤ 12 * (M : ℤ) := by exact_mod_cast hLM
  rcases lt_trichotomy (a + b) (c + d) with hlt | he | hlt
  · have hgap := cube_collision_pair_gap hlt heq
    have hbound := sq_gap_le_of_mem_Icc ha hb
    have haM := (Finset.mem_Icc.mp ha).1
    have hbM := (Finset.mem_Icc.mp hb).1
    omega
  · exact he
  · have hgap := cube_collision_pair_gap hlt heq.symm
    have hbound := sq_gap_le_of_mem_Icc hc hd
    have hcM := (Finset.mem_Icc.mp hc).1
    have hdM := (Finset.mem_Icc.mp hd).1
    omega

/-- The actual cubes in a short interval form a Sidon set. -/
theorem isSidon_image_cubes_Icc_of_sq_le_twelve_mul {M L : ℕ}
    (hLM : L ^ 2 ≤ 12 * M) :
    IsSidon (↑((Finset.Icc M (M + L)).image (fun n => n ^ 3)) : Set ℕ) :=
  (cubeSidon_iff_isSidon_image _).mp (cubeSidon_Icc_of_sq_le_twelve_mul hLM)

/-- A completion of three roots in a short interval remains in a controlled
expanded interval. The lower endpoint is stated without natural subtraction. -/
theorem cube_completion_bounds {M L n a b c : ℕ} (hLM : 5 * L ≤ M)
    (ha : a ∈ Finset.Icc M (M + L)) (hb : b ∈ Finset.Icc M (M + L))
    (hc : c ∈ Finset.Icc M (M + L))
    (heq : n ^ 3 + a ^ 3 = b ^ 3 + c ^ 3) :
    M ≤ n + 2 * L ∧ n ≤ M + 2 * L := by
  have haL := Nat.pow_le_pow_left (Finset.mem_Icc.mp ha).1 3
  have haU := Nat.pow_le_pow_left (Finset.mem_Icc.mp ha).2 3
  have hbL := Nat.pow_le_pow_left (Finset.mem_Icc.mp hb).1 3
  have hbU := Nat.pow_le_pow_left (Finset.mem_Icc.mp hb).2 3
  have hcL := Nat.pow_le_pow_left (Finset.mem_Icc.mp hc).1 3
  have hcU := Nat.pow_le_pow_left (Finset.mem_Icc.mp hc).2 3
  constructor
  · have hLM' : 5 * (L : ℤ) ≤ M := by exact_mod_cast hLM
    have heq' : (n : ℤ) ^ 3 + (a : ℤ) ^ 3 = (b : ℤ) ^ 3 + (c : ℤ) ^ 3 := by
      exact_mod_cast heq
    have haU' : (a : ℤ) ^ 3 ≤ ((M : ℤ) + L) ^ 3 := by exact_mod_cast haU
    have hbL' : (M : ℤ) ^ 3 ≤ (b : ℤ) ^ 3 := by exact_mod_cast hbL
    have hcL' : (M : ℤ) ^ 3 ≤ (c : ℤ) ^ 3 := by exact_mod_cast hcL
    have hpoly : ((M : ℤ) - 2 * L) ^ 3 + ((M : ℤ) + L) ^ 3 ≤ 2 * (M : ℤ) ^ 3 := by
      have hp : 0 ≤ (M : ℤ) * ((M : ℤ) - 5 * L) :=
        mul_nonneg (Int.natCast_nonneg M) (by omega)
      have hq : 0 ≤ 3 * (M : ℤ) ^ 2 - 15 * (M : ℤ) * L + 7 * (L : ℤ) ^ 2 := by
        nlinarith only [hp, sq_nonneg (L : ℤ)]
      have hr := mul_nonneg (Int.natCast_nonneg L) hq
      nlinarith only [hr]
    have hn3 : ((M : ℤ) - 2 * L) ^ 3 ≤ (n : ℤ) ^ 3 := by
      linarith only [hpoly, haU', hbL', hcL', heq']
    by_contra h
    have hlt : (n : ℤ) < (M : ℤ) - 2 * L := by omega
    have hlt3 : (n : ℤ) ^ 3 < ((M : ℤ) - 2 * L) ^ 3 :=
      pow_lt_pow_left₀ hlt (Int.natCast_nonneg n) (by decide)
    omega
  · have hpoly : 2 * (M + L) ^ 3 ≤ (M + 2 * L) ^ 3 + M ^ 3 := by
      nlinarith only [Nat.zero_le (M * L ^ 2), Nat.zero_le (L ^ 3)]
    have hn3 : n ^ 3 ≤ (M + 2 * L) ^ 3 := by omega
    exact (Nat.pow_le_pow_iff_left (by decide : 3 ≠ 0)).mp hn3

/-- A root whose doubled cube is a sum of two cubes from an interval lies
in that same interval. -/
theorem double_cube_sum_mem_Icc {M L n a b : ℕ}
    (ha : a ∈ Finset.Icc M (M + L)) (hb : b ∈ Finset.Icc M (M + L))
    (heq : n ^ 3 + n ^ 3 = a ^ 3 + b ^ 3) :
    n ∈ Finset.Icc M (M + L) := by
  rw [Finset.mem_Icc]
  constructor
  · by_contra h
    have hn : n < M := by omega
    have hn3 := Nat.pow_lt_pow_left hn (by decide : 3 ≠ 0)
    have ha3 := Nat.pow_le_pow_left (Finset.mem_Icc.mp ha).1 3
    have hb3 := Nat.pow_le_pow_left (Finset.mem_Icc.mp hb).1 3
    omega
  · by_contra h
    have hn : M + L < n := by omega
    have hn3 := Nat.pow_lt_pow_left hn (by decide : 3 ≠ 0)
    have ha3 := Nat.pow_le_pow_left (Finset.mem_Icc.mp ha).2 3
    have hb3 := Nat.pow_le_pow_left (Finset.mem_Icc.mp hb).2 3
    omega

/-- An interval of square-root length at height at least one hundred tolerates
any single extra natural root, even zero. -/
theorem cubeSidon_insert_Icc_of_sq_le {M L : ℕ} (hM : 100 ≤ M) (hL : L ^ 2 ≤ M)
    (n : ℕ) : CubeSidon (insert n (Finset.Icc M (M + L))) := by
  have hI : CubeSidon (Finset.Icc M (M + L)) :=
    cubeSidon_Icc_of_sq_le_twelve_mul (by omega)
  by_cases hn : n ∈ Finset.Icc M (M + L)
  · simpa only [Finset.insert_eq_of_mem hn] using hI
  have h10 : 10 * L ≤ M := by
    by_cases h : L ≤ 10
    · omega
    · nlinarith only [hL, h]
  apply (cubeSidon_insert_iff hI hn).mpr
  intro a ha b hb
  constructor
  · intro heq
    exact hn (double_cube_sum_mem_Icc ha hb heq)
  · intro c hc heq
    have hbounds := cube_completion_bounds (by omega : 5 * L ≤ M) ha hb hc heq
    have close (K W : ℕ) (hW : W ^ 2 ≤ 12 * K)
        (hnK : n ∈ Finset.Icc K (K + W))
        (hIK : Finset.Icc M (M + L) ⊆ Finset.Icc K (K + W)) : False := by
      have hK := cubeSidon_Icc_of_sq_le_twelve_mul hW
      rcases hK n hnK a (hIK ha) b (hIK hb) c (hIK hc) heq with ⟨hnb, _⟩ | ⟨hnc, _⟩
      · exact hn (hnb.symm ▸ hb)
      · exact hn (hnc.symm ▸ hc)
    by_cases hnm : n < M
    · have hbase : M - 2 * L + 2 * L = M := Nat.sub_add_cancel (by omega)
      apply close (M - 2 * L) (3 * L)
      · nlinarith only [hbase, hL, h10]
      · simp only [Finset.mem_Icc]
        omega
      · intro x hx
        simp only [Finset.mem_Icc] at hx ⊢
        omega
    · apply close M (2 * L)
      · nlinarith only [hL, Nat.zero_le M]
      · simp only [Finset.mem_Icc]
        omega
      · intro x hx
        simp only [Finset.mem_Icc] at hx ⊢
        omega

/-- Image formulation of the protected one-root extension. -/
theorem isSidon_image_cubes_insert_Icc_of_sq_le {M L : ℕ}
    (hM : 100 ≤ M) (hL : L ^ 2 ≤ M) (n : ℕ) :
    IsSidon (↑((insert n (Finset.Icc M (M + L))).image (fun x => x ^ 3)) : Set ℕ) :=
  (cubeSidon_iff_isSidon_image _).mp (cubeSidon_insert_Icc_of_sq_le hM hL n)

/-- A protected interval has no forbidden insertion roots, at any ambient height. -/
theorem forbiddenRoots_Icc_eq_empty {M L : ℕ} (hM : 100 ≤ M) (hL : L ^ 2 ≤ M)
    (N : ℕ) : forbiddenRoots N (Finset.Icc M (M + L)) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  have hI : CubeSidon (Finset.Icc M (M + L)) :=
    cubeSidon_Icc_of_sq_le_twelve_mul (by omega)
  have hf := (mem_forbiddenRoots_iff_not_cubeSidon_insert hI).mp hn
  exact hf.2.2 (cubeSidon_insert_Icc_of_sq_le hM hL n)

end Erdos1206
