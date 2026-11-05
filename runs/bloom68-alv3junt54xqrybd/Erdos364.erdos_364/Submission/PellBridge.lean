import Submission.ChebyshevDescent
import Mathlib.NumberTheory.Pell

/-!
# The actual powerful-triple Pell bridge

An unconditional structural helper for Erdős problem 364. A hypothetical full
natural triple supplies a least full center via `Nat.find`, and its positive
canonical square--cube factors supply a positive, nonsquare Pell parameter.
Mathlib's fundamental-solution theorem then supplies the unit and natural index.

The power recurrence identifies its x-coordinate with the existing integer
Chebyshev evaluation. Four-divisibility of the *powered point*, not merely
`d ≡ 7 mod 8`, forces an even fundamental seed divisible by four and an odd,
positive index. Leastness and `ChebyshevDescent.least_full_index_squarefree`
then make that index squarefree.

The main APIs are `natFull_exists_fundamental_pell`,
`leastNatFull_exists_squarefree_pell`, and
`exists_powerful_triple_iff_exists_least_Pell_full`. The complete witness
`SquarefreePellFull` retains all three positive canonical decompositions and
both coordinates of the Pell power, including the middle entry's powerfulness.

No existence or nonexistence of a full triple is asserted. In particular the
index-one case and the global EMW exclusion remain unresolved. The original
specification is neither imported nor used.
-/
namespace Erdos364.PellBridge

open Erdos364.PowerfulStructure Erdos364.ChebyshevDescent

/-- Natural centered powerfulness. The lower bound is kept separate. -/
def NatFull (t : ℕ) : Prop :=
  Nat.Powerful (t - 1) ∧ Nat.Powerful t ∧ Nat.Powerful (t + 1)

/-- The least nondegenerate natural full center. -/
def LeastNatFull (t : ℕ) : Prop :=
  4 ≤ t ∧ NatFull t ∧ ∀ s : ℕ, 4 ≤ s → NatFull s → t ≤ s

/-- The positive canonical square--cube decompositions of all three entries. -/
def CanonicalTriple (t A B C a b c : ℕ) : Prop :=
  (0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < a ∧ 0 < b ∧ 0 < c) ∧
  (Squarefree A ∧ Squarefree B ∧ Squarefree C) ∧
  (Nat.Coprime A B ∧ Nat.Coprime A C ∧ Nat.Coprime B C) ∧
  (t - 1 = A ^ 3 * a ^ 2 ∧ t = B ^ 3 * b ^ 2 ∧ t + 1 = C ^ 3 * c ^ 2)

/-- The natural and signed formulations agree once subtraction is exact. -/
theorem natFull_iff_full {t : ℕ} (ht : 1 ≤ t) : NatFull t ↔ Full (t : ℤ) :=
  (full_natCast_iff ht).symm

/-- An actual nondegenerate full center is at least four, divisible by four,
even, and has pairwise coprime entries. -/
theorem natFull_properties {t : ℕ} (ht : 2 ≤ t) (h : NatFull t) :
    4 ≤ t ∧ 4 ∣ t ∧ Even t ∧
    (Nat.Coprime (t - 1) t ∧ Nat.Coprime (t - 1) (t + 1) ∧ Nat.Coprime t (t + 1)) := by
  have h1 : t - 1 + 1 = t := by omega
  have h2 : t - 1 + 2 = t + 1 := by omega
  have htr : Nat.Powerful (t - 1) ∧ Nat.Powerful (t - 1 + 1) ∧
      Nat.Powerful (t - 1 + 2) := by simpa only [h1, h2] using h
  have hp := triple_middle_properties htr
  have hfour : 4 ∣ t := Nat.dvd_of_mod_eq_zero (by omega)
  exact ⟨by omega, hfour, by simpa only [h1] using hp.2.2,
    centered_pairwise_coprime ht (by simpa only [h1] using hp.2.2)⟩

/-- Exact transfer of leastness between natural and positive signed centers. -/
theorem leastNatFull_iff_leastFull {t : ℕ} : LeastNatFull t ↔ LeastFull (t : ℤ) := by
  constructor
  · rintro ⟨ht, hf, hmin⟩
    refine ⟨by exact_mod_cast ht, (natFull_iff_full (by omega)).mp hf, ?_⟩
    intro s hs hsf
    have hsn : 4 ≤ s.toNat := by omega
    have hnat : NatFull s.toNat := (full_iff_toNat (by omega)).mp hsf
    have hle := hmin s.toNat hsn hnat
    have hle' : (t : ℤ) ≤ (s.toNat : ℤ) := by exact_mod_cast hle
    simpa only [Int.toNat_of_nonneg (show 0 ≤ s by omega)] using hle'
  · rintro ⟨ht, hf, hmin⟩
    have htn : 4 ≤ t := by exact_mod_cast ht
    refine ⟨htn, (natFull_iff_full (by omega)).mpr hf, ?_⟩
    intro s hs hsf
    exact_mod_cast hmin (s : ℤ) (by exact_mod_cast hs)
      ((natFull_iff_full (by omega)).mp hsf)

/-- A hypothetical actual triple has a least nondegenerate full center,
chosen by `Nat.find`, without using any conjectural exclusion theorem. -/
theorem exists_leastNatFull_of_exists_powerful_triple
    (h : ∃ k : ℕ, Nat.Powerful k ∧ Nat.Powerful (k + 1) ∧ Nat.Powerful (k + 2)) :
    ∃ t : ℕ, LeastNatFull t := by
  classical
  have hex : ∃ t : ℕ, 4 ≤ t ∧ NatFull t := by
    obtain ⟨k, hk⟩ := h
    have hp := triple_middle_properties hk
    refine ⟨k + 1, hp.1, ?_⟩
    simpa only [NatFull, Nat.add_sub_cancel, Nat.add_assoc] using hk
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro s hs hsf
  exact Nat.find_min' hex ⟨hs, hsf⟩

private theorem cube_factor_dvd (A a : ℕ) : A ∣ A ^ 3 * a ^ 2 :=
  dvd_mul_of_dvd_left (dvd_pow_self A (by decide : 3 ≠ 0)) _

/-- Decompose all three actual powerful entries into their positive
square--cube forms, with pairwise coprime squarefree cube kernels. -/
theorem natFull_exists_canonical {t : ℕ} (ht : 2 ≤ t) (h : NatFull t) :
    ∃ A B C a b c : ℕ, CanonicalTriple t A B C a b c := by
  have hp := natFull_properties ht h
  obtain ⟨a, A, ha, hA, hsA, heA⟩ :=
    (powerful_iff_positive_sq_mul_cube_squarefree (show 0 < t - 1 by omega)).mp h.1
  obtain ⟨b, B, hb, hB, hsB, heB⟩ :=
    (powerful_iff_positive_sq_mul_cube_squarefree (show 0 < t by omega)).mp h.2.1
  obtain ⟨c, C, hc, hC, hsC, heC⟩ :=
    (powerful_iff_positive_sq_mul_cube_squarefree (show 0 < t + 1 by omega)).mp h.2.2
  have heA' : t - 1 = A ^ 3 * a ^ 2 := by simpa only [mul_comm] using heA
  have heB' : t = B ^ 3 * b ^ 2 := by simpa only [mul_comm] using heB
  have heC' : t + 1 = C ^ 3 * c ^ 2 := by simpa only [mul_comm] using heC
  have hdA : A ∣ t - 1 := heA' ▸ cube_factor_dvd A a
  have hdB : B ∣ t := heB' ▸ cube_factor_dvd B b
  have hdC : C ∣ t + 1 := heC' ▸ cube_factor_dvd C c
  refine ⟨A, B, C, a, b, c, ⟨hA, hB, hC, ha, hb, hc⟩, ⟨hsA, hsB, hsC⟩,
    ⟨(hp.2.2.2.1.coprime_dvd_left hdA).coprime_dvd_right hdB,
      (hp.2.2.2.2.1.coprime_dvd_left hdA).coprime_dvd_right hdC,
      (hp.2.2.2.2.2.coprime_dvd_left hdB).coprime_dvd_right hdC⟩, heA', heB', heC'⟩

/-- The canonical endpoint product is the norm-one Pell identity over `ℕ`. -/
theorem canonical_pell_norm {t A B C a b c : ℕ} (ht : 2 ≤ t)
    (h : CanonicalTriple t A B C a b c) :
    t ^ 2 = 1 + (A * C) * ((A * C) * a * c) ^ 2 := by
  obtain ⟨_, _, _, hlow, _, hhigh⟩ := h
  have hsub : t - 1 + 1 = t := by omega
  calc
    t ^ 2 = (t - 1) * (t + 1) + 1 := by nlinarith
    _ = 1 + (A * C) * ((A * C) * a * c) ^ 2 := by rw [hlow, hhigh]; ring

private theorem odd_sq_mod_eight {x : ℕ} (hx : Odd x) : x ^ 2 % 8 = 1 := by
  have ho := Nat.odd_iff.mp hx
  have hm := Nat.mod_lt x (by decide : 0 < 8)
  have hmod : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  rcases hmod with h | h | h | h <;> simp [Nat.pow_mod, h]

private theorem four_dvd_sq_mod_eight {x : ℕ} (hx : 4 ∣ x) : x ^ 2 % 8 = 0 := by
  have ho := Nat.mod_eq_zero_of_dvd hx
  have hm := Nat.mod_lt x (by decide : 0 < 8)
  have hmod : x % 8 = 0 ∨ x % 8 = 4 := by omega
  rcases hmod with h | h <;> simp [Nat.pow_mod, h]

/-- For a natural norm-one point with center divisible by four,
the parameter is seven modulo eight and the second coordinate is odd. -/
theorem pell_parameter_mod_eight {t d y : ℕ} (ht : 4 ∣ t)
    (h : t ^ 2 = 1 + d * y ^ 2) : d % 8 = 7 ∧ Odd y := by
  have ht2 : t % 2 = 0 := Nat.mod_eq_zero_of_dvd
    (dvd_trans (by decide : 2 ∣ 4) ht)
  have h2 := congrArg (fun z : ℕ => z % 2) h
  dsimp only at h2
  rw [Nat.pow_mod, ht2, zero_pow (by decide : (2 : ℕ) ≠ 0), Nat.add_mod] at h2
  norm_num at h2
  have hdy : Odd (d * y ^ 2) := Nat.odd_iff.mpr (by omega)
  have hy : Odd y := hdy.of_dvd_nat
    (dvd_mul_of_dvd_right (dvd_pow_self y (by decide : 2 ≠ 0)) d)
  refine ⟨?_, hy⟩
  have h8 := congrArg (fun z : ℕ => z % 8) h
  dsimp only at h8
  rw [four_dvd_sq_mod_eight ht, Nat.add_mod, Nat.mul_mod, odd_sq_mod_eight hy] at h8
  norm_num at h8
  omega

/-- Signed norm-one equation for the exact canonical point `(t, A*C*a*c)`. -/
theorem canonical_pell_equation {t A B C a b c : ℕ} (ht : 2 ≤ t)
    (hc : CanonicalTriple t A B C a b c) :
    (t : ℤ) ^ 2 - ((A * C : ℕ) : ℤ) * (((A * C) * a * c : ℕ) : ℤ) ^ 2 = 1 := by
  have hn : (t : ℤ) ^ 2 = 1 + ((A * C : ℕ) : ℤ) * (((A * C) * a * c : ℕ) : ℤ) ^ 2 := by
    exact_mod_cast canonical_pell_norm ht hc
  linarith

/-- The actual canonical Pell parameter is positive and squarefree,
is seven modulo eight, and is nonsquare over `ℤ`; its second coordinate is positive and odd. -/
theorem canonical_pell_properties {t A B C a b c : ℕ} (ht : 2 ≤ t)
    (h : NatFull t) (hc : CanonicalTriple t A B C a b c) :
    0 < A * C ∧ Squarefree (A * C) ∧ (A * C) % 8 = 7 ∧
      0 < (A * C) * a * c ∧ Odd ((A * C) * a * c) ∧
      ¬IsSquare ((A * C : ℕ) : ℤ) := by
  have hn := canonical_pell_norm ht hc
  have hp := natFull_properties ht h
  have hmod := pell_parameter_mod_eight hp.2.1 hn
  have hdpos : 0 < A * C := Nat.mul_pos hc.1.1 hc.1.2.2.1
  have hypos : 0 < (A * C) * a * c :=
    Nat.mul_pos (Nat.mul_pos hdpos hc.1.2.2.2.1) hc.1.2.2.2.2.2
  have hnorm := canonical_pell_equation ht hc
  let point : Pell.Solution₁ ((A * C : ℕ) : ℤ) :=
    Pell.Solution₁.mk t ((A * C) * a * c) hnorm
  refine ⟨hdpos, (Nat.squarefree_mul hc.2.2.1.2.1).mpr ⟨hc.2.1.1, hc.2.1.2.2⟩,
    hmod.1, hypos, hmod.2, ?_⟩
  exact Pell.Solution₁.d_nonsquare_of_one_lt_x (a := point) (by
    simp only [point, Pell.Solution₁.x_mk]; exact_mod_cast (show 1 < t by omega))

/-- The x-coordinates of powers of any norm-one Pell solution satisfy
the first-kind Chebyshev recurrence. No sign or nonsquare hypothesis is needed. -/
theorem pell_x_pow_add_two {d : ℤ} (ε : Pell.Solution₁ d) (n : ℕ) :
    (ε ^ (n + 2)).x = 2 * ε.x * (ε ^ (n + 1)).x - (ε ^ n).x := by
  simp only [pow_succ, Pell.Solution₁.x_mul, Pell.Solution₁.y_mul]
  linear_combination -(ε ^ n).x * ε.prop

/-- The x-coordinate of every natural Pell power is exactly `cheb`. -/
theorem pell_x_pow_eq_cheb {d : ℤ} (ε : Pell.Solution₁ d) (n : ℕ) :
    (ε ^ n).x = cheb n ε.x := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 => rw [pell_x_pow_add_two, ih0, ih1, cheb_add_two]

/-- Modulo two, every even-index value is one and every odd-index
value is the seed. This also detects the seed parity from an even powered point. -/
theorem cheb_mod_two (n : ℕ) (x : ℤ) :
    (cheb n x : ZMod 2) = if Even n then 1 else (x : ZMod 2) := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hneg (z : ZMod 2) : -z = z := by
    have hz : 2 * z = 0 := by rw [h2, zero_mul]
    linear_combination -hz
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
    rw [cheb_add_two]
    push_cast
    rw [h2, zero_mul, zero_mul, zero_sub, ih0]
    have hpar : Even (n + 2) ↔ Even n := by
      simp only [Nat.even_iff]; omega
    simp only [hpar, hneg]

/-- At any even integer seed, every odd-index value has the same
residue modulo four as that seed, regardless of its sign. -/
theorem cheb_odd_mod_four {n : ℕ} (hn : Odd n) {x : ℤ} (hx : Even x) :
    (cheb n x : ZMod 4) = (x : ZMod 4) := by
  have h2x : 2 * (x : ZMod 4) = 0 := by
    have hfour : (4 : ℤ) ∣ 2 * x := by
      obtain ⟨k, rfl⟩ := hx
      exact ⟨k, by ring⟩
    simpa only [Int.cast_mul, Int.cast_ofNat] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * x) 4).mpr hfour
  have hnegx : -(x : ZMod 4) = (x : ZMod 4) := by
    linear_combination -h2x
  obtain ⟨k, rfl⟩ := hn
  induction k with
  | zero => simp
  | succ k ih =>
    have hn' : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
    rw [hn', cheb_add_two]
    push_cast
    rw [h2x, zero_mul, zero_sub, ih, hnegx]

/-- Four-divisibility of a Chebyshev value forces an odd index and
an even seed divisible by four. Nothing about the seed or index is assumed. -/
theorem cheb_four_dvd_seed_index {n : ℕ} {x : ℤ}
    (h : (4 : ℤ) ∣ cheb n x) : Odd n ∧ Even x ∧ (4 : ℤ) ∣ x := by
  have htwo : (2 : ℤ) ∣ cheb n x := dvd_trans (by norm_num : (2 : ℤ) ∣ 4) h
  have hz : (cheb n x : ZMod 2) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr htwo
  have hmod := cheb_mod_two n x
  have hn : Odd n := Nat.not_even_iff_odd.mp (by
    intro he
    rw [if_pos he, hz] at hmod
    norm_num at hmod)
  have he : ¬Even n := Nat.not_even_iff_odd.mpr hn
  rw [if_neg he, hz] at hmod
  have hx : Even x := even_iff_two_dvd.mpr
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod.symm)
  refine ⟨hn, hx, ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  rw [← cheb_odd_mod_four hn hx]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h

/-- An even x-coordinate of a norm-one Pell solution forces an odd
y-coordinate, independently of the parameter. -/
theorem pell_y_odd_of_x_even {d : ℤ} (ε : Pell.Solution₁ d) (hx : Even ε.x) : Odd ε.y := by
  apply Int.not_even_iff_odd.mp
  intro hy
  have hx2 : Even (ε.x ^ 2) := by simpa only [pow_two] using hx.mul_right ε.x
  have hy2 : Even (ε.y ^ 2) := by simpa only [pow_two] using hy.mul_right ε.y
  have h1 : Even (1 : ℤ) := ε.prop ▸ hx2.sub (hy2.mul_left d)
  norm_num at h1

/-- Complete positive fundamental-unit power data. Neither the seed parity nor
any property of the exponent is an input to its construction. -/
def FundamentalPower (t d a c : ℕ) (ε : Pell.Solution₁ (d : ℤ)) (n : ℕ) : Prop :=
  Pell.IsFundamental ε ∧
  (4 ≤ ε.x ∧ Even ε.x ∧ (4 : ℤ) ∣ ε.x ∧ 0 < ε.y ∧ Odd ε.y) ∧
  (0 < n ∧ Odd n) ∧
  ((ε ^ n).x = (t : ℤ) ∧ (ε ^ n).y = ((d * a * c : ℕ) : ℤ) ∧
    (t : ℤ) = cheb n ε.x)

/-- Canonical endpoints of an actual full center give a positive power of the
positive fundamental Pell solution. The index is obtained from mathlib, not
assumed; its positivity and oddness, and the seed's four-divisibility, are proved. -/
theorem canonical_exists_fundamentalPower {t A B C a b c : ℕ} (ht : 2 ≤ t)
    (h : NatFull t) (hc : CanonicalTriple t A B C a b c) :
    ∃ ε : Pell.Solution₁ ((A * C : ℕ) : ℤ), ∃ n : ℕ,
      FundamentalPower t (A * C) a c ε n := by
  have hp := natFull_properties ht h
  have hcp := canonical_pell_properties ht h hc
  have hnorm := canonical_pell_equation ht hc
  let point : Pell.Solution₁ ((A * C : ℕ) : ℤ) :=
    Pell.Solution₁.mk t ((A * C) * a * c) hnorm
  obtain ⟨ε, hε⟩ := Pell.IsFundamental.exists_of_not_isSquare
    (by exact_mod_cast hcp.1) hcp.2.2.2.2.2
  have hpointx : 0 < point.x := by
    simp only [point, Pell.Solution₁.x_mk]; exact_mod_cast (show 0 < t by omega)
  have hpointy : 0 < point.y := by
    simp only [point, Pell.Solution₁.y_mk]; exact_mod_cast hcp.2.2.2.1
  obtain ⟨n, hpower⟩ := hε.eq_pow_of_nonneg hpointx hpointy.le
  have hx : (ε ^ n).x = (t : ℤ) := by rw [← hpower]; rfl
  have hy : (ε ^ n).y = (((A * C) * a * c : ℕ) : ℤ) := by rw [← hpower]; rfl
  have hnpos : 0 < n := Nat.pos_of_ne_zero (by
    intro hn0
    have hx0 := hx
    simp only [hn0, pow_zero, Pell.Solution₁.x_one] at hx0
    omega)
  have heq : (t : ℤ) = cheb n ε.x := hx.symm.trans (pell_x_pow_eq_cheb ε n)
  have ht4 : (4 : ℤ) ∣ (t : ℤ) := by exact_mod_cast hp.2.1
  have hseed := cheb_four_dvd_seed_index (by rw [← heq]; exact ht4)
  have hr : 4 ≤ ε.x := by
    obtain ⟨k, hk⟩ := hseed.2.2
    have hrpos := hε.x_pos
    omega
  exact ⟨ε, n, hε, ⟨hr, hseed.2.1, hseed.2.2, hε.2.1,
    pell_y_odd_of_x_even ε hseed.2.1⟩, ⟨hnpos, hseed.1⟩, hx, hy, heq⟩

/-- The full canonical Pell bridge for any nondegenerate natural full center. -/
theorem natFull_exists_fundamental_pell {t : ℕ} (ht : 2 ≤ t) (h : NatFull t) :
    ∃ A B C a b c d : ℕ, CanonicalTriple t A B C a b c ∧ d = A * C ∧
      0 < d ∧ Squarefree d ∧ d % 8 = 7 ∧ ¬IsSquare (d : ℤ) ∧
      ∃ ε : Pell.Solution₁ (d : ℤ), ∃ n : ℕ, FundamentalPower t d a c ε n := by
  obtain ⟨A, B, C, a, b, c, hc⟩ := natFull_exists_canonical ht h
  have hcp := canonical_pell_properties ht h hc
  obtain ⟨ε, n, hpower⟩ := canonical_exists_fundamentalPower ht h hc
  exact ⟨A, B, C, a, b, c, A * C, hc, rfl, hcp.1, hcp.2.1, hcp.2.2.1,
    hcp.2.2.2.2.2, ε, n, hpower⟩

/-- Complete canonical Pell data with a squarefree fundamental-unit index.
Existence is not asserted by this definition. -/
def SquarefreePellFull (t : ℕ) : Prop :=
  ∃ A B C a b c d : ℕ, CanonicalTriple t A B C a b c ∧ d = A * C ∧
    0 < d ∧ Squarefree d ∧ d % 8 = 7 ∧ ¬IsSquare (d : ℤ) ∧
    ∃ ε : Pell.Solution₁ (d : ℤ), ∃ n : ℕ, FundamentalPower t d a c ε n ∧ Squarefree n

/-- The actual least full triple has a positive fundamental Pell representation
with an odd squarefree index. The Chebyshev descent is applied only after all
its seed and index hypotheses have been derived from that triple. -/
theorem leastNatFull_exists_squarefree_pell {t : ℕ} (ht : LeastNatFull t) :
    SquarefreePellFull t := by
  obtain ⟨A, B, C, a, b, c, d, hc, hd, hdpos, hdsf, hdmod, hdns, ε, n, hpower⟩ :=
    natFull_exists_fundamental_pell (show 2 ≤ t by have := ht.1; omega) ht.2.1
  have hn : Squarefree n := least_full_index_squarefree hpower.2.1.1 hpower.2.2.1.2
    (leastNatFull_iff_leastFull.mp ht) hpower.2.2.2.2.2
  exact ⟨A, B, C, a, b, c, d, hc, hd, hdpos, hdsf, hdmod, hdns, ε, n, hpower, hn⟩

/-- A concise projection of the complete actual-minimum witness. In particular,
`n = 1` remains possible in this reduction; no global exclusion is claimed. -/
theorem leastNatFull_exists_odd_squarefree_index {t : ℕ} (ht : LeastNatFull t) :
    ∃ d : ℕ, 0 < d ∧ Squarefree d ∧ d % 8 = 7 ∧ ¬IsSquare (d : ℤ) ∧
      ∃ ε : Pell.Solution₁ (d : ℤ), Pell.IsFundamental ε ∧
        4 ≤ ε.x ∧ (4 : ℤ) ∣ ε.x ∧ 0 < ε.y ∧
        ∃ n : ℕ, 0 < n ∧ Odd n ∧ Squarefree n ∧ (t : ℤ) = cheb n ε.x := by
  obtain ⟨A, B, C, a, b, c, d, _, _, hdpos, hdsf, hdmod, hdns, ε, n, hpower, hnsf⟩ :=
    leastNatFull_exists_squarefree_pell ht
  exact ⟨d, hdpos, hdsf, hdmod, hdns, ε, hpower.1, hpower.2.1.1,
    hpower.2.1.2.2.1, hpower.2.1.2.2.2.1, n, hpower.2.2.1.1,
    hpower.2.2.1.2, hnsf, hpower.2.2.2.2.2⟩

/-- Signed least full centers have the same complete witness at their exact
natural value; the lower bound prevents any truncation or absolute-value issue. -/
theorem leastFull_exists_squarefree_pell {t : ℤ} (ht : LeastFull t) :
    SquarefreePellFull t.toNat := by
  have hcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg (by have := ht.1; omega)
  apply leastNatFull_exists_squarefree_pell
  apply leastNatFull_iff_leastFull.mpr
  simpa only [hcast] using ht

/-- Global existence reduction for the actual full triple. The least center is
obtained with `Nat.find`; neither the original specification nor an assumed Pell
index is used. This equivalence is a structural reduction, not a settlement of
Erdős problem 364. -/
theorem exists_powerful_triple_iff_exists_least_Pell_full :
    (∃ k : ℕ, Nat.Powerful k ∧ Nat.Powerful (k + 1) ∧ Nat.Powerful (k + 2)) ↔
      ∃ t : ℕ, LeastNatFull t ∧ SquarefreePellFull t := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := exists_leastNatFull_of_exists_powerful_triple h
    exact ⟨t, ht, leastNatFull_exists_squarefree_pell ht⟩
  · rintro ⟨t, ht, _⟩
    have h1 : t - 1 + 1 = t := by have := ht.1; omega
    have h2 : t - 1 + 2 = t + 1 := by have := ht.1; omega
    refine ⟨t - 1, ?_⟩
    simpa only [h1, h2] using ht.2.1

end Erdos364.PellBridge

-- Exhaustive axiom audit of every public definition and theorem in this helper.
#print axioms Erdos364.PellBridge.NatFull
#print axioms Erdos364.PellBridge.LeastNatFull
#print axioms Erdos364.PellBridge.CanonicalTriple
#print axioms Erdos364.PellBridge.natFull_iff_full
#print axioms Erdos364.PellBridge.natFull_properties
#print axioms Erdos364.PellBridge.leastNatFull_iff_leastFull
#print axioms Erdos364.PellBridge.exists_leastNatFull_of_exists_powerful_triple
#print axioms Erdos364.PellBridge.natFull_exists_canonical
#print axioms Erdos364.PellBridge.canonical_pell_norm
#print axioms Erdos364.PellBridge.pell_parameter_mod_eight
#print axioms Erdos364.PellBridge.canonical_pell_equation
#print axioms Erdos364.PellBridge.canonical_pell_properties
#print axioms Erdos364.PellBridge.pell_x_pow_add_two
#print axioms Erdos364.PellBridge.pell_x_pow_eq_cheb
#print axioms Erdos364.PellBridge.cheb_mod_two
#print axioms Erdos364.PellBridge.cheb_odd_mod_four
#print axioms Erdos364.PellBridge.cheb_four_dvd_seed_index
#print axioms Erdos364.PellBridge.pell_y_odd_of_x_even
#print axioms Erdos364.PellBridge.FundamentalPower
#print axioms Erdos364.PellBridge.canonical_exists_fundamentalPower
#print axioms Erdos364.PellBridge.natFull_exists_fundamental_pell
#print axioms Erdos364.PellBridge.SquarefreePellFull
#print axioms Erdos364.PellBridge.leastNatFull_exists_squarefree_pell
#print axioms Erdos364.PellBridge.leastNatFull_exists_odd_squarefree_index
#print axioms Erdos364.PellBridge.leastFull_exists_squarefree_pell
#print axioms Erdos364.PellBridge.exists_powerful_triple_iff_exists_least_Pell_full
