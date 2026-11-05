import FormalConjecturesUtil

/-!
# The isotropic nine-norm obstruction

This auxiliary module is independent of `Submission.Spec`. It formalizes the
common-squareclass obstruction for the nine quadratic forms obtained from a
three-dimensional projection, and its application to rational coordinates in
`ℚ(√(-k))`, with `k > 0`.

The local calculation is a finite, kernel-checked calculation modulo 16.
Integer normals are then handled by descent at 2, and rational normals by
clearing denominators. This rules out the isotropic nine-norm construction;
it is not a proof of Erdős 213.

Main APIs:
* `commonSquares_zero` and `no_common_multiplier` are the complete rational
  nine-form arithmetic obstruction, for any nonzero rational multiplier.
* `isotropic_weightedGram_projection` and `isotropic_nineNorms_projection`
  give the exact rational Gram and norm projection formulas.
* `weightedGaussian_isotropic_zero` (or its version
  `weightedGaussian_isotropic_zero_of_nine_squares`) is the complete
  weighted-Gaussian nine-norm obstruction.

Only rational squares are treated here; no local-field infrastructure is
required. Axiom audits for every theorem are included at the end.
-/

namespace IsotropicObstruction

/- ## The common-squareclass arithmetic obstruction -/

/-- The nine forms, ordered as the three diagonal entries and the six signed
pair norms of `d (T I - n nᵀ)`, for `n = (x,y,z)` and `T = x²+y²+z²`. -/
def nineForms {R : Type*} [CommRing R] (x y z : R) : Fin 9 → R :=
  ![y ^ 2 + z ^ 2, x ^ 2 + z ^ 2, x ^ 2 + y ^ 2,
    (x - y) ^ 2 + 2 * z ^ 2, (x + y) ^ 2 + 2 * z ^ 2,
    (x - z) ^ 2 + 2 * y ^ 2, (x + z) ^ 2 + 2 * y ^ 2,
    (y - z) ^ 2 + 2 * x ^ 2, (y + z) ^ 2 + 2 * x ^ 2]

/-- All nine forms become rational squares after multiplication by `d`. -/
def CommonSquares (d x y z : ℚ) : Prop :=
  ∀ i : Fin 9, IsSquare (d * nineForms x y z i)

/-- Homogeneity of the nine forms. -/
theorem nineForms_scale {R : Type*} [CommRing R] (t x y z : R) (i : Fin 9) :
    nineForms (t * x) (t * y) (t * z) i = t ^ 2 * nineForms x y z i := by
  fin_cases i <;> simp [nineForms] <;> ring

/-- Ring homomorphisms preserve the nine forms. -/
theorem map_nineForms {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x y z : R) (i : Fin 9) :
    f (nineForms x y z i) = nineForms (f x) (f y) (f z) i := by
  fin_cases i <;> simp [nineForms, map_ofNat]

/-- The four square residues modulo 16. -/
def SquareResidue16 (r : ZMod 16) : Prop :=
  r = 0 ∨ r = 1 ∨ r = 4 ∨ r = 9

instance (r : ZMod 16) : Decidable (SquareResidue16 r) := by
  unfold SquareResidue16
  infer_instance

/-- A kernel-checked calculation of all sixteen square residues. -/
theorem squareResidue16_mul_self : ∀ r : ZMod 16, SquareResidue16 (r * r) := by
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
/-- A kernel-checked local certificate over all `16³` residue triples.
Only six of the 36 unordered products are needed. If they are all square
residues, every coordinate is even. No `native_decide` is used. -/
theorem mod16_certificate : ∀ x y z : ZMod 16,
    SquareResidue16 (nineForms x y z 0 * nineForms x y z 1) →
    SquareResidue16 (nineForms x y z 0 * nineForms x y z 2) →
    SquareResidue16 (nineForms x y z 0 * nineForms x y z 3) →
    SquareResidue16 (nineForms x y z 0 * nineForms x y z 5) →
    SquareResidue16 (nineForms x y z 1 * nineForms x y z 7) →
    SquareResidue16 (nineForms x y z 3 * nineForms x y z 4) →
    x.val % 2 = 0 ∧ y.val % 2 = 0 ∧ z.val % 2 = 0 := by
  decide

/-- Squares with a common nonzero multiplier have square pairwise products. -/
theorem isSquare_product_of_common {d a b : ℚ} (hd : d ≠ 0)
    (ha : IsSquare (d * a)) (hb : IsSquare (d * b)) : IsSquare (a * b) := by
  have h := (ha.mul hb).div (IsSquare.mul_self d)
  have he : (d * a) * (d * b) / (d * d) = a * b := by
    field_simp
  rwa [he] at h

/-- An integral normal with a common multiplier has integral-square products. -/
theorem commonSquares_int_products {d : ℚ} {x y z : ℤ} (hd : d ≠ 0)
    (h : CommonSquares d (x : ℚ) (y : ℚ) (z : ℚ)) (i j : Fin 9) :
    IsSquare (nineForms x y z i * nineForms x y z j) := by
  apply Rat.isSquare_intCast_iff.mp
  have hh := isSquare_product_of_common hd (h i) (h j)
  convert hh using 1
  change (Int.castRingHom ℚ) (nineForms x y z i * nineForms x y z j) = _
  rw [map_mul, map_nineForms, map_nineForms]
  rfl

/-- Every square modulo 16 belongs to the four certified residues. -/
theorem squareResidue16_of_isSquare {r : ZMod 16} (h : IsSquare r) :
    SquareResidue16 r := by
  obtain ⟨s, rfl⟩ := h
  exact squareResidue16_mul_self s

/-- Evenness of a residue modulo 16 implies divisibility by 2 in `ℤ`. -/
theorem two_dvd_of_even_residue16 (t : ℤ) (h : (t : ZMod 16).val % 2 = 0) :
    (2 : ℤ) ∣ t := by
  apply Int.dvd_iff_emod_eq_zero.mpr
  have hc := congrArg (fun n : ℕ => (n : ℤ)) h
  change (((t : ZMod 16).val % 2 : ℕ) : ℤ) = 0 at hc
  rw [Int.natCast_emod, ZMod.val_intCast] at hc
  norm_num only [Nat.cast_ofNat, Nat.cast_zero] at hc
  rwa [Int.emod_emod_of_dvd t (by norm_num : (2 : ℤ) ∣ 16)] at hc

/-- The local obstruction forces all three integer coordinates to be even. -/
theorem two_dvd_coordinates_of_square_products {x y z : ℤ}
    (h : ∀ i j : Fin 9, IsSquare (nineForms x y z i * nineForms x y z j)) :
    (2 : ℤ) ∣ x ∧ (2 : ℤ) ∣ y ∧ (2 : ℤ) ∣ z := by
  have hh (i j : Fin 9) :
      SquareResidue16
        (nineForms (x : ZMod 16) (y : ZMod 16) (z : ZMod 16) i *
          nineForms (x : ZMod 16) (y : ZMod 16) (z : ZMod 16) j) := by
    apply squareResidue16_of_isSquare
    have hs := (h i j).map (Int.castRingHom (ZMod 16))
    simpa only [map_mul, map_nineForms] using hs
  obtain ⟨hx, hy, hz⟩ := mod16_certificate (x : ZMod 16) (y : ZMod 16) (z : ZMod 16)
    (hh 0 1) (hh 0 2) (hh 0 3) (hh 0 5) (hh 1 7) (hh 3 4)
  exact ⟨two_dvd_of_even_residue16 x hx, two_dvd_of_even_residue16 y hy,
    two_dvd_of_even_residue16 z hz⟩

/-- Infinite descent at 2, measured by the sum of the coordinate absolute
values. The multiplier changes from `d` to `4*d` at each descent step. -/
theorem commonSquares_int_zero {d : ℚ} {x y z : ℤ} (hd : d ≠ 0)
    (hs : CommonSquares d (x : ℚ) (y : ℚ) (z : ℚ)) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  generalize hm : x.natAbs + y.natAbs + z.natAbs = m
  induction m using Nat.strong_induction_on generalizing x y z d with
  | h m ih =>
    by_cases hzero : x = 0 ∧ y = 0 ∧ z = 0
    · exact hzero
    have hmpos : 0 < m := by
      by_contra hn
      have hx : x.natAbs = 0 := by omega
      have hy : y.natAbs = 0 := by omega
      have hz : z.natAbs = 0 := by omega
      exact hzero ⟨Int.natAbs_eq_zero.mp hx, Int.natAbs_eq_zero.mp hy,
        Int.natAbs_eq_zero.mp hz⟩
    obtain ⟨hx, hy, hz⟩ :=
      two_dvd_coordinates_of_square_products (commonSquares_int_products hd hs)
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    obtain ⟨z', hz'⟩ := hz
    have hm' : x'.natAbs + y'.natAbs + z'.natAbs < m := by
      simp only [hx', hy', hz', Int.natAbs_mul] at hm
      norm_num at hm
      omega
    have hs' : CommonSquares (4 * d) (x' : ℚ) (y' : ℚ) (z' : ℚ) := by
      intro i
      have he : d * nineForms (x : ℚ) (y : ℚ) (z : ℚ) i =
          (4 * d) * nineForms (x' : ℚ) (y' : ℚ) (z' : ℚ) i := by
        rw [hx', hy', hz']
        push_cast
        rw [nineForms_scale]
        ring
      rw [← he]
      exact hs i
    have hz' := ih (x'.natAbs + y'.natAbs + z'.natAbs) hm'
      (mul_ne_zero (by norm_num) hd) hs' rfl
    rcases hz' with ⟨hx0, hy0, hz0⟩
    simp [hx', hy', hz', hx0, hy0, hz0]

/-- Three rational numbers admit a common nonzero rational multiplier that
makes all three integral. The multiplier is the product of their denominators. -/
theorem exists_common_integer_multiple (x y z : ℚ) :
    ∃ D : ℚ, D ≠ 0 ∧ ∃ X Y Z : ℤ,
      (X : ℚ) = D * x ∧ (Y : ℚ) = D * y ∧ (Z : ℚ) = D * z := by
  refine ⟨(x.den : ℚ) * (y.den : ℚ) * (z.den : ℚ), ?_,
    x.num * (y.den : ℤ) * (z.den : ℤ),
    y.num * (x.den : ℤ) * (z.den : ℤ),
    z.num * (x.den : ℤ) * (y.den : ℤ), ?_, ?_, ?_⟩
  · exact mul_ne_zero
      (mul_ne_zero (Nat.cast_ne_zero.mpr x.den_ne_zero) (Nat.cast_ne_zero.mpr y.den_ne_zero))
      (Nat.cast_ne_zero.mpr z.den_ne_zero)
  · push_cast
    rw [← x.mul_den_eq_num]
    ring
  · push_cast
    rw [← y.mul_den_eq_num]
    ring
  · push_cast
    rw [← z.mul_den_eq_num]
    ring

/-- The complete rational common-squareclass obstruction: a nonzero common
multiplier can make all nine forms squares only for the zero normal. -/
theorem commonSquares_zero {d x y z : ℚ} (hd : d ≠ 0)
    (hs : CommonSquares d x y z) : x = 0 ∧ y = 0 ∧ z = 0 := by
  obtain ⟨D, hD, X, Y, Z, hX, hY, hZ⟩ := exists_common_integer_multiple x y z
  have hs' : CommonSquares (d / D ^ 2) (X : ℚ) (Y : ℚ) (Z : ℚ) := by
    intro i
    rw [hX, hY, hZ, nineForms_scale]
    convert hs i using 1
    field_simp
  obtain ⟨hX0, hY0, hZ0⟩ :=
    commonSquares_int_zero (div_ne_zero hd (pow_ne_zero _ hD)) hs'
  have hx : D * x = 0 := by rw [← hX, hX0]; simp
  have hy : D * y = 0 := by rw [← hY, hY0]; simp
  have hz : D * z = 0 := by rw [← hZ, hZ0]; simp
  exact ⟨(mul_eq_zero.mp hx).resolve_left hD, (mul_eq_zero.mp hy).resolve_left hD,
    (mul_eq_zero.mp hz).resolve_left hD⟩

/-- In particular, every nonzero rational normal admits no nonzero common
rational multiplier for the nine forms. No sign assumption on `d` is needed. -/
theorem no_common_multiplier {x y z : ℚ} (hn : ¬ (x = 0 ∧ y = 0 ∧ z = 0)) :
    ¬ ∃ d : ℚ, d ≠ 0 ∧ CommonSquares d x y z := by
  rintro ⟨d, hd, hs⟩
  exact hn (commonSquares_zero hd hs)

/- ## Rational weighted-Gaussian coordinates and the explicit projection -/

/-- Rational coordinates for `a + b√(-k)`. Multiplication is not the
componentwise multiplication on the product; `weightedSquare` gives the
quadratic-field square explicitly. -/
abbrev WeightedGaussian := ℚ × ℚ

/-- The norm of `a + b√(-k)`. -/
def weightedNorm (k : ℚ) (u : WeightedGaussian) : ℚ :=
  u.1 ^ 2 + k * u.2 ^ 2

/-- The coordinates of the square of `a + b√(-k)`. -/
def weightedSquare (k : ℚ) (u : WeightedGaussian) : WeightedGaussian :=
  (u.1 ^ 2 - k * u.2 ^ 2, 2 * u.1 * u.2)

/-- Squared length of the vector of real coordinates. -/
def realSqSum (u v w : WeightedGaussian) : ℚ :=
  u.1 ^ 2 + v.1 ^ 2 + w.1 ^ 2

/-- Squared length of the vector of imaginary-coordinate coefficients. -/
def imagSqSum (u v w : WeightedGaussian) : ℚ :=
  u.2 ^ 2 + v.2 ^ 2 + w.2 ^ 2

/-- Dot product of the real and imaginary-coefficient vectors. -/
def coordDot (u v w : WeightedGaussian) : ℚ :=
  u.1 * u.2 + v.1 * v.2 + w.1 * w.2

/-- The two rational equations equivalent to `u² + v² + w² = 0`
in `ℚ(√(-k))`. -/
def Isotropic (k : ℚ) (u v w : WeightedGaussian) : Prop :=
  realSqSum u v w = k * imagSqSum u v w ∧ coordDot u v w = 0

/-- The coordinate model faithfully expresses the square-sum equation. -/
theorem weightedSquare_sum_eq_zero_iff {k : ℚ} {u v w : WeightedGaussian} :
    weightedSquare k u + weightedSquare k v + weightedSquare k w = 0 ↔
      Isotropic k u v w := by
  rw [Prod.ext_iff]
  change (u.1 ^ 2 - k * u.2 ^ 2 + (v.1 ^ 2 - k * v.2 ^ 2) +
      (w.1 ^ 2 - k * w.2 ^ 2) = 0 ∧
      2 * u.1 * u.2 + 2 * v.1 * v.2 + 2 * w.1 * w.2 = 0) ↔
    (u.1 ^ 2 + v.1 ^ 2 + w.1 ^ 2 = k * (u.2 ^ 2 + v.2 ^ 2 + w.2 ^ 2) ∧
      u.1 * u.2 + v.1 * v.2 + w.1 * w.2 = 0)
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

/-- The nine norms, in the order `u,v,w,u+v,u-v,u+w,u-w,v+w,v-w`. -/
def nineNorms (k : ℚ) (u v w : WeightedGaussian) : Fin 9 → ℚ :=
  ![weightedNorm k u, weightedNorm k v, weightedNorm k w,
    weightedNorm k (u + v), weightedNorm k (u - v),
    weightedNorm k (u + w), weightedNorm k (u - w),
    weightedNorm k (v + w), weightedNorm k (v - w)]

/-- The nine rational-square norm tests. -/
def NineNormSquares (k : ℚ) (u v w : WeightedGaussian) : Prop :=
  ∀ i : Fin 9, IsSquare (nineNorms k u v w i)

/-- Expanded form of the nine square tests, for callers without finite indices. -/
theorem nineNormSquares_iff {k : ℚ} {u v w : WeightedGaussian} :
    NineNormSquares k u v w ↔
      IsSquare (weightedNorm k u) ∧ IsSquare (weightedNorm k v) ∧
      IsSquare (weightedNorm k w) ∧ IsSquare (weightedNorm k (u + v)) ∧
      IsSquare (weightedNorm k (u - v)) ∧ IsSquare (weightedNorm k (u + w)) ∧
      IsSquare (weightedNorm k (u - w)) ∧ IsSquare (weightedNorm k (v + w)) ∧
      IsSquare (weightedNorm k (v - w)) := by
  simp [NineNormSquares, nineNorms, Fin.forall_fin_succ]

/-- The explicit rational cross product `a × b`; no abstract kernel or
linear-algebra selection is used. -/
def crossNormal (u v w : WeightedGaussian) : Fin 3 → ℚ :=
  ![v.1 * w.2 - w.1 * v.2, w.1 * u.2 - u.1 * w.2, u.1 * v.2 - v.1 * u.2]

/-- Squared length of the explicit rational normal. -/
def normalSqSum (u v w : WeightedGaussian) : ℚ :=
  crossNormal u v w 0 ^ 2 + crossNormal u v w 1 ^ 2 + crossNormal u v w 2 ^ 2

/-- Lagrange's cross-product identity, verified directly as a polynomial. -/
theorem crossNormal_sq_sum (u v w : WeightedGaussian) :
    normalSqSum u v w = realSqSum u v w * imagSqSum u v w - coordDot u v w ^ 2 := by
  simp [normalSqSum, crossNormal, realSqSum, imagSqSum, coordDot]
  ring

/-- On the isotropic locus, `k T = c²`. -/
theorem isotropic_normalSqSum {k : ℚ} {u v w : WeightedGaussian}
    (h : Isotropic k u v w) : k * normalSqSum u v w = realSqSum u v w ^ 2 := by
  rw [crossNormal_sq_sum, h.2]
  simp only [zero_pow (by decide : 2 ≠ 0), sub_zero]
  calc
    k * (realSqSum u v w * imagSqSum u v w) =
        realSqSum u v w * (k * imagSqSum u v w) := by ring
    _ = realSqSum u v w ^ 2 := by rw [← h.1]; ring

/-- Positivity and nonvanishing of the normal length in the nonzero branch. -/
theorem normalSqSum_pos {k : ℚ} {u v w : WeightedGaussian} (hk : 0 < k)
    (h : Isotropic k u v w) (hc : 0 < realSqSum u v w) :
    0 < normalSqSum u v w := by
  apply (mul_pos_iff_of_pos_left hk).mp
  rw [isotropic_normalSqSum h]
  exact sq_pos_of_pos hc

/-- The cross product is nonzero on the positive-length isotropic branch. -/
theorem crossNormal_nonzero {k : ℚ} {u v w : WeightedGaussian} (hk : 0 < k)
    (h : Isotropic k u v w) (hc : 0 < realSqSum u v w) :
    ¬ (crossNormal u v w 0 = 0 ∧ crossNormal u v w 1 = 0 ∧ crossNormal u v w 2 = 0) := by
  rintro ⟨hx, hy, hz⟩
  have hp := normalSqSum_pos hk h hc
  simp [normalSqSum, hx, hy, hz] at hp

/-- Polynomial form of all nine projection identities: `c Nᵢ = k Fᵢ`.
The normal is the explicit cross product. -/
theorem isotropic_nineNorms_scaled {k : ℚ} {u v w : WeightedGaussian}
    (h : Isotropic k u v w) (i : Fin 9) :
    realSqSum u v w * nineNorms k u v w i =
      k * nineForms (crossNormal u v w 0) (crossNormal u v w 1)
        (crossNormal u v w 2) i := by
  rcases u with ⟨a1, b1⟩
  rcases v with ⟨a2, b2⟩
  rcases w with ⟨a3, b3⟩
  rcases h with ⟨hlen, hdot⟩
  change a1 ^ 2 + a2 ^ 2 + a3 ^ 2 = k * (b1 ^ 2 + b2 ^ 2 + b3 ^ 2) at hlen
  change a1 * b1 + a2 * b2 + a3 * b3 = 0 at hdot
  fin_cases i <;> simp [realSqSum, nineNorms, weightedNorm, nineForms, crossNormal]
  · linear_combination a1 ^ 2 * hlen + (2 * k * a1 * b1) * hdot
  · linear_combination a2 ^ 2 * hlen + (2 * k * a2 * b2) * hdot
  · linear_combination a3 ^ 2 * hlen + (2 * k * a3 * b3) * hdot
  · linear_combination (a1 + a2) ^ 2 * hlen + (2 * k * (a1 + a2) * (b1 + b2)) * hdot
  · linear_combination (a1 - a2) ^ 2 * hlen + (2 * k * (a1 - a2) * (b1 - b2)) * hdot
  · linear_combination (a1 + a3) ^ 2 * hlen + (2 * k * (a1 + a3) * (b1 + b3)) * hdot
  · linear_combination (a1 - a3) ^ 2 * hlen + (2 * k * (a1 - a3) * (b1 - b3)) * hdot
  · linear_combination (a2 + a3) ^ 2 * hlen + (2 * k * (a2 + a3) * (b2 + b3)) * hdot
  · linear_combination (a2 - a3) ^ 2 * hlen + (2 * k * (a2 - a3) * (b2 - b3)) * hdot

/-- The two expressions for the common projection multiplier agree. -/
theorem projection_multiplier_eq {k : ℚ} {u v w : WeightedGaussian} (hk : 0 < k)
    (h : Isotropic k u v w) (hc : 0 < realSqSum u v w) :
    k / realSqSum u v w = realSqSum u v w / normalSqSum u v w := by
  apply (div_eq_div_iff hc.ne' (normalSqSum_pos hk h hc).ne').mpr
  simpa only [pow_two] using isotropic_normalSqSum h

/-- Exact projection equations for the nine norms with `d = c/T > 0`. -/
theorem isotropic_nineNorms_projection {k : ℚ} {u v w : WeightedGaussian} (hk : 0 < k)
    (h : Isotropic k u v w) (hc : 0 < realSqSum u v w) (i : Fin 9) :
    nineNorms k u v w i = (realSqSum u v w / normalSqSum u v w) *
      nineForms (crossNormal u v w 0) (crossNormal u v w 1) (crossNormal u v w 2) i := by
  rw [← projection_multiplier_eq hk h hc]
  calc
    nineNorms k u v w i =
        (k * nineForms (crossNormal u v w 0) (crossNormal u v w 1)
          (crossNormal u v w 2) i) / realSqSum u v w := by
      apply (eq_div_iff hc.ne').mpr
      simpa only [mul_comm] using isotropic_nineNorms_scaled h i
    _ = _ := by ring


/-- The weighted rational inner product. -/
def weightedInner (k : ℚ) (u v : WeightedGaussian) : ℚ :=
  u.1 * v.1 + k * u.2 * v.2

/-- The rational Gram entries of the three quadratic-field coordinates. -/
def weightedGram (k : ℚ) (u v w : WeightedGaussian) (i j : Fin 3) : ℚ :=
  weightedInner k (![u, v, w] i) (![u, v, w] j)

/-- The explicit normal is orthogonal to both coordinate vectors. -/
theorem crossNormal_orthogonal (u v w : WeightedGaussian) :
    (u.1 * crossNormal u v w 0 + v.1 * crossNormal u v w 1 +
      w.1 * crossNormal u v w 2 = 0) ∧
    (u.2 * crossNormal u v w 0 + v.2 * crossNormal u v w 1 +
      w.2 * crossNormal u v w 2 = 0) := by
  constructor <;> simp [crossNormal] <;> ring

/-- The polynomial Gram projection identity `c G = k (T I - n nᵀ)`.
It follows from the already verified diagonal and signed-pair identities. -/
theorem isotropic_weightedGram_scaled {k : ℚ} {u v w : WeightedGaussian}
    (h : Isotropic k u v w) (i j : Fin 3) :
    realSqSum u v w * weightedGram k u v w i j =
      k * ((if i = j then normalSqSum u v w else 0) -
        crossNormal u v w i * crossNormal u v w j) := by
  have h0 := isotropic_nineNorms_scaled h 0
  have h1 := isotropic_nineNorms_scaled h 1
  have h2 := isotropic_nineNorms_scaled h 2
  have h3 := isotropic_nineNorms_scaled h 3
  have h5 := isotropic_nineNorms_scaled h 5
  have h7 := isotropic_nineNorms_scaled h 7
  simp [realSqSum, nineNorms, weightedNorm, nineForms, crossNormal] at h0 h1 h2 h3 h5 h7
  fin_cases i <;> fin_cases j <;>
    simp [realSqSum, weightedGram, weightedInner, normalSqSum, crossNormal]
  · linear_combination h0
  · linear_combination (h3 - h0 - h1) / 2
  · linear_combination (h5 - h0 - h2) / 2
  · linear_combination (h3 - h0 - h1) / 2
  · linear_combination h1
  · linear_combination (h7 - h1 - h2) / 2
  · linear_combination (h5 - h0 - h2) / 2
  · linear_combination (h7 - h1 - h2) / 2
  · linear_combination h2

/-- Exact rational Gram projection, including all off-diagonal entries:
`G = (c/T) (T I - n nᵀ)`. -/
theorem isotropic_weightedGram_projection {k : ℚ} {u v w : WeightedGaussian}
    (hk : 0 < k) (h : Isotropic k u v w) (hc : 0 < realSqSum u v w) (i j : Fin 3) :
    weightedGram k u v w i j = (realSqSum u v w / normalSqSum u v w) *
      ((if i = j then normalSqSum u v w else 0) -
        crossNormal u v w i * crossNormal u v w j) := by
  rw [← projection_multiplier_eq hk h hc]
  calc
    weightedGram k u v w i j =
        (k * ((if i = j then normalSqSum u v w else 0) -
          crossNormal u v w i * crossNormal u v w j)) / realSqSum u v w := by
      apply (eq_div_iff hc.ne').mpr
      simpa only [mul_comm] using isotropic_weightedGram_scaled h i j
    _ = _ := by ring

/-- Nonnegativity of the real-coordinate squared length. -/
theorem realSqSum_nonneg (u v w : WeightedGaussian) : 0 ≤ realSqSum u v w := by
  exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)

/-- The zero-length isotropic branch is the zero triple when `k > 0`. -/
theorem isotropic_zero_of_realSqSum_eq_zero {k : ℚ} {u v w : WeightedGaussian}
    (hk : 0 < k) (h : Isotropic k u v w) (hc : realSqSum u v w = 0) :
    u = 0 ∧ v = 0 ∧ w = 0 := by
  have hb : imagSqSum u v w = 0 := by
    apply (mul_eq_zero.mp (h.1.symm.trans hc)).resolve_left hk.ne'
  dsimp [realSqSum] at hc
  dsimp [imagSqSum] at hb
  have ha1 : u.1 = 0 := by nlinarith [sq_nonneg v.1, sq_nonneg w.1]
  have ha2 : v.1 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg w.1]
  have ha3 : w.1 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg v.1]
  have hb1 : u.2 = 0 := by nlinarith [sq_nonneg v.2, sq_nonneg w.2]
  have hb2 : v.2 = 0 := by nlinarith [sq_nonneg u.2, sq_nonneg w.2]
  have hb3 : w.2 = 0 := by nlinarith [sq_nonneg u.2, sq_nonneg v.2]
  exact ⟨Prod.ext ha1 hb1, Prod.ext ha2 hb2, Prod.ext ha3 hb3⟩

/-- Every isotropic rational-coordinate weighted-Gaussian triple passing all
nine rational-square norm tests is zero. Zero generators and zero normal
coordinates are included; no nondegeneracy hypotheses are omitted. -/
theorem isotropic_nineNormSquares_zero {k : ℚ} {u v w : WeightedGaussian}
    (hk : 0 < k) (h : Isotropic k u v w) (hs : NineNormSquares k u v w) :
    u = 0 ∧ v = 0 ∧ w = 0 := by
  by_cases hc : realSqSum u v w = 0
  · exact isotropic_zero_of_realSqSum_eq_zero hk h hc
  · have hcpos : 0 < realSqSum u v w :=
      lt_of_le_of_ne (realSqSum_nonneg u v w) (Ne.symm hc)
    have hd : realSqSum u v w / normalSqSum u v w ≠ 0 :=
      (div_pos hcpos (normalSqSum_pos hk h hcpos)).ne'
    have hf : CommonSquares (realSqSum u v w / normalSqSum u v w)
        (crossNormal u v w 0) (crossNormal u v w 1) (crossNormal u v w 2) := by
      intro i
      rw [← isotropic_nineNorms_projection hk h hcpos i]
      exact hs i
    exact False.elim (crossNormal_nonzero hk h hcpos (commonSquares_zero hd hf))

/-- The same complete obstruction stated using the actual quadratic-field
square formula rather than the two separate isotropy equations. -/
theorem weightedGaussian_isotropic_zero {k : ℚ} {u v w : WeightedGaussian}
    (hk : 0 < k)
    (hiso : weightedSquare k u + weightedSquare k v + weightedSquare k w = 0)
    (hs : NineNormSquares k u v w) : u = 0 ∧ v = 0 ∧ w = 0 := by
  exact isotropic_nineNormSquares_zero hk (weightedSquare_sum_eq_zero_iff.mp hiso) hs

/-- A version of the complete weighted-Gaussian theorem taking the nine
square hypotheses individually. -/
theorem weightedGaussian_isotropic_zero_of_nine_squares {k : ℚ}
    {u v w : WeightedGaussian} (hk : 0 < k)
    (hiso : weightedSquare k u + weightedSquare k v + weightedSquare k w = 0)
    (hu : IsSquare (weightedNorm k u)) (hv : IsSquare (weightedNorm k v))
    (hw : IsSquare (weightedNorm k w)) (huv : IsSquare (weightedNorm k (u + v)))
    (huv' : IsSquare (weightedNorm k (u - v))) (huw : IsSquare (weightedNorm k (u + w)))
    (huw' : IsSquare (weightedNorm k (u - w))) (hvw : IsSquare (weightedNorm k (v + w)))
    (hvw' : IsSquare (weightedNorm k (v - w))) : u = 0 ∧ v = 0 ∧ w = 0 := by
  exact weightedGaussian_isotropic_zero hk hiso
    (nineNormSquares_iff.mpr ⟨hu, hv, hw, huv, huv', huw, huw', hvw, hvw'⟩)

/-- The nine-norm square cover has no nonzero isotropic triple in any
positive rational weighted-Gaussian model. -/
theorem no_nonzero_isotropic_nineNormSquares {k : ℚ} (hk : 0 < k) :
    ¬ ∃ u v w : WeightedGaussian, NineNormSquares k u v w ∧
      Isotropic k u v w ∧ ¬ (u = 0 ∧ v = 0 ∧ w = 0) := by
  rintro ⟨u, v, w, hs, h, hn⟩
  exact hn (isotropic_nineNormSquares_zero hk h hs)

/- ## Axiom audit

All theorems below are derived; these commands expose their transitive axiom
dependencies. The allowed foundational axioms are `propext`,
`Classical.choice`, and `Quot.sound`.
-/

#print axioms nineForms_scale
#print axioms map_nineForms
#print axioms squareResidue16_mul_self
#print axioms mod16_certificate
#print axioms isSquare_product_of_common
#print axioms commonSquares_int_products
#print axioms squareResidue16_of_isSquare
#print axioms two_dvd_of_even_residue16
#print axioms two_dvd_coordinates_of_square_products
#print axioms commonSquares_int_zero
#print axioms exists_common_integer_multiple
#print axioms commonSquares_zero
#print axioms no_common_multiplier
#print axioms weightedSquare_sum_eq_zero_iff
#print axioms nineNormSquares_iff
#print axioms crossNormal_sq_sum
#print axioms isotropic_normalSqSum
#print axioms normalSqSum_pos
#print axioms crossNormal_nonzero
#print axioms isotropic_nineNorms_scaled
#print axioms projection_multiplier_eq
#print axioms isotropic_nineNorms_projection
#print axioms crossNormal_orthogonal
#print axioms isotropic_weightedGram_scaled
#print axioms isotropic_weightedGram_projection
#print axioms realSqSum_nonneg
#print axioms isotropic_zero_of_realSqSum_eq_zero
#print axioms isotropic_nineNormSquares_zero
#print axioms weightedGaussian_isotropic_zero
#print axioms weightedGaussian_isotropic_zero_of_nine_squares
#print axioms no_nonzero_isotropic_nineNormSquares

end IsotropicObstruction
