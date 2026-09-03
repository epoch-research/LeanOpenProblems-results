import Submission.AsymptoticBridge

/-!
# The known `r = 3` Zarankiewicz lower bound

We use a quadratic finite-field norm. The incidence family is
`f (a, α) t = N(t + a) / α`, with `a,t ∈ K` and `α ∈ Fˣ`.
Allowing the right-hand color to be zero adds only stars to the usual
bipartite norm graph and makes the incidence count particularly simple.

This file concerns only `K_{3,3}`. It does not import `Submission.Spec`
and makes no assertion about the open general-`r` problem.
-/

noncomputable section

namespace Erdos714.CaseThree

open Filter SimpleGraph IncidenceBridge

section QuadraticNorm

variable {F K : Type*} [Field F] [Field K] [Fintype F] [Finite K] [Algebra F K]

/-- The norm in a quadratic finite-field extension is the product with
its Frobenius conjugate. -/
theorem quadratic_norm_formula (h₂ : Module.finrank F K = 2) (z : K) :
    algebraMap F K (Algebra.norm F z) =
      z * FiniteField.frobeniusAlgHom F K z := by
  rw [FiniteField.algebraMap_norm_eq_prod_pow, h₂]
  simp [Finset.prod_range_succ, Nat.card_eq_fintype_card]

omit [Fintype F] in
/-- Multiplicativity of the norm, also for a zero numerator or denominator. -/
theorem norm_div (x y : K) :
    Algebra.norm F (x / y) = Algebra.norm F x / Algebra.norm F y := by
  simp only [div_eq_mul_inv, map_mul, Algebra.norm_inv]

/-- Two prescribed norms determine a monic quadratic equation. This
argument works in characteristic two as well. -/
theorem quadratic_of_norms (h₂ : Module.finrank F K = 2) {z : K} {A B : F}
    (hA : Algebra.norm F z = A) (hB : Algebra.norm F (z + 1) = B) :
    z ^ 2 - algebraMap F K (B - A - 1) * z + algebraMap F K A = 0 := by
  have hA' := congrArg (algebraMap F K) hA
  have hB' := congrArg (algebraMap F K) hB
  rw [quadratic_norm_formula h₂] at hA' hB'
  rw [map_add, map_one] at hB'
  simp only [map_sub, map_one]
  linear_combination z * hB' - (z + 1) * hA'

omit [Finite K] in
/-- A monic quadratic over a field cannot have three distinct roots. -/
private theorem no_three_quadratic_roots (b c : K) (z : Fin 3 → K)
    (hz : Function.Injective z) (h : ∀ i, z i ^ 2 - b * z i + c = 0) : False := by
  have h₀₁ : z 0 ≠ z 1 := hz.ne (by decide)
  have h₀₂ : z 0 ≠ z 2 := hz.ne (by decide)
  have hs₁ : z 0 + z 1 - b = 0 := by
    have hm : (z 0 - z 1) * (z 0 + z 1 - b) = 0 := by
      linear_combination h 0 - h 1
    exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr h₀₁)
  have hs₂ : z 0 + z 2 - b = 0 := by
    have hm : (z 0 - z 2) * (z 0 + z 2 - b) = 0 := by
      linear_combination h 0 - h 2
    exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr h₀₂)
  have he : z 1 = z 2 := by linear_combination hs₁ - hs₂
  exact hz.ne (by decide : (1 : Fin 3) ≠ 2) he

/-- Two norm circles with different centers have at most two common
points, expressed without any enumeration or generic-position assumption. -/
theorem no_three_on_norm_circles (h₂ : Module.finrank F K = 2)
    {c d : K} (hcd : c ≠ d) (u : Fin 3 → K) (hu : Function.Injective u)
    {A B : F} (hA : ∀ i, Algebra.norm F (u i + c) = A)
    (hB : ∀ i, Algebra.norm F (u i + d) = B) : False := by
  have hdc : d - c ≠ 0 := sub_ne_zero.mpr hcd.symm
  let z : Fin 3 → K := fun i => (u i + c) / (d - c)
  have hz : Function.Injective z := by
    intro i j hij
    apply hu
    exact add_right_cancel ((div_left_inj' hdc).mp hij)
  apply no_three_quadratic_roots
    (algebraMap F K (B / Algebra.norm F (d - c) -
      A / Algebra.norm F (d - c) - 1))
    (algebraMap F K (A / Algebra.norm F (d - c))) z hz
  intro i
  apply quadratic_of_norms h₂
  · dsimp [z]
    rw [norm_div, hA]
  · have he : z i + 1 = (u i + d) / (d - c) := by
      dsimp [z]
      field_simp
      ring
    rw [he, norm_div, hB]

end QuadraticNorm

section NormFamily

variable {F K : Type*} [Field F] [Field K] [Fintype F] [Finite K] [Algebra F K]

/-- A norm-graph vertex gives a function on the quadratic extension. -/
def normFamily (x : K × Fˣ) (t : K) : F :=
  Algebra.norm F (t + x.1) / (x.2 : F)

omit [Fintype F] in
/-- If the first coordinates coincide, two distinct evaluation points
already distinguish the unit coordinates. -/
theorem eq_of_same_fst_of_agree_two {x y : K × Fˣ} {t u : K}
    (htu : t ≠ u) (hxy : x.1 = y.1)
    (ht : normFamily x t = normFamily y t)
    (hu : normFamily x u = normFamily y u) : x = y := by
  have hone : Algebra.norm F (t + x.1) ≠ 0 ∨ Algebra.norm F (u + x.1) ≠ 0 := by
    by_contra! h
    have ht0 : t + x.1 = 0 := Algebra.norm_eq_zero_iff.mp h.1
    have hu0 : u + x.1 = 0 := Algebra.norm_eq_zero_iff.mp h.2
    exact htu (add_right_cancel (ht0.trans hu0.symm))
  have hunit : ∀ v, Algebra.norm F (v + x.1) ≠ 0 →
      normFamily x v = normFamily y v → x.2 = y.2 := by
    intro v hv he
    dsimp [normFamily] at he
    rw [← hxy] at he
    have hm := (div_eq_div_iff (Units.ne_zero x.2) (Units.ne_zero y.2)).mp he
    apply Units.ext
    exact (mul_left_cancel₀ hv hm).symm
  apply Prod.ext hxy
  rcases hone with hv | hv
  · exact hunit t hv ht
  · exact hunit u hv hu

omit [Fintype F] in
/-- Agreement between vertices with different first coordinates cannot
have zero norm. Thus the inversion used below loses no common neighbor. -/
theorem add_ne_zero_of_agree {x y : K × Fˣ} {t : K}
    (hxy : x.1 ≠ y.1) (ht : normFamily x t = normFamily y t) :
    t + x.1 ≠ 0 := by
  intro hz
  have hy : normFamily y t = 0 := by
    rw [← ht]
    simp [normFamily, hz]
  have hy0 : t + y.1 = 0 := by
    simpa [normFamily, Units.ne_zero] using hy
  exact hxy (add_left_cancel (hz.trans hy0.symm))

omit [Fintype F] in
/-- Invert around one vertex. Each other vertex now prescribes a norm
circle with a center independent of the evaluation point. -/
theorem norm_inversion_of_agree {x y : K × Fˣ} {t : K}
    (hxy : x.1 ≠ y.1) (ht : normFamily x t = normFamily y t) :
    Algebra.norm F ((t + x.1)⁻¹ + (y.1 - x.1)⁻¹) =
      (y.2 : F) / (x.2 : F) / Algebra.norm F (y.1 - x.1) := by
  have ht0 := add_ne_zero_of_agree hxy ht
  have hd : y.1 - x.1 ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hn : Algebra.norm F (t + x.1) ≠ 0 := Algebra.norm_ne_zero_iff.mpr ht0
  have he : (t + x.1)⁻¹ + (y.1 - x.1)⁻¹ =
      (t + y.1) / (t + x.1) / (y.1 - x.1) := by
    field_simp
    ring
  rw [he, norm_div, norm_div]
  dsimp [normFamily] at ht
  have hm := (div_eq_div_iff (Units.ne_zero x.2) (Units.ne_zero y.2)).mp ht
  have hratio : Algebra.norm F (t + y.1) / Algebra.norm F (t + x.1) =
      (y.2 : F) / (x.2 : F) := by
    apply (div_eq_div_iff hn (Units.ne_zero x.2)).mpr
    simpa only [mul_comm] using hm.symm
  rw [hratio]

/-- No three distinct norm-family vertices agree at three distinct
coordinates. Repeated first coordinates, zero values, and all
characteristics are included. -/
theorem normFamily_noAgreementRectangle (h₂ : Module.finrank F K = 2) :
    ¬ HasAgreementRectangle (normFamily (F := F) (K := K)) 3 := by
  rintro ⟨x, t, hx, ht, hagree⟩
  have hfst : Function.Injective (fun i => (x i).1) := by
    intro i j hij
    apply hx
    exact eq_of_same_fst_of_agree_two (ht.ne (by decide : (0 : Fin 3) ≠ 1)) hij
      (hagree i j 0) (hagree i j 1)
  let u : Fin 3 → K := fun j => (t j + (x 0).1)⁻¹
  have hu : Function.Injective u := by
    intro i j hij
    apply ht
    exact add_right_cancel (inv_injective hij)
  have hc : ((x 1).1 - (x 0).1)⁻¹ ≠ ((x 2).1 - (x 0).1)⁻¹ := by
    intro he
    exact hfst.ne (by decide : (1 : Fin 3) ≠ 2) (sub_left_injective (inv_injective he))
  apply no_three_on_norm_circles h₂ hc u hu
    (A := ((x 1).2 : F) / ((x 0).2 : F) / Algebra.norm F ((x 1).1 - (x 0).1))
    (B := ((x 2).2 : F) / ((x 0).2 : F) / Algebra.norm F ((x 2).1 - (x 0).1))
  · intro j
    exact norm_inversion_of_agree (hfst.ne (by decide : (0 : Fin 3) ≠ 1)) (hagree 0 1 j)
  · intro j
    exact norm_inversion_of_agree (hfst.ne (by decide : (0 : Fin 3) ≠ 2)) (hagree 0 2 j)

/-- The bipartite norm incidence graph is `K_{3,3}`-free, in either
orientation of a potential copy. -/
theorem normGraph_free (h₂ : Module.finrank F K = 2) :
    (completeBipartiteGraph (Fin 3) (Fin 3)).Free
      (incidenceGraph (normFamily (F := F) (K := K))) :=
  (free_iff_noAgreementRectangle _ (by decide)).2 (normFamily_noAgreementRectangle h₂)

end NormFamily

section Counts

variable {F K : Type*} [Field F] [Field K] [Fintype F] [Fintype K] [Algebra F K]
  [DecidableEq F]

omit [Field K] [Algebra F K] in
/-- The two parts have sizes `|K| (|F| - 1)` and `|K| |F|`. -/
theorem normGraph_card_vertices :
    Fintype.card ((K × Fˣ) ⊕ (K × F)) =
      Fintype.card K * (Fintype.card F - 1) + Fintype.card K * Fintype.card F := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_units]

/-- There is exactly one edge for every left vertex and every coordinate
in `K`, including the unique coordinate with zero norm. -/
theorem normGraph_card_edgeFinset
    [Fintype (incidenceGraph (normFamily (F := F) (K := K))).edgeSet] :
    (incidenceGraph (normFamily (F := F) (K := K))).edgeFinset.card =
      Fintype.card K ^ 2 * (Fintype.card F - 1) := by
  rw [incidenceGraph_card_edgeFinset, Fintype.card_prod, Fintype.card_units]
  ring

omit [DecidableEq F] in
/-- An unconditional finite norm-graph lower bound over any quadratic
extension of finite fields. The construction has at most `2q³` vertices
and exactly `q⁴(q-1)` edges. -/
theorem normGraph_le_extremalNumber (h₂ : Module.finrank F K = 2) :
    Fintype.card F ^ 4 * (Fintype.card F - 1) ≤
      extremalNumber (2 * Fintype.card F ^ 3)
        (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  classical
  have hK : Fintype.card K = Fintype.card F ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := F), h₂]
  have hv : Fintype.card ((K × Fˣ) ⊕ (K × F)) ≤ 2 * Fintype.card F ^ 3 := by
    rw [normGraph_card_vertices (F := F) (K := K), hK]
    calc
      _ ≤ Fintype.card F ^ 2 * Fintype.card F +
          Fintype.card F ^ 2 * Fintype.card F := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) _
      _ = _ := by ring
  have h := AsymptoticBridge.card_edgeFinset_le_extremalNumber_of_card_le
    (AsymptoticBridge.completeBipartiteGraph_noIsolated (by decide : 0 < 3))
    (normGraph_free h₂) hv
  rw [normGraph_card_edgeFinset, hK] at h
  convert h using 1; ring

end Counts

/-- Finite fields and their quadratic extensions supply the construction
for every nontrivial prime power, without any field-existence hypothesis. -/
theorem primePower_norm_bound {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    (p ^ m) ^ 4 * (p ^ m - 1) ≤
      extremalNumber (2 * (p ^ m) ^ 3)
        (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p m
  let K := FiniteField.Extension F p 2
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card F = p ^ m := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p m hm
  have h₂ : Module.finrank F K = 2 := FiniteField.finrank_extension F p 2
  simpa only [hF] using normGraph_le_extremalNumber h₂

/-- Choosing `q = 2^(k+1)` gives a fixed geometric sequence of sizes.
The deliberately relaxed constants avoid any rounding losses. -/
theorem geometric_norm_bound (k : ℕ) :
    2 ^ (5 * k) ≤ extremalNumber (16 * 2 ^ (3 * k))
      (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  have h := primePower_norm_bound (p := 2) (m := k + 1) (by decide) (by omega)
  have hp₃ : (2 ^ k) ^ 3 = 2 ^ (3 * k) := by rw [← pow_mul, Nat.mul_comm k 3]
  have hv : 2 * (2 ^ (k + 1)) ^ 3 = 16 * 2 ^ (3 * k) := by
    rw [pow_succ 2 k, mul_pow, hp₃]
    norm_num
    ring
  rw [hv] at h
  apply le_trans ?_ h
  have hpos : 0 < 2 ^ k := by positivity
  have hq : 2 ^ k ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
  have hsub : 2 ^ k ≤ 2 ^ (k + 1) - 1 := by rw [pow_succ]; omega
  calc
    2 ^ (5 * k) = (2 ^ k) ^ 4 * 2 ^ k := by
      rw [← pow_succ, ← pow_mul, Nat.mul_comm k 5]
    _ ≤ (2 ^ (k + 1)) ^ 4 * (2 ^ (k + 1) - 1) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hq 4) hsub

/-- The known `r = 3` instance of the Zarankiewicz lower bound, with the
same quantifiers and real exponent as Erdős problem 714. Only this
instance, not the open assertion for all `r`, is claimed. -/
theorem erdos_714_case_three :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (3 : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin 3) (Fin 3)) : ℝ) := by
  apply AsymptoticBridge.eventually_extremalNumber_lower_bound_of_geometric_bounds
    (r := 3) (A := 16) (B := 1) (b := 2)
    (by decide) (by decide) (by decide) (by decide)
  intro k _
  simpa using geometric_norm_bound k

end Erdos714.CaseThree
