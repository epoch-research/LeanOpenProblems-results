import FormalConjecturesUtil

/-!
A parametric obstruction to multiplicatively weighted cubic norm-plus-quintic graphs.
This development does not prove or disprove Erdős Problem 714.
-/

open SimpleGraph Polynomial

set_option maxHeartbeats 4000000

namespace Erdos714QuinticNormProduct

variable {F : Type*} [Field F] [CharP F 3]

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The restriction to the plane spanned by 1 and an Artin--Schreier generator. -/
def planeKernel (d δ : F) (v : F × F) : F :=
  (v.1 ^ 3 - v.1 * v.2 ^ 2 + d * v.2 ^ 3) * (1 - δ * v.2 ^ 2)

/-- Multiplicative weights on the two sides of a graph defined by a kernel. -/
def weightedGraph {A : Type*} [AddCommMonoid A] (f : A → F) :
    SimpleGraph ((A × Fˣ) ⊕ (A × Fˣ)) where
  Adj v w := match v, w with
    | .inl x, .inr y => f (x.1 + y.1) = (x.2 : F) * (y.2 : F)
    | .inr y, .inl x => f (x.1 + y.1) = (x.2 : F) * (y.2 : F)
    | _, _ => False
  symm := by intro v w; cases v <;> cases w <;> simp_all
  loopless := by intro v; cases v <;> simp

/-- The explicit four-by-four configuration, under its single parameter identity. -/
def planeCopy (δ u c d : F) (hu : u ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hK : 1 - δ * u ^ 2 ≠ 0)
    (hrel : (1 - δ * u ^ 2) * d = (1 + (1 - δ * u ^ 2)) * c ^ 3 -
      (1 - δ * u ^ 2) * c) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (weightedGraph (planeKernel d δ)) := by
  let B : Fˣ := Units.mk0 (u ^ 3 * (1 - δ * u ^ 2) * d)
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hu) hK) hd)
  let C : Fˣ := Units.mk0 (-u ^ 3 * c ^ 3)
    (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 3 hu)) (pow_ne_zero 3 hc))
  let L : Fin 4 → (F × F) × Fˣ := ![((0,0),1), ((u,0),1), ((-u,0),1), ((0,u),-1)]
  let R : Fin 4 → (F × F) × Fˣ := ![((0,u),B), ((u,u),B), ((-u,u),B), ((u*c,-u),C)]
  have hneg : u ≠ -u := by
    intro h
    have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
    apply hu
    linear_combination -h + u * h3
  have hL : Function.Injective L := by
    intro i j hij
    have h := congrArg Prod.fst hij
    fin_cases i <;> fin_cases j <;>
      simp [L, hu, Ne.symm hu, hneg, Ne.symm hneg] at h ⊢
  have hR : Function.Injective R := by
    intro i j hij
    have h := congrArg Prod.fst hij
    fin_cases i <;> fin_cases j <;>
      simp [R, hu, Ne.symm hu, hneg, Ne.symm hneg] at h ⊢
  have hE : ∀ i j, planeKernel d δ ((L i).1 + (R j).1) =
      ((L i).2 : F) * ((R j).2 : F) := by
    intro i j
    fin_cases i <;> fin_cases j <;> dsimp [L, R, B, C, planeKernel]
    all_goals apply sub_eq_zero.mp
    all_goals ring_nf
    all_goals reduce_mod_char!
    all_goals linear_combination (norm := skip) -(u ^ 3) * hrel
    all_goals ring_nf
    all_goals reduce_mod_char!
  let le : Fin 4 ↪ (F × F) × Fˣ := ⟨L, hL⟩
  let re : Fin 4 ↪ (F × F) × Fˣ := ⟨R, hR⟩
  refine ⟨⟨le.sumMap re, ?_⟩, (le.sumMap re).injective⟩
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j => simp at hab
    | inr j => exact hE i j
  | inr j =>
    cases b with
    | inl i => exact hE i j
    | inr i => simp at hab

omit [CharP F 3] in
/-- More than three scalars permit a nonzero scale avoiding the two bad roots. -/
lemma exists_scale [Fintype F] (δ : F) (hq : 3 < Fintype.card F) :
    ∃ u : F, u ≠ 0 ∧ 1 - δ * u ^ 2 ≠ 0 := by
  classical
  by_cases hδ : δ = 1
  · subst δ
    have hsmall : ({0, 1, -1} : Finset F).card ≤ 3 := Finset.card_le_three
    obtain ⟨u, _, hu⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, 1, -1} : Finset F)) (t := Finset.univ)
      (by simpa using hsmall.trans_lt hq)
    have hn : u ≠ 0 ∧ u ≠ 1 ∧ u ≠ -1 := by simpa using hu
    refine ⟨u, hn.1, ?_⟩
    intro h
    have hs : u ^ 2 = 1 := (sub_eq_zero.mp (by simpa using h)).symm
    exact (sq_eq_one_iff.mp hs).elim hn.2.1 hn.2.2
  · refine ⟨1, one_ne_zero, ?_⟩
    simpa only [one_pow, mul_one] using (sub_ne_zero.mpr (Ne.symm hδ))

omit [CharP F 3] in
/-- The Artin--Schreier map omits some scalar in every finite field of characteristic three. -/
lemma exists_outside_artinSchreier [Finite F] : ∃ D : F, ∀ x : F, x ^ 3 - x ≠ D := by
  have hn : ¬ Function.Surjective (fun x : F => x ^ 3 - x) := by
    intro hs
    have hi := Finite.injective_iff_surjective.mpr hs
    exact zero_ne_one (hi (by simp : (0 : F) ^ 3 - 0 = 1 ^ 3 - 1))
  simpa only [Function.Surjective, not_forall, not_exists] using hn

/-- Choose parameters satisfying the configuration identity and an irreducible
Artin--Schreier polynomial, not merely a split cubic coordinate algebra. -/
theorem parameters [Fintype F] (δ : F) (hq : 3 < Fintype.card F) :
    ∃ u c d : F, u ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧ 1 - δ * u ^ 2 ≠ 0 ∧
      (1 - δ * u ^ 2) * d = (1 + (1 - δ * u ^ 2)) * c ^ 3 -
        (1 - δ * u ^ 2) * c ∧
      Irreducible (X ^ 3 - X - Polynomial.C d : F[X]) := by
  obtain ⟨u, hu, hK⟩ := exists_scale δ hq
  obtain ⟨D, hD⟩ := exists_outside_artinSchreier (F := F)
  have hD0 : D ≠ 0 := fun h => hD 0 (by simp [h])
  obtain ⟨c, hc⟩ := surjective_frobenius F 3 ((1 - δ * u ^ 2) * D)
  change c ^ 3 = (1 - δ * u ^ 2) * D at hc
  have hc0 : c ≠ 0 := by
    intro h
    have : (1 - δ * u ^ 2) * D = 0 := by simpa [h] using hc.symm
    exact mul_ne_zero hK hD0 this
  let d := c ^ 3 - c + D
  have hroot : ∀ x : F, x ^ 3 - x ≠ d := by
    intro x hx
    apply hD (x - c)
    rw [sub_pow_char]
    dsimp [d] at hx
    linear_combination hx
  have hd0 : d ≠ 0 := fun h => hroot 0 (by simp [h])
  refine ⟨u, c, d, hu, hc0, hd0, hK, ?_, ?_⟩
  · dsimp [d]
    linear_combination -hc
  · apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · have hdeg : (X ^ 3 - X - Polynomial.C d : F[X]).natDegree = 3 := by compute_degree!
      rw [hdeg]
      decide
    · intro x hx
      apply hroot x
      simpa [Polynomial.IsRoot, sub_eq_zero] using hx

/-- Uniform coordinate obstruction, with the cubic polynomial certified irreducible. -/
theorem coordinate_obstruction [Fintype F] (δ : F) (hq : 3 < Fintype.card F) :
    ∃ d : F, Irreducible (X ^ 3 - X - Polynomial.C d : F[X]) ∧
      ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (weightedGraph (planeKernel d δ)) := by
  obtain ⟨u, c, d, hu, hc, hd, hK, hrel, hirr⟩ := parameters δ hq
  exact ⟨d, hirr, fun h => h ⟨planeCopy δ u c d hu hc hd hK hrel⟩⟩

section NormInterpretation

variable {E : Type*} [Field E] [Algebra F E] [CharP E 3]

/-- Coordinates in the power basis of a cubic Artin--Schreier extension. -/
def element (z : E) (a b c : F) : E :=
  algebraMap F E a + algebraMap F E b * z + algebraMap F E c * z ^ 2

/-- The multiplication matrix in that power basis. -/
def multiplicationMatrix (d a b c : F) : Matrix (Fin 3) (Fin 3) F :=
  !![a, d*c, d*b; b, a+c, b+d*c; c, b, a+c]

omit [CharP F 3] [CharP E 3] in
/-- Identification of the coordinate matrix with actual multiplication. -/
theorem leftMulMatrix_element (d : F) (z : E) (hz : z ^ 3 = z + algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i = z ^ (i : ℕ)) (a b c : F) :
    Algebra.leftMulMatrix B (element z a b c) = multiplicationMatrix d a b c := by
  have hz4 : z ^ 4 = z ^ 2 + algebraMap F E d * z := by
    calc
      z ^ 4 = z ^ 3 * z := by ring
      _ = _ := by rw [hz]; ring
  have hcol (j : Fin 3) :
      ∑ i, multiplicationMatrix d a b c i j • B i = element z a b c * B j := by
    simp only [Fin.sum_univ_three, hB, Algebra.smul_def]
    fin_cases j
    · change algebraMap F E a * z^0 + algebraMap F E b * z^1 +
        algebraMap F E c * z^2 = element z a b c * z^0
      unfold element
      ring
    · change algebraMap F E (d*c) * z^0 + algebraMap F E (a+c) * z^1 +
        algebraMap F E b * z^2 = element z a b c * z^1
      simp only [map_mul, map_add]
      unfold element
      ring_nf
      rw [hz]
      ring
    · change algebraMap F E (d*b) * z^0 + algebraMap F E (b+d*c) * z^1 +
        algebraMap F E (a+c) * z^2 = element z a b c * z^2
      simp only [map_mul, map_add]
      unfold element
      ring_nf
      rw [hz4, hz]
      ring
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, ← hcol j]
  simp [Finsupp.single_apply]

omit [CharP F 3] [CharP E 3] in
/-- The norm formula on the plane used by the configuration. -/
theorem norm_plane (d : F) (z : E) (hz : z ^ 3 = z + algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i = z ^ (i : ℕ)) (a b : F) :
    Algebra.norm F (element z a b 0) = a ^ 3 - a * b ^ 2 + d * b ^ 3 := by
  rw [Algebra.norm_eq_matrix_det B, leftMulMatrix_element d z hz B hB,
    Matrix.det_fin_three]
  simp [multiplicationMatrix]
  ring

omit [CharP E 3] in
/-- In characteristic three the coordinate trace is minus the quadratic coefficient. -/
theorem trace_element (d : F) (z : E) (hz : z ^ 3 = z + algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i = z ^ (i : ℕ)) (a b c : F) :
    Algebra.trace F E (element z a b c) = -c := by
  rw [Algebra.trace_eq_matrix_trace B, leftMulMatrix_element d z hz B hB]
  simp only [Matrix.trace, Fin.sum_univ_three]
  change a + (a+c) + (a+c) = -c
  apply sub_eq_zero.mp
  ring_nf
  reduce_mod_char!

/-- The trace-quintic on this plane is exactly minus the squared second coordinate
multiplied by the norm. -/
theorem trace_fifth_plane (d : F) (z : E) (hz : z ^ 3 = z + algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i = z ^ (i : ℕ)) (a b : F) :
    Algebra.trace F E ((element z a b 0) ^ 5) =
      -b ^ 2 * (a ^ 3 - a * b ^ 2 + d * b ^ 3) := by
  have hz4 : z ^ 4 = z ^ 2 + algebraMap F E d * z := by
    calc
      z ^ 4 = z ^ 3 * z := by ring
      _ = _ := by rw [hz]; ring
  have hz5 : z ^ 5 = z + algebraMap F E d + algebraMap F E d * z ^ 2 := by
    calc
      z ^ 5 = z ^ 4 * z := by ring
      _ = z ^ 3 + algebraMap F E d * z ^ 2 := by rw [hz4]; ring
      _ = _ := by rw [hz]
  have he : (element z a b 0) ^ 5 = element z
      (a ^ 5 + d * a ^ 2 * b ^ 3 + d * b ^ 5)
      (2 * a ^ 4 * b + 2 * d * a * b ^ 4 + a ^ 2 * b ^ 3 + b ^ 5)
      (a ^ 3 * b ^ 2 + d * b ^ 5 + 2 * a * b ^ 4) := by
    unfold element
    simp only [map_zero, zero_mul, add_zero, map_add, map_mul, map_pow, map_ofNat]
    ring_nf
    rw [hz5, hz4, hz]
    apply sub_eq_zero.mp
    ring_nf
    reduce_mod_char!
  rw [he, trace_element d z hz B hB]
  apply sub_eq_zero.mp
  ring_nf
  reduce_mod_char!

/-- The coordinate kernel is the restriction of the actual norm-plus-trace kernel. -/
theorem kernel_plane (d δ : F) (z : E) (hz : z ^ 3 = z + algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i = z ^ (i : ℕ)) (a b : F) :
    Algebra.norm F (element z a b 0) + δ * Algebra.trace F E ((element z a b 0) ^ 5) =
      planeKernel d δ (a,b) := by
  rw [norm_plane d z hz B hB, trace_fifth_plane d z hz B hB]
  unfold planeKernel
  ring

omit [CharP F 3] [CharP E 3] in
/-- Independence of the first two basis vectors gives injectivity of plane coordinates. -/
lemma plane_element_injective (z : E) (B : Module.Basis (Fin 3) F E)
    (hB : ∀ i, B i = z ^ (i : ℕ)) :
    Function.Injective (fun v : F × F => element z v.1 v.2 0) := by
  have hform (a b : F) : element z a b 0 = a • B 0 + b • B 1 := by
    simp [element, hB, Algebra.smul_def]
  intro v w hvw
  have h0 := congrArg (fun x => B.repr x 0) hvw
  have h1 := congrArg (fun x => B.repr x 1) hvw
  simp only [hform, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul] at h0 h1
  exact Prod.ext (by simpa using h0) (by simpa using h1)

/-- The whole plane graph embeds into the actual norm-plus-quintic graph. -/
def planeGraphCopy (d δ : F) (z : E) (hz : z ^ 3 = z + algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i = z ^ (i : ℕ)) :
    Copy (weightedGraph (planeKernel d δ))
      (weightedGraph (fun x : E => Algebra.norm F x + δ * Algebra.trace F E (x ^ 5))) := by
  let e : (F × F) × Fˣ ↪ E × Fˣ :=
    ⟨fun v => (element z v.1.1 v.1.2 0, v.2), by
      intro v w h
      exact Prod.ext (plane_element_injective z B hB (congrArg Prod.fst h))
        (congrArg (fun p : E × Fˣ => p.2) h)⟩
  have hadd (v w : F × F) :
      element z v.1 v.2 0 + element z w.1 w.2 0 =
        element z (v+w).1 (v+w).2 0 := by
    simp [element]
    ring
  have he (v w : (F × F) × Fˣ)
      (h : planeKernel d δ (v.1+w.1) = (v.2 : F)*(w.2 : F)) :
      Algebra.norm F ((e v).1+(e w).1) +
          δ * Algebra.trace F E (((e v).1+(e w).1) ^ 5) = ((e v).2 : F)*((e w).2 : F) := by
    change Algebra.norm F (element z v.1.1 v.1.2 0 + element z w.1.1 w.1.2 0) +
      δ * Algebra.trace F E ((element z v.1.1 v.1.2 0 + element z w.1.1 w.1.2 0)^5) = _
    rw [hadd, kernel_plane d δ z hz B hB]
    exact h
  refine ⟨⟨e.sumMap e, ?_⟩, (e.sumMap e).injective⟩
  intro v w hvw
  cases v with
  | inl v =>
    cases w with
    | inl w => simp [weightedGraph] at hvw
    | inr w => exact he v w hvw
  | inr v =>
    cases w with
    | inl w => exact he w v hvw
    | inr w => simp [weightedGraph] at hvw

/-- Transfer of the parameter certificate to an actual cubic power basis. -/
theorem not_free_of_power_basis (δ u c d : F) (hu : u ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hK : 1 - δ * u ^ 2 ≠ 0)
    (hrel : (1 - δ * u ^ 2) * d = (1 + (1 - δ * u ^ 2)) * c ^ 3 -
      (1 - δ * u ^ 2) * c)
    (z : E) (hz : z ^ 3 = z + algebraMap F E d)
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i = z ^ (i : ℕ)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (weightedGraph (fun x : E => Algebra.norm F x + δ * Algebra.trace F E (x ^ 5))) := by
  intro hfree
  exact hfree ⟨(planeGraphCopy d δ z hz B hB).comp (planeCopy δ u c d hu hc hd hK hrel)⟩

end NormInterpretation

section FiniteExtension

variable {E : Type*} [Field E] [Algebra F E]

/-- An irreducible Artin--Schreier cubic has its natural power basis in every
cubic extension of a finite field, by uniqueness of finite-field extensions. -/
theorem exists_cubic_power_basis [Finite F] (hdegree : Module.finrank F E = 3)
    (d : F) (hirr : Irreducible (X ^ 3 - X - Polynomial.C d : F[X])) :
    ∃ z : E, z ^ 3 = z + algebraMap F E d ∧
      ∃ B : Module.Basis (Fin 3) F E, ∀ i, B i = z ^ (i : ℕ) := by
  let P : F[X] := X ^ 3 - X - Polynomial.C d
  letI : Fact (Irreducible P) := ⟨hirr⟩
  let A := AdjoinRoot P
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  have hdim : pb.dim = 3 := by
    change P.natDegree = 3
    dsimp [P]
    compute_degree!
  have hA : Module.finrank F A = 3 := pb.finrank.trans hdim
  let e : A ≃ₐ[F] E :=
    (FiniteField.algEquivExtension F 3 3 A hA).trans
      (FiniteField.algEquivExtension F 3 3 E hdegree).symm
  let pe := pb.map e
  have hedim : pe.dim = 3 := hdim
  let B := pe.basis.reindex (finCongr hedim)
  refine ⟨pe.gen, ?_, B, ?_⟩
  · have hroot : (AdjoinRoot.root P) ^ 3 = AdjoinRoot.root P + algebraMap F A d := by
      have h := AdjoinRoot.eval₂_root P
      change Polynomial.eval₂ (AdjoinRoot.of P) (AdjoinRoot.root P)
        (X ^ 3 - X - Polynomial.C d) = 0 at h
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
      change (AdjoinRoot.root P) ^ 3 - AdjoinRoot.root P - algebraMap F A d = 0 at h
      linear_combination h
    have h := congrArg e hroot
    simpa [pe, pb, AdjoinRoot.powerBasis_gen] using h
  · intro i
    simp [B]

/-- The multiplicative norm-plus-quintic construction fails in every cubic
extension of a characteristic-three field of order greater than three, for
any base-field trace coefficient. -/
theorem base_coefficient_not_free [Fintype F] (δ : F)
    (hq : 3 < Fintype.card F) (hdegree : Module.finrank F E = 3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (weightedGraph (fun x : E => Algebra.norm F x + δ * Algebra.trace F E (x ^ 5))) := by
  letI : CharP E 3 := (Algebra.charP_iff F E 3).mp inferInstance
  obtain ⟨u, c, d, hu, hc, hd, hK, hrel, hirr⟩ := parameters δ hq
  obtain ⟨z, hz, B, hB⟩ := exists_cubic_power_basis hdegree d hirr
  exact not_free_of_power_basis δ u c d hu hc hd hK hrel z hz B hB

private lemma five_coprime_cubic_index (q : ℕ) : (5 : ℕ).Coprime (q ^ 2 + q + 1) := by
  apply Nat.prime_five.coprime_iff_not_dvd.mpr
  intro hd
  have hz : (q ^ 2 + q + 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd hd
  have hq : q % 5 < 5 := Nat.mod_lt q (by decide)
  have cases : q % 5 = 0 ∨ q % 5 = 1 ∨ q % 5 = 2 ∨ q % 5 = 3 ∨ q % 5 = 4 := by omega
  rcases cases with h | h | h | h | h <;> norm_num [Nat.add_mod, Nat.pow_mod, h] at hz

omit [CharP F 3] in
/-- Every coefficient becomes a base-field scalar after multiplication by a fifth
power. This uses only the cubic extension degree, not a congruence on the field order. -/
theorem coefficient_normalization [Fintype F] [Finite E]
    (hdegree : Module.finrank F E = 3) (δ : Eˣ) :
    ∃ a : Eˣ, ∃ β : Fˣ, (δ : E) * (a : E) ^ 5 = algebraMap F E (β : F) := by
  let M := Fintype.card F ^ 2 + Fintype.card F + 1
  have hcop : (5 : ℕ).Coprime M := five_coprime_cubic_index _
  let N : Fˣ := Units.map (Algebra.norm F) δ
  let j : Fˣ →* Eˣ := Units.map (algebraMap F E).toMonoidHom
  have hN : j N = δ ^ M := by
    apply Units.ext
    change algebraMap F E (Algebra.norm F (δ : E)) = (δ : E) ^ M
    rw [FiniteField.algebraMap_norm_eq_pow_sum, hdegree]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, zero_add,
      pow_one, Nat.card_eq_fintype_card]
    congr 1
    dsimp [M]
    omega
  have hbez := Nat.gcd_eq_gcd_ab 5 M
  rw [hcop.gcd_eq_one] at hbez
  have hi : (1 : ℤ) + (-(Nat.gcdA 5 M)) * 5 = (M : ℤ) * Nat.gcdB 5 M := by
    norm_num only [Nat.cast_ofNat, Nat.cast_one] at hbez
    linear_combination hbez
  let a : Eˣ := δ ^ (-(Nat.gcdA 5 M))
  let β : Fˣ := N ^ (Nat.gcdB 5 M)
  have he : δ * a ^ 5 = j β := by
    dsimp [a, β]
    calc
      δ * (δ ^ (-(Nat.gcdA 5 M))) ^ 5 =
          δ ^ ((1 : ℤ) + (-(Nat.gcdA 5 M)) * 5) := by
        rw [zpow_add, zpow_one, zpow_mul, zpow_ofNat]
      _ = δ ^ ((M : ℤ) * Nat.gcdB 5 M) := by rw [hi]
      _ = j (N ^ (Nat.gcdB 5 M)) := by
        rw [map_zpow, hN, zpow_mul, zpow_natCast]
  refine ⟨a, β, ?_⟩
  simpa [j] using congrArg Units.val he

omit [CharP F 3] in
/-- Point scaling and a compensating column-weight scaling transfer graph copies. -/
def kernelScaleCopy (f g : E → F) (a : E) (ha : a ≠ 0) (k : Fˣ)
    (h : ∀ x, f (a * x) = (k : F) * g x) :
    Copy (weightedGraph g) (weightedGraph f) := by
  let l : E × Fˣ ↪ E × Fˣ := ⟨fun v => (a*v.1,v.2), by
    intro v w hvw
    exact Prod.ext (mul_left_cancel₀ ha (congrArg Prod.fst hvw)) (by simpa only using congrArg (fun v : E × Fˣ => v.2) hvw)⟩
  let r : E × Fˣ ↪ E × Fˣ := ⟨fun v => (a*v.1,k*v.2), by
    intro v w hvw
    exact Prod.ext (mul_left_cancel₀ ha (congrArg Prod.fst hvw))
      (mul_left_cancel (congrArg Prod.snd hvw))⟩
  have he (v w : E × Fˣ) (hvw : g (v.1+w.1) = (v.2 : F)*(w.2 : F)) :
      f ((l v).1+(r w).1) = ((l v).2 : F)*((r w).2 : F) := by
    change f (a*v.1+a*w.1) = (v.2 : F)*((k*w.2 : Fˣ) : F)
    rw [← mul_add, h, hvw]
    simp only [Units.val_mul]
    ring
  refine ⟨⟨l.sumMap r, ?_⟩, (l.sumMap r).injective⟩
  intro v w hvw
  cases v with
  | inl v =>
    cases w with
    | inl w => simp [weightedGraph] at hvw
    | inr w => exact he v w hvw
  | inr v =>
    cases w with
    | inl w => exact he w v hvw
    | inr w => simp [weightedGraph] at hvw

/-- Surjectivity of fifth powering reduces every nonzero extension-field trace
coefficient to a base-field coefficient. -/
theorem arbitrary_coefficient_not_free [Fintype F] (δ : E)
    (hq : 3 < Fintype.card F) (hdegree : Module.finrank F E = 3)
    (hpow : Function.Surjective (fun x : E => x ^ 5)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (weightedGraph (fun x : E => Algebra.norm F x + Algebra.trace F E (δ * x ^ 5))) := by
  by_cases hδ : δ = 0
  · subst δ
    simpa only [zero_mul, map_zero, add_zero] using
      (base_coefficient_not_free (E := E) (0 : F) hq hdegree)
  obtain ⟨a, ha⟩ := hpow δ⁻¹
  change a ^ 5 = δ⁻¹ at ha
  have ha0 : a ≠ 0 := by
    intro h
    exact inv_ne_zero hδ (by simpa [h] using ha.symm)
  have hN : Algebra.norm F a ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr ha0).map (Algebra.norm F)).ne_zero
  let k : Fˣ := Units.mk0 (Algebra.norm F a) hN
  have he (x : E) :
      Algebra.norm F (a*x) + Algebra.trace F E (δ*(a*x)^5) =
        (k : F)*(Algebra.norm F x + (Algebra.norm F a)⁻¹*Algebra.trace F E (x^5)) := by
    rw [map_mul, mul_pow, ← mul_assoc, ha, mul_inv_cancel₀ hδ, one_mul]
    change Algebra.norm F a * Algebra.norm F x + Algebra.trace F E (x^5) =
      Algebra.norm F a * (Algebra.norm F x + (Algebra.norm F a)⁻¹ * Algebra.trace F E (x^5))
    field_simp
  intro hfree
  apply base_coefficient_not_free (E := E) (Algebra.norm F a)⁻¹ hq hdegree
  rintro ⟨c⟩
  exact hfree ⟨(kernelScaleCopy _ _ a ha0 k he).comp c⟩

/-- Full uniform obstruction: every coefficient in every finite cubic extension,
with no congruence restriction on the characteristic-three base-field order. -/
theorem all_coefficients_not_free [Fintype F] (δ : E)
    (hq : 3 < Fintype.card F) (hdegree : Module.finrank F E = 3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (weightedGraph (fun x : E => Algebra.norm F x + Algebra.trace F E (δ * x ^ 5))) := by
  letI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hdegree]; decide)
  letI : Finite E := Module.finite_of_finite F
  by_cases hδ : δ = 0
  · subst δ
    simpa only [zero_mul, map_zero, add_zero] using
      (base_coefficient_not_free (E := E) (0 : F) hq hdegree)
  obtain ⟨a, β, hc⟩ := coefficient_normalization hdegree (Units.mk0 δ hδ)
  have hcoeff : δ * (a : E) ^ 5 = algebraMap F E (β : F) := hc
  let k : Fˣ := Units.map (Algebra.norm F) a
  let γ : F := (β : F) / (k : F)
  have he (x : E) :
      Algebra.norm F ((a : E)*x) + Algebra.trace F E (δ*((a : E)*x)^5) =
        (k : F)*(Algebra.norm F x + γ*Algebra.trace F E (x^5)) := by
    rw [map_mul, mul_pow, ← mul_assoc, hcoeff, ← Algebra.smul_def, LinearMap.map_smul]
    change (k : F) * Algebra.norm F x + (β : F) * Algebra.trace F E (x^5) =
      (k : F) * (Algebra.norm F x + γ*Algebra.trace F E (x^5))
    dsimp [γ]
    field_simp
  intro hfree
  apply base_coefficient_not_free (E := E) γ hq hdegree
  rintro ⟨c⟩
  exact hfree ⟨(kernelScaleCopy _ _ (a : E) a.ne_zero k he).comp c⟩

private lemma odd_power_three_mod_five (k : ℕ) :
    3 ^ (2 * k + 1) % 5 = 2 ∨ 3 ^ (2 * k + 1) % 5 = 3 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have he : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
    rw [he, pow_add, Nat.mul_mod]
    rcases ih with h | h <;> norm_num [h]

/-- The unit-group argument supplies the required surjectivity over odd-degree
extensions of the prime field. -/
lemma fifth_power_surjective [Fintype E] (k : ℕ)
    (hcard : Fintype.card E = 3 ^ (2 * k + 1)) :
    Function.Surjective (fun x : E => x ^ 5) := by
  classical
  have hcop : (3 ^ (2 * k + 1) - 1).Coprime 5 := by
    apply Nat.Coprime.symm
    apply (Nat.prime_five.coprime_iff_not_dvd).mpr
    intro hd
    have hp : 1 ≤ 3 ^ (2 * k + 1) := Nat.one_le_pow _ _ (by decide)
    have hm : (3 ^ (2 * k + 1) - 1 + 1) % 5 = 1 := by
      simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]
    rw [Nat.sub_add_cancel hp] at hm
    have h := odd_power_three_mod_five k
    omega
  have hunit : (Nat.card Eˣ).Coprime 5 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_units, hcard] using hcop
  intro x
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  · obtain ⟨y, hy⟩ := hunit.pow_left_bijective.surjective (Units.mk0 x hx)
    exact ⟨(y : E), by simpa using congrArg Units.val hy⟩

/-- Uniform failure over every sufficiently large odd-degree base-field order,
for arbitrary trace coefficients in the cubic extension. -/
theorem odd_base_not_free [Fintype F] [Fintype E] (δ : E)
    (hdegree : Module.finrank F E = 3) (k : ℕ)
    (hcard : Fintype.card F = 3 ^ (2 * k + 3)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (weightedGraph (fun x : E => Algebra.norm F x + Algebra.trace F E (δ * x ^ 5))) := by
  refine arbitrary_coefficient_not_free δ ?_ hdegree ?_
  · rw [hcard, pow_add]
    have hp : 1 ≤ 3 ^ (2 * k) := Nat.one_le_pow _ _ (by decide)
    norm_num
    omega
  · apply fifth_power_surjective (3 * k + 4)
    rw [Module.card_eq_pow_finrank (K := F) (V := E), hdegree, hcard, ← pow_mul]
    congr 1
    omega

end FiniteExtension

end Erdos714QuinticNormProduct

#print axioms Erdos714QuinticNormProduct.planeCopy
#print axioms Erdos714QuinticNormProduct.parameters
#print axioms Erdos714QuinticNormProduct.coordinate_obstruction

#print axioms Erdos714QuinticNormProduct.kernel_plane
#print axioms Erdos714QuinticNormProduct.planeGraphCopy
#print axioms Erdos714QuinticNormProduct.exists_cubic_power_basis
#print axioms Erdos714QuinticNormProduct.base_coefficient_not_free

#print axioms Erdos714QuinticNormProduct.kernelScaleCopy
#print axioms Erdos714QuinticNormProduct.arbitrary_coefficient_not_free
#print axioms Erdos714QuinticNormProduct.odd_base_not_free

#print axioms Erdos714QuinticNormProduct.coefficient_normalization
#print axioms Erdos714QuinticNormProduct.all_coefficients_not_free
