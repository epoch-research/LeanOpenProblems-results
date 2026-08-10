import FormalConjectures.Util.ProblemImports

open Matrix Nat Int Finset

noncomputable section

variable {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)

/-- The quadratic character on `ZMod p`. -/
local notation "χ" => quadraticChar (ZMod p)

include hp2 in
theorem ringChar_ne_two : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; exact hp2

include hp2 in
theorem jacobiSum_chi : jacobiSum χ χ = - χ (-1) := by
  have hq : (quadraticChar (ZMod p)).IsQuadratic := quadraticChar_isQuadratic _
  have hne : quadraticChar (ZMod p) ≠ 1 := quadraticChar_ne_one (ringChar_ne_two hp2)
  have := jacobiSum_nontrivial_inv (R := ℤ) hne
  rwa [hq.inv] at this

include hp2 in
/-- Jacobsthal-type sum: for `a ≠ b`, `∑_x χ((x-a)(x-b)) = -1`. -/
theorem sum_chi_quad (a b : ZMod p) (hab : a ≠ b) :
    ∑ x : ZMod p, χ ((x - a) * (x - b)) = -1 := by
  have hd : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  let e : ZMod p ≃ ZMod p := (Equiv.mulLeft₀ (b - a) hd).trans (Equiv.addLeft a)
  have hpt : ∀ t : ZMod p, χ ((e t - a) * (e t - b)) = χ (-1) * (χ t * χ (1 - t)) := by
    intro t
    have h1 : e t = a + (b - a) * t := rfl
    have e1 : e t - a = (b - a) * t := by rw [h1]; ring
    have e2 : e t - b = (b - a) * (t - 1) := by rw [h1]; ring
    rw [e1, e2]
    have : (b - a) * t * ((b - a) * (t - 1)) = (b - a)^2 * (t * (t - 1)) := by ring
    rw [this, map_mul, quadraticChar_sq_one' hd, one_mul, map_mul]
    have ht1 : t - 1 = (-1) * (1 - t) := by ring
    rw [ht1, map_mul]
    ring
  rw [← Equiv.sum_comp e (fun x => χ ((x - a) * (x - b)))]
  simp only [hpt]
  rw [← Finset.mul_sum, ← jacobiSum]
  rw [jacobiSum_chi hp2]
  have : χ (-1) * - χ (-1) = - (χ (-1))^2 := by ring
  rw [this, quadraticChar_sq_one (by simp)]

include hp2 in
/-- `∑_x χ((A-x)(B+x)) = -χ(-1)` when `A + B ≠ 0`. -/
theorem sum_chi_AB (A B : ZMod p) (h : A + B ≠ 0) :
    ∑ x : ZMod p, χ ((A - x) * (B + x)) = - χ (-1) := by
  have hAB : A ≠ -B := by intro hc; apply h; rw [hc]; ring
  have key := sum_chi_quad hp2 A (-B) hAB
  have : ∀ x : ZMod p, χ ((A - x) * (B + x)) = χ (-1) * χ ((x - A) * (x - (-B))) := by
    intro x
    rw [← map_mul]
    congr 1
    ring
  simp only [this]
  rw [← Finset.mul_sum, key]
  ring

/-- Wilson's lemma, the half-factorial squared. -/
theorem wilson_half (m : ℕ) (hm : p = 2 * m + 1) :
    ((m ! : ZMod p))^2 = (-1)^(m+1) := by
  have hmp : m ≤ p := by omega
  have key : (m !) * (p - 1).descFactorial m = (p - 1)! := by
    have h := Nat.factorial_mul_descFactorial (n := p - 1) (k := m) (by omega)
    rwa [show p - 1 - m = m by omega] at h
  have hcast : ((p - 1)! : ZMod p) = (m ! : ZMod p) * ((-1)^m * (m ! : ZMod p)) := by
    rw [← key]
    push_cast
    rw [ZMod.cast_descFactorial hmp]
  rw [ZMod.wilsons_lemma] at hcast
  -- hcast : -1 = m! * ((-1)^m * m!)
  have h2 : (-1 : ZMod p) = (-1)^m * (m ! : ZMod p)^2 := by linear_combination hcast
  have hsq : ((-1 : ZMod p)^m)^2 = 1 := by
    rw [← pow_mul]; exact Even.neg_one_pow ⟨m, by ring⟩
  rw [show (-1:ZMod p)^(m+1) = (-1)^m * (-1) from pow_succ _ _]
  have h3 : (-1:ZMod p)^m * (-1) = (-1)^m * ((-1)^m * (m ! : ZMod p)^2) := by rw [← h2]
  rw [h3, ← mul_assoc, ← sq, hsq, one_mul]

section Partition
variable {m : ℕ}

/-- The values `1, 2, …, m` in `ZMod p`. -/
def betaV (j : Fin m) : ZMod p := ((j.val + 1 : ℕ) : ZMod p)

theorem beta_ne_zero (hm : p = 2 * m + 1) (j : Fin m) : betaV (p := p) j ≠ 0 := by
  unfold betaV
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have hlt : j.val + 1 < p := by have := j.isLt; omega
  have hpos : 0 < j.val + 1 := by omega
  exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)

theorem beta_injective (hm : p = 2 * m + 1) :
    Function.Injective (betaV (p := p) (m := m)) := by
  intro a b hab
  unfold betaV at hab
  have ha : a.val + 1 < p := by have := a.isLt; omega
  have hb : b.val + 1 < p := by have := b.isLt; omega
  have : a.val + 1 = b.val + 1 := by
    have := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at this
  exact Fin.ext (by omega)

theorem beta_sum_ne_zero (hm : p = 2 * m + 1) (a b : Fin m) :
    betaV (p := p) a + betaV (p := p) b ≠ 0 := by
  unfold betaV
  rw [← Nat.cast_add, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have hlt : (a.val + 1) + (b.val + 1) < p := by
    have := a.isLt; have := b.isLt; omega
  have hpos : 0 < (a.val + 1) + (b.val + 1) := by omega
  exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)

end Partition

section SumSplit
variable {m : ℕ}

open Finset in
theorem sum_split (hm : p = 2 * m + 1) (g : ZMod p → ℤ) :
    (∑ j : Fin m, g (betaV (p := p) j)) + (∑ j : Fin m, g (- betaV (p := p) j))
      = ∑ x ∈ univ \ {(0 : ZMod p)}, g x := by
  classical
  -- injectivity
  have inj1 : Set.InjOn (betaV (p := p)) ↑(univ : Finset (Fin m)) :=
    (beta_injective hm).injOn
  have inj2 : Set.InjOn (fun j => - betaV (p := p) j) ↑(univ : Finset (Fin m)) :=
    (neg_injective.comp (beta_injective hm)).injOn
  set S1 : Finset (ZMod p) := (univ : Finset (Fin m)).image (betaV (p := p)) with hS1
  set S2 : Finset (ZMod p) := (univ : Finset (Fin m)).image (fun j => - betaV (p := p) j) with hS2
  -- disjoint
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    rintro x hx1 hx2
    rw [hS1, Finset.mem_image] at hx1
    rw [hS2, Finset.mem_image] at hx2
    obtain ⟨a, -, ha⟩ := hx1
    obtain ⟨b, -, hb⟩ := hx2
    apply beta_sum_ne_zero hm a b
    rw [← ha] at hb
    linear_combination -hb
  -- cards
  have hc1 : S1.card = m := by
    rw [hS1, Finset.card_image_of_injOn inj1, Finset.card_univ,
      Fintype.card_fin]
  have hc2 : S2.card = m := by
    rw [hS2, Finset.card_image_of_injOn inj2, Finset.card_univ,
      Fintype.card_fin]
  -- subset
  have hsub : S1 ∪ S2 ⊆ univ \ {(0 : ZMod p)} := by
    intro x hx
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · rw [hS1, Finset.mem_image] at hx
      obtain ⟨a, -, ha⟩ := hx
      rw [← ha]; exact beta_ne_zero hm a
    · rw [hS2, Finset.mem_image] at hx
      obtain ⟨a, -, ha⟩ := hx
      rw [← ha]; simpa using beta_ne_zero hm a
  -- card of target
  have hcardT : (univ \ {(0 : ZMod p)}).card = 2 * m := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, ZMod.card,
      Finset.card_singleton]
    omega
  -- equality of sets
  have heq : S1 ∪ S2 = univ \ {(0 : ZMod p)} := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcardT, Finset.card_union_of_disjoint hdisj, hc1, hc2]
    omega
  -- conclude
  rw [← heq, Finset.sum_union hdisj, hS1, hS2,
    Finset.sum_image inj1,
    Finset.sum_image inj2]

end SumSplit

section AntiSym
variable {m : ℕ}

/-- `χ(-1) = -1` when `p ≡ 3 (mod 4)`. -/
theorem chi_neg_one (hp4 : p % 4 = 3) : χ (-1 : ZMod p) = -1 := by
  rw [quadraticChar_neg_one_iff_not_isSquare]
  rw [ZMod.exists_sq_eq_neg_one_iff]
  simp [hp4]

/-- For `p ≡ 3 (mod 4)`, `a²+b² ≠ 0` for nonzero `a,b`. -/
theorem sq_add_sq_ne_zero (hp4 : p % 4 = 3) {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) :
    a^2 + b^2 ≠ 0 := by
  intro h
  have hsq : IsSquare (-1 : ZMod p) := by
    refine ⟨a * b⁻¹, ?_⟩
    have haa : a * a = -(b * b) := by linear_combination h
    have hbb : b * b⁻¹ = 1 := mul_inv_cancel₀ hb
    have key : (a * b⁻¹) * (a * b⁻¹) = -((b * b⁻¹) * (b * b⁻¹)) := by
      rw [show (a * b⁻¹) * (a * b⁻¹) = (a * a) * (b⁻¹ * b⁻¹) from by ring, haa]; ring
    rw [key, hbb]; ring
  rw [ZMod.exists_sq_eq_neg_one_iff] at hsq
  exact hsq hp4

include hp2 in
/-- Full quadratic character sum over `ZMod p`. -/
theorem full_chi_sum (c : ZMod p) (hc : c ≠ 0) (A B : ZMod p) (hAB : A + B ≠ 0) :
    ∑ x : ZMod p, χ ((A - c * x) * (B + c * x)) = - χ (-1) := by
  rw [← sum_chi_AB hp2 A B hAB]
  apply Fintype.sum_equiv (Equiv.mulLeft₀ c hc)
  intro x
  simp [Equiv.mulLeft₀]

include hp2 in
/-- The core antisymmetry identity: for `p ≡ 3 (mod 4)` the off-diagonal sums cancel. -/
theorem antisym_sum (hm : p = 2 * m + 1) (hp4 : p % 4 = 3) (c : ZMod p) (hc : c ≠ 0)
    (i k : Fin m) :
    (∑ j : Fin m, χ ((betaV (p := p) i ^ 2 - c * betaV j) * (betaV k ^ 2 + c * betaV j)))
    + (∑ j : Fin m, χ ((betaV (p := p) k ^ 2 - c * betaV j) * (betaV i ^ 2 + c * betaV j))) = 0 := by
  set ai := betaV (p := p) i with hai_def
  set ak := betaV (p := p) k with hak_def
  have hai : ai ≠ 0 := beta_ne_zero hm i
  have hak : ak ≠ 0 := beta_ne_zero hm k
  have e2 : (∑ j : Fin m, χ ((ak ^ 2 - c * betaV j) * (ai ^ 2 + c * betaV j)))
      = ∑ j : Fin m, (fun x => χ ((ai ^ 2 - c * x) * (ak ^ 2 + c * x))) (- betaV j) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only
    congr 1
    ring
  have key : (∑ j : Fin m, χ ((ai ^ 2 - c * betaV j) * (ak ^ 2 + c * betaV j)))
      + (∑ j : Fin m, χ ((ak ^ 2 - c * betaV j) * (ai ^ 2 + c * betaV j)))
      = ∑ x ∈ univ \ {(0 : ZMod p)}, χ ((ai ^ 2 - c * x) * (ak ^ 2 + c * x)) := by
    rw [e2]
    exact sum_split hm (fun x => χ ((ai ^ 2 - c * x) * (ak ^ 2 + c * x)))
  rw [key, Finset.sum_sdiff_eq_sub (Finset.subset_univ _), Finset.sum_singleton]
  have hg0 : χ ((ai ^ 2 - c * 0) * (ak ^ 2 + c * 0)) = 1 := by
    rw [mul_zero, sub_zero, add_zero, show ai ^ 2 * ak ^ 2 = (ai * ak) ^ 2 from by ring]
    exact quadraticChar_sq_one' (mul_ne_zero hai hak)
  have hAB : ai ^ 2 + ak ^ 2 ≠ 0 := sq_add_sq_ne_zero hp4 hai hak
  have hfull := full_chi_sum hp2 c hc (ai ^ 2) (ak ^ 2) hAB
  rw [hfull, hg0, chi_neg_one hp4]
  ring

end AntiSym

section Matrices
variable {m : ℕ}

/-- The integer matrix of Legendre symbols with constant `C`. -/
def matL (C : ℤ) : Matrix (Fin m) (Fin m) ℤ :=
  fun i j => legendreSym p (((i.val + 1 : ℕ) : ℤ) * ((i.val + 1 : ℕ) : ℤ)
    - C * ((j.val + 1 : ℕ) : ℤ))

theorem matL_eq_chi (C : ℤ) (i j : Fin m) :
    matL (p := p) C i j = χ ((betaV i) ^ 2 - (C : ZMod p) * betaV j) := by
  unfold matL
  rw [legendreSym]
  congr 1
  unfold betaV
  push_cast
  ring

include hp2 in
theorem det_mul_det_eq_zero (hm : p = 2 * m + 1) (hp4 : p % 4 = 3) (C : ℤ)
    (hC : (C : ZMod p) ≠ 0) :
    (matL (p := p) (m := m) C).det * (matL (p := p) (m := m) (-C)).det = 0 := by
  set c : ZMod p := (C : ZMod p) with hc_def
  set K : Matrix (Fin m) (Fin m) ℤ := matL (p := p) C * (matL (p := p) (-C))ᵀ with hK_def
  have hKval : ∀ i k, K i k
      = ∑ j : Fin m, χ ((betaV i ^ 2 - c * betaV j) * (betaV k ^ 2 + c * betaV j)) := by
    intro i k
    simp only [hK_def, Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [matL_eq_chi, matL_eq_chi, ← map_mul]
    congr 1
    push_cast
    ring
  have hanti : Kᵀ = -K := by
    ext i k
    simp only [Matrix.transpose_apply, Matrix.neg_apply]
    have h := antisym_sum hp2 hm hp4 c hC i k
    rw [hKval k i, hKval i k]
    linarith [h]
  have hodd : Odd m := by rw [Nat.odd_iff]; omega
  have hdet0 : K.det = 0 := by
    have h1 : K.det = (-1) ^ m * K.det := by
      conv_lhs => rw [← Matrix.det_transpose K, hanti, Matrix.det_neg]
      rw [Fintype.card_fin]
    rw [hodd.neg_one_pow] at h1
    linarith [h1]
  have hprod := Matrix.det_mul (matL (p := p) (m := m) C) (matL (p := p) (m := m) (-C))ᵀ
  rw [Matrix.det_transpose] at hprod
  rw [← hprod]
  exact hdet0

end Matrices

section LemmaM
variable {m : ℕ}

theorem choose_cast_ne_zero (hm : p = 2 * m + 1) (k : ℕ) (hk : k ≤ m) :
    ((m.choose k : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have hpp : p.Prime := Fact.out
  have hdvdfac : m.choose k ∣ m ! := by
    have := Nat.choose_mul_factorial_mul_factorial hk
    exact ⟨k ! * (m - k)!, by rw [← this]; ring⟩
  have hpfac : p ∣ m ! := dvd_trans hdvd hdvdfac
  rw [hpp.dvd_factorial] at hpfac
  omega

theorem r_pow_m (hm : p = 2 * m + 1) (i : Fin m) :
    (betaV (p := p) i ^ 2) ^ m = 1 := by
  rw [← pow_mul]
  have h2m : 2 * m = p - 1 := by omega
  rw [h2m]
  exact ZMod.pow_card_sub_one_eq_one (beta_ne_zero hm i)

theorem r_injective (hm : p = 2 * m + 1) :
    Function.Injective (fun i : Fin m => betaV (p := p) i ^ 2) := by
  intro a b hab
  simp only at hab
  have hd : (betaV (p := p) a - betaV b) * (betaV a + betaV b) = 0 := by ring_nf; linear_combination hab
  rcases mul_eq_zero.mp hd with h | h
  · exact beta_injective hm (by linear_combination h)
  · exact absurd h (beta_sum_ne_zero hm a b)

/-- Binomial expansion of the matrix-vector relation, as powers of `(betaV i)^2`. -/
theorem relExpand (c : ZMod p) (v : Fin m → ZMod p) (i : Fin m) :
    ∑ j : Fin m, (betaV (p := p) i ^ 2 - c * betaV j) ^ m * v j
    = ∑ k ∈ range (m + 1),
        ((m.choose k : ZMod p) * (-c) ^ (m - k) * (∑ j : Fin m, betaV j ^ (m - k) * v j))
          * (betaV i ^ 2) ^ k := by
  have expand : ∀ j : Fin m, (betaV (p := p) i ^ 2 - c * betaV j) ^ m
      = ∑ k ∈ range (m + 1),
          (betaV i ^ 2) ^ k * ((-c) ^ (m - k) * betaV j ^ (m - k)) * (m.choose k : ZMod p) := by
    intro j
    rw [show betaV (p := p) i ^ 2 - c * betaV j = betaV i ^ 2 + (-(c * betaV j)) from by ring,
      add_pow]
    apply Finset.sum_congr rfl
    intro k _
    rw [show -(c * betaV j) = (-c) * betaV j from by ring, mul_pow]
  simp_rw [expand, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

open Polynomial in
/-- The moment relation arising from the columns being supported on `{1,…,m}`. -/
theorem momentRel (hm : p = 2 * m + 1) (v : Fin m → ZMod p)
    (hmid : ∀ k, 1 ≤ k → k < m → (∑ j : Fin m, betaV (p := p) j ^ k * v j) = 0) :
    (-1) ^ m * (m ! : ZMod p) * (∑ j : Fin m, betaV (p := p) j ^ 0 * v j)
      + (∑ j : Fin m, betaV (p := p) j ^ m * v j) = 0 := by
  have hm1 : 1 ≤ m := by
    have : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  set s : ℕ → ZMod p := fun k => ∑ j : Fin m, betaV (p := p) j ^ k * v j with hs
  set W : (ZMod p)[X] := ∏ l ∈ range m, (X - C (((l + 1 : ℕ) : ZMod p))) with hW
  have hWdeg : W.natDegree = m := by
    rw [hW, natDegree_prod _ _ (fun l _ => X_sub_C_ne_zero _)]
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have hWeval : ∀ j : Fin m, W.eval (betaV (p := p) j) = 0 := by
    intro j
    rw [hW, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_range.mpr j.isLt)
    simp only [eval_sub, eval_X, eval_C, betaV]
    ring
  have hmoment : ∑ d ∈ Finset.range (m + 1), W.coeff d * s d = 0 := by
    have step : ∑ d ∈ Finset.range (m + 1), W.coeff d * s d
        = ∑ j : Fin m, W.eval (betaV (p := p) j) * v j := by
      simp only [hs]
      rw [show (∑ d ∈ Finset.range (m + 1), W.coeff d * ∑ j : Fin m, betaV (p := p) j ^ d * v j)
            = ∑ d ∈ Finset.range (m + 1), ∑ j : Fin m, W.coeff d * (betaV (p := p) j ^ d * v j) from by
            apply Finset.sum_congr rfl; intro d _; rw [Finset.mul_sum]]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [eval_eq_sum_range' (n := m + 1) (by rw [hWdeg]; omega) (betaV (p := p) j),
        Finset.sum_mul]
      apply Finset.sum_congr rfl; intro d _; ring
    rw [step]
    apply Finset.sum_eq_zero
    intro j _
    rw [hWeval j, zero_mul]
  -- Reduce: only d = 0 and d = m survive.
  have hsplit : ∑ d ∈ Finset.range (m + 1), W.coeff d * s d = W.coeff 0 * s 0 + W.coeff m * s m := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (m + 1)) (fun d => d = 0 ∨ d = m)]
    have h1 : ∑ d ∈ (Finset.range (m + 1)).filter (fun d => ¬(d = 0 ∨ d = m)), W.coeff d * s d = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      rw [Finset.mem_filter, Finset.mem_range] at hd
      have hsd : s d = 0 := hmid d (by omega) (by omega)
      rw [hsd, mul_zero]
    rw [h1, add_zero]
    have h2 : (Finset.range (m + 1)).filter (fun d => d = 0 ∨ d = m) = {0, m} := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [h2, Finset.sum_pair (by omega : (0 : ℕ) ≠ m)]
  rw [hsplit] at hmoment
  -- coefficients
  have hc0 : W.coeff 0 = (-1) ^ m * (m ! : ZMod p) := by
    rw [hW, coeff_zero_eq_eval_zero, eval_prod]
    simp only [eval_sub, eval_X, eval_C, zero_sub]
    rw [show (fun l => -(((l + 1 : ℕ) : ZMod p))) = fun l => (-1) * (((l + 1 : ℕ) : ZMod p))
          from by funext l; ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← Nat.cast_prod,
      Finset.prod_range_add_one_eq_factorial]
  have hcm : W.coeff m = 1 := by
    have : W.Monic := monic_prod_of_monic _ _ (fun l _ => monic_X_sub_C _)
    rw [← hWdeg]; exact this.coeff_natDegree
  rw [hc0, hcm, one_mul] at hmoment
  exact hmoment

/-- **Lemma M**: nonsingularity of the power matrix over `ZMod p`. -/
theorem lemmaM (hm : p = 2 * m + 1) (c : ZMod p) (hc : c ≠ 0)
    (hcond : c ^ m * (m ! : ZMod p) ≠ 1) :
    (Matrix.of (fun i j : Fin m => (betaV (p := p) i ^ 2 - c * betaV j) ^ m)).det ≠ 0 := by
  have hm1 : 1 ≤ m := by
    have : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set s : ℕ → ZMod p := fun k => ∑ j : Fin m, betaV (p := p) j ^ k * v j with hs
  -- coefficient of (betaV i ^ 2) ^ k
  set cf : ℕ → ZMod p := fun k => (m.choose k : ZMod p) * (-c) ^ (m - k) * s (m - k) with hcf
  -- the relation from P v = 0
  have rel : ∀ i : Fin m, ∑ k ∈ range (m + 1), cf k * (betaV (p := p) i ^ 2) ^ k = 0 := by
    intro i
    have h0 : ∑ j : Fin m, (betaV (p := p) i ^ 2 - c * betaV j) ^ m * v j = 0 := by
      have hi := congrFun hMv i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at hi
      exact hi
    rw [relExpand] at h0
    exact h0
  -- truncate: drop the top term using r^m = 1
  have relTrunc : ∀ i : Fin m, ∑ k ∈ range m, cf k * (betaV (p := p) i ^ 2) ^ k = - cf m := by
    intro i
    have h := rel i
    rw [Finset.sum_range_succ, r_pow_m hm i, mul_one] at h
    linear_combination h
  -- the kernel vector
  set u : Fin m → ZMod p := fun k => cf k.val - (if k.val = 0 then - cf m else 0) with hu
  have hker : u = 0 := by
    apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero (r_injective hm)
    intro i
    have e1 : ∑ k : Fin m, (betaV (p := p) i ^ 2) ^ (k : ℕ) * cf k.val
        = ∑ k ∈ range m, cf k * (betaV (p := p) i ^ 2) ^ k := by
      rw [Fin.sum_univ_eq_sum_range (fun k => (betaV (p := p) i ^ 2) ^ k * cf k)]
      apply Finset.sum_congr rfl; intro k _; ring
    have e2 : ∑ k : Fin m, (betaV (p := p) i ^ 2) ^ (k : ℕ) * (if k.val = 0 then - cf m else 0)
        = - cf m := by
      rw [Finset.sum_eq_single (⟨0, hm1⟩ : Fin m)]
      · simp
      · intro b _ hb
        have : b.val ≠ 0 := fun h => hb (Fin.ext h)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [hu, mul_sub]
    rw [Finset.sum_sub_distrib, e1, e2, relTrunc i]
    ring
  -- extract the facts
  have hcfm : cf m = s 0 := by simp [hcf]
  have hcf0 : cf 0 = (-c) ^ m * s m := by simp [hcf]
  -- A2 : (-c)^m * s m + s 0 = 0
  have hA2 : (-c) ^ m * s m + s 0 = 0 := by
    have h := congrFun hker (⟨0, hm1⟩ : Fin m)
    rw [Pi.zero_apply] at h
    rw [show u (⟨0, hm1⟩ : Fin m) = cf 0 + cf m from by simp [hu]] at h
    rw [hcf0, hcfm] at h
    linear_combination h
  -- A1 : s a = 0 for 1 ≤ a ≤ m-1
  have hA1 : ∀ a, 1 ≤ a → a < m → s a = 0 := by
    intro a ha1 ham
    have hl : m - a < m := by omega
    have := congrFun hker (⟨m - a, hl⟩ : Fin m)
    simp only [hu, Pi.zero_apply] at this
    have hne : (m - a) ≠ 0 := by omega
    rw [if_neg hne, sub_zero] at this
    -- this : cf (m - a) = 0, i.e. (m.choose (m-a))*(-c)^(m-(m-a))*s(m-(m-a)) = 0
    rw [hcf] at this
    simp only at this
    rw [show m - (m - a) = a from by omega] at this
    have h1 : ((m.choose (m - a) : ℕ) : ZMod p) ≠ 0 := choose_cast_ne_zero hm _ (by omega)
    have h2 : (-c) ^ a ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hc)
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' h1
      · exact absurd h' h2
    · exact h
  -- B : moment relation
  have hB : (-1) ^ m * (m ! : ZMod p) * s 0 + s m = 0 := by
    have := momentRel hm v (fun k hk1 hk2 => hA1 k hk1 hk2)
    simpa [hs] using this
  -- combine to get s 0 = 0
  have hs0 : s 0 = 0 := by
    have hsm_eq : s m = - ((-1) ^ m * (m ! : ZMod p) * s 0) := by linear_combination hB
    have hcc : (-c) ^ m * (-1) ^ m = c ^ m := by rw [← mul_pow]; ring_nf
    have hkey : (c ^ m * (m ! : ZMod p) - 1) * s 0 = 0 := by
      have h2 : (-c) ^ m * s m + s 0 = 0 := hA2
      rw [hsm_eq] at h2
      linear_combination -h2 - (m ! : ZMod p) * s 0 * hcc
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd (sub_eq_zero.mp h).symm hcond.symm
    · exact h
  have hsm : s m = 0 := by
    have h : (-c) ^ m * s m = 0 := by linear_combination hA2 - hs0
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (pow_ne_zero _ (neg_ne_zero.mpr hc))
    · exact h
  -- v = 0
  have hv0 : v = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (beta_injective hm)
    intro k
    have hsk : s (k : ℕ) = 0 := by
      rcases Nat.eq_zero_or_pos (k : ℕ) with h | h
      · rw [h]; exact hs0
      · exact hA1 _ h k.isLt
    rw [← hsk, hs]
    apply Finset.sum_congr rfl; intro j _; ring
  exact hv hv0

end LemmaM

section Reduction
variable {m : ℕ}

theorem matL_det_cast (hm : p = 2 * m + 1) (C : ℤ) :
    ((matL (p := p) (m := m) C).det : ZMod p)
      = (Matrix.of (fun i j : Fin m => (betaV (p := p) i ^ 2 - (C : ZMod p) * betaV j) ^ m)).det := by
  have hmap : (matL (p := p) (m := m) C).map (Int.castRingHom (ZMod p))
      = Matrix.of (fun i j : Fin m => (betaV (p := p) i ^ 2 - (C : ZMod p) * betaV j) ^ m) := by
    ext i j
    rw [Matrix.map_apply, Matrix.of_apply]
    show ((matL (p := p) C i j : ℤ) : ZMod p) = _
    unfold matL
    rw [legendreSym.eq_pow]
    rw [show p / 2 = m from by omega]
    congr 1
    unfold betaV
    push_cast
    ring
  have := RingHom.map_det (Int.castRingHom (ZMod p)) (matL (p := p) (m := m) C)
  simp only [eq_intCast] at this
  rw [this, RingHom.mapMatrix_apply, hmap]

theorem matL_det_ne_zero (hm : p = 2 * m + 1) (C : ℤ) (hc : (C : ZMod p) ≠ 0)
    (hcond : (C : ZMod p) ^ m * (m ! : ZMod p) ≠ 1) :
    (matL (p := p) (m := m) C).det ≠ 0 := by
  intro h
  have hz : ((matL (p := p) (m := m) C).det : ZMod p) = 0 := by rw [h]; simp
  rw [matL_det_cast hm C] at hz
  exact lemmaM hm (C : ZMod p) hc hcond hz

end Reduction

section FinalCond
variable {m : ℕ}

include hp2 in
theorem neg_one_ne_one_zmod : (-1 : ZMod p) ≠ 1 := by
  intro h
  have h2 : (2 : ZMod p) = 0 := by linear_combination -h
  rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by push_cast; ring, ZMod.natCast_eq_zero_iff] at h2
  have hle := Nat.le_of_dvd (by norm_num) h2
  have := (Fact.out : p.Prime).two_le
  omega

include hp2 in
theorem hcond_pos (hm : p = 2 * m + 1) (hp4 : p % 4 = 1) :
    (m ! : ZMod p) ^ m * (m ! : ZMod p) ≠ 1 := by
  set w : ZMod p := (m ! : ZMod p) with hw
  intro hcon
  -- hcon : w^m * w = 1, i.e. w^(m+1) = 1
  have hpow : w ^ (m + 1) = 1 := by rw [pow_succ]; exact hcon
  have hsq : (w ^ (m + 1)) ^ 2 = -1 := by
    rw [← pow_mul, mul_comm (m + 1) 2, pow_mul, wilson_half m hm, ← pow_mul]
    apply Odd.neg_one_pow
    rw [Nat.odd_mul]
    constructor <;> · rw [Nat.odd_iff]; omega
  rw [hpow, one_pow] at hsq
  exact neg_one_ne_one_zmod hp2 hsq.symm

theorem hcond_neg (hm : p = 2 * m + 1) (hp4 : p % 4 = 3) :
    (-(m ! : ZMod p)) ^ m * (m ! : ZMod p) = -1 := by
  set w : ZMod p := (m ! : ZMod p) with hw
  have hmodd : Odd m := by rw [Nat.odd_iff]; omega
  have hw2 : w ^ 2 = 1 := by
    rw [wilson_half m hm]; apply Even.neg_one_pow; rw [Nat.even_iff]; omega
  have hwm1 : w ^ (m + 1) = 1 := by
    obtain ⟨t, ht⟩ : Even (m + 1) := by rw [Nat.even_iff]; omega
    rw [show m + 1 = 2 * t from by omega, pow_mul, hw2, one_pow]
  rw [neg_pow, hmodd.neg_one_pow, mul_assoc, ← pow_succ, hwm1, mul_one]

end FinalCond

open Matrix Nat Int

/--
A226163: Determinant of the $(p_n-1)/2$-by-$(p_n-1)/2$ matrix with $(i,j)$-entry being the Legendre symbol
$$\left(\frac{i^2 - \left(\frac{p_n-1}{2}\right)! \cdot j}{p_n}\right)$$
where $p_n$ is the $n$-th prime.
The sequence is naturally indexed starting from $n=2$.
-/
noncomputable def A226163 (n : ℕ) : ℤ :=
  if h : n < 2 then 0 else

  -- p is the n-th prime, p_n. Mathlib's nth Nat.Prime is 0-indexed, so we use (n-1).
  -- Since n >= 2, p >= 3 is an an odd prime.
  let p : ℕ := Nat.nth Nat.Prime (n - 1)

  -- Matrix dimension m = (p-1)/2.
  let m : ℕ := (p - 1) / 2

  -- The constant C = ((p-1)/2)! as an integer.
  let C : ℤ := m.factorial.cast

  -- The matrix M has entries in ℤ.
  let M : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    -- 1-based indices i' and j' for the formula: 1 <= i', j' <= m.
    let i' : ℤ := (i.val + 1).cast
    let j' : ℤ := (j.val + 1).cast

    -- Argument for the Legendre symbol: i'^2 - C * j'
    let arg : ℤ := i' * i' - C * j'

    -- jacobiSym is the Legendre symbol since p is prime.
    jacobiSym arg p

  M.det

/--
Conjecture: a(n) = 0 if and only if p_n ≡ 3 (mod 4).
-/
theorem oeis_226163_conjecture_0 (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  have hpprime : (Nat.nth Nat.Prime (n - 1)).Prime := Nat.prime_nth_prime (n - 1)
  haveI : Fact (Nat.nth Nat.Prime (n - 1)).Prime := ⟨hpprime⟩
  have hp3 : 3 ≤ Nat.nth Nat.Prime (n - 1) := by
    have := Nat.add_two_le_nth_prime (n - 1); omega
  set p := Nat.nth Nat.Prime (n - 1) with hp_def
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hpprime.odd_of_ne_two hp2
  have hp2mod : p % 2 = 1 := Nat.odd_iff.mp hpodd
  have hm : p = 2 * ((p - 1) / 2) + 1 := by omega
  set m := (p - 1) / 2 with hm_def
  have hmlt : m < p := by omega
  have hc : ((m ! : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    rw [hpprime.dvd_factorial] at hdvd
    omega
  -- Bridging: A226163 n is the determinant of matL (m!).
  have hA : A226163 n = (matL (p := p) (m := m) ((m ! : ℤ))).det := by
    rw [A226163, dif_neg (show ¬ n < 2 by omega)]
    dsimp only
    congr 1
    funext i j
    rw [matL]
    exact (jacobiSym.legendreSym.to_jacobiSym p _).symm
  rw [hA]
  constructor
  · intro hdet
    by_contra hp4
    have hp41 : p % 4 = 1 := by omega
    have hcond : ((m ! : ℤ) : ZMod p) ^ m * (m ! : ZMod p) ≠ 1 := by
      rw [Int.cast_natCast]; exact hcond_pos hp2 hm hp41
    exact matL_det_ne_zero hm (m ! : ℤ) hc hcond hdet
  · intro hp4
    have hprod := det_mul_det_eq_zero hp2 hm hp4 (m ! : ℤ) hc
    have hcast : ((-(m ! : ℤ) : ℤ) : ZMod p) = -(m ! : ZMod p) := by push_cast; ring
    have hNZ : (matL (p := p) (m := m) (-(m ! : ℤ))).det ≠ 0 := by
      apply matL_det_ne_zero hm (-(m ! : ℤ))
      · rw [hcast, neg_ne_zero]; rw [Int.cast_natCast] at hc; exact hc
      · rw [hcast, hcond_neg hm hp4]; exact neg_one_ne_one_zmod hp2
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · exact absurd h hNZ
