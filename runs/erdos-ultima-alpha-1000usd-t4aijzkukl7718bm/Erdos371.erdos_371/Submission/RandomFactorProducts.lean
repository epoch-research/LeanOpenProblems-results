import Submission.RandomFactorBins

/-! Arithmetic specialization of the random-bin collision bound. The factors
are arbitrary positive integers; prime-power specialization is not assumed. -/
namespace Erdos371.RandomBins
open Finset

section Products
variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]

def boxProduct (f : ι → ℕ) (a : ι → κ) (c : κ) : ℕ :=
  ∏ i ∈ univ.filter (fun i => a i = c), f i

lemma boxProduct_pos (f : ι → ℕ) (hf : ∀ i, 0 < f i) (a : ι → κ) (c : κ) :
    0 < boxProduct f a c := prod_pos (fun i _hi => hf i)

lemma prod_boxProduct [Fintype κ] (f : ι → ℕ) (a : ι → κ) :
    (∏ c : κ, boxProduct f a c) = ∏ i : ι, f i :=
  prod_fiberwise univ a f

lemma log_boxProduct (f : ι → ℕ) (hf : ∀ i, 0 < f i) (a : ι → κ) (c : κ) :
    Real.log (boxProduct f a c) =
      ∑ i ∈ univ.filter (fun i => a i = c), Real.log (f i) := by
  rw [boxProduct,Nat.cast_prod]
  apply Real.log_prod
  intro i hi
  exact_mod_cast (hf i).ne'

lemma boxMass_log_eq (N : ℕ) (f : ι → ℕ) (hf : ∀ i, 0 < f i)
    (a : ι → κ) (c : κ) :
    boxMass (fun i => Real.log (f i)/Real.log N) a c =
      Real.log (boxProduct f a c)/Real.log N := by
  rw [boxMass,← sum_div,log_boxProduct f hf]

lemma boxProduct_large_iff (N : ℕ) (hN : 1 < N) (f : ι → ℕ) (hf : ∀ i, 0 < f i)
    (a : ι → κ) (c : κ) (u : ℝ) :
    (N : ℝ)^u < boxProduct f a c ↔
      u < boxMass (fun i => Real.log (f i)/Real.log N) a c := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hb : (0 : ℝ) < boxProduct f a c := by exact_mod_cast boxProduct_pos f hf a c
  rw [boxMass_log_eq N f hf,lt_div_iff₀ hlog,← Real.log_rpow hNr]
  exact (Real.log_lt_log_iff (Real.rpow_pos_of_pos hNr u) hb).symm
end Products

section Random
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def productOverflowCount (K N : ℕ) (f : ι → ℕ) (u : ℝ) : ℕ := by
  classical
  exact (univ.filter fun a : ι → Fin K => ∃ c, (N : ℝ)^u < boxProduct f a c).card

/-- If the total product is at most N and each individual factor is at most
N^(u-delta), at most 1/(K*u*delta) of the assignments make a box exceed N^u. -/
theorem product_overflow_fraction_le (K N : ℕ) (hK : 0 < K) (hN : 1 < N)
    (f : ι → ℕ) (hf : ∀ i, 0 < f i) (hprod : (∏ i : ι, f i) ≤ N)
    (u δ : ℝ) (hu : 0 < u) (hδ : 0 < δ)
    (hmax : ∀ i, (f i : ℝ) ≤ (N : ℝ)^(u-δ)) :
    (productOverflowCount K N f u : ℝ)/(K : ℝ)^Fintype.card ι ≤ 1/((K : ℝ)*u*δ) := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  let w : ι → ℝ := fun i => Real.log (f i)/Real.log N
  have hw : ∀ i, 0 ≤ w i := fun i => div_nonneg (Real.log_natCast_nonneg _) hlog.le
  have htotal : (∑ i, w i) ≤ 1 := by
    have hlogprod : (∑ i, Real.log (f i : ℝ)) = Real.log ((∏ i, f i : ℕ) : ℝ) := by
      rw [Nat.cast_prod,Real.log_prod (fun i hi => by exact_mod_cast (hf i).ne')]
    dsimp only [w]
    rw [← sum_div,hlogprod]
    apply (div_le_one hlog).mpr
    exact Real.log_le_log (by exact_mod_cast prod_pos (fun i hi => hf i)) (by exact_mod_cast hprod)
  have hbound : ∀ i, w i ≤ u-δ := by
    intro i
    apply (div_le_iff₀ hlog).mpr
    have h := Real.log_le_log (by exact_mod_cast hf i) (hmax i)
    rwa [Real.log_rpow hNr] at h
  have he : productOverflowCount K N f u = overflowCount K w u := by
    unfold productOverflowCount overflowCount
    congr 1
    ext a
    simp only [mem_filter,mem_univ,true_and,boxProduct_large_iff N hN f hf]
    rfl
  rw [he]
  have h := overflow_fraction_le K hK w hw htotal u δ hu hδ hbound
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using h

noncomputable def productGoodCount (K N : ℕ) (f : ι → ℕ) (u : ℝ) : ℕ := by
  classical
  exact (univ.filter fun a : ι → Fin K => ∀ c, (boxProduct f a c : ℝ) ≤ (N : ℝ)^u).card

lemma productGoodCount_add_overflow (K N : ℕ) (f : ι → ℕ) (u : ℝ) :
    productGoodCount K N f u + productOverflowCount K N f u = K^Fintype.card ι := by
  classical
  have h := card_filter_add_card_filter_not (s := (univ : Finset (ι → Fin K)))
    (fun a => ∀ c, (boxProduct f a c : ℝ) ≤ (N : ℝ)^u)
  simpa only [productGoodCount,productOverflowCount,not_forall,not_le,
    card_univ,Fintype.card_fun,Fintype.card_fin] using h

/-- The retained assignment weight is uniformly close to one; it does not
use the reciprocal of the number of retained assignments. -/
theorem product_good_fraction_lower (K N : ℕ) (hK : 0 < K) (hN : 1 < N)
    (f : ι → ℕ) (hf : ∀ i, 0 < f i) (hprod : (∏ i : ι, f i) ≤ N)
    (u δ : ℝ) (hu : 0 < u) (hδ : 0 < δ)
    (hmax : ∀ i, (f i : ℝ) ≤ (N : ℝ)^(u-δ)) :
    1 - 1/((K : ℝ)*u*δ) ≤
      (productGoodCount K N f u : ℝ)/(K : ℝ)^Fintype.card ι := by
  have he : (productGoodCount K N f u : ℝ) + productOverflowCount K N f u =
      (K : ℝ)^Fintype.card ι := by exact_mod_cast productGoodCount_add_overflow K N f u
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hden : (K : ℝ)^Fintype.card ι ≠ 0 := ne_of_gt (pow_pos hKr _)
  have he' := congrArg (fun x : ℝ => x/(K : ℝ)^Fintype.card ι) he
  dsimp only at he'
  rw [add_div,div_self hden] at he'
  have hb := product_overflow_fraction_le K N hK hN f hf hprod u δ hu hδ hmax
  linarith

#print axioms prod_boxProduct
#print axioms product_overflow_fraction_le
#print axioms product_good_fraction_lower
end Random
end Erdos371.RandomBins
