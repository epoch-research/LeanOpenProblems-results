import Submission.FiniteRationalFamilyBound
import Submission.GrowthReduction
import Submission.Spec

/-! Representations whose projective directions belong to a fixed reduced
polynomial curve have subpolynomial counts at arbitrary positive targets.
This does not bound a collection of varying curves or all representations. -/
namespace Erdos322Research.FixedDirectionCurveBound

open Polynomial Finset FiniteRationalFamilyBound
set_option Elab.async false

/-- A power vector records a polynomial curve of directions. -/
noncomputable def powerVector {ι : Type*} (P : ι → ℤ[X]) (e : ℕ) : ι → ℤ[X] :=
  fun i => P i ^ e

noncomputable def powerSum {ι : Type*} [Fintype ι] (P : ι → ℤ[X]) (e : ℕ) : ℤ[X] :=
  ∑ i, P i ^ e

/-- The normalized power fractions determine a nonnegative tuple uniquely
at any prescribed target. -/
def onDirection {ι : Type*} [Fintype ι] (P : ι → ℤ[X]) (e n : ℕ)
    (a : ι → ℕ) : Prop :=
  ∃ t : Option ℚ, ∀ i, (a i : ℚ)^e =
    (n : ℚ)*projectiveValue (powerSum P e) (powerVector P e) t i

lemma powerSum_no_real_zero {ι : Type*} [Fintype ι]
    (P A : ι → ℤ[X]) (m C : ℕ) (hC : 0 < C)
    (hbez : ∑ i, A i * P i^(2*m) = Polynomial.C (C : ℤ)) :
    ∀ t : ℝ, (powerSum P (2*m)).eval₂ (Int.castRingHom ℝ) t ≠ 0 := by
  intro t hz
  simp only [powerSum,eval₂_finset_sum,eval₂_pow] at hz
  have hi (i : ι) : ((P i).eval₂ (Int.castRingHom ℝ) t)^(2*m)=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => (even_two_mul m).pow_nonneg _)).mp hz i (Finset.mem_univ i)
  have hb := congrArg (Polynomial.eval₂ (Int.castRingHom ℝ) t) hbez
  simp only [eval₂_finset_sum,eval₂_mul,eval₂_pow,eval₂_C,hi,mul_zero,
    Finset.sum_const_zero,Int.coe_castRingHom] at hb
  have hp : (0 : ℝ) < C := by exact_mod_cast hC
  norm_cast at hb
  linarith

/-- A generic injection from tuples into their chosen normalized parameters. -/
theorem tuple_card_le_parameter_card {ι α : Type*} [Fintype ι]
    (f : ℤ[X]) (g : ι → ℤ[X]) (e n : ℕ) (he : e ≠ 0)
    (S : Finset α) (v : α → ι → ℕ) (hv : Function.Injective v)
    (hS : ∀ a ∈ S, ∃ t : Option ℚ, ∀ i,
      (v a i : ℚ)^e=(n : ℚ)*projectiveValue f g t i)
    (hfinite : (projectiveIntegralParameters f g n).Finite) :
    S.card ≤ (projectiveIntegralParameters f g n).ncard := by
  classical
  let T := hfinite.toFinset
  have hx (a : S) : ∃ t : Option ℚ, ∀ i,
      (v a.val i : ℚ)^e=(n : ℚ)*projectiveValue f g t i := hS a a.property
  let p (a : S) := Classical.choose (hx a)
  have hp (a : S) (i : ι) :
      (v a.val i : ℚ)^e=(n : ℚ)*projectiveValue f g (p a) i :=
    Classical.choose_spec (hx a) i
  have hmem (a : S) : p a ∈ T := by
    apply hfinite.mem_toFinset.mpr
    intro i
    refine ⟨(v a.val i : ℤ)^e,?_⟩
    rw [← hp a i]
    push_cast
    rfl
  let q : S → T := fun a => ⟨p a,hmem a⟩
  have hq : Function.Injective q := by
    intro a b hab
    have hpab : p a=p b := congrArg Subtype.val hab
    apply Subtype.ext
    apply hv
    funext i
    have hpow : (v a.val i : ℚ)^e=(v b.val i : ℚ)^e := by
      rw [hp a i,hp b i,hpab]
    exact Nat.pow_left_injective he (by exact_mod_cast hpow)
  have hc := Fintype.card_le_of_injective q hq
  simpa only [Fintype.card_coe, T, ← Set.ncard_eq_toFinset_card _ hfinite] using hc

/-- Uniform subpolynomial count on every finite set of nonnegative tuples
lying in one fixed polynomial curve of directions. Targets are unrestricted. -/
theorem fixed_direction_finset_bound {ι α : Type*} [Fintype ι]
    (P A : ι → ℤ[X]) (m C : ℕ) (hm : 0 < m) (hC : 0 < C)
    (hd : 0 < (powerSum P (2*m)).natDegree)
    (hbez : ∑ i, A i * P i^(2*m) = Polynomial.C (C : ℤ))
    (v : α → ι → ℕ) (hv : Function.Injective v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ S : Finset α,
      (∀ a ∈ S, onDirection P (2*m) n (v a)) →
      (S.card : ℝ) ≤ K*(n : ℝ)^ε := by
  have hn := powerSum_no_real_zero P A m C hC hbez
  have hb : (∑ i, A i*powerVector P (2*m) i)+
      (0 : ℤ[X])*powerSum P (2*m)=Polynomial.C (C : ℤ) := by
    simpa only [powerVector,zero_mul,add_zero] using hbez
  obtain ⟨K,hK,hbound⟩ := projective_parameter_set_bound
    (powerSum P (2*m)) 0 (powerVector P (2*m)) A C hd hC hn hb ε hε
  refine ⟨K,hK,?_⟩
  intro n hn S hS
  obtain ⟨hfinite,hcard⟩ := hbound n hn
  have hc := tuple_card_le_parameter_card (powerSum P (2*m))
    (powerVector P (2*m)) (2*m) n (by omega) S v hv hS hfinite
  exact (show (S.card : ℝ) ≤ (projectiveIntegralParameters
    (powerSum P (2*m)) (powerVector P (2*m)) n).ncard by exact_mod_cast hc).trans hcard

/-- The actual representation count restricted to a fixed direction curve. -/
noncomputable def directionCount {k : ℕ} (P : Fin k → ℤ[X]) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin k → Fin (n+1))).filter
    (fun a => (∑ i, (a i : ℕ)^k=n) ∧
      onDirection P k n (fun i => (a i : ℕ)))).card

lemma directionCount_le {k : ℕ} (P : Fin k → ℤ[X]) (n : ℕ) :
    directionCount P n ≤ Erdos322.representationCount k n := by
  classical
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
  exact ha.1

/-- This fixed-curve contribution cannot witness a positive power peak. -/
theorem fixed_direction_no_polynomial_peaks (m : ℕ) (hm : 0 < m)
    (P A : Fin (2*m) → ℤ[X]) (C : ℕ) (hC : 0 < C)
    (hd : 0 < (powerSum P (2*m)).natDegree)
    (hbez : ∑ i, A i * P i^(2*m) = Polynomial.C (C : ℤ)) :
    ¬ ∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ)^c < (directionCount P n : ℝ)}.Infinite := by
  classical
  rw [no_polynomial_peaks_iff_uniform_bound]
  intro ε hε
  obtain ⟨K,hK,hbound⟩ := fixed_direction_finset_bound P A m C hm hC hd hbez
    (id : (Fin (2*m) → ℕ) → (Fin (2*m) → ℕ)) Function.injective_id ε hε
  refine ⟨K,hK,?_⟩
  intro n hn
  let S := ((Finset.univ : Finset (Fin (2*m) → Fin (n+1))).filter
    (fun a => (∑ i, (a i : ℕ)^(2*m)=n) ∧
      onDirection P (2*m) n (fun i => (a i : ℕ))))
  let v : (Fin (2*m) → Fin (n+1)) → (Fin (2*m) → ℕ) := fun a i => a i
  have hv : Function.Injective v := by
    intro a b hab
    funext i
    exact Fin.ext (congrFun hab i)
  have hc : (S.image v).card = directionCount P n := by
    rw [Finset.card_image_of_injective _ hv]
    rfl
  rw [← hc]
  apply hbound n (by omega) (S.image v)
  intro a ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
  exact (Finset.mem_filter.mp hb).2.2

end Erdos322Research.FixedDirectionCurveBound
