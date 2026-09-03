import Submission.QuarticDivisorSieve
import Submission.PrimitiveRepresentation

/-! Unbounded primitive quartic exact counts away from any fixed polynomial
zero set. This is not a fixed-positive-power growth theorem. -/
namespace Erdos322Research.OffPolynomialQuarticPeaks
noncomputable section
open Finset UnimodularRootCRT UnimodularBoxCounts QuarticDivisorSieve
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

abbrev Poly := MvPolynomial (Fin 4) ℚ

abbrev evalTuple {B : ℕ} (P : Poly) (x : Fin 4 → Fin B) : ℚ :=
  MvPolynomial.eval (fun i ↦ ((x i : ℕ) : ℚ)) P

def offCount (P : Poly) (n : ℕ) : ℕ :=
  ((univ : Finset (Fin 4 → Fin (n+1))).filter (fun x ↦
    (∑ i, (x i : ℕ)^4=n) ∧ coordGCD x=1 ∧ evalTuple P x ≠ 0)).card

lemma offCount_le_primitive (P : Poly) (n : ℕ) :
    offCount P n ≤ Erdos322.primitiveRepresentationCount 4 n := by
  apply Finset.card_le_card
  intro x hx
  simp only [mem_filter,mem_univ,true_and] at hx
  exact mem_filter.mpr ⟨mem_univ _,hx.1,hx.2.1⟩

abbrev Zeros (P : Poly) (B : ℕ) := {x : Fin 4 → Fin B // evalTuple P x=0}

lemma zero_box_bound (P : Poly) (hP : P ≠ 0) (B : ℕ) (hB : 0<B) :
    Fintype.card (Zeros P B) ≤ P.totalDegree*B^3 := by
  let S : Finset ℚ := (range B).image (fun n : ℕ ↦ (n : ℚ))
  let Z := (Fintype.piFinset (fun _ : Fin 4 ↦ S)).filter (fun x ↦ MvPolynomial.eval x P=0)
  have hS : S.card=B := by
    rw [Finset.card_image_of_injective _ (Nat.cast_injective (R := ℚ)),Finset.card_range]
  let f : Zeros P B → Z := fun x ↦ ⟨fun i ↦ ((x.val i : ℕ) : ℚ),by
    apply mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun i ↦ ?_),x.property⟩
    exact mem_image.mpr ⟨x.val i,mem_range.mpr (x.val i).isLt,rfl⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hh := congrArg (fun z : Z ↦ z.val i) h
    change (((x.val i : ℕ) : ℚ))=(((y.val i : ℕ) : ℚ)) at hh
    exact_mod_cast hh
  have hinj := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe] at hinj
  have hs := MvPolynomial.schwartz_zippel_totalDegree hP S
  change (Z.card : ℚ≥0)/(S.card : ℚ≥0)^4 ≤ (P.totalDegree : ℚ≥0)/S.card at hs
  rw [hS] at hs
  have hs' : (Z.card : ℝ)/(B : ℝ)^4 ≤ (P.totalDegree : ℝ)/B := by
    have hh := (NNRat.cast_le (K := ℝ)).mpr hs
    simpa only [NNRat.cast_div,NNRat.cast_natCast,NNRat.cast_pow] using hh
  have hB0 : (0 : ℝ)<B := by exact_mod_cast hB
  have hm := (div_le_div_iff₀ (pow_pos hB0 4) hB0).mp hs'
  have hbnd : (Z.card : ℝ) ≤ (P.totalDegree : ℝ)*(B : ℝ)^3 := by
    apply (mul_le_mul_iff_right₀ hB0).mp
    nlinarith only [hm]
  have hbnd' : Z.card ≤ P.totalDegree*B^3 := by exact_mod_cast hbnd
  exact hinj.trans hbnd'

abbrev GoodBox (P : Poly) (q B : ℕ) :=
  {x : BoxRoots 4 q B // coordGCD x.val=1 ∧ evalTuple P x.val ≠ 0}

lemma primitive_le_good_add_zeros (P : Poly) (q B : ℕ) :
    primitiveBoxCount 4 q B ≤ Fintype.card (GoodBox P q B)+Fintype.card (Zeros P B) := by
  let A := {x : BoxRoots 4 q B // coordGCD x.val=1}
  let Bad := {x : A // ¬evalTuple P x.val.val ≠ 0}
  let Good := {x : A // evalTuple P x.val.val ≠ 0}
  let e : Good ≃ GoodBox P q B :=
    { toFun := fun x ↦ ⟨x.val.val,x.val.property,x.property⟩
      invFun := fun x ↦ ⟨⟨x.val,x.property.1⟩,x.property.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let f : Bad → Zeros P B := fun x ↦ ⟨x.val.val.val,not_not.mp x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    have hx : x.val.val.val=y.val.val.val := congrArg (fun z : Zeros P B ↦ z.val) h
    exact Subtype.ext (Subtype.ext (Subtype.ext hx))
  have hbad := Fintype.card_le_of_injective f hf
  have hgood := Fintype.card_congr e
  have he := Fintype.card_subtype_compl (fun x : A ↦ evalTuple P x.val.val ≠ 0)
  have hle := Fintype.card_subtype_le (fun x : A ↦ evalTuple P x.val.val ≠ 0)
  change Fintype.card Bad=primitiveBoxCount 4 q B-Fintype.card Good at he
  change Fintype.card Good≤primitiveBoxCount 4 q B at hle
  omega

lemma good_box_large (P : Poly) (hP : P≠0) (M : ℕ) :
    ∃ q T : ℕ, 1<q ∧ 0<T ∧
      (4*q^3*T^4+1)*M < Fintype.card (GoodBox P q (q*T)) := by
  let C : ℕ := 32*(P.totalDegree+M+1)
  obtain ⟨q,hq,hR⟩ := unbounded_quartic_density (C : ℝ)
  letI := hq
  have hq0 : 0<q := Nat.pos_of_ne_zero hq.out
  have hC : 32≤C := by dsimp only [C]; omega
  have hq1 : 1<q := by
    by_contra h
    have hqeq : q=1 := by omega
    subst q
    simp only [Nat.cast_one,one_pow,one_mul,count_one] at hR
    have hC' : (32 : ℝ)≤C := by exact_mod_cast hC
    norm_num at hR
    linarith
  have hRnat : q^3*C < count 4 q := by exact_mod_cast hR
  have hcount : q≤count 4 q := by
    have hp : q≤q^3 := Nat.le_pow (by decide)
    have hm : q^3≤q^3*C := Nat.le_mul_of_pos_right _ (by omega)
    omega
  let T := 16*q
  let B := q*T
  have hT : 0<T := by dsimp only [T]; omega
  have hB : 0<B := Nat.mul_pos hq0 hT
  have hprim : (count 4 q : ℝ)*(T : ℝ)^4/4 ≤ primitiveBoxCount 4 q B := by
    simpa only [B,T,Nat.cast_mul,Nat.cast_ofNat] using primitive_box_lower q hq1 hcount
  have hzero : (Fintype.card (Zeros P B) : ℝ)≤(P.totalDegree : ℝ)*(B : ℝ)^3 := by
    exact_mod_cast zero_box_bound P hP B hB
  have hgood : (primitiveBoxCount 4 q B : ℝ) ≤ Fintype.card (GoodBox P q B)+Fintype.card (Zeros P B) := by
    exact_mod_cast primitive_le_good_add_zeros P q B
  let F : ℝ := (q : ℝ)^3*(T : ℝ)^4
  have hF : 1≤F := by
    dsimp only [F]
    have hq' : (1 : ℝ)≤q := by exact_mod_cast hq0
    have hT' : (1 : ℝ)≤T := by exact_mod_cast hT
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq') (one_le_pow₀ hT')
  have hZT : (P.totalDegree : ℝ)*(B : ℝ)^3 ≤ (P.totalDegree : ℝ)*F := by
    dsimp only [F,B]
    push_cast
    rw [mul_pow]
    gcongr
    · exact_mod_cast hT
    · norm_num
  have hRmul := mul_lt_mul_of_pos_right hR (show (0 : ℝ)<(T : ℝ)^4 by positivity)
  have hRmul' : 32*((P.totalDegree : ℝ)+M+1)*F < (count 4 q : ℝ)*(T : ℝ)^4 := by
    dsimp only [C] at hRmul
    push_cast at hRmul
    dsimp only [F]
    nlinarith only [hRmul]
  have hMF : (M : ℝ)≤(M : ℝ)*F := by
    simpa using mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg M)
  have hDF : (0 : ℝ)≤(P.totalDegree : ℝ)*F := by positivity
  have htarget : (4*F+1)*(M : ℝ)<Fintype.card (GoodBox P q B) := by nlinarith
  refine ⟨q,T,hq1,hT,?_⟩
  dsimp only [F] at htarget
  have hn : (4*(q^3*T^4)+1)*M<Fintype.card (GoodBox P q B) := by exact_mod_cast htarget
  simpa only [B,mul_assoc] using hn

lemma target_sum_bound (q T : ℕ) (x : Fin 4 → Fin (q*T)) :
    ∑ i, (x i : ℕ)^4 ≤ q*(4*q^3*T^4) := by
  calc
    ∑ i, (x i : ℕ)^4 ≤ ∑ _i : Fin 4, (q*T)^4 := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.pow_le_pow_left (x i).isLt.le _
    _ = _ := by simp; ring

lemma peak_of_good_box (P : Poly) (q T M : ℕ) (hq : 0<q)
    (hsize : (4*q^3*T^4+1)*M < Fintype.card (GoodBox P q (q*T))) :
    ∃ n, M < offCount P n := by
  let A := GoodBox P q (q*T)
  have hdiv (x : A) : q ∣ ∑ i, (x.val.val i : ℕ)^4 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_sum,Nat.cast_pow] using x.val.property.1
  let f : A → Fin (4*q^3*T^4+1) := fun x ↦
    ⟨(∑ i, (x.val.val i : ℕ)^4)/q,by
      have hh := Nat.div_le_div_right (c := q) (target_sum_bound q T x.val.val)
      rw [Nat.mul_div_cancel_left _ hq] at hh
      omega⟩
  have hfsize : Fintype.card (Fin (4*q^3*T^4+1))*M < Fintype.card A := by
    simpa only [A,Fintype.card_fin] using hsize
  obtain ⟨y,hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f hfsize
  let U := {x : A // f x=y}
  let V := {b : Fin 4 → Fin (q*(y : ℕ)+1) //
    (∑ i, (b i : ℕ)^4=q*(y : ℕ)) ∧ coordGCD b=1 ∧ evalTuple P b ≠ 0}
  have hsum (x : U) : ∑ i, (x.val.val.val i : ℕ)^4=q*(y : ℕ) := by
    have he : (f x.val : ℕ)=(y : ℕ) := congrArg Fin.val x.property
    change (∑ i, (x.val.val.val i : ℕ)^4)/q=(y : ℕ) at he
    rw [← he,Nat.mul_div_cancel' (hdiv x.val)]
  let g : U → V := fun x ↦ ⟨fun i ↦ ⟨(x.val.val.val i : ℕ),by
    have hi : (x.val.val.val i : ℕ)^4 ≤ ∑ j, (x.val.val.val j : ℕ)^4 :=
      Finset.single_le_sum (f := fun j : Fin 4 ↦ (x.val.val.val j : ℕ)^4)
        (fun _ _ ↦ Nat.zero_le _) (mem_univ i)
    have hpow : (x.val.val.val i : ℕ) ≤ (x.val.val.val i : ℕ)^4 := Nat.le_pow (by decide)
    rw [hsum x] at hi
    omega⟩,hsum x,x.val.property⟩
  have hg : Function.Injective g := by
    intro x z h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrArg (fun b : V ↦ (b.val i : ℕ)) h
  have hcard := Fintype.card_le_of_injective g hg
  have hy' : M < Fintype.card U := by simpa only [U,Fintype.card_subtype] using hy
  refine ⟨q*(y : ℕ),?_⟩
  have hcount : Fintype.card V=offCount P (q*(y : ℕ)) := by
    simp only [V,Fintype.card_subtype,offCount]
  exact (hy'.trans_le hcard).trans_eq hcount

/-- Primitive quartic exact counts remain unbounded after excluding any fixed
nonzero polynomial locus. No parametrized family is assumed. -/
theorem unbounded_off_polynomial (P : Poly) (hP : P≠0) (M : ℕ) :
    ∃ n, M < offCount P n := by
  obtain ⟨q,T,hq,_,h⟩ := good_box_large P hP M
  exact peak_of_good_box P q T M (by omega) h

/-- Every fixed threshold is exceeded at infinitely many targets, even off a
fixed polynomial locus. This does not give a threshold n to a fixed power. -/
theorem infinite_off_polynomial_peaks (P : Poly) (hP : P≠0) (M : ℕ) :
    {n : ℕ | M < offCount P n}.Infinite := by
  intro hf
  let C := hf.toFinset.sup (offCount P)
  obtain ⟨n,hn⟩ := unbounded_off_polynomial P hP (max M C)
  have hm : n ∈ {n : ℕ | M < offCount P n} := lt_of_le_of_lt (le_max_left _ _) hn
  have hC : offCount P n ≤ C := Finset.le_sup (f := offCount P) (hf.mem_toFinset.mpr hm)
  omega

/-- Unrestricted primitive quartic counts are unbounded at infinitely many targets. -/
theorem infinite_primitive_quartic_peaks (M : ℕ) :
    {n : ℕ | M < Erdos322.primitiveRepresentationCount 4 n}.Infinite := by
  apply (infinite_off_polynomial_peaks 1 one_ne_zero M).mono
  intro n hn
  exact hn.trans_le (offCount_le_primitive 1 n)

end
end Erdos322Research.OffPolynomialQuarticPeaks
