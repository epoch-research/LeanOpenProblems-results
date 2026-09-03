import Submission.QuarticHuaBox
import Submission.MomentReduction

/-! An unrestricted quartic second-moment bound obtained by finite differencing. -/
namespace Erdos322Research.QuarticHuaMoment

open Erdos322 Erdos322.MomentReduction QuarticHuaBox FiniteCollisionEnergy
open scoped Classical
set_option Elab.async false

private abbrev Rep (n : ℕ) :=
  {a : Fin 4 → Fin (n+1) // ∑ i, (a i : ℕ)^4=n}

private theorem rep_card (n : ℕ) : Fintype.card (Rep n)=representationCount 4 n := by
  simp [Rep,Fintype.card_subtype,representationCount]

private def boxTuple (N : ℕ) (n : Fin (N+1)) (a : Rep n) :
    Fin 4 → Fin (Nat.nthRoot 4 N+1) :=
  fun i => ⟨a.1 i,by
    have hi : (a.1 i : ℕ)^4 ≤ n :=
      (Finset.single_le_sum (f := fun j : Fin 4 => (a.1 j : ℕ)^4)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans_eq a.2
    exact Nat.lt_succ_of_le ((Nat.le_nthRoot_iff (by decide : 4 ≠ 0)).mpr
      (hi.trans (Nat.le_of_lt_succ n.isLt)))⟩

private def boxQuad (N : ℕ) (n : Fin (N+1)) (a : Rep n) : Quad (Nat.nthRoot 4 N+1) :=
  let t := boxTuple N n a
  ((t 0,t 1),(t 2,t 3))

private theorem boxQuad_value (N : ℕ) (n : Fin (N+1)) (a : Rep n) :
    quadValue (boxQuad N n a)=n := by
  have h := a.2
  simp only [Fin.sum_univ_four] at h
  dsimp [quadValue,pairValue,boxQuad,boxTuple]
  omega

private theorem boxQuad_injective (N : ℕ) (n : Fin (N+1)) :
    Function.Injective (boxQuad N n) := by
  intro a b he
  have h0 := congrArg (fun q => (q.1.1 : ℕ)) he
  have h1 := congrArg (fun q => (q.1.2 : ℕ)) he
  have h2 := congrArg (fun q => (q.2.1 : ℕ)) he
  have h3 := congrArg (fun q => (q.2.2 : ℕ)) he
  apply Subtype.ext
  funext i
  apply Fin.ext
  fin_cases i <;> assumption

private abbrev Collision (B : ℕ) :=
  {p : Quad B × Quad B // quadValue p.1=quadValue p.2}

private def collisionMap (N : ℕ) (v : (n : Fin (N+1)) × (Rep n × Rep n)) :
    Collision (Nat.nthRoot 4 N+1) :=
  ⟨(boxQuad N v.1 v.2.1,boxQuad N v.1 v.2.2),by simp only [boxQuad_value]⟩

private theorem collisionMap_injective (N : ℕ) :
    Function.Injective (collisionMap N) := by
  rintro ⟨n,a⟩ ⟨m,b⟩ he
  have h0 := congrArg (fun q => q.1.1) he
  have h1 := congrArg (fun q => q.1.2) he
  change boxQuad N n a.1=boxQuad N m b.1 at h0
  change boxQuad N n a.2=boxQuad N m b.2 at h1
  have hnm : n=m := by
    apply Fin.ext
    have ht := congrArg quadValue h0
    simpa only [boxQuad_value] using ht
  subst m
  have ha : a=b := Prod.ext (boxQuad_injective N n h0) (boxQuad_injective N n h1)
  subst b
  rfl

private theorem collision_card (B : ℕ) : Fintype.card (Collision B)=boxEnergy B := by
  rw [Fintype.card_subtype]
  unfold boxEnergy
  rw [energy_def,Finset.univ_product_univ]

/-- All equal-target representation pairs up to `N` fit in the root box. -/
theorem summatory_square_le_root_box (N : ℕ) :
    ∑ n ∈ Finset.range (N+1), representationCount 4 n ^ 2 ≤
      boxEnergy (Nat.nthRoot 4 N+1) := by
  have hc := Fintype.card_le_of_injective (collisionMap N) (collisionMap_injective N)
  simp only [Fintype.card_sigma,Fintype.card_prod,rep_card,collision_card,
    ← pow_two] at hc
  calc
    _ = ∑ n : Fin (N+1), representationCount 4 n ^ 2 :=
      (Fin.sum_univ_eq_sum_range (fun n => representationCount 4 n ^ 2) (N+1)).symm
    _ ≤ _ := hc

theorem second_moment_le_root_box (N : ℕ) :
    countMoment (representationCount 4) 2 N ≤ (boxEnergy (Nat.nthRoot 4 N+1) : ℝ) := by
  have hsub : ∑ n ∈ Finset.Icc 1 N, representationCount 4 n ^ 2 ≤
      ∑ n ∈ Finset.range (N+1), representationCount 4 n ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hn).2; omega)
    · intros; exact Nat.zero_le _
  have h := hsub.trans (summatory_square_le_root_box N)
  unfold countMoment
  exact_mod_cast h

/-- Hua's differencing estimate for the full quartic representation count. -/
theorem quartic_second_moment_five_fourths (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      countMoment (representationCount 4) 2 N ≤ C*(N : ℝ)^(5/4+ε) := by
  obtain ⟨K,hK,hbox⟩ := box_energy_subpolynomial_loss ε hε
  refine ⟨K*32*33^ε,by positivity,?_⟩
  intro N hN
  let r := Nat.nthRoot 4 N
  have hr : 1 ≤ r := (Nat.le_nthRoot_iff (by decide : 4 ≠ 0)).mpr (by simpa using hN)
  have hr4 : r^4 ≤ N := Nat.pow_nthRoot_le (.inl (by decide : 4 ≠ 0))
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < N := zero_lt_one.trans_le hNr
  have hrr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hroot5 : (r : ℝ)^5 ≤ (N : ℝ)^(5/4 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (r : ℝ)^4)
      (show (r : ℝ)^4 ≤ N by exact_mod_cast hr4) (by norm_num : (0 : ℝ) ≤ 5/4)
    rw [← Real.rpow_natCast_mul hrr] at h
    norm_num at h
    exact h
  have hB5 : ((r+1 : ℕ) : ℝ)^5 ≤ 32*(N : ℝ)^(5/4 : ℝ) := by
    calc
      ((r+1 : ℕ) : ℝ)^5 ≤ (2*(r : ℝ))^5 := by
        gcongr
        exact_mod_cast (show r+1 ≤ 2*r by omega)
      _ = 32*(r : ℝ)^5 := by ring
      _ ≤ 32*(N : ℝ)^(5/4 : ℝ) := by gcongr
  have hB4 : ((r+1 : ℕ) : ℝ)^4 ≤ 16*(N : ℝ) := by
    have hn : (r+1)^4 ≤ 16*N := by
      calc
        (r+1)^4 ≤ (2*r)^4 := Nat.pow_le_pow_left (by omega) 4
        _ = 16*r^4 := by ring
        _ ≤ 16*N := Nat.mul_le_mul_left _ hr4
    exact_mod_cast hn
  have hP : (2*(((r+1 : ℕ) : ℝ))^4+1)^ε ≤ 33^ε*(N : ℝ)^ε := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 33) hNr0.le]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith) hε.le
  calc
    countMoment (representationCount 4) 2 N ≤ (boxEnergy (r+1) : ℝ) :=
      second_moment_le_root_box N
    _ ≤ K*((r+1 : ℕ) : ℝ)^5*(2*(((r+1 : ℕ) : ℝ))^4+1)^ε := hbox (r+1) (by omega)
    _ ≤ K*(32*(N : ℝ)^(5/4 : ℝ))*(33^ε*(N : ℝ)^ε) := by gcongr
    _ = (K*32*33^ε)*(N : ℝ)^(5/4+ε) := by rw [Real.rpow_add hNr0]; ring

/-- Interpolation with the pointwise bound improves every higher moment,
but its exponent still increases with the moment order. -/
theorem quartic_higher_moment_upper (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      countMoment (representationCount 4) (q+2) N ≤
        C*(N : ℝ)^(5/4+(q : ℝ)/2+ε) := by
  let δ : ℝ := ε/(2*((q : ℝ)+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A,hA,hpoint⟩ := quartic_count_upper_half δ hδ
  obtain ⟨K,hK,hsecond⟩ := quartic_second_moment_five_fourths (ε/2) (by linarith)
  refine ⟨A^q*K,by positivity,?_⟩
  intro N hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNr
  have hδq : δ*(q : ℝ) ≤ ε/2 := by
    have hcancel : δ*((q : ℝ)+1)=ε/2 := by
      dsimp [δ]
      field_simp
    nlinarith [hδ]
  have hpointN (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (representationCount 4 n : ℝ) ≤ A*(N : ℝ)^(1/2+δ) := by
    have hb := hpoint n (Finset.mem_Icc.mp hn).1
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg n)
        (by exact_mod_cast (Finset.mem_Icc.mp hn).2) (by positivity)) hA.le)
  have hm : countMoment (representationCount 4) (q+2) N ≤
      (A*(N : ℝ)^(1/2+δ))^q*countMoment (representationCount 4) 2 N := by
    unfold countMoment
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (hpointN n hn) q) (by positivity)
  calc
    countMoment (representationCount 4) (q+2) N ≤
        (A*(N : ℝ)^(1/2+δ))^q*countMoment (representationCount 4) 2 N := hm
    _ ≤ (A*(N : ℝ)^(1/2+δ))^q*(K*(N : ℝ)^(5/4+ε/2)) := by
      gcongr
      exact hsecond N hN
    _ = (A^q*K)*(N : ℝ)^((1/2+δ)*(q : ℝ)+(5/4+ε/2)) := by
      rw [mul_pow,← Real.rpow_mul_natCast hNpos.le,
        Real.rpow_add hNpos ((1/2+δ)*(q : ℝ)) (5/4+ε/2)]
      ring
    _ ≤ (A^q*K)*(N : ℝ)^(5/4+(q : ℝ)/2+ε) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hNr (by nlinarith)

/-- In particular the third quartic moment has a genuinely subquadratic
bound, with any positive loss over the exponent `7/4`. -/
theorem quartic_third_moment_seven_fourths (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      countMoment (representationCount 4) 3 N ≤ C*(N : ℝ)^(7/4+ε) := by
  convert quartic_higher_moment_upper 1 ε hε using 1; norm_num

/-- The third moment now also satisfies the quadratic-moment criterion.
This is still only one order, not the all-order hypothesis in that criterion. -/
theorem quartic_third_moment_quadratic :
    ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      countMoment (representationCount 4) 3 N ≤ C*(N : ℝ)^2 := by
  obtain ⟨C,hC,hbound⟩ := quartic_third_moment_seven_fourths (1/4) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro N hN
  convert hbound N hN using 1; norm_num

end Erdos322Research.QuarticHuaMoment
