import Submission.CompactGapRatioColoring

/-!
Every sufficiently large multiplicative interval of fixed relative width
contains a nontrivial cubic collision. Thus a union of full geometric bands
cannot itself be the set in Erdős 1206. This does not exclude positive-density
subsets of the bands.
-/
namespace Erdos1206.GeometricBandObstruction
open CompactGapRatioColoring

private def a (k : ℕ) : ℕ := k^3+7*k^2+15*k+6
private def b (k : ℕ) : ℕ := k^3+8*k^2+24*k+27
private def c (k : ℕ) : ℕ := k^3+10*k^2+36*k+45
private def d (k : ℕ) : ℕ := k^3+11*k^2+39*k+48

private lemma identity (k : ℕ) : (a k)^3+(d k)^3=(b k)^3+(c k)^3 := by
  dsimp [a,b,c,d]
  ring

private lemma ordered (k : ℕ) : 0<a k ∧ a k<b k ∧ b k<c k ∧ c k<d k := by
  dsimp [a,b,c,d]
  constructor
  · positivity
  constructor
  · omega
  constructor <;> omega

/-- Nontrivial integral cubic collisions can have all four roots in a
multiplicative interval of arbitrarily small fixed relative width. -/
theorem narrow_collision {q : ℝ} (hq : 1<q) :
    ∃ A B C D : ℕ, 0<A ∧ A<B ∧ B<C ∧ C<D ∧
      A^3+D^3=B^3+C^3 ∧ (D:ℝ)<q*A := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max 1 (70/(q-1)))
  have hk1 : (1:ℝ)<k := (le_max_left _ _).trans_lt hk
  have hk0 : (0:ℝ)<k := by linarith
  have hlarge : 70<(k:ℝ)*(q-1) :=
    (div_lt_iff₀ (sub_pos.mpr hq)).mp ((le_max_right _ _).trans_lt hk)
  obtain ⟨ha,hab,hbc,hcd⟩ := ordered k
  refine ⟨a k,b k,c k,d k,ha,hab,hbc,hcd,identity k,?_⟩
  have hks : (k:ℝ)≤(k:ℝ)^2 := by nlinarith
  have haR : (k:ℝ)^3≤a k := by
    simp only [a,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    nlinarith [sq_nonneg (k:ℝ)]
  have hdR : (d k:ℝ)-(a k:ℝ)≤70*(k:ℝ)^2 := by
    simp only [a,d,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    nlinarith [sq_nonneg ((k:ℝ)-1)]
  have hm := mul_lt_mul_of_pos_right hlarge (sq_pos_of_pos hk0)
  have haM := mul_le_mul_of_nonneg_left haR (sub_pos.mpr hq).le
  nlinarith only [hdR,hm,haM]

/-- Every sufficiently remote full interval `[X,q*X)` contains a collision.
The threshold depends on `q`, but not on the interval's location `X`. -/
theorem collision_in_every_relative_interval {q : ℝ} (hq : 1<q) :
    ∃ M : ℝ, 0<M ∧ ∀ X : ℝ, M≤X →
      ∃ A B C D : ℕ, X≤(A:ℝ) ∧ (D:ℝ)<q*X ∧
        0<A ∧ A<B ∧ B<C ∧ C<D ∧ A^3+D^3=B^3+C^3 := by
  obtain ⟨A,B,C,D,hA,hAB,hBC,hCD,he,hqD⟩ := narrow_collision hq
  have hAR : (0:ℝ)<A := by exact_mod_cast hA
  have hDR : (0:ℝ)<D := by exact_mod_cast (hA.trans (hAB.trans (hBC.trans hCD)))
  let η : ℝ := q-(D:ℝ)/A
  have hη : 0<η := sub_pos.mpr ((div_lt_iff₀ hAR).mpr hqD)
  let M : ℝ := max 1 ((D:ℝ)/η+1)
  have hM : 0<M := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨M,hM,fun X hX => ?_⟩
  have hX0 : 0<X := hM.trans_le hX
  let m : ℕ := ⌈X/(A:ℝ)⌉₊
  have hm : 0 < m := Nat.ceil_pos.mpr (div_pos hX0 hAR)
  have hmL : X≤(m:ℝ)*A := (div_le_iff₀ hAR).mp (Nat.le_ceil _)
  have hmU : (m:ℝ)<X/(A:ℝ)+1 := Nat.ceil_lt_add_one (div_pos hX0 hAR).le
  have hXlarge : (D:ℝ)/η<X := by
    have hh := (le_max_right 1 ((D:ℝ)/η+1)).trans hX
    linarith
  have hDη : (D:ℝ)<X*η := (div_lt_iff₀ hη).mp hXlarge
  have hupper : (m:ℝ)*D<q*X := by
    have hh := mul_lt_mul_of_pos_right hmU hDR
    dsimp only [η] at hDη
    have heq : (X/(A:ℝ)+1)*D=X*((D:ℝ)/A)+D := by ring
    rw [heq] at hh
    nlinarith only [hh,hDη]
  refine ⟨m*A,m*B,m*C,m*D,?_,?_,Nat.mul_pos hm hA,
    Nat.mul_lt_mul_of_pos_left hAB hm,Nat.mul_lt_mul_of_pos_left hBC hm,
    Nat.mul_lt_mul_of_pos_left hCD hm,?_⟩
  · exact_mod_cast hmL
  · exact_mod_cast hupper
  · simpa only [mul_pow,←Nat.mul_add] using congrArg (fun n : ℕ => m^3*n) he

/-- The full geometric bands have positive density, but are never themselves
cube-Sidon. No assertion is made about their arbitrary subsets. -/
theorem geometricBand_not_sidon {q r : ℝ} (hq : 1<q) (hr : 1<r) :
    ¬ IsSidon ((fun n : ℕ => n^3) '' geometricBand q r) := by
  obtain ⟨M,hM,hinterval⟩ := collision_in_every_relative_interval hq
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt M hr
  obtain ⟨A,B,C,D,hlo,hhi,hA,hAB,hBC,hCD,he⟩ := hinterval (r^k) hk.le
  have hABR : (A:ℝ)<B := by exact_mod_cast hAB
  have hBCR : (B:ℝ)<C := by exact_mod_cast hBC
  have hCDR : (C:ℝ)<D := by exact_mod_cast hCD
  have hmemA : A∈geometricBand q r := ⟨k,hlo,by linarith⟩
  have hmemB : B∈geometricBand q r := ⟨k,by linarith,by linarith⟩
  have hmemC : C∈geometricBand q r := ⟨k,by linarith,by linarith⟩
  have hmemD : D∈geometricBand q r := ⟨k,by linarith,hhi⟩
  intro hs
  have hh := hs _ ⟨A,hmemA,rfl⟩ _ ⟨B,hmemB,rfl⟩
    _ ⟨D,hmemD,rfl⟩ _ ⟨C,hmemC,rfl⟩ he
  have h₁ : A^3<B^3 := Nat.pow_lt_pow_left hAB (by norm_num)
  have h₂ : A^3<C^3 := Nat.pow_lt_pow_left (hAB.trans hBC) (by norm_num)
  change (A^3=B^3 ∧ D^3=C^3) ∨ (A^3=C^3 ∧ D^3=B^3) at hh
  exact hh.elim (fun h => (ne_of_lt h₁) h.1) (fun h => (ne_of_lt h₂) h.1)

#print axioms narrow_collision
#print axioms collision_in_every_relative_interval
#print axioms geometricBand_not_sidon
end Erdos1206.GeometricBandObstruction
