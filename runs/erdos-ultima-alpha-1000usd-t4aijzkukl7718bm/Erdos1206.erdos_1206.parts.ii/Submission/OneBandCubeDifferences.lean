import Submission.LocalCubeDifferences

/-! Infinitely many rational pairs with common cubic difference in one
arbitrarily narrow multiplicative band. No integral height estimate is claimed. -/

namespace Erdos1206.OneBandCubeDifferences
open scoped Classical
set_option maxHeartbeats 1000000

/-- A fixed positive cubic-difference pair is approached by infinitely many
positive pairs from below. -/
lemma infinite_below_pair {a b ε : ℚ} (hb : 0<b) (hab : b<a) (hε : 0<ε) :
    {y : ℚ | b-ε<y ∧ y<b ∧ 0<y ∧
      ∃ x : ℚ, 0<x ∧ x<a ∧ x^3-y^3=a^3-b^3}.Infinite := by
  let S : Set ℚ := {y | b-ε<y ∧ y<b ∧ 0<y ∧
    ∃ x : ℚ, 0<x ∧ x<a ∧ x^3-y^3=a^3-b^3}
  have hnear {δ : ℚ} (hδ : 0<δ) (hδε : δ≤ε) : ∃ y∈S, b-δ<y := by
    obtain ⟨x,y,hy,hclose,hyb,hx,he⟩ := LocalCubeDifferences.near_pair_below hb hab hδ
    have hxa : x<a := (Odd.pow_lt_pow (by decide : Odd 3)).mp (by
      have hpow := (Odd.strictMono_pow (by decide : Odd 3)) hyb
      linarith)
    exact ⟨y,by exact ⟨by linarith,hyb,hy,x,hx,hxa,he⟩,hclose⟩
  have hS : S.Nonempty := by
    obtain ⟨y,hy,_⟩ := hnear hε le_rfl
    exact ⟨y,hy⟩
  change S.Infinite
  intro hfin
  obtain ⟨y,hy,hmax⟩ := hfin.toFinset.exists_max_image id (by simpa using hS)
  have hyS : y∈S := by simpa using hy
  have hδ : 0 < min ε (b-y) := lt_min hε (sub_pos.mpr hyS.2.1)
  obtain ⟨z,hz,hclose⟩ := hnear hδ (min_le_left _ _)
  have hmax' : z≤y := hmax z (by simpa using hz)
  have hmin : min ε (b-y)≤b-y := min_le_right _ _
  linarith

/-- Both roots of infinitely many pairs lie in the same arbitrarily narrow
multiplicative band. In particular the cross-band separation can approach one. -/
theorem infinite_one_band (K : ℕ) :
    ∃ L U : ℚ, 0<L ∧ L<U ∧ (K : ℚ)*U≤(K+1)*L ∧
      {y : ℚ | L<y ∧ y<U ∧ ∃ x : ℚ, L<x ∧ x<U ∧ x^3-y^3=7}.Infinite := by
  obtain ⟨a,b,hbig,hb,ha,he⟩ :=
    UnboundedCubeDifferences.unbounded_rational_difference
      (a := 2) (b := 1) (by norm_num) (by norm_num) (4*((K : ℚ)+1))
  norm_num only [Nat.reducePow,Int.reducePow,reduceCtorEq] at he
  have he7 : a^3-b^3=7 := by norm_num at he ⊢; exact he
  have hab : b<a := (Odd.pow_lt_pow (by decide : Odd 3)).mp (by linarith)
  have ha2 : a≤b+2 := (Odd.pow_le_pow (by decide : Odd 3)).mp (by
    nlinarith [sq_nonneg b])
  let L := b-1
  let U := a+1
  have hK : (0 : ℚ)≤K := Nat.cast_nonneg _
  have hL : 0<L := by dsimp [L]; nlinarith
  have hLU : L<U := by dsimp [L,U]; linarith
  have hband : (K : ℚ)*U≤(K+1)*L := by
    have hmul := mul_le_mul_of_nonneg_left ha2 hK
    dsimp [L,U]
    nlinarith
  refine ⟨L,U,hL,hLU,hband,?_⟩
  have hi := infinite_below_pair hb hab (by norm_num : (0 : ℚ)<1)
  apply hi.mono
  rintro y ⟨hyL,hyb,hy,x,hx,hxa,hexy⟩
  have hxy : y<x := (Odd.pow_lt_pow (by decide : Odd 3)).mp (by linarith)
  refine ⟨hyL,by dsimp [U]; linarith,x,by dsimp [L]; linarith,?_,?_⟩
  · dsimp [U]; linarith
  · linarith

#print axioms infinite_below_pair
#print axioms infinite_one_band
end Erdos1206.OneBandCubeDifferences
