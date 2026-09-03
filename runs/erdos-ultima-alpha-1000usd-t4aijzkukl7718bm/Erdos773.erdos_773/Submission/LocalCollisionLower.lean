import Submission.LocalCollisionBounds

/-!
Exact local collision families attaining the power scale H^3/L in a
structured family of intervals. This is a lower bound for collision counts,
not an upper bound for the maximum Sidon-subset cardinality.
-/
namespace Erdos773.LocalCollisionLower
open Finset
set_option maxHeartbeats 2000000

private def leftEnd (K T : ℕ) : ℕ := 16*K^2*T
private def width (K T : ℕ) : ℕ := 32*K*T
private def params (K T : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Icc K (2*K-1)) ×ˢ ((Icc 1 T) ×ˢ range T)
private def auxm (K T : ℕ) (p : ℕ × ℕ × ℕ) : ℕ :=
  (leftEnd K T+p.2.1)/p.1+1+p.2.2
private def rootA (K T : ℕ) (p : ℕ × ℕ × ℕ) : ℕ := p.1*auxm K T p-p.2.1
private def gap (p : ℕ × ℕ × ℕ) : ℕ := 2*p.2.1*p.1
private def midgap (K T : ℕ) (p : ℕ × ℕ × ℕ) : ℕ := auxm K T p-gap p
private def quad (K T : ℕ) (p : ℕ × ℕ × ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  let a := rootA K T p
  let z := gap p
  let y := midgap K T p
  let t := p.2.1
  ((a,a+z+2*t),(a+z+2*t+y,a+2*z+2*t+y))

private lemma param_bounds {K T : ℕ} (hK : 1 ≤ K) (_hT : 1 ≤ T)
    {p : ℕ × ℕ × ℕ} (hp : p ∈ params K T) :
    0 < p.1 ∧ 0 < p.2.1 ∧ 0 < gap p ∧ 0 < midgap K T p ∧
      leftEnd K T ≤ rootA K T p ∧
      rootA K T p ≤ leftEnd K T+2*K*T ∧
      gap p ≤ 4*K*T ∧ auxm K T p ≤ 18*K*T ∧
      rootA K T p+p.2.1 = p.1*auxm K T p ∧
      gap p+midgap K T p = auxm K T p := by
  obtain ⟨hk,hp'⟩ := mem_product.mp hp
  obtain ⟨ht,hj⟩ := mem_product.mp hp'
  obtain ⟨hk0,hk1⟩ := mem_Icc.mp hk
  obtain ⟨ht0,ht1⟩ := mem_Icc.mp ht
  have hj := mem_range.mp hj
  have hkpos : 0 < p.1 := by omega
  have hk2 : p.1 ≤ 2*K := by omega
  have hnumlo : p.1*(4*K*T) ≤ leftEnd K T+p.2.1 := by
    have hh := Nat.mul_le_mul_right (4*K*T) hk2
    dsimp [leftEnd]
    nlinarith only [hh,Nat.zero_le (K^2*T),Nat.zero_le p.2.1]
  have hmlo : 4*K*T+1 ≤ auxm K T p := by
    have hh : 4*K*T ≤ (leftEnd K T+p.2.1)/p.1 :=
      (Nat.le_div_iff_mul_le hkpos).mpr (by simpa [mul_comm] using hnumlo)
    dsimp [auxm]
    omega
  have hnumhi : leftEnd K T+p.2.1 ≤ p.1*(16*K*T+T) := by
    have hh := Nat.mul_le_mul_right (16*K*T) hk0
    have hh' := Nat.mul_le_mul_right T (show 1 ≤ p.1 by omega)
    dsimp [leftEnd]
    nlinarith only [hh,hh',ht1]
  have hmhi : auxm K T p ≤ 16*K*T+2*T := by
    have hh := Nat.div_le_div_right (c := p.1) hnumhi
    rw [Nat.mul_div_cancel_left _ hkpos] at hh
    dsimp [auxm]
    omega
  have hKT : T ≤ K*T := by nlinarith only [Nat.mul_le_mul_right T hK]
  have hmhi' : auxm K T p ≤ 18*K*T := by nlinarith only [hmhi,hKT]
  have hzhi : gap p ≤ 4*K*T := by
    have hh := Nat.mul_le_mul ht1 hk2
    dsimp [gap]
    nlinarith only [hh]
  have hz : 0 < gap p := by dsimp [gap]; positivity
  have hy : 0 < midgap K T p := by
    apply Nat.sub_pos_of_lt
    omega
  have hym : gap p+midgap K T p = auxm K T p := by
    dsimp [midgap]
    omega
  have hceil : leftEnd K T+p.2.1 < p.1*((leftEnd K T+p.2.1)/p.1+1) := by
    have hh := Nat.mod_lt (leftEnd K T+p.2.1) hkpos
    have he := Nat.mod_add_div (leftEnd K T+p.2.1) p.1
    nlinarith only [hh,he]
  have hmullo : leftEnd K T+p.2.1 < p.1*auxm K T p := by
    dsimp [auxm]
    nlinarith only [hceil,Nat.zero_le (p.1*p.2.2)]
  have haeq : rootA K T p+p.2.1 = p.1*auxm K T p := by
    dsimp [rootA]
    omega
  have halo : leftEnd K T ≤ rootA K T p := by omega
  have hahi : rootA K T p ≤ leftEnd K T+2*K*T := by
    have hh := Nat.div_mul_le_self (leftEnd K T+p.2.1) p.1
    have hj' : 1+p.2.2 ≤ T := by omega
    have hmul := Nat.mul_le_mul hk2 hj'
    dsimp [auxm] at haeq
    nlinarith only [hh,hmul,haeq]
  exact ⟨hkpos,ht0,hz,hy,halo,hahi,hzhi,hmhi',haeq,hym⟩

private lemma quad_mem {K T : ℕ} (hK : 1 ≤ K) (hT : 1 ≤ T)
    {p : ℕ × ℕ × ℕ} (hp : p ∈ params K T) :
    quad K T p ∈ LocalCollisionBounds.collisions (leftEnd K T) (width K T) := by
  obtain ⟨hk,ht,hz,hy,halo,hahi,hzhi,hmhi,haeq,hym⟩ := param_bounds hK hT hp
  have htT : p.2.1 ≤ T := (mem_Icc.mp (mem_product.mp (mem_product.mp hp).2).1).2
  have hKT : T ≤ K*T := by nlinarith only [Nat.mul_le_mul_right T hK]
  have hprod : 2*p.2.1*(rootA K T p+p.2.1) =
      gap p*(gap p+midgap K T p) := by
    rw [haeq,hym]
    dsimp [gap]
    ring
  have hd : rootA K T p+2*gap p+2*p.2.1+midgap K T p ≤ leftEnd K T+width K T := by
    dsimp [width]
    nlinarith only [hahi,hzhi,hmhi,hym,htT,hKT]
  apply mem_filter.mpr
  dsimp [quad]
  refine ⟨?_,by omega,by omega,by omega,?_⟩
  · simp only [mem_product,mem_Icc]
    omega
  · nlinarith only [hprod]

private lemma encode_quad (K T : ℕ) (p : ℕ × ℕ × ℕ) :
    LocalCollisionBounds.encode (quad K T p) = ((rootA K T p,p.2.1),gap p) := by
  dsimp [LocalCollisionBounds.encode,quad]
  congr 2 <;> omega

private lemma quad_injective (K T : ℕ) (hK : 1 ≤ K) (hT : 1 ≤ T) :
    Set.InjOn (quad K T) (params K T : Set (ℕ × ℕ × ℕ)) := by
  intro p hp w hw he
  have henc := congrArg LocalCollisionBounds.encode he
  rw [encode_quad,encode_quad] at henc
  have ha : rootA K T p = rootA K T w := congrArg (fun v => v.1.1) henc
  have ht : p.2.1 = w.2.1 := congrArg (fun v => v.1.2) henc
  have hz : gap p = gap w := congrArg Prod.snd henc
  obtain ⟨hkpos,htpos,_,_,_,_,_,_,hap,_⟩ := param_bounds hK hT hp
  obtain ⟨_,_,_,_,_,_,_,_,haw,_⟩ := param_bounds hK hT hw
  have hk : p.1 = w.1 := by
    dsimp [gap] at hz
    rw [← ht] at hz
    exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2*p.2.1) hz
  have hm : auxm K T p = auxm K T w := by
    apply Nat.eq_of_mul_eq_mul_left hkpos
    rw [← hk,← ht,← ha] at haw
    omega
  have hj : p.2.2 = w.2.2 := by
    dsimp [auxm] at hm
    rw [← hk,← ht] at hm
    omega
  exact Prod.ext hk (Prod.ext ht hj)

/-- A two-parameter family with at least K*T² distinct four-root collisions
inside [16K²T,16K²T+32KT]. This attains the power scale H³/L up to a fixed
constant and shows that the uniform local counting exponent cannot simply
be decreased. It is not a Sidon-subset upper bound. -/
theorem local_count_lower (K T : ℕ) (hK : 1 ≤ K) (hT : 1 ≤ T) :
    K*T^2 ≤ (LocalCollisionBounds.collisions (16*K^2*T) (32*K*T)).card := by
  have hc : (params K T).card = K*T^2 := by
    simp only [params,card_product,Nat.card_Icc,card_range,Nat.add_sub_cancel]
    have he : 2*K-1+1-K = K := by omega
    rw [he]
    ring
  rw [← hc]
  exact card_le_card_of_injOn (quad K T) (fun _ hp => quad_mem hK hT hp)
    (quad_injective K T hK hT)

/-- The constructed family's lower bound in the natural H³/L scale. -/
theorem scaled_count_lower (K T : ℕ) (hK : 1 ≤ K) (hT : 1 ≤ T) :
    (32*K*T)^3 ≤ 2048*(16*K^2*T)*
      (LocalCollisionBounds.collisions (16*K^2*T) (32*K*T)).card := by
  calc
    _ = 2048*(16*K^2*T)*(K*T^2) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (local_count_lower K T hK hT)

/-- Monotonicity of the strictly ordered collision count under interval inclusion. -/
theorem collisions_mono {L H L' H' : ℕ} (hlo : L' ≤ L) (hhi : L+H ≤ L'+H') :
    LocalCollisionBounds.collisions L H ⊆ LocalCollisionBounds.collisions L' H' := by
  have hI : Icc L (L+H) ⊆ Icc L' (L'+H') := Icc_subset_Icc hlo hhi
  exact filter_subset_filter _ (product_subset_product
    (product_subset_product hI hI) (product_subset_product hI hI))

/-- A quadratic lower bound for the full interval's nontrivial four-root
collision count. This is not a Sidon-subset cardinality bound. -/
theorem global_count_lower (N : ℕ) (hN : 96 ≤ N) :
    N^2 ≤ 9216*(LocalCollisionBounds.collisions 1 (N-1)).card := by
  let T := N/48
  have hT : 1 ≤ T := (Nat.le_div_iff_mul_le (by decide : 0 < 48)).mpr (by omega)
  have hlow := local_count_lower 1 T (by decide) hT
  norm_num at hlow
  have hsub : LocalCollisionBounds.collisions (16*T) (32*T) ⊆
      LocalCollisionBounds.collisions 1 (N-1) := by
    apply collisions_mono (by omega)
    have hh := Nat.div_mul_le_self N 48
    dsimp [T]
    omega
  have hcount := hlow.trans (card_le_card hsub)
  have hNT : N ≤ 96*T := by
    have hm := Nat.mod_lt N (by decide : 0 < 48)
    have he := Nat.mod_add_div N 48
    change N ≤ 96*(N/48)
    omega
  have hh := Nat.pow_le_pow_left hNT 2
  nlinarith only [hh,hcount]

/-- The displayed full-interval Bernoulli alteration expression cannot
exceed a constant times N^(2/3), even if its probability is optimized.
This bounds only that expression, NOT the maximum Sidon-subset cardinality;
it leaves selective low-collision constructions completely open. -/
theorem alteration_expression_upper (N : ℕ) (hN : 96 ≤ N)
    (p : ℝ) (hp : 0 ≤ p) :
    (p*N-p^4*(LocalCollisionBounds.collisions 1 (N-1)).card)/4 ≤
      8*(N : ℝ)^(2/3 : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let E : ℝ := (LocalCollisionBounds.collisions 1 (N-1)).card
  have hE : (N : ℝ)^2 ≤ 9216*E := by
    dsimp [E]
    exact_mod_cast global_count_lower N hN
  let R : ℝ := (N : ℝ)^(1/3 : ℝ)
  let X : ℝ := (N : ℝ)^(2/3 : ℝ)
  have hR : 0 < R := by dsimp [R]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hR3 : R^3 = (N : ℝ) := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast hNp.le]
    norm_num
  have hRX : R*X = (N : ℝ) := by
    dsimp [R,X]
    rw [← Real.rpow_add hNp]
    norm_num
  change (p*N-p^4*E)/4 ≤ 8*X
  by_cases hsmall : p*R ≤ 32
  · have hh := mul_le_mul_of_nonneg_right hsmall hX
    have hpN : p*(N : ℝ) ≤ 32*X := by simpa only [mul_assoc,hRX] using hh
    have hcost : 0 ≤ p^4*E := by dsimp [E]; positivity
    linarith
  · have hlarge : (32 : ℝ) < p*R := lt_of_not_ge hsmall
    have hc := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 32) hlarge.le 3
    rw [mul_pow,hR3] at hc
    norm_num at hc
    have hpn : (9216 : ℝ) ≤ p^3*(N : ℝ) := by linarith
    have hNE : (N : ℝ) ≤ p^3*E := by
      have hbig : 9216*(N : ℝ) ≤ 9216*(p^3*E) := by
        calc
          9216*(N : ℝ) ≤ p^3*(N : ℝ)*(N : ℝ) := mul_le_mul_of_nonneg_right hpn hNp.le
          _ = p^3*(N : ℝ)^2 := by ring
          _ ≤ p^3*(9216*E) := mul_le_mul_of_nonneg_left hE (pow_nonneg hp _)
          _ = _ := by ring
      linarith
    have hh := mul_le_mul_of_nonneg_left hNE hp
    nlinarith only [hh,hX]

#print axioms local_count_lower
#print axioms scaled_count_lower
#print axioms collisions_mono
#print axioms global_count_lower
#print axioms alteration_expression_upper
end Erdos773.LocalCollisionLower
