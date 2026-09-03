import FormalConjecturesUtil

/-!
# Four-root collisions in a complete common-residue carrier

This counts collisions in the whole carrier, not in an arbitrary selected
subset. It does not settle Erdős 773.
-/
namespace Erdos773.CommonResidueCollisionCount
open Finset
set_option maxHeartbeats 1000000

/-- Strictly ordered collisions, counted once, in a common-residue carrier. -/
def collisions (Q r N : ℕ) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (((Icc 1 (N : ℤ)) ×ˢ (Icc 1 (N : ℤ))) ×ˢ
    ((Icc 1 (N : ℤ)) ×ˢ (Icc 1 (N : ℤ)))).filter fun p =>
    p.1.1 < p.1.2 ∧ p.1.2 < p.2.1 ∧ p.2.1 < p.2.2 ∧
    p.1.1 ^ 2 + p.2.2 ^ 2 = p.1.2 ^ 2 + p.2.1 ^ 2 ∧
    Int.ModEq Q p.1.1 r ∧ Int.ModEq Q p.1.2 r ∧
    Int.ModEq Q p.2.1 r ∧ Int.ModEq Q p.2.2 r

private def u (Q r T i : ℕ) : ℤ := (Q : ℤ) * (2*T+i) + r
private def v (Q r T j : ℕ) : ℤ := (Q : ℤ) * (3*T+j) + r
private def quad (Q r T : ℕ) (p : ℕ × ℕ) : (ℤ × ℤ) × (ℤ × ℤ) :=
  let x := u Q r T p.1
  let y := v Q r T p.2
  let m := 2*(Q : ℤ)+1
  ((m*x-Q*y, m*y-Q*x), (m*x+Q*y, m*y+Q*x))

private lemma uv_bounds (Q r T i j : ℕ) (hQ : 1 ≤ Q) (hr : r ≤ Q)
    (hT : 1 ≤ T) (hi : i < T) (hj : j < T) :
    0 < u Q r T i ∧ u Q r T i < v Q r T j ∧
      v Q r T j < 2*u Q r T i ∧
      u Q r T i ≤ 4*(Q : ℤ)*T ∧ v Q r T j ≤ 5*(Q : ℤ)*T := by
  have hQ' : (1 : ℤ) ≤ Q := by exact_mod_cast hQ
  have hr' : (r : ℤ) ≤ Q := by exact_mod_cast hr
  have hT' : (1 : ℤ) ≤ T := by exact_mod_cast hT
  have hi' : (i : ℤ) < T := by exact_mod_cast hi
  have hj' : (j : ℤ) < T := by exact_mod_cast hj
  have hQT : (Q : ℤ) ≤ (Q : ℤ)*T := by nlinarith
  have hiQ : (Q : ℤ)*(i+1) ≤ (Q : ℤ)*T :=
    mul_le_mul_of_nonneg_left (by omega) (by positivity)
  have hjQ : (Q : ℤ)*(j+1) ≤ (Q : ℤ)*T :=
    mul_le_mul_of_nonneg_left (by omega) (by positivity)
  have hi0 : (0 : ℤ) ≤ (Q : ℤ)*i := by positivity
  have hj0 : (0 : ℤ) ≤ (Q : ℤ)*j := by positivity
  have hr0 : (0 : ℤ) ≤ r := by positivity
  dsimp [u,v]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private lemma geometry (q x y : ℤ) (hq : 1 ≤ q) (hx : 0 < x)
    (hxy : x < y) (hyx : y < 2*x) :
    0 < (2*q+1)*x-q*y ∧
      (2*q+1)*x-q*y < (2*q+1)*y-q*x ∧
      (2*q+1)*y-q*x < (2*q+1)*x+q*y ∧
      (2*q+1)*x+q*y < (2*q+1)*y+q*x := by
  have h1 : 0 < q*(2*x-y) := mul_pos (by omega) (by omega)
  have h2 : 0 < (3*q+1)*(y-x) := mul_pos (by omega) (by omega)
  have h3 : 0 < (q+1)*(2*x-y) := mul_pos (by omega) (by omega)
  have h4 : 0 ≤ (q-1)*x := mul_nonneg (by omega) hx.le
  have h5 : 0 < (q+1)*(y-x) := mul_pos (by omega) (by omega)
  constructor
  · nlinarith only [h1,hx]
  constructor
  · nlinarith only [h2]
  constructor
  · nlinarith only [h3,h4]
  · nlinarith only [h5]

private lemma common_mod (Q r T : ℕ) (p : ℕ × ℕ) :
    Int.ModEq Q (quad Q r T p).1.1 r ∧
      Int.ModEq Q (quad Q r T p).1.2 r ∧
      Int.ModEq Q (quad Q r T p).2.1 r ∧
      Int.ModEq Q (quad Q r T p).2.2 r := by
  dsimp [quad,u,v]
  simp [Int.ModEq, Int.add_emod, Int.sub_emod, Int.mul_emod]
  simp only [Int.emod_emod]
  rw [← Int.mul_emod]
  simp

private lemma quad_mem (Q r T : ℕ) (hQ : 1 ≤ Q) (hr : r ≤ Q) (hT : 1 ≤ T)
    (p : ℕ × ℕ) (hp : p ∈ range T ×ˢ range T) :
    quad Q r T p ∈ collisions Q r (20*Q^2*T) := by
  obtain ⟨hi,hj⟩ := mem_product.mp hp
  obtain ⟨hu,huv,hvu,hulo,hvhi⟩ := uv_bounds Q r T p.1 p.2 hQ hr hT
    (mem_range.mp hi) (mem_range.mp hj)
  have hQ' : (1 : ℤ) ≤ Q := by exact_mod_cast hQ
  obtain ⟨ha,hab,hbc,hcd⟩ := geometry Q (u Q r T p.1) (v Q r T p.2) hQ' hu huv hvu
  have hm : 2*(Q : ℤ)+1 ≤ 3*(Q : ℤ) := by omega
  have hv0 : 0 ≤ v Q r T p.2 := by omega
  have hm0 : 0 ≤ 2*(Q : ℤ)+1 := by omega
  have hbound1 := mul_le_mul_of_nonneg_left hvhi hm0
  have hbound2 := mul_le_mul_of_nonneg_right hm (show (0 : ℤ) ≤ 5*Q*T by positivity)
  have hbound3 := mul_le_mul_of_nonneg_left hulo (show (0 : ℤ) ≤ Q by positivity)
  have htop : (2*(Q : ℤ)+1)*v Q r T p.2+Q*u Q r T p.1 ≤ (20*Q^2*T : ℕ) := by
    push_cast
    nlinarith only [hbound1,hbound2,hbound3,show (0 : ℤ) ≤ (Q : ℤ)^2*T by positivity]
  push_cast at htop
  apply mem_filter.mpr
  refine ⟨?_,hab,hbc,hcd,?_,common_mod Q r T p⟩
  · dsimp [quad]
    simp only [mem_product,mem_Icc]
    omega
  · dsimp [quad]
    ring

private lemma quad_injective (Q r T : ℕ) (hQ : 1 ≤ Q) :
    Function.Injective (quad Q r T) := by
  intro p w h
  have ha := congrArg (fun z : (ℤ × ℤ) × (ℤ × ℤ) => z.1.1) h
  have hc := congrArg (fun z : (ℤ × ℤ) × (ℤ × ℤ) => z.2.1) h
  dsimp [quad] at ha hc
  have hQ' : (1 : ℤ) ≤ Q := by exact_mod_cast hQ
  have hx : u Q r T p.1 = u Q r T w.1 := by nlinarith only [ha,hc,hQ']
  have hy : v Q r T p.2 = v Q r T w.2 := by nlinarith only [ha,hc,hQ']
  have hp : p.1 = w.1 := by
    dsimp [u] at hx
    have : (p.1 : ℤ) = w.1 := by nlinarith only [hx,hQ']
    exact_mod_cast this
  have hw : p.2 = w.2 := by
    dsimp [v] at hy
    have : (p.2 : ℤ) = w.2 := by nlinarith only [hy,hQ']
    exact_mod_cast this
  exact Prod.ext hp hw

/-- A complete residue carrier of height `20 Q² T` has at least `T²`
strictly ordered four-root collisions. This is not a bound for arbitrary
subsets of that carrier. -/
theorem quadratic_count (Q r T : ℕ) (hQ : 1 ≤ Q) (hr : r ≤ Q) (hT : 1 ≤ T) :
    T^2 ≤ (collisions Q r (20*Q^2*T)).card := by
  have h := card_le_card_of_injOn (quad Q r T)
    (fun p hp => quad_mem Q r T hQ hr hT p hp)
    (quad_injective Q r T hQ).injOn
  simpa only [card_product,card_range,pow_two] using h

lemma collisions_mono (Q r : ℕ) {N M : ℕ} (hNM : N ≤ M) :
    collisions Q r N ⊆ collisions Q r M := by
  intro p hp
  obtain ⟨hp,hp'⟩ := mem_filter.mp hp
  refine mem_filter.mpr ⟨?_,hp'⟩
  have hNM' : (N : ℤ) ≤ M := by exact_mod_cast hNM
  simp only [mem_product,mem_Icc] at hp ⊢
  omega

/-- The quadratic lower count holds at every sufficiently large height,
not merely at the selected heights in `quadratic_count`. -/
theorem count_at_height (Q r N : ℕ) (hQ : 1 ≤ Q) (hr : r ≤ Q)
    (hN : 20*Q^2 ≤ N) :
    N^2 ≤ 1600*Q^4*(collisions Q r N).card := by
  let D := 20*Q^2
  let T := N/D
  have hD : 0 < D := by dsimp [D]; positivity
  have hT : 1 ≤ T := by
    apply (Nat.le_div_iff_mul_le hD).mpr
    simpa only [one_mul] using hN
  have hDT : D*T ≤ N := by
    dsimp [T]
    simpa only [mul_comm] using Nat.div_mul_le_self N D
  have hNlt : N < D*(T+1) := by
    have hm := Nat.mod_lt N hD
    have he := Nat.mod_add_div N D
    dsimp [T]
    nlinarith only [hm,he]
  have hDbudget : D ≤ D*T := by nlinarith only [Nat.mul_le_mul_left D hT]
  have hNupper : N ≤ 2*D*T := by nlinarith only [hNlt,hDbudget]
  have hcount : T^2 ≤ (collisions Q r N).card :=
    (quadratic_count Q r T hQ hr hT).trans
      (card_le_card (collisions_mono Q r hDT))
  calc
    N^2 ≤ (2*D*T)^2 := Nat.pow_le_pow_left hNupper 2
    _ = 1600*Q^4*T^2 := by dsimp [D]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ hcount

lemma power_count (Q r N : ℕ) (hQ : 1 ≤ Q) (hr : r ≤ Q)
    (hN : 20*Q^2 ≤ N) (hN0 : 0 < N) (δ : ℝ)
    (hQupper : (Q : ℝ) ≤ (N : ℝ)^δ) (hlarge : 1600 ≤ (N : ℝ)^δ) :
    (N : ℝ)^(2-5*δ) ≤ (collisions Q r N).card := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hQ4 : (Q : ℝ)^4 ≤ (N : ℝ)^(4*δ) := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Q) hQupper 4
    rw [← Real.rpow_mul_natCast hNpos.le] at h
    convert h using 1
    congr 1
    ring
  have hfactor : 1600*(Q : ℝ)^4 ≤ (N : ℝ)^(5*δ) := by
    calc
      _ ≤ (N : ℝ)^δ*(N : ℝ)^(4*δ) :=
        mul_le_mul hlarge hQ4 (by positivity) (Real.rpow_nonneg hNpos.le _)
      _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring
  have hcount : (N : ℝ)^2 ≤ 1600*(Q : ℝ)^4*(collisions Q r N).card := by
    exact_mod_cast count_at_height Q r N hQ hr hN
  apply le_of_mul_le_mul_left (a := (N : ℝ)^(5*δ)) ?_
    (Real.rpow_pos_of_pos hNpos (5*δ))
  calc
    (N : ℝ)^(5*δ)*(N : ℝ)^(2-5*δ) = (N : ℝ)^2 := by
      rw [← Real.rpow_add hNpos]
      norm_num
    _ ≤ _ := hcount
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (by positivity)

/-- Uniformly for small moduli, the full residue carrier still has nearly
quadratically many four-distinct-root collisions. No claim is made about
an arbitrary sparse subset of the carrier. -/
theorem eventual_uniform_count (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ Q r : ℕ,
      1 ≤ Q → r ≤ Q → (Q : ℝ) ≤ (N : ℝ)^(ε/8) →
      (N : ℝ)^(2-ε) ≤ (collisions Q r N).card := by
  have hsmall := ((tendsto_rpow_atTop (by linarith : 0 < ε/8)).comp
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun N : ℕ => (N : ℝ))
      Filter.atTop Filter.atTop)).eventually_ge_atTop 1600
  have hheight := ((tendsto_rpow_atTop (by linarith : 0 < 1-2*(ε/8))).comp
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun N : ℕ => (N : ℝ))
      Filter.atTop Filter.atTop)).eventually_ge_atTop 20
  filter_upwards [hsmall,hheight,Filter.eventually_ge_atTop (1 : ℕ)] with N hsmall hheight hN
  intro Q r hQ hr hQupper
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hQ2 : (Q : ℝ)^2 ≤ (N : ℝ)^(2*(ε/8)) := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Q) hQupper 2
    rw [← Real.rpow_mul_natCast hNpos.le] at h
    convert h using 1
    congr 1
    ring
  have hheight' : 20*(Q : ℝ)^2 ≤ N := by
    calc
      _ ≤ 20*(N : ℝ)^(2*(ε/8)) := mul_le_mul_of_nonneg_left hQ2 (by norm_num)
      _ ≤ (N : ℝ)^(1-2*(ε/8))*(N : ℝ)^(2*(ε/8)) :=
        mul_le_mul_of_nonneg_right hheight (Real.rpow_nonneg hNpos.le _)
      _ = _ := by rw [← Real.rpow_add hNpos]; ring_nf; simp
  have hheightNat : 20*Q^2 ≤ N := by exact_mod_cast hheight'
  exact (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : 2-ε ≤ 2-5*(ε/8))).trans
    (power_count Q r N hQ hr hheightNat (by omega) (ε/8) hQupper hsmall)

end Erdos773.CommonResidueCollisionCount

#print axioms Erdos773.CommonResidueCollisionCount.quadratic_count
#print axioms Erdos773.CommonResidueCollisionCount.count_at_height
#print axioms Erdos773.CommonResidueCollisionCount.eventual_uniform_count
