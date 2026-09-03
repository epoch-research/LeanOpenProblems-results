import Submission.QuadraticLevelSelectionExplore
import Submission.EveryPrimeBandedRelativeExplore

/-! Mixed-flat finite-field families whose starting level and repair band
are independent of the maximum level. No infinite integer construction is
asserted. -/
namespace Erdos66RangeIndependentFamily
open Erdos66QuadraticLevelSelection Erdos66CharacterTranslateSelection
  Erdos66BandedRepairFamily Erdos66EveryPrimeBandedRelative Erdos66CrossGraph
  Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 2400000

 theorem quadratic_level_flat_family (η : ℝ) (hη : 0<η) (D g J p : ℕ)
    [Fact p.Prime] (hg : 0<g) (hgD : g ≤ D)
    (hDscale : 1536 ≤ (D:ℝ)*η^4) (hgscale : 34 ≤ η*(g:ℝ))
    (hp : max (8*level D J+3) (4*g*level D J)<p) :
    ∃ B : ℕ → Finset (ZMod p × ZMod p), Monotone B ∧
      ∀ i≤J, ∀ j≤J, ∀ z,
        |(pairCount (B i) (B j) z:ℝ)-4*(level D i:ℝ)*(level D j:ℝ)| ≤
          η*(4*(level D i:ℝ)*(level D j:ℝ)) := by
  let H := level D J
  have hp1 : 8*H+3<p := lt_of_le_of_lt (le_max_left _ _) hp
  have hp2 : 4*g*H<p := lt_of_le_of_lt (le_max_right _ _) hp
  have hD : 0<D := lt_of_lt_of_le hg hgD
  have hF : ringChar (ZMod p)≠2 := by rw [ZMod.ringChar_zmod_n]; omega
  have he : 96 ≤ (D:ℝ)*(η/2)^4 := by nlinarith only [hDscale]
  obtain ⟨a,hzero,hopp,hchar⟩ := exists_quadratic_level_parameters (η/2) (by positivity) D J p hD he hp1
  let U := fun i ↦ intervalTranslate p a (2*i)
  have hcard : ∀ i≤H, (U i).card=2*i := by
    intro i hi
    exact intervalTranslate_card p a (by omega)
  have hspace : 2*(2*H+(H/g+1))+1<Fintype.card (ZMod p) := by
    rw [ZMod.card]
    have hh : H/g ≤ H := Nat.div_le_self _ _
    omega
  obtain ⟨C,hCmono,hC⟩ := banded_origin_repair hF H g hg (by simpa using hp2) U
    (fun i j hij ↦ intervalTranslate_mono p a (by omega)) hcard hzero hopp hspace
  refine ⟨fun j ↦ C (level D j),hCmono.comp (level_mono D),?_⟩
  intro i hi j hj z
  let u := level D i
  let v := level D j
  have hu : 0<u := level_pos D i hD
  have hv : 0<v := level_pos D j hD
  have huH : u ≤ H := level_mono D hi
  have hvH : v ≤ H := level_mono D hj
  have hgu : g ≤ u := hgD.trans (level_ge D i)
  have hgv : g ≤ v := hgD.trans (level_ge D j)
  have hu0 : (0:ℝ) ≤ u := by positivity
  have hv0 : (0:ℝ) ≤ v := by positivity
  have hv1 : (1:ℝ) ≤ v := by exact_mod_cast hv
  have hgu' : (g:ℝ) ≤ u := by exact_mod_cast hgu
  have hgpos : (0:ℝ)<g := by exact_mod_cast hg
  have hratio : 17/(g:ℝ) ≤ η/2 := by
    apply (div_le_iff₀ hgpos).mpr
    linarith
  obtain ⟨h0,hother⟩ := hC u hu huH v hv hvH
  by_cases hz : z=0
  · subst z
    change |(pairCount (C u) (C v) 0:ℝ)-4*(u:ℝ)*v| ≤ η*(4*(u:ℝ)*v)
    rw [h0]
    push_cast
    rw [show (1:ℝ)+4*u*v-4*u*v=1 by ring,abs_one]
    have hscaleu : 34 ≤ η*(u:ℝ) := hgscale.trans (mul_le_mul_of_nonneg_left hgu' hη.le)
    have hm := mul_le_mul_of_nonneg_right hscaleu hv0
    nlinarith only [hm,hv1]
  · have hUu : ∀ x∈U u, x≠0 := fun x hx ↦ hzero x (intervalTranslate_mono p a (Nat.mul_le_mul_left 2 huH) hx)
    have hUv : ∀ x∈U v, x≠0 := fun x hx ↦ hzero x (intervalTranslate_mono p a (Nat.mul_le_mul_left 2 hvH) hx)
    have hUuv : ∀ x∈U u, ∀ y∈U v, x+y≠0 := fun x hx y hy ↦
      hopp x (intervalTranslate_mono p a (Nat.mul_le_mul_left 2 huH) hx)
        y (intervalTranslate_mono p a (Nat.mul_le_mul_left 2 hvH) hy)
    have hneU : (U u).Nonempty := Finset.card_pos.mp (by rw [hcard u huH]; omega)
    have hneV : (U v).Nonempty := Finset.card_pos.mp (by rw [hcard v hvH]; omega)
    have hbase := cross_graph_error hF (U u) (U v) hUu hUv hUuv hneU hneV z hz
    rw [hcard u huH,hcard v hvH] at hbase
    have hbase' : |(pairCount (parabolaSet (U u)) (parabolaSet (U v)) z:ℝ)-4*(u:ℝ)*v| ≤
        (∑ w : ZMod p, |(crossCharFiber (U u) (U v) w:ℝ)|)+2*u+2*v := by
      convert (by exact_mod_cast hbase :
        |(pairCount (parabolaSet (U u)) (parabolaSet (U v)) z:ℝ)-(2*u:ℕ)*(2*v:ℕ)| ≤
        (∑ w : ZMod p, |(crossCharFiber (U u) (U v) w:ℝ)|)+(2*u:ℕ)+(2*v:ℕ)) using 1 <;> push_cast <;> ring
    have hchar' : (∑ w : ZMod p, |(crossCharFiber (U u) (U v) w:ℝ)|) ≤ (η/2)*(4*(u:ℝ)*v) := hchar i hi j hj
    have hcost := natural_banded_cost u v g hg hgu hgv
    have hcost' := mul_le_mul_of_nonneg_right hratio (show (0:ℝ) ≤ 4*(u:ℝ)*v by positivity)
    obtain ⟨hlo,hhi⟩ := hother z hz
    have hlo' : (pairCount (parabolaSet (U u)) (parabolaSet (U v)) z:ℝ) ≤ pairCount (C u) (C v) z := by exact_mod_cast hlo
    have hhi' : (pairCount (C u) (C v) z:ℝ) ≤
        (pairCount (parabolaSet (U u)) (parabolaSet (U v)) z:ℝ)+
          8*u*((v/g:ℕ)+1)+8*((u/g:ℕ)+1)*v+8*((u/g:ℕ)+1)*((v/g:ℕ)+1) := by exact_mod_cast hhi
    change |(pairCount (C u) (C v) z:ℝ)-4*(u:ℝ)*v| ≤ η*(4*(u:ℝ)*v)
    rw [abs_le] at hbase' ⊢
    constructor <;> nlinarith only [hbase'.1,hbase'.2,hchar',hcost,hcost',hlo',hhi']

 theorem exists_range_independent_flat_family (η : ℝ) (hη : 0<η) :
    ∃ D g : ℕ, 0<g ∧ g ≤ D ∧ ∀ J p : ℕ, ∀ hp : p.Prime,
      max (8*level D J+3) (4*g*level D J)<p →
      ∃ B : ℕ → Finset (ZMod p × ZMod p), Monotone B ∧
        ∀ i≤J, ∀ j≤J, ∀ z,
          |(pairCount (B i) (B j) z:ℝ)-4*(level D i:ℝ)*(level D j:ℝ)| ≤
            η*(4*(level D i:ℝ)*(level D j:ℝ)) := by
  let g : ℕ := ⌈34/η⌉₊+1
  let D : ℕ := ⌈1536/η^4⌉₊+g
  have hg : 0<g := by dsimp [g]; omega
  have hgD : g ≤ D := by dsimp [D]; omega
  have hgscale : 34 ≤ η*(g:ℝ) := by
    have hh := Nat.le_ceil (34/η)
    have he := (div_le_iff₀ hη).mp hh
    dsimp only [g]
    push_cast
    nlinarith only [he,hη]
  have hDscale : 1536 ≤ (D:ℝ)*η^4 := by
    have hh := Nat.le_ceil (1536/η^4)
    have he := (div_le_iff₀ (pow_pos hη 4)).mp hh
    have hg0 : (0:ℝ) ≤ g := by positivity
    dsimp only [D]
    push_cast
    nlinarith only [he,mul_nonneg hg0 (pow_nonneg hη.le 4)]
  refine ⟨D,g,hg,hgD,?_⟩
  intro J p hp hprime
  letI : Fact p.Prime := ⟨hp⟩
  exact quadratic_level_flat_family η hη D g J p hg hgD hDscale hgscale hprime

end Erdos66RangeIndependentFamily
