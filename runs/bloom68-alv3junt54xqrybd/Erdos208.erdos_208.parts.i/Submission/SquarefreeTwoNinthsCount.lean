import Submission.SquarefreeTwoNinthsLocal
import Submission.SquarefreeTwoNinthsTargets

/-!
# Root-free unconditional two-ninths witness count

For any positive natural parameter `t` with `N ≤ t⁹`, every finite set of
actual large-square witnesses has at most `260 t²` elements. Reverse dyadic
four-point cells below `t³` cost `240 t²`. Roth cells above `t³` cost `20 t²`.
All cell ceilings are absorbed into their geometric targets, so there is no
additive logarithmic loss.
-/
namespace SquarefreeTwoNinths

open scoped BigOperators
open SquarefreeRoth

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

/-- Reverse dyadic four-point counting below the natural pivot `t³`. -/
theorem witnesses_low_card_le (N H t : ℕ) (S : Finset (ℕ × ℕ))
    (hH : 0 < H) (ht : 0 < t) (hHt : H ≤ t^3) (hN : N ≤ t^9)
    (hS : ∀ w ∈ S, Witness N H w ∧ w.1 ≤ t^3) :
    (S.card : ℚ) ≤ 240*(t : ℚ)^2 := by
  classical
  have hex : ∃ L : ℕ, t^3 ≤ 2^L*H := by
    refine ⟨t^3, ?_⟩
    have hpow : t^3 < 2^(t^3) := Nat.lt_two_pow_self
    have hm := Nat.mul_le_mul_left (2^(t^3)) (show 1 ≤ H by omega)
    nlinarith
  let L := Nat.find hex
  have htop : t^3 ≤ 2^L*H := Nat.find_spec hex
  have hactive : ∀ k < L, 2^k*H < t^3 := by
    intro k hk
    have h := Nat.find_min hex hk
    omega
  have hscale : ∀ k < L, 2^(L-1-k)*(2^k*H) ≤ t^3 := by
    intro k hk
    have hlast : 2^(L-1)*H < t^3 := hactive (L-1) (by omega)
    have hid : 2^(L-1-k)*(2^k*H) = 2^(L-1)*H := by
      rw [← Nat.mul_assoc, ← pow_add]
      congr 2
      omega
    rw [hid]
    exact hlast.le
  let B := fun k : ℕ => S.filter (fun w => 2^k*H < w.1 ∧ w.1 ≤ 2*(2^k*H))
  have hcover : S ⊆ (Finset.range L).biUnion B := by
    intro w hw
    have hws := hS w hw
    obtain ⟨k,hk,hkw,hwk⟩ := dyadic_cover H L w.1 hws.1.1 (hws.2.trans htop)
    exact Finset.mem_biUnion.mpr
      ⟨k,Finset.mem_range.mpr hk,Finset.mem_filter.mpr ⟨hw,hkw,hwk⟩⟩
  have hc : S.card ≤ ∑ k ∈ Finset.range L, (B k).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hlocal : ∀ k ∈ Finset.range L,
      ((B k).card : ℚ) ≤ 24*(t : ℚ)^2*(9/10 : ℚ)^(L-1-k) := by
    intro k hk
    have hkL : k < L := Finset.mem_range.mp hk
    have hPH : H ≤ 2^k*H := by nlinarith [Nat.one_le_two_pow (n := k)]
    have hP0 : 0 < 2^k*H := hH.trans_le hPH
    obtain ⟨hmain,hnoise,hceil⟩ := four_dyadic_target N H (2^k*H) t (L-1-k)
      ht hP0 hHt hN (hscale k hkL)
    have hb : (B k).card ≤ 3*⌈4*(t : ℚ)^2*(9/10 : ℚ)^(L-1-k)⌉₊ := by
      apply band_card_le_four N H (2^k*H) _ (B k) hH hPH hmain hnoise
      intro w hw
      obtain ⟨hwS,hwb⟩ := Finset.mem_filter.mp hw
      exact ⟨(hS w hwS).1,hwb⟩
    have hbq : ((B k).card : ℚ) ≤
        3*(⌈4*(t : ℚ)^2*(9/10 : ℚ)^(L-1-k)⌉₊ : ℚ) := by exact_mod_cast hb
    linarith
  calc
    (S.card : ℚ) ≤ ∑ k ∈ Finset.range L, ((B k).card : ℚ) := by exact_mod_cast hc
    _ ≤ ∑ k ∈ Finset.range L, 24*(t : ℚ)^2*(9/10 : ℚ)^(L-1-k) :=
      Finset.sum_le_sum hlocal
    _ = (24*(t : ℚ)^2)*(∑ k ∈ Finset.range L, (9/10 : ℚ)^(L-1-k)) := by
      rw [Finset.mul_sum]
    _ = (24*(t : ℚ)^2)*(∑ k ∈ Finset.range L, (9/10 : ℚ)^k) := by
      rw [Finset.sum_range_reflect]
    _ ≤ (24*(t : ℚ)^2)*10 :=
      mul_le_mul_of_nonneg_left (geometric_sum_le_ten L) (by positivity)
    _ = 240*(t : ℚ)^2 := by ring

/-- The far witnesses are also witnesses for the enlarged interval length
`t³`, so the already-proved Roth count applies directly. -/
theorem witnesses_high_card_le (N H t : ℕ) (S : Finset (ℕ × ℕ))
    (hH : 64 ≤ H) (ht : 0 < t) (hHt : H ≤ t^3) (hN : N ≤ t^9)
    (hS : ∀ w ∈ S, Witness N H w ∧ t^3 < w.1) :
    (S.card : ℚ) ≤ 20*(t : ℚ)^2 := by
  have hU : (0 : ℚ) < (t : ℚ)^2 := by positivity
  have hNU : (N : ℚ) ≤ (t^3 : ℕ)*((t : ℚ)^2)^3 := by
    have hnq : (N : ℚ) ≤ (t : ℚ)^9 := by exact_mod_cast hN
    simpa only [Nat.cast_pow] using
      (show (N : ℚ) ≤ (t : ℚ)^3*((t : ℚ)^2)^3 by convert hnq using 1; ring)
  apply SquarefreeRoth.witnesses_card_le N (t^3) S ((t : ℚ)^2)
    (hH.trans hHt) hU hNU
  intro w hw
  have hws := hS w hw
  refine ⟨hws.2,hws.1.2.1,hws.1.2.2.1,?_⟩
  exact hws.1.2.2.2.trans (Nat.add_le_add_left hHt N)

/-- Unconditional count of any finite actual Witness set, stated with a
natural ninth-power parameter and no roots or sign assumptions. -/
theorem witnesses_card_le (N H t : ℕ) (S : Finset (ℕ × ℕ))
    (hH : 64 ≤ H) (ht : 0 < t) (hN : N ≤ t^9)
    (hS : ∀ w ∈ S, Witness N H w) :
    (S.card : ℚ) ≤ 260*(t : ℚ)^2 := by
  classical
  by_cases hlarge : t^3 ≤ H
  · have hNU' : N ≤ H*(t^2)^3 := by
      calc
        N ≤ t^9 := hN
        _ = t^3*(t^2)^3 := by ring
        _ ≤ H*(t^2)^3 := Nat.mul_le_mul_right _ hlarge
    have hNU : (N : ℚ) ≤ (H : ℚ)*((t : ℚ)^2)^3 := by exact_mod_cast hNU'
    have hcount := SquarefreeRoth.witnesses_card_le N H S ((t : ℚ)^2) hH
      (by positivity) hNU hS
    have hsq : (0 : ℚ) ≤ (t : ℚ)^2 := sq_nonneg _
    linarith
  · have hHt : H ≤ t^3 := by omega
    let A := S.filter (fun w => w.1 ≤ t^3)
    let B := S.filter (fun w => ¬ w.1 ≤ t^3)
    have ha : (A.card : ℚ) ≤ 240*(t : ℚ)^2 := by
      apply witnesses_low_card_le N H t A (by omega) ht hHt hN
      intro w hw
      obtain ⟨hwS,hwb⟩ := Finset.mem_filter.mp hw
      exact ⟨hS w hwS,hwb⟩
    have hb : (B.card : ℚ) ≤ 20*(t : ℚ)^2 := by
      apply witnesses_high_card_le N H t B hH ht hHt hN
      intro w hw
      obtain ⟨hwS,hwb⟩ := Finset.mem_filter.mp hw
      exact ⟨hS w hwS,by omega⟩
    have hcard : A.card+B.card = S.card :=
      Finset.card_filter_add_card_filter_not (s := S) (p := fun w => w.1 ≤ t^3)
    have hcardq : (A.card : ℚ)+(B.card : ℚ) = (S.card : ℚ) := by exact_mod_cast hcard
    linarith

/-- Survivors in a wholly nonsquarefree interval inject into actual natural
witnesses, with their product recovering the survivor. -/
theorem survivors_card_le (N H t : ℕ)
    (hH : 64 ≤ H) (ht : 0 < t) (hN : N ≤ t^9)
    (hbad : ∀ m : ℕ, N < m → m ≤ N+H → ¬ Squarefree m) :
    ((SquarefreeCubic.survivors N H).card : ℚ) ≤ 260*(t : ℚ)^2 := by
  classical
  let S := SquarefreeCubic.survivors N H
  have hw : ∀ m : S, ∃ w : ℕ × ℕ, Witness N H w ∧ (m : ℕ) = w.2*w.1^2 := by
    intro m
    have hm := SquarefreeCubic.mem_survivors.mp m.property
    obtain ⟨p,q,_hp,hpH,hq,heq⟩ :=
      SquarefreeCubic.survivor_large_square m.property (hbad m hm.1 hm.2.1)
    refine ⟨(p,q),⟨hpH,hq,?_,?_⟩,heq⟩
    · simpa only [heq] using hm.1
    · simpa only [heq] using hm.2.1
  choose w hw heq using hw
  have hinj : Function.Injective w := by
    intro a b hab
    apply Subtype.ext
    rw [heq a,heq b,hab]
  let T := (Finset.univ : Finset S).image w
  have hT : ∀ a ∈ T, Witness N H a := by
    intro a ha
    obtain ⟨m,_hm,rfl⟩ := Finset.mem_image.mp ha
    exact hw m
  have hcard : T.card = S.card := by
    dsimp [T]
    rw [Finset.card_image_of_injOn hinj.injOn]
    simp
  have hcount := witnesses_card_le N H t T hH ht hN hT
  simpa only [hcard] using hcount

end SquarefreeTwoNinths
