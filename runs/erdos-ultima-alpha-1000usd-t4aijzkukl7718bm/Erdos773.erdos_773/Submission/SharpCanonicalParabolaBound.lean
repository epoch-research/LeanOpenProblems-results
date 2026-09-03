import Submission.AffineDigitLiftBound

/-!
A sharp height ceiling for the slope-one, zero-intercept square-digit lift.
This is a restriction on that construction, not on arbitrary square-Sidon sets.
-/
namespace Erdos773.SharpCanonicalParabolaBound
open Finset FloorParabolaLineBound AffineDigitLiftBound
set_option maxHeartbeats 2000000
noncomputable section

lemma digit_lt_root {p b : ℕ} (hb : 0<b) (hbp : b<p) : digit p b<b := by
  apply (Nat.div_lt_iff_lt_mul (by omega : 0<p)).mpr
  nlinarith

/-- At quotient t, the canonical slope-one digit equation has at most 2t-1
    nonzero labels. At t=0 it has none. -/
lemma label_card {p t : ℕ} {B : Finset ℕ} (hB : ∀ b ∈ B, 0<b ∧ b<p)
    (hline : ∀ b ∈ B, digit p b+2*b*t ≡ b [MOD p]) : B.card≤2*t-1 := by
  by_cases ht : t=0
  · subst t
    have he : B=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro b hb
      have hh := hline b hb
      simp only [mul_zero,add_zero] at hh
      have hd := digit_lt_root (hB b hb).1 (hB b hb).2
      have he := hh.eq_of_lt_of_lt (hd.trans (hB b hb).2) (hB b hb).2
      omega
    simp [he]
  have ht : 1≤t := by omega
  let f := fun b => digit p b+(2*t-1)*b
  have hdiv {b : ℕ} (hb : b ∈ B) : p ∣ f b := by
    have hh := hline b hb
    have hf : f b+b=digit p b+2*b*t := by dsimp [f]; nlinarith [Nat.sub_add_cancel (by omega : 1≤2*t)]
    have he : f b+b ≡ 0+b [MOD p] := by simpa only [hf,zero_add] using hh
    exact Nat.dvd_of_mod_eq_zero (Nat.ModEq.add_right_cancel' b he)
  have hfpos {b : ℕ} (hb : b ∈ B) : 0<f b := by
    have hb0 := (hB b hb).1
    dsimp [f]
    nlinarith [Nat.sub_add_cancel (by omega : 1≤2*t)]
  have hfupper {b : ℕ} (hb : b ∈ B) : f b<2*t*p := by
    have hd := digit_lt_root (hB b hb).1 (hB b hb).2
    have hb' := (hB b hb).2
    dsimp [f]
    nlinarith [Nat.sub_add_cancel (by omega : 1≤2*t)]
  have hinj : Set.InjOn (fun b => f b/p) B := by
    intro b hb c hc he
    change f b/p=f c/p at he
    have hb' := Nat.div_mul_cancel (hdiv hb)
    have hc' := Nat.div_mul_cancel (hdiv hc)
    have hef : f b=f c := by rw [← hb',← hc',he]
    have hstrict : StrictMono f := by
      intro x y hxy
      have hd := digit_mono p hxy.le
      dsimp [f]
      nlinarith [Nat.sub_add_cancel (by omega : 1≤2*t)]
    exact hstrict.injective hef
  have himage : B.image (fun b => f b/p) ⊆ Icc 1 (2*t-1) := by
    intro k hk
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hk
    have hp : 0<p := by have := hB b hb; omega
    have hmul := Nat.div_mul_cancel (hdiv hb)
    have hpos := hfpos hb
    have hupper := hfupper hb
    apply mem_Icc.mpr
    constructor
    · apply Nat.one_le_iff_ne_zero.mpr
      intro hz
      rw [hz,zero_mul] at hmul
      omega
    · have hh : f b/p<2*t := (Nat.div_lt_iff_lt_mul hp).mpr hupper
      omega
  have hc := card_le_card himage
  rw [card_image_of_injOn hinj,Nat.card_Icc,Nat.add_sub_cancel] at hc
  exact hc

lemma layer_card_bound {p : ℕ} (hp : 0<p) {A : Finset ℕ}
    (hA : AffineDigits p 1 0 A) (hunit : ∀ n ∈ A, 0<n%p) (t : ℕ) :
    (A.filter (fun n => n/p=t)).card≤2*t-1 := by
  rw [← AffineDigitLiftBound.layer_card]
  apply label_card
  · intro b hb
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hb
    exact ⟨hunit n (mem_filter.mp hn).1,Nat.mod_lt _ hp⟩
  · intro b hb
    have hh := (layer_onLine hp hA t b hb).2
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    push_cast
    linear_combination hh

lemma odd_sum (T : ℕ) : (∑ t ∈ range (T+1), (2*t-1))=T^2 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ,ih]
    have ht : 1≤2*(T+1) := by omega
    have hh := Nat.sub_add_cancel ht
    nlinarith

/-- There are at most T² nonzero-residue roots through quotient T. -/
theorem quotient_square_bound {p N : ℕ} (hp : 0<p) {A : Finset ℕ}
    (hA : AffineDigits p 1 0 A) (hunit : ∀ n ∈ A, 0<n%p)
    (hheight : ∀ n ∈ A, n≤N) : A.card≤(N/p)^2 := by
  rw [card_partition hheight]
  calc
    _ ≤ ∑ t ∈ range (N/p+1), (2*t-1) :=
      sum_le_sum (fun t _ => layer_card_bound hp hA hunit t)
    _ = _ := odd_sum _

/-- Sharp cubic height bound, without the earlier p<=N assumption. -/
theorem cubic_bound {p N : ℕ} (hp : 0<p) {A : Finset ℕ}
    (hA : AffineDigits p 1 0 A) (hunit : ∀ n ∈ A, 0<n%p)
    (hheight : ∀ n ∈ A, n≤N) (hinj : Set.InjOn (fun n => n%p) A) :
    A.card^3≤N^2 := by
  have hq := quotient_square_bound hp hA hunit hheight
  have hr := residue_card_bound hp hinj
  have hh := Nat.div_mul_le_self N p
  calc
    A.card^3 = A.card*A.card^2 := by ring
    _ ≤ (N/p)^2*p^2 := Nat.mul_le_mul hq (Nat.pow_le_pow_left hr 2)
    _ = (N/p*p)^2 := by ring
    _ ≤ N^2 := Nat.pow_le_pow_left hh 2

/-- Any short-root subset of the existing canonical parabola lift obeys
    |B|³<=N², uniformly in its odd prime modulus. -/
theorem canonical_cubic_bound {p N : ℕ} [Fact p.Prime] (h2 : (2:ZMod p)≠0)
    (B : Finset ℕ) (hB : ∀ b ∈ B, 0<b ∧ b<p)
    (hheight : ∀ b ∈ B, ParabolaSquareLift.root p b≤N) : B.card^3≤N^2 := by
  have hh := cubic_bound (Fact.out : p.Prime).pos
    (parabola_affine_digits h2 B hB)
    (show ∀ n ∈ B.image (ParabolaSquareLift.root p), 0<n%p from by
      intro n hn
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hn
      rw [ParabolaSquareLift.root_mod p b (hB b hb).2]
      exact (hB b hb).1)
    (show ∀ n ∈ B.image (ParabolaSquareLift.root p), n≤N from by
      intro n hn
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hn
      exact hheight b hb)
    (parabola_residue_injective B (fun b hb => (hB b hb).2))
  rwa [ParabolaSquareLift.lift_card p B (fun b hb => (hB b hb).2)] at hh

#print axioms label_card
#print axioms quotient_square_bound
#print axioms cubic_bound
#print axioms canonical_cubic_bound
end
end Erdos773.SharpCanonicalParabolaBound
