import Submission.ParityTriangleCount
import Submission.TranslatedIntersectionSelection

/-!
A modular affine line contains few points of the digit graph
b -> floor(b^2/p), 0<=b<p. This restricts a modular lifting construction;
it is not an upper bound for arbitrary square-Sidon sets.
-/
namespace Erdos773.FloorParabolaLineBound
open Finset TranslatedIntersectionSelection
set_option maxHeartbeats 2000000
noncomputable section

def digit (p b : ℕ) := b^2/p

def OnLine (p : ℕ) (a c : ZMod p) (B : Finset ℕ) : Prop :=
  ∀ b ∈ B, b<p ∧ (digit p b : ZMod p)=a*b+c

lemma digit_lt {p b : ℕ} (hp : 0<p) (hb : b<p) : digit p b<p := by
  apply (Nat.div_lt_iff_lt_mul hp).mpr
  nlinarith

lemma digit_mono (p : ℕ) : Monotone (digit p) := by
  intro x y h
  exact Nat.div_le_div_right (Nat.pow_le_pow_left h 2)

lemma gap_difference {p d x y : ℕ} (hp : 0<p) {a c : ZMod p} {B : Finset ℕ}
    (hB : OnLine p a c B) (hx : x ∈ overlap B d) (hy : y ∈ overlap B d) :
    digit p (x+d)-digit p x=digit p (y+d)-digit p y := by
  have hx₀ := (mem_filter.mp hx).1
  have hx₁ := (mem_filter.mp hx).2
  have hy₀ := (mem_filter.mp hy).1
  have hy₁ := (mem_filter.mp hy).2
  have hdx := digit_mono p (Nat.le_add_right x d)
  have hdy := digit_mono p (Nat.le_add_right y d)
  have he (z : ℕ) (hz₀ : z ∈ B) (hz₁ : z+d ∈ B) :
      ((digit p (z+d)-digit p z : ℕ) : ZMod p)=a*d := by
    rw [Nat.cast_sub (digit_mono p (Nat.le_add_right z d)),(hB _ hz₁).2,(hB _ hz₀).2]
    push_cast
    ring
  have hcast : ((digit p (x+d)-digit p x : ℕ) : ZMod p)=
      ((digit p (y+d)-digit p y : ℕ) : ZMod p) := by rw [he x hx₀ hx₁,he y hy₀ hy₁]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hcast).eq_of_lt_of_lt
    ((Nat.sub_le _ _).trans_lt (digit_lt hp (hB _ hx₁).1))
    ((Nat.sub_le _ _).trans_lt (digit_lt hp (hB _ hy₁).1))

lemma gap_spacing {p d x y : ℕ} (hp : 0<p) {a c : ZMod p} {B : Finset ℕ}
    (hB : OnLine p a c B) (hx : x ∈ overlap B d) (hy : y ∈ overlap B d) :
    d*y<d*x+p := by
  have he := gap_difference hp hB hx hy
  have hdx := digit_mono p (Nat.le_add_right x d)
  have hdy := digit_mono p (Nat.le_add_right y d)
  have he' : digit p (x+d)+digit p y=digit p (y+d)+digit p x := by omega
  have hm := congrArg (fun t => p*t) he'
  have hlo (t : ℕ) : p*digit p t ≤ t^2 := by
    simpa only [digit,Nat.mul_comm] using Nat.div_mul_le_self (t^2) p
  have hhi (t : ℕ) : t^2<p*digit p t+p := by
    have h := Nat.mod_lt (t^2) hp
    have h' := Nat.mod_add_div (t^2) p
    dsimp only [digit]
    omega
  dsimp only at hm
  nlinarith only [hm,hlo (x+d),hlo y,hhi (y+d),hhi x]

/-- Positive-gap multiplicity on a modular affine line. -/
theorem overlap_card {p d : ℕ} (hp : 0<p) (hd : 0<d) {a c : ZMod p} {B : Finset ℕ}
    (hB : OnLine p a c B) : ((overlap B d).card : ℝ) ≤ (p:ℝ)/d+1 := by
  classical
  rcases (overlap B d).eq_empty_or_nonempty with he | hS
  · rw [he,card_empty,Nat.cast_zero]
    positivity
  · let l := (overlap B d).min' hS
    have hl : l ∈ overlap B d := min'_mem _ hS
    have hdR : (0:ℝ)<d := by exact_mod_cast hd
    have hh := ParityTriangleCount.interval_card_bound (overlap B d) (l:ℝ) (l+(p:ℝ)/d)
      (le_add_of_nonneg_right (by positivity)) (fun x hx => ?_)
    · simpa only [add_sub_cancel_left] using hh
    · constructor
      · exact_mod_cast min'_le _ _ hx
      · have hs : (d:ℝ)*x<d*l+p := by exact_mod_cast gap_spacing hp hB hl hx
        have ht : (x:ℝ)-l ≤ (p:ℝ)/d := (le_div_iff₀ hdR).mpr (by nlinarith only [hs])
        linarith only [ht]

lemma pair_sum_bound (p : ℕ) (B : Finset ℕ) (hB : B ⊆ range p) :
    B.card^2 ≤ B.card+2*∑ d ∈ Icc 1 p, (overlap B d).card := by
  classical
  let P := (B ×ˢ B).filter (fun t => t.1<t.2)
  have hcover : B.offDiag ⊆ P ∪ P.image Prod.swap := by
    intro t ht
    obtain ⟨ha,hb,hne⟩ := mem_offDiag.mp ht
    rcases lt_or_gt_of_ne hne with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,h⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨t.swap,
        mem_filter.mpr ⟨mem_product.mpr ⟨hb,ha⟩,h⟩,Prod.swap_swap t⟩)
  have hpair : B.card^2 ≤ B.card+2*P.card := by
    have h₁ := card_le_card hcover
    have h₂ := card_union_le P (P.image Prod.swap)
    have h₃ := card_image_le (s := P) (f := Prod.swap)
    rw [offDiag_card] at h₁
    have hm : B.card ≤ B.card*B.card := by
      by_cases hz : B.card=0
      · simp [hz]
      · have hpos : 1 ≤ B.card := by omega
        nlinarith
    rw [pow_two]
    omega
  have hgap {t : ℕ × ℕ} (ht : t ∈ P) : t.2-t.1 ∈ Icc 1 p := by
    obtain ⟨ht,hlt⟩ := mem_filter.mp ht
    have hh := mem_range.mp (hB (mem_product.mp ht).2)
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  have hsum : P.card=∑ d ∈ Icc 1 p, (P.filter (fun t => t.2-t.1=d)).card :=
    card_eq_sum_card_fiberwise (fun _ ht => hgap ht)
  have hfiber (d : ℕ) (hd : d ∈ Icc 1 p) :
      (P.filter (fun t => t.2-t.1=d)).card ≤ (overlap B d).card := by
    apply card_le_card_of_injOn Prod.fst
    · intro t ht
      obtain ⟨ht,he⟩ := mem_filter.mp ht
      obtain ⟨ht,hlt⟩ := mem_filter.mp ht
      obtain ⟨h₁,h₂⟩ := mem_product.mp ht
      refine mem_filter.mpr ⟨h₁,?_⟩
      convert h₂ using 1
      omega
    · intro t ht s hs he
      have ht₁ := (mem_filter.mp ht).2
      have hs₁ := (mem_filter.mp hs).2
      have ht₂ := (mem_filter.mp (mem_filter.mp ht).1).2
      have hs₂ := (mem_filter.mp (mem_filter.mp hs).1).2
      apply Prod.ext he
      omega
  have hb : P.card ≤ ∑ d ∈ Icc 1 p, (overlap B d).card := by
    rw [hsum]
    exact sum_le_sum hfiber
  omega

/-- Uniform in the modulus and in both affine-line parameters. -/
theorem line_card_bound {p : ℕ} (hp : 0<p) {a c : ZMod p} {B : Finset ℕ}
    (hB : OnLine p a c B) : (B.card:ℝ)^2 ≤ p*(5+2*Real.log p) := by
  have hsub : B ⊆ range p := fun b hb => mem_range.mpr (hB b hb).1
  have hsize : (B.card:ℝ) ≤ p := by exact_mod_cast (card_le_card hsub).trans_eq (card_range p)
  have hpair : (B.card:ℝ)^2 ≤ B.card+2*∑ d ∈ Icc 1 p, ((overlap B d).card:ℝ) := by
    exact_mod_cast pair_sum_bound p B hsub
  have hsum : (∑ d ∈ Icc 1 p, ((overlap B d).card:ℝ)) ≤
      ∑ d ∈ Icc 1 p, ((p:ℝ)/d+1) := sum_le_sum (fun d hd => overlap_card hp (mem_Icc.mp hd).1 hB)
  have hh : (∑ d ∈ Icc 1 p, 1/(d:ℝ)) ≤ 1+Real.log p := by
    have ht := harmonic_le_one_add_log p
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,Rat.cast_inv,one_div] using ht
  have he : (∑ d ∈ Icc 1 p, ((p:ℝ)/d+1)) = p*(∑ d ∈ Icc 1 p, 1/(d:ℝ))+p := by
    simp only [sum_add_distrib,div_eq_mul_inv,one_mul,← mul_sum,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_one]
  have hm := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg p : (0:ℝ) ≤ p)
  rw [he] at hsum
  nlinarith only [hpair,hsize,hsum,hm]

#print axioms gap_difference
#print axioms gap_spacing
#print axioms overlap_card
#print axioms pair_sum_bound
#print axioms line_card_bound
end
end Erdos773.FloorParabolaLineBound
