import Submission.OuterCarryProfileExplore

/-! Integer transfer for varying low templates after outer repetition. The
only dependence on the choice of colors is through their scalar weights.
This does not supply an infinite scalar profile at logarithmic mean. -/
namespace Erdos66ColoredBlockTransfer
open AdditiveCombinatorics Erdos66IntegerBlock Erdos66CyclicThickening
  Erdos66OuterCarryProfile
open scoped Classical

noncomputable def profileConv (w : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (q+1), w i*w (q-i)

lemma profileConv_nonneg (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (q : ℕ) :
    0 ≤ profileConv w q := Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hw i) (hw (q-i)))

variable (M K : ℕ) [NeZero M] [NeZero K]

/-- Separate carry profiles permit different neighboring templates. The
resulting scalar expression is a carry interpolation of two weighted high
convolutions. -/
theorem colored_block_profile_error (C : ℕ → Finset (ZMod M)) (w : ℕ → ℝ)
    (β η : ℝ) (hβ : 0 ≤ β) (hη : 0 ≤ η) (hw : ∀ i, 0 ≤ w i)
    (hC : ∀ i j z, |(cyclicCount M (C i) (C j) z : ℝ)-β*w i*w j| ≤ η*(β*w i*w j))
    (q : ℕ) (hq : 0 < q) (t : ZMod M) (r : Fin K) :
    |(sumRep (blockSet (M*K) (fun i ↦ outerLift M K (C i)))
        (q*(M*K)+(blockDigit M K t r).val) : ℝ)-
      β*(r.val*profileConv w q+((K : ℝ)-r.val)*profileConv w (q-1))| ≤
      β*(K*η+1+η)*(profileConv w q+profileConv w (q-1)) := by
  let A : Set ℕ := blockSet (M*K) (fun i ↦ outerLift M K (C i))
  let L : ℕ → ℕ → ℝ := fun i j ↦
    lower (M*K) (outerLift M K (C i)) (outerLift M K (C j)) (blockDigit M K t r).val
  let U : ℕ → ℕ → ℝ := fun i j ↦
    upper (M*K) (outerLift M K (C i)) (outerLift M K (C j)) (blockDigit M K t r).val
  let δ : ℝ := β*(K*η+1+η)
  have hpair (i j : ℕ) :
      |L i j-(r.val : ℝ)*(β*w i*w j)| ≤ δ*w i*w j ∧
      |U i j-((K : ℝ)-r.val)*(β*w i*w j)| ≤ δ*w i*w j := by
    have hm : 0 ≤ β*w i*w j := mul_nonneg (mul_nonneg hβ (hw i)) (hw j)
    obtain ⟨hl,hu⟩ := outer_carry_error M K (C i) (C j) t r
      (β*w i*w j) (η*(β*w i*w j)) hm (mul_nonneg hη hm) (hC i j t)
    constructor
    · convert hl using 1
      dsimp [L,δ]
      ring
    · convert hu using 1
      dsimp [U,δ]
      ring
  have hformula : (sumRep A (q*(M*K)+(blockDigit M K t r).val) : ℝ) =
      (∑ i ∈ Finset.range (q+1), L i (q-i))+
        ∑ i ∈ Finset.range q, U i (q-i-1) := by
    have hh := block_formula (M*K) (fun i ↦ outerLift M K (C i)) q
      (blockDigit M K t r).val (ZMod.val_lt _)
    dsimp only at hh
    dsimp only [A,L,U]
    exact_mod_cast hh
  have hprev : (∑ i ∈ Finset.range q, w i*w (q-i-1))=profileConv w (q-1) := by
    unfold profileConv
    rw [show q-1+1=q by omega]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show q-i-1=q-1-i by omega]
  have he : (sumRep A (q*(M*K)+(blockDigit M K t r).val) : ℝ)-
      β*(r.val*profileConv w q+((K : ℝ)-r.val)*profileConv w (q-1)) =
      (∑ i ∈ Finset.range (q+1), (L i (q-i)-(r.val : ℝ)*(β*w i*w (q-i))))+
        ∑ i ∈ Finset.range q, (U i (q-i-1)-((K : ℝ)-r.val)*(β*w i*w (q-i-1))) := by
    rw [hformula]
    simp only [Finset.sum_sub_distrib]
    have hl : (∑ i ∈ Finset.range (q+1), (r.val : ℝ)*(β*w i*w (q-i))) =
        (r.val : ℝ)*β*profileConv w q := by
      rw [profileConv,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hu : (∑ i ∈ Finset.range q, ((K : ℝ)-r.val)*(β*w i*w (q-i-1))) =
        ((K : ℝ)-r.val)*β*profileConv w (q-1) := by
      rw [← hprev,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hl,hu]
    ring
  change |(sumRep A (q*(M*K)+(blockDigit M K t r).val) : ℝ)-
    β*(r.val*profileConv w q+((K : ℝ)-r.val)*profileConv w (q-1))| ≤ _
  rw [he]
  calc
    _ ≤ |∑ i ∈ Finset.range (q+1), (L i (q-i)-(r.val : ℝ)*(β*w i*w (q-i)))|+
        |∑ i ∈ Finset.range q, (U i (q-i-1)-((K : ℝ)-r.val)*(β*w i*w (q-i-1)))| := abs_add_le _ _
    _ ≤ (∑ i ∈ Finset.range (q+1), |L i (q-i)-(r.val : ℝ)*(β*w i*w (q-i))|)+
        ∑ i ∈ Finset.range q, |U i (q-i-1)-((K : ℝ)-r.val)*(β*w i*w (q-i-1))| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (∑ i ∈ Finset.range (q+1), δ*w i*w (q-i))+
        ∑ i ∈ Finset.range q, δ*w i*w (q-i-1) :=
      add_le_add (Finset.sum_le_sum (fun i _ ↦ (hpair i (q-i)).1))
        (Finset.sum_le_sum (fun i _ ↦ (hpair i (q-i-1)).2))
    _ = _ := by
      simp only [mul_assoc,← Finset.mul_sum]
      rw [hprev]
      dsimp [δ,profileConv]
      ring

/-- Near-constant weighted high convolutions yield near-constant natural
representation counts, without requiring neighboring low colors to agree. -/
theorem colored_block_constant_error (C : ℕ → Finset (ZMod M)) (w : ℕ → ℝ)
    (β η μ ε : ℝ) (hβ : 0 ≤ β) (hη : 0 ≤ η)
    (hw : ∀ i, 0 ≤ w i)
    (hC : ∀ i j z, |(cyclicCount M (C i) (C j) z : ℝ)-β*w i*w j| ≤ η*(β*w i*w j))
    (q : ℕ) (hq : 0 < q) (t : ZMod M) (r : Fin K)
    (hqerr : |profileConv w q-μ| ≤ ε*μ)
    (hprev : |profileConv w (q-1)-μ| ≤ ε*μ) :
    |(sumRep (blockSet (M*K) (fun i ↦ outerLift M K (C i)))
        (q*(M*K)+(blockDigit M K t r).val) : ℝ)-K*β*μ| ≤
      β*μ*(K*ε+2*(K*η+1+η)*(1+ε)) := by
  have hmain := colored_block_profile_error M K C w β η hβ hη hw hC q hq t r
  let s := profileConv w q
  let s' := profileConv w (q-1)
  have hr : (0 : ℝ) ≤ r.val := Nat.cast_nonneg _
  have hrK : (r.val : ℝ) ≤ K := by exact_mod_cast r.isLt.le
  have hKr : 0 ≤ (K : ℝ)-r.val := by linarith
  have hinterp : |β*(r.val*s+((K : ℝ)-r.val)*s')-K*β*μ| ≤ β*K*(ε*μ) := by
    have he : β*(r.val*s+((K : ℝ)-r.val)*s')-K*β*μ =
        β*((r.val : ℝ)*(s-μ)+((K : ℝ)-r.val)*(s'-μ)) := by ring
    rw [he,abs_mul,abs_of_nonneg hβ]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hβ
    calc
      _ ≤ |(r.val : ℝ)*(s-μ)|+|((K : ℝ)-r.val)*(s'-μ)| := abs_add_le _ _
      _ = (r.val : ℝ)*|s-μ|+((K : ℝ)-r.val)*|s'-μ| := by
        rw [abs_mul,abs_mul,abs_of_nonneg hr,abs_of_nonneg hKr]
      _ ≤ (r.val : ℝ)*(ε*μ)+((K : ℝ)-r.val)*(ε*μ) :=
        add_le_add (mul_le_mul_of_nonneg_left hqerr hr) (mul_le_mul_of_nonneg_left hprev hKr)
      _ = _ := by ring
  have hsup : s+s' ≤ 2*(1+ε)*μ := by
    have h1 := (abs_le.mp hqerr).2
    have h2 := (abs_le.mp hprev).2
    dsimp [s,s']
    linarith
  have hδ : 0 ≤ β*((K : ℝ)*η+1+η) := by positivity
  have hm := mul_le_mul_of_nonneg_left hsup hδ
  have ht := abs_sub_le (sumRep (blockSet (M*K) (fun i ↦ outerLift M K (C i)))
      (q*(M*K)+(blockDigit M K t r).val) : ℝ)
    (β*(r.val*s+((K : ℝ)-r.val)*s')) (K*β*μ)
  change |_ - β*(r.val*s+((K : ℝ)-r.val)*s')| ≤ β*(K*η+1+η)*(s+s') at hmain
  nlinarith

end Erdos66ColoredBlockTransfer
