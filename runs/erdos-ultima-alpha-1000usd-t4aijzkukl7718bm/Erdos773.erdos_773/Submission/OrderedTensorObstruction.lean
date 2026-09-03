import Submission.TensorMomentBalance
import Submission.SmallRotationLifting

/-!
Ordered digit tensors with balanced power moments.  This is an auxiliary
obstruction to a sufficient digit criterion, not a settlement of Erdős 773.
-/
namespace Erdos773.OrderedTensorObstruction
open Finset TensorMomentBalance SmallRotationLifting
set_option maxHeartbeats 3000000
noncomputable section

abbrev Grid (D : ℕ) := Fin D × Fin D

def key {D : ℕ} (ij : Grid D) : ℕ := ij.1.val+D*ij.2.val

def error (D : ℕ) : ℤ := 100*(D:ℤ)^3+10*D+10*(D:ℤ)^2+1

def scale (D : ℕ) : ℤ := error D+10

def fine (D : ℕ) (i : Fin D) : ℤ := scale D+10*i.val

def coarse (D : ℕ) (j : Fin D) : ℤ := scale D+10*(D:ℤ)*j.val

def digits {D : ℕ} (f g : Fin D → ℤ) : Grid D → ℤ :=
  tensor (fine D) f (coarse D) g

def radix (D : ℕ) : ℤ := scale D^2+(10*(D:ℤ)^2+2)*scale D+error D+1

lemma error_nonneg (D : ℕ) : 0 ≤ error D := by unfold error; positivity
lemma scale_ge (D : ℕ) : 10 ≤ scale D := by
  have := error_nonneg D
  unfold scale
  omega

private lemma remainder_bound {D : ℕ} (i j : Fin D) {f g : ℤ}
    (hf : -1 ≤ f ∧ f ≤ 1) (hg : -1 ≤ g ∧ g ≤ 1) :
    |100*(D:ℤ)*i.val*j.val+10*i.val*g+10*(D:ℤ)*j.val*f-f*g| ≤ error D := by
  have hi0 : (0:ℤ) ≤ i.val := by positivity
  have hj0 : (0:ℤ) ≤ j.val := by positivity
  have hD0 : (0:ℤ) ≤ D := by positivity
  have hi : (i.val:ℤ) ≤ D := by exact_mod_cast i.isLt.le
  have hj : (j.val:ℤ) ≤ D := by exact_mod_cast j.isLt.le
  have hfg : |f*g| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (abs_le.mpr hf) (abs_le.mpr hg) (abs_nonneg g) (by norm_num)).trans_eq (by norm_num)
  have h1 : |100*(D:ℤ)*i.val*j.val| ≤ 100*(D:ℤ)^3 := by
    rw [abs_of_nonneg (by positivity)]
    have hh := mul_le_mul hi hj hj0 hD0
    have hh' := mul_le_mul_of_nonneg_left hh (show (0:ℤ)≤100*D by positivity)
    nlinarith only [hh']
  have h2 : |10*(i.val:ℤ)*g| ≤ 10*D := by
    rw [abs_mul,abs_of_nonneg (by positivity)]
    have hh := mul_le_mul_of_nonneg_left (abs_le.mpr hg) (show (0:ℤ)≤10*i.val by positivity)
    nlinarith only [hh,hi]
  have h3 : |10*(D:ℤ)*j.val*f| ≤ 10*(D:ℤ)^2 := by
    rw [abs_mul,abs_of_nonneg (by positivity)]
    have hh := mul_le_mul_of_nonneg_left (abs_le.mpr hf) (show (0:ℤ)≤10*D*j.val by positivity)
    have hh' := mul_le_mul_of_nonneg_left hj (show (0:ℤ)≤10*D by positivity)
    nlinarith only [hh,hh']
  have ha := abs_add_le (100*(D:ℤ)*i.val*j.val) (10*i.val*g)
  have hb := abs_add_le (100*(D:ℤ)*i.val*j.val+10*i.val*g) (10*(D:ℤ)*j.val*f)
  have hc := abs_sub (100*(D:ℤ)*i.val*j.val+10*i.val*g+10*(D:ℤ)*j.val*f) (f*g)
  unfold error
  linarith

lemma digit_strip {D : ℕ} (f g : Fin D → ℤ)
    (hf : ∀ i, -1 ≤ f i ∧ f i ≤ 1) (hg : ∀ j, -1 ≤ g j ∧ g j ≤ 1)
    (ij : Grid D) :
    scale D^2+(10*(key ij:ℤ)-2)*scale D-error D ≤ digits f g ij ∧
    digits f g ij ≤ scale D^2+(10*(key ij:ℤ)+2)*scale D+error D := by
  have hrem := abs_le.mp (remainder_bound ij.1 ij.2 (hf ij.1) (hg ij.2))
  have hfi := hf ij.1
  have hgj := hg ij.2
  have hT : 0 ≤ scale D := (by norm_num : (0:ℤ)≤10).trans (scale_ge D)
  have hlo := mul_le_mul_of_nonneg_right (show (-2:ℤ)≤f ij.1+g ij.2 by omega) hT
  have hhi := mul_le_mul_of_nonneg_right (show f ij.1+g ij.2≤(2:ℤ) by omega) hT
  have he : digits f g ij = scale D^2 +
      (10*(key ij:ℤ)+f ij.1+g ij.2)*scale D +
      (100*(D:ℤ)*ij.1.val*ij.2.val+10*ij.1.val*g ij.2+
        10*(D:ℤ)*ij.2.val*f ij.1-f ij.1*g ij.2) := by
    simp only [digits,tensor,fine,coarse,key,Nat.cast_add,Nat.cast_mul]
    ring
  constructor <;> nlinarith only [hrem.1,hrem.2,hlo,hhi,he]

lemma key_lt {D : ℕ} (ij : Grid D) : key ij < D^2 := by
  have h1 := ij.1.isLt
  have h2 := ij.2.isLt
  have hh := Nat.mul_le_mul_left D (show ij.2.val+1≤D by omega)
  unfold key
  nlinarith

lemma key_injective (D : ℕ) : Function.Injective (@key D) := by
  intro ij kl h
  have hD : 0<D := lt_of_le_of_lt (Nat.zero_le _) ij.1.isLt
  have hm := congrArg (fun x : ℕ => x%D) h
  have hi : ij.1.val=kl.1.val := by
    simpa [key,Nat.add_mod,Nat.mod_eq_of_lt ij.1.isLt,Nat.mod_eq_of_lt kl.1.isLt] using hm
  have hj : ij.2.val=kl.2.val := by
    apply Nat.eq_of_mul_eq_mul_left hD
    dsimp [key] at h
    omega
  exact Prod.ext (Fin.ext hi) (Fin.ext hj)

/-- Every ordinary position from zero through D^2-1 occurs exactly once. -/
lemma position_bijective (D : ℕ) :
    Function.Bijective (fun ij : Grid D => (⟨key ij,key_lt ij⟩ : Fin (D^2))) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro ij kl h
    exact key_injective D (congrArg Fin.val h)
  · simp [Grid,pow_two]

lemma digit_positive {D : ℕ} (f g : Fin D → ℤ)
    (hf : ∀ i, -1 ≤ f i ∧ f i ≤ 1) (hg : ∀ j, -1 ≤ g j ∧ g j ≤ 1)
    (ij : Grid D) : 0 < digits f g ij := by
  have hh := (digit_strip f g hf hg ij).1
  have hT := scale_ge D
  have he : scale D=error D+10 := rfl
  have hk : (0:ℤ) ≤ key ij := by positivity
  have hm := mul_nonneg hk (show (0:ℤ)≤scale D by omega)
  nlinarith only [hh,hT,he,hm]

lemma digit_lt_radix {D : ℕ} (f g : Fin D → ℤ)
    (hf : ∀ i, -1 ≤ f i ∧ f i ≤ 1) (hg : ∀ j, -1 ≤ g j ∧ g j ≤ 1)
    (ij : Grid D) : digits f g ij < radix D := by
  have hh := (digit_strip f g hf hg ij).2
  have hk : (key ij:ℤ) ≤ (D:ℤ)^2 := by exact_mod_cast (key_lt ij).le
  have hT := scale_ge D
  have hm := mul_le_mul_of_nonneg_right hk (show (0:ℤ)≤scale D by omega)
  unfold radix
  nlinarith only [hh,hm]

lemma digit_order {D : ℕ} (f g : Fin D → ℤ)
    (hf : ∀ i, -1 ≤ f i ∧ f i ≤ 1) (hg : ∀ j, -1 ≤ g j ∧ g j ≤ 1)
    {ij kl : Grid D} (h : key ij < key kl) : digits f g ij < digits f g kl := by
  have hu := (digit_strip f g hf hg ij).2
  have hl := (digit_strip f g hf hg kl).1
  have hk : (key ij:ℤ)+1≤key kl := by exact_mod_cast h
  have hT := scale_ge D
  have he : scale D=error D+10 := rfl
  have hm := mul_le_mul_of_nonneg_right hk (show (0:ℤ)≤scale D by omega)
  nlinarith only [hu,hl,hT,he,hm]

/-- Ordinary base evaluation, with the second coordinate as the block index. -/
def gridValue {D : ℕ} (B : ℤ) (w : Grid D → ℤ) : ℤ :=
  ∑ ij, w ij*B^(key ij)

lemma tensor_eval {D : ℕ} (B : ℤ) (a f d g : Fin D → ℤ) :
    gridValue B (tensor a f d g) =
      (value B a+value B f)*value (B^D) d +
        (value B a-value B f)*value (B^D) g := by
  simp only [gridValue,tensor,key,Fintype.sum_prod_type,value,pow_add,pow_mul,
    add_mul,sub_mul,sum_add_distrib,sum_sub_distrib,mul_sum,sum_mul]
  congr 1 <;> congr 1 <;> rw [sum_comm] <;> apply sum_congr rfl <;> intro i hi <;>
    apply sum_congr rfl <;> intro j hj <;> ring

lemma gridValue_pos {D : ℕ} (hD : 0 < D) {B : ℤ} (hB : 0 < B)
    (w : Grid D → ℤ) (hw : ∀ ij, 0 < w ij) : 0 < gridValue B w := by
  apply sum_pos
  · intro ij hij
    exact mul_pos (hw ij) (pow_pos hB _)
  · exact ⟨(⟨0,hD⟩,⟨0,hD⟩),mem_univ _⟩

lemma bounded_neg {D : ℕ} {f : Fin D → ℤ} (hf : ∀ i, -1 ≤ f i ∧ f i ≤ 1) :
    ∀ i, -1 ≤ (-f) i ∧ (-f) i ≤ 1 := by
  intro i
  have h := hf i
  simp only [Pi.neg_apply]
  omega

lemma value_nonzero {D : ℕ} {B : ℤ} (hB : 2 ≤ B) (f : Fin D → ℤ)
    (hf : ∀ i, -1 ≤ f i ∧ f i ≤ 1) (hne : ∃ i, f i=1) : value B f ≠ 0 := by
  intro h
  have hh := signed_zero (by omega : 0<B) f
    (fun i => (abs_le.mpr (hf i)).trans_lt (by omega : (1:ℤ)<B)) h
  obtain ⟨i,hi⟩ := hne
  have := hh i
  omega

lemma value_difference_pos {D : ℕ} (hD : 0 < D) {B : ℤ} (hB : 0 < B)
    (a f : Fin D → ℤ) (ha : ∀ i, 2 ≤ a i) (hf : ∀ i, -1 ≤ f i ∧ f i ≤ 1) :
    0 < value B a-value B f := by
  rw [value,value,← sum_sub_distrib]
  apply sum_pos
  · intro i hi
    have hh : 0<a i-f i := by have := ha i; have := hf i; omega
    rw [← sub_mul]
    exact mul_pos hh (pow_pos hB _)
  · exact ⟨⟨0,hD⟩,mem_univ _⟩

lemma value_neg {D : ℕ} (B : ℤ) (f : Fin D → ℤ) : value B (-f) = -value B f := by
  simp only [value,Pi.neg_apply,neg_mul,sum_neg_distrib]

lemma radix_ge_two (D : ℕ) : 2 ≤ radix D := by
  have hT := scale_ge D
  have hE := error_nonneg D
  have ht : 0 ≤ (10*(D:ℤ)^2+2)*scale D := by positivity
  unfold radix
  nlinarith only [hT,hE,ht]

lemma four_tensor_collision {D : ℕ} (B : ℤ) (f g : Fin D → ℤ) :
    gridValue B (digits f g)^2+gridValue B (digits (-f) (-g))^2 =
      gridValue B (digits f (-g))^2+gridValue B (digits (-f) g)^2 := by
  simp only [digits,tensor_eval,value_neg]
  ring

/-- The balanced-digit construction is not Sidon whenever both signed factors
are nonzero.  The proof uses actual integer evaluations, not a modeling map. -/
theorem tensor_not_sidon {D : ℕ} (hD : 0<D) {B : ℤ} (hB : 2≤B)
    (f g : Fin D → ℤ) (hf : ∀ i, -1≤f i ∧ f i≤1) (hg : ∀ j, -1≤g j ∧ g j≤1)
    (hfn : ∃ i, f i=1) (hgn : ∃ j, g j=1) :
    ¬ IsSidon ({gridValue B (digits f g)^2,gridValue B (digits (-f) (-g))^2,
      gridValue B (digits f (-g))^2,gridValue B (digits (-f) g)^2} : Set ℤ) := by
  have hB0 : 0<B := by omega
  have hBD : 2≤B^D := hB.trans (le_self_pow₀ (by omega) (by omega))
  have hBD0 : 0<B^D := by omega
  have hF := value_nonzero hB f hf hfn
  have hG := value_nonzero hBD g hg hgn
  have ha : ∀ i : Fin D, 2≤fine D i := by
    intro i
    have := scale_ge D
    unfold fine
    have : (0 : ℤ) ≤ i.val := by positivity
    omega
  have hd : ∀ j : Fin D, 2≤coarse D j := by
    intro j
    have := scale_ge D
    unfold coarse
    have : (0:ℤ)≤10*(D:ℤ)*j.val := by positivity
    omega
  have hAF := value_difference_pos hD hB0 (fine D) f ha hf
  have hDG := value_difference_pos hD hBD0 (coarse D) g hd hg
  have hpr : gridValue B (digits f g)-gridValue B (digits f (-g)) ≠ 0 := by
    have he : gridValue B (digits f g)-gridValue B (digits f (-g)) =
        2*(value B (fine D)-value B f)*value (B^D) g := by
      simp only [digits,tensor_eval,value_neg]
      ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hAF.ne') hG
  have hps : gridValue B (digits f g)-gridValue B (digits (-f) g) ≠ 0 := by
    have he : gridValue B (digits f g)-gridValue B (digits (-f) g) =
        2*value B f*(value (B^D) (coarse D)-value (B^D) g) := by
      simp only [digits,tensor_eval,value_neg]
      ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hF) hDG.ne'
  have hp := gridValue_pos hD hB0 (digits f g) (digit_positive f g hf hg)
  have hr := gridValue_pos hD hB0 (digits f (-g)) (digit_positive f (-g) hf (bounded_neg hg))
  have hs := gridValue_pos hD hB0 (digits (-f) g) (digit_positive (-f) g (bounded_neg hf) hg)
  intro h
  rcases h _ (by simp) _ (by simp) _ (by simp) _ (by simp) (four_tensor_collision B f g) with he | he
  · exact hpr (sub_eq_zero.mpr ((sq_eq_sq₀ hp.le hr.le).mp he.1))
  · exact hps (sub_eq_zero.mpr ((sq_eq_sq₀ hp.le hs.le).mp he.1))

/-- Strict order in the ordinary low-to-high radix positions. -/
def Ordered {D : ℕ} (w : Grid D → ℤ) : Prop :=
  ∀ ij kl, key ij < key kl → w ij < w kl

/-- Every digit is strictly positive and smaller than the radix. -/
def Canonical {D : ℕ} (B : ℤ) (w : Grid D → ℤ) : Prop :=
  ∀ ij, 0<w ij ∧ w ij<B

/-- A canonical grid is a genuine D^2-digit integer word. -/
lemma gridValue_lt {D : ℕ} {B : ℤ} (hB : 0≤B) (w : Grid D → ℤ)
    (hw : Canonical B w) : gridValue B w < B^(D^2) := by
  have he : (∑ ij : Grid D, B^(key ij)) = ∑ i : Fin (D^2), B^i.val :=
    Fintype.sum_bijective _ (position_bijective D) _ _ (fun ij => rfl)
  have hh : gridValue B w ≤ (∑ ij : Grid D, B^(key ij))*(B-1) := by
    rw [gridValue,sum_mul]
    apply sum_le_sum
    intro ij hij
    have hd : w ij≤B-1 := by have := (hw ij).2; omega
    have hm := mul_le_mul_of_nonneg_right hd (pow_nonneg hB (key ij))
    simpa only [mul_comm] using hm
  rw [he,Fin.sum_univ_eq_sum_range (fun i : ℕ => B^i),geom_sum_mul] at hh
  omega

/-- Fixed-dimension, all-large-radix obstructions for arbitrarily many power
moments.  This does not assert a collision in every moment class. -/
theorem arbitrary_ordered_moments (k : ℕ) :
    ∃ D : ℕ, 0<D ∧ D≤16*(k+1)^2*((k+1).log2+1) ∧
      ∃ P Q R S : Grid D → ℤ,
        (∀ w ∈ ({P,Q,R,S} : Set (Grid D → ℤ)), Ordered w) ∧
        (∀ n≤k, (∑ ij, P ij^n)=(∑ ij, Q ij^n) ∧
          (∑ ij, P ij^n)=(∑ ij, R ij^n) ∧ (∑ ij, P ij^n)=(∑ ij, S ij^n)) ∧
        ∀ B : ℤ, radix D≤B →
          (∀ w ∈ ({P,Q,R,S} : Set (Grid D → ℤ)), Canonical B w) ∧
          ¬ IsSidon ({gridValue B P^2,gridValue B Q^2,gridValue B R^2,gridValue B S^2} : Set ℤ) := by
  obtain ⟨D,hD,hbound,f,hf,hfn,hbal⟩ := exists_balanced_signs k
  have ha : Balanced (fine D) f k := affine_balanced _ _ _ hbal (scale D) 10
  have hd : Balanced (coarse D) f k := affine_balanced _ _ _ hbal (scale D) (10*(D:ℤ))
  refine ⟨D,hD,hbound,digits f f,digits (-f) (-f),digits f (-f),digits (-f) f,?_,?_,?_⟩
  · intro w hw
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    all_goals
      intro ij kl hkey
      apply digit_order _ _ _ _ hkey
      all_goals first | exact hf | exact bounded_neg hf
  · intro n hn
    have hm := four_moments (fine D) f (coarse D) f k hf hf ha hd n hn
    exact ⟨hm.2.2,hm.2.1,hm.1⟩
  · intro B hB
    constructor
    · intro w hw
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl
      all_goals
        intro ij
        constructor
        · apply digit_positive
          all_goals first | exact hf | exact bounded_neg hf
        · apply lt_of_lt_of_le (digit_lt_radix _ _ _ _ ij) hB
          all_goals first | exact hf | exact bounded_neg hf
    · exact tensor_not_sidon hD ((radix_ge_two D).trans hB) f f hf hf hfn hfn

#print axioms digit_order
#print axioms digit_positive
#print axioms tensor_eval
#print axioms tensor_not_sidon
#print axioms arbitrary_ordered_moments
end
end Erdos773.OrderedTensorObstruction
