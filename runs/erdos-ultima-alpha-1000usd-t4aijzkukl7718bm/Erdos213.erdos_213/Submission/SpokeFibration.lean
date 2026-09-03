import FormalConjecturesUtil

/-! A restricted fibration for the extra odd-spoke square condition.
These identities and exclusions do not settle Erdős Problem 213. -/

namespace Erdos213.SpokeFibration

def median0 (α β t : ℝ) : ℝ := 2*t^2+2-(α*t+β)^2
def median1 (α β t : ℝ) : ℝ := 2*t^2-1+2*(α*t+β)^2
def median2 (α β t : ℝ) : ℝ := -t^2+2+2*(α*t+β)^2

def quadDisc {R : Type*} [CommRing R] (a b c : R) : R := b^2-4*a*c

def quadRes {R : Type*} [CommRing R] (a b c d e f : R) : R :=
  (a*f-c*d)^2-(a*e-b*d)*(b*f-c*e)

lemma quadRes_eq_zero_of_common_root {R : Type*} [CommRing R]
    (a b c d e f t : R) (h₁ : a*t^2+b*t+c=0) (h₂ : d*t^2+e*t+f=0) :
    quadRes a b c d e f = 0 := by
  unfold quadRes
  linear_combination
    ((a*e-b*d)*(e+d*t)-(a*f-c*d)*d)*h₁ +
    ((a*f-c*d)*a-(a*e-b*d)*(b+a*t))*h₂

/-- The conic relation makes one additional spoke norm a square identically. -/
lemma extra_square_identity (α β a b : ℝ) (h : β^2=3*α^2-2) :
    -2*a^2+6*b^2+3*(α*a+β*b)^2=(β*a+3*α*b)^2 := by
  linear_combination (3*b^2-a^2)*h

lemma conic_parameter (k : ℝ) (hk : k^2-3≠0) :
    ((k^2+6*k+3)/(k^2-3))^2 = 3*((k^2+2*k+3)/(k^2-3))^2-2 := by
  field_simp
  ring

lemma median_discriminants (α β : ℝ) (h : β^2=3*α^2-2) :
    quadDisc (2-α^2) (-2*α*β) (2-β^2) = 32*(α^2-1) ∧
    quadDisc (2+2*α^2) (4*α*β) (-1+2*β^2) = -40*(α^2-1) ∧
    quadDisc (-1+2*α^2) (4*α*β) (2+2*β^2) = 8*(α^2-1) := by
  unfold quadDisc
  constructor
  · linear_combination 8*h
  constructor
  · linear_combination -16*h
  · linear_combination 8*h

lemma no_repeated_branch (α β : ℝ) (h : β^2=3*α^2-2) (ha : α^2≠1) :
    quadDisc (2-α^2) (-2*α*β) (2-β^2) ≠ 0 ∧
    quadDisc (2+2*α^2) (4*α*β) (-1+2*β^2) ≠ 0 ∧
    quadDisc (-1+2*α^2) (4*α*β) (2+2*β^2) ≠ 0 := by
  rcases median_discriminants α β h with ⟨h₀,h₁,h₂⟩
  rw [h₀,h₁,h₂]
  constructor
  · exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr ha)
  constructor
  · exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr ha)
  · exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr ha)

lemma repeated_branch_degenerate (α β : ℝ) (h : β^2=3*α^2-2) (ha : α^2=1) :
    (α=1 ∨ α=-1) ∧ (β=1 ∨ β=-1) := by
  have hb : β^2=1 := by nlinarith
  constructor
  · rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (show α^2=(1:ℝ)^2 by nlinarith) with h|h
    · exact Or.inl h
    · exact Or.inr h
  · rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (show β^2=(1:ℝ)^2 by nlinarith) with h|h
    · exact Or.inl h
    · exact Or.inr h

lemma resultant01 (α β : ℝ) (h : β^2=3*α^2-2) :
    quadRes (2-α^2) (-2*α*β) (2-β^2)
      (2+2*α^2) (4*α*β) (-1+2*β^2) = (7*β^2-4)^2+24*β^2+48 := by
  unfold quadRes
  linear_combination -(3*α^2+13*β^2+14)*h

lemma resultant02 (α β : ℝ) (h : β^2=3*α^2-2) :
    quadRes (2-α^2) (-2*α*β) (2-β^2)
      (-1+2*α^2) (4*α*β) (2+2*β^2) = 25*β^4+52*β^2+4 := by
  unfold quadRes
  linear_combination -(12*α^2+16*β^2-16)*h

lemma resultant12 (α β : ℝ) (h : β^2=3*α^2-2) :
    quadRes (2+2*α^2) (4*α*β) (-1+2*β^2)
      (-1+2*α^2) (4*α*β) (2+2*β^2) = 16*β^4+16*β^2+49 := by
  unfold quadRes
  linear_combination -(12*α^2-20*β^2+20)*h

lemma resultants_positive (α β : ℝ) (h : β^2=3*α^2-2) :
    0 < quadRes (2-α^2) (-2*α*β) (2-β^2)
      (2+2*α^2) (4*α*β) (-1+2*β^2) ∧
    0 < quadRes (2-α^2) (-2*α*β) (2-β^2)
      (-1+2*α^2) (4*α*β) (2+2*β^2) ∧
    0 < quadRes (2+2*α^2) (4*α*β) (-1+2*β^2)
      (-1+2*α^2) (4*α*β) (2+2*β^2) := by
  rw [resultant01 α β h,resultant02 α β h,resultant12 α β h]
  exact ⟨by positivity,by positivity,by positivity⟩

/-- Positive resultant excludes a shared root even in the complex plane. -/
lemma no_common_complex_root (a b c d e f : ℝ)
    (hr : 0 < quadRes a b c d e f) :
    ¬ ∃ t : ℂ, a*t^2+b*t+c=0 ∧ d*t^2+e*t+f=0 := by
  rintro ⟨t,h₁,h₂⟩
  have hz := quadRes_eq_zero_of_common_root
    (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) (e : ℂ) (f : ℂ) t h₁ h₂
  have he : quadRes a b c d e f = 0 := by
    apply Complex.ofReal_injective
    simpa only [quadRes, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_zero] using hz
  exact (ne_of_gt hr) he

lemma median_roots_disjoint (α β : ℝ) (h : β^2=3*α^2-2) :
    (¬ ∃ t : ℂ, 2*t^2+2-((α : ℂ)*t+β)^2=0 ∧
      2*t^2-1+2*((α : ℂ)*t+β)^2=0) ∧
    (¬ ∃ t : ℂ, 2*t^2+2-((α : ℂ)*t+β)^2=0 ∧
      -t^2+2+2*((α : ℂ)*t+β)^2=0) ∧
    (¬ ∃ t : ℂ, 2*t^2-1+2*((α : ℂ)*t+β)^2=0 ∧
      -t^2+2+2*((α : ℂ)*t+β)^2=0) := by
  rcases resultants_positive α β h with ⟨h₀,h₁,h₂⟩
  constructor
  · rintro ⟨t,ht,ht'⟩
    apply no_common_complex_root _ _ _ _ _ _ h₀
    refine ⟨t,?_,?_⟩
    · push_cast; linear_combination ht
    · push_cast; linear_combination ht'
  constructor
  · rintro ⟨t,ht,ht'⟩
    apply no_common_complex_root _ _ _ _ _ _ h₁
    refine ⟨t,?_,?_⟩
    · push_cast; linear_combination ht
    · push_cast; linear_combination ht'
  · rintro ⟨t,ht,ht'⟩
    apply no_common_complex_root _ _ _ _ _ _ h₂
    refine ⟨t,?_,?_⟩
    · push_cast; linear_combination ht
    · push_cast; linear_combination ht'

lemma exceptional_heron_zero (α β a b : ℝ) (h : β^2=3*α^2-2)
    (ha : α^2=1) :
    -a^4-b^4-(α*a+β*b)^4+2*a^2*b^2+
      2*a^2*(α*a+β*b)^2+2*b^2*(α*a+β*b)^2=0 := by
  rcases repeated_branch_degenerate α β h ha with ⟨ha,hb⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> ring

#print axioms median_roots_disjoint
#print axioms exceptional_heron_zero

#print axioms quadRes_eq_zero_of_common_root
#print axioms extra_square_identity
#print axioms conic_parameter
#print axioms no_repeated_branch
#print axioms repeated_branch_degenerate
#print axioms resultants_positive

end Erdos213.SpokeFibration
