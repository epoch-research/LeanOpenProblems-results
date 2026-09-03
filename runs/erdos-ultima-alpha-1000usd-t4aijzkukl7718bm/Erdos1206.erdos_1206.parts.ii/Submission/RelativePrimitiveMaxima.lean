import Submission.RelativePrimitiveCover

/-! A global sufficient criterion stated in terms of distinct normalized
primitive maxima. No source satisfying this global hypothesis is constructed. -/
namespace Erdos1206.RelativePrimitiveMaxima
open RelativePrimitiveCover
open scoped Classical

def commonGcd (a b c d : ℕ) : ℕ := Nat.gcd (Nat.gcd a b) (Nat.gcd c d)
def primitiveMax (a b c d : ℕ) : ℕ := d/commonGcd a b c d

def maxima (S : Set ℕ) : Set ℕ :=
  {q | ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S,
    0 < a ∧ a < b ∧ b < c ∧ c < d ∧ a^3+d^3=b^3+c^3 ∧ q=primitiveMax a b c d}

lemma ratio_of_common_divisor {a d g : ℕ} (ha : 0 < a) (had : a ≤ d)
    (hga : g ∣ a) (hgd : g ∣ d) :
    d/g ∣ d ∧ ∃ r ∈ Set.Icc 1 (d/g), ∃ s ∈ Set.Icc 1 (d/g), r*a=s*d := by
  have hg : 0 < g := Nat.pos_of_dvd_of_pos hga ha
  have hd : 0 < d := ha.trans_le had
  have hq : 0 < d/g := Nat.div_pos (Nat.le_of_dvd hd hgd) hg
  have hs : 0 < a/g := Nat.div_pos (Nat.le_of_dvd ha hga) hg
  have hsq : a/g ≤ d/g := Nat.div_le_div_right had
  refine ⟨⟨g,?_⟩,d/g,⟨hq,le_rfl⟩,a/g,⟨hs,hsq⟩,?_⟩
  · rw [mul_comm,Nat.mul_div_cancel' hgd]
  · calc
      _ = (d/g)*(g*(a/g)) := by rw [Nat.mul_div_cancel' hga]
      _ = (a/g)*(g*(d/g)) := by ring
      _ = _ := by rw [Nat.mul_div_cancel' hgd]

lemma maxima_ratio_compatible (S : Set ℕ) : RatioCompatibleCover S (maxima S) := by
  intro a ha b hb c hc d hd ha0 hab hbc hcd he
  have hga : commonGcd a b c d ∣ a := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hgd : commonGcd a b c d ∣ d := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  refine ⟨primitiveMax a b c d,⟨a,ha,b,hb,c,hc,d,hd,ha0,hab,hbc,hcd,he,rfl⟩,?_⟩
  exact ratio_of_common_divisor ha0 (hab.trans (hbc.trans hcd)).le hga hgd

/-- A positive-density source whose distinct primitive collision maxima have
summable reciprocals would settle the conjecture. This controls the finite
head as well as the tail. -/
theorem summable_maxima_suffice {S : Set ℕ} (hS : 0 < S.lowerDensity)
    (hpos : ∀ n ∈ S, 0 < n)
    (hs : Summable (fun d : ℕ => if d ∈ maxima S then (1:ℝ)/d else 0)) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧ IsSidon ((fun n : ℕ => n^3) '' A) :=
  ratio_compatible_cover_suffices hS hpos hs (maxima_ratio_compatible S)

#print axioms ratio_of_common_divisor
#print axioms maxima_ratio_compatible
#print axioms summable_maxima_suffice
end Erdos1206.RelativePrimitiveMaxima
