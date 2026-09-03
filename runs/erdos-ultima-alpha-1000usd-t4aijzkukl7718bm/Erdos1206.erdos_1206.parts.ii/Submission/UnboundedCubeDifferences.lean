import Submission.GeneralCubeDifferences

/-! Unbounded rational representations of cubic differences. This file makes
no assertion about the density of integral cube-Sidon sets. -/

namespace Erdos1206.UnboundedCubeDifferences
open scoped Classical
set_option maxHeartbeats 1000000

/-- Difference of two points on the cubic, written without projective notation. -/
def newLowerNum (D a b c d : ℚ) : ℚ := b*c*(a*c-b*d)+D*(a+d)
def newUpperNum (D a b c d : ℚ) : ℚ := a*d*(a*c-b*d)+D*(b+c)
def newDen (a b c d : ℚ) : ℚ := a*d*(a+d)-b*c*(b+c)

lemma chord_identity {D a b c d : ℚ}
    (h₁ : a^3-b^3=D) (h₂ : c^3-d^3=D) :
    (newUpperNum D a b c d)^3-(newLowerNum D a b c d)^3=
      D*(newDen a b c d)^3 := by
  simp only [newUpperNum,newLowerNum,newDen]
  linear_combination (a*d^2-b*c^2-D)^3*h₁-(-a^2*d+b^2*c-D)^3*h₂

lemma strict_increment {D a b c d : ℚ} (hD : 0<D)
    (h₁ : a^3-b^3=D) (h₂ : c^3-d^3=D) (hb : 0<b) (hbd : b<d) :
    b<a ∧ a<c ∧ c<a+d-b := by
  have hba : b<a := (Odd.pow_lt_pow (by decide : Odd 3)).mp (by linarith)
  have hac : a<c := (Odd.pow_lt_pow (by decide : Odd 3)).mp (by
    have hh := (Odd.strictMono_pow (by decide : Odd 3)) hbd
    linarith)
  refine ⟨hba,hac,?_⟩
  have hid : (a+d-b)^3-c^3=3*(d-b)*(a-b)*(a+d) := by
    linear_combination h₁-h₂
  have hp : 0<3*(d-b)*(a-b)*(a+d) := by
    apply mul_pos
    · exact mul_pos (mul_pos (by norm_num) (sub_pos.mpr hbd)) (sub_pos.mpr hba)
    · linarith
  exact (Odd.pow_lt_pow (by decide : Odd 3)).mp (by linarith)

lemma denominator_pos {D a b c d : ℚ} (hD : 0<D)
    (h₁ : a^3-b^3=D) (h₂ : c^3-d^3=D) (hb : 0<b) (hbd : b<d) :
    0<newDen a b c d := by
  have hg := (strict_increment hD h₁ h₂ hb hbd).2.2
  have hpow := (Odd.strictMono_pow (by decide : Odd 3))
    (show b+c<a+d by linarith)
  have hid : 3*newDen a b c d=(a+d)^3-(b+c)^3 := by
    dsimp [newDen]
    linear_combination -(h₁-h₂)
  linarith

lemma numerators_pos {D a b c d : ℚ} (hD : 0<D)
    (h₁ : a^3-b^3=D) (h₂ : c^3-d^3=D) (hb : 0<b) (hbd : b<d) :
    0<newLowerNum D a b c d ∧ 0<newUpperNum D a b c d := by
  obtain ⟨hba,hac,_⟩ := strict_increment hD h₁ h₂ hb hbd
  have hdc : d<c := (Odd.pow_lt_pow (by decide : Odd 3)).mp (by linarith)
  have habcd : b*d<a*c := mul_lt_mul hba hdc.le (by linarith) (by linarith)
  have ha : 0<a := hb.trans hba
  have hc : 0<c := ha.trans hac
  have hd : 0<d := hb.trans hbd
  have hsub : 0<a*c-b*d := sub_pos.mpr habcd
  simp only [newLowerNum,newUpperNum]
  constructor <;> positivity

lemma denominator_upper {D a b c d H : ℚ} (hD : 0<D)
    (h₁ : a^3-b^3=D) (h₂ : c^3-d^3=D) (hb : 0<b) (hbd : b<d)
    (haH : a≤H) (hbH : b≤H) (hdH : d≤H) :
    newDen a b c d≤3*H^2*(d-b) := by
  obtain ⟨hba,hac,_⟩ := strict_increment hD h₁ h₂ hb hbd
  have ha : 0<a := hb.trans hba
  have hd : 0<d := hb.trans hbd
  have hH : 0<H := ha.trans_le haH
  have hCA : 0<c-a := sub_pos.mpr hac
  have hc : 0<c := ha.trans hac
  have hsubtract : 0≤b*(c-a)*(a+b+c) := by positivity
  have hid : newDen a b c d=a*(d-b)*(a+b+d)-b*(c-a)*(a+b+c) := by
    simp only [newDen]
    ring
  have hprod : a*(a+b+d)≤H*(3*H) := mul_le_mul haH (by linarith)
    (by positivity) hH.le
  have hm := mul_le_mul_of_nonneg_right hprod (sub_pos.mpr hbd).le
  rw [hid]
  nlinarith

lemma numerator_lower {D a b c d H : ℚ} (hD : 0<D)
    (h₁ : a^3-b^3=D) (h₂ : c^3-d^3=D) (hb : 0<b) (hbd : b<d)
    (haH : a≤H) : D^2≤H^2*newLowerNum D a b c d := by
  obtain ⟨hba,hac,_⟩ := strict_increment hD h₁ h₂ hb hbd
  have hdc : d<c := (Odd.pow_lt_pow (by decide : Odd 3)).mp (by linarith)
  have ha : 0<a := hb.trans hba
  have hc : 0<c := ha.trans hac
  have hd : 0<d := hb.trans hbd
  have hH : 0<H := ha.trans_le haH
  have habcd : 0<a*c-b*d := sub_pos.mpr (mul_lt_mul hba hdc.le hd ha.le)
  have hsq := pow_le_pow_left₀ ha.le haH 2
  have hcube := mul_le_mul_of_nonneg_right hsq ha.le
  have hDa : D≤H^2*a := by nlinarith [pow_pos hb 3]
  have hDX := mul_le_mul_of_nonneg_left hDa hD.le
  have hnum : D*a≤newLowerNum D a b c d := by
    have hp : 0≤b*c*(a*c-b*d) := by positivity
    dsimp [newLowerNum]
    nlinarith [mul_pos hD hd]
  have hmul := mul_le_mul_of_nonneg_left hnum (sq_nonneg H)
  nlinarith

/-- Close distinct input pairs give a large positive output pair. -/
lemma large_pair_of_close {D a b c d H M : ℚ} (hD : 0<D) (hM : 0≤M)
    (h₁ : a^3-b^3=D) (h₂ : c^3-d^3=D) (hb : 0<b) (hbd : b<d)
    (haH : a≤H) (hbH : b≤H) (hdH : d≤H)
    (hclose : 3*(M+1)*H^4*(d-b)<D^2) :
    ∃ x y : ℚ, M<y ∧ 0<y ∧ 0<x ∧ x^3-y^3=D := by
  let X := newLowerNum D a b c d
  let Y := newUpperNum D a b c d
  let T := newDen a b c d
  have hT : 0<T := denominator_pos hD h₁ h₂ hb hbd
  obtain ⟨hX,hY⟩ := numerators_pos hD h₁ h₂ hb hbd
  have hTU := denominator_upper hD h₁ h₂ hb hbd haH hbH hdH
  have hXL := numerator_lower hD h₁ h₂ hb hbd haH
  have hH : 0<H := (hb.trans (strict_increment hD h₁ h₂ hb hbd).1).trans_le haH
  have hbound : (M+1)*T<X := by
    apply (mul_lt_mul_iff_right₀ (sq_pos_of_pos hH)).mp
    have hmul := mul_le_mul_of_nonneg_left hTU
      (show 0≤(M+1)*H^2 by positivity)
    dsimp [X,T]
    nlinarith
  refine ⟨Y/T,X/T,?_,div_pos hX hT,div_pos hY hT,?_⟩
  · apply (lt_div_iff₀ hT).mpr
    nlinarith
  · have he := chord_identity h₁ h₂
    rw [div_pow,div_pow,← sub_div]
    exact (div_eq_iff (pow_ne_zero 3 hT.ne')).mpr he


lemma exists_close_pair {S : Set ℚ} (hS : S.Infinite) {M δ : ℚ}
    (hpos : ∀ y∈S, 0<y) (hbound : ∀ y∈S, y≤M) (hδ : 0<δ) :
    ∃ b∈S, ∃ d∈S, b<d ∧ d-b<δ := by
  let N : ℕ := ⌊M/δ⌋₊
  let V : ℕ → Set ℚ := fun n => {y | y∈S ∧ ⌊y/δ⌋₊=n}
  have hcover : S⊆⋃ n∈Set.Icc 0 N, V n := by
    intro y hy
    have hn : ⌊y/δ⌋₊≤N := Nat.floor_mono
      (div_le_div_of_nonneg_right (hbound y hy) hδ.le)
    exact Set.mem_iUnion₂.mpr ⟨⌊y/δ⌋₊,⟨Nat.zero_le _,hn⟩,hy,rfl⟩
  have hex : ∃ n∈Set.Icc 0 N, (V n).Infinite := by
    by_contra h
    push_neg at h
    exact hS (((Set.finite_Icc 0 N).biUnion (fun n hn => h n hn)).subset hcover)
  obtain ⟨n,_,hn⟩ := hex
  obtain ⟨b,hb⟩ := hn.nonempty
  obtain ⟨d,hd,hdb⟩ := hn.exists_notMem_finset {b}
  have hne : b≠d := by simpa [eq_comm] using hdb
  have hinterval (y : ℚ) (hy : y∈V n) :
      (n : ℚ)*δ≤y ∧ y<((n : ℚ)+1)*δ := by
    have hy0 : 0≤y/δ := div_nonneg (hpos y hy.1).le hδ.le
    constructor
    · have h := Nat.floor_le hy0
      rw [hy.2] at h
      exact (le_div_iff₀ hδ).mp h
    · have h := Nat.lt_floor_add_one (y/δ)
      rw [hy.2] at h
      exact (div_lt_iff₀ hδ).mp h
  have hbi := hinterval b hb
  have hdi := hinterval d hd
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨b,hb.1,d,hd.1,h,by nlinarith⟩
  · exact ⟨d,hd.1,b,hb.1,h,by nlinarith⟩

lemma root_upper {D a b : ℚ} (hD : 0<D) (hb : 0<b) (he : a^3-b^3=D) :
    a≤b+D+1 := by
  apply (Odd.pow_le_pow (by decide : Odd 3)).mp
  have hDcube : D≤(D+1)^3 := by nlinarith [sq_nonneg D, pow_pos hD 3]
  have hcross : 0≤3*b*(D+1)*(b+D+1) := by positivity
  nlinarith

/-- Infinitely many positive rational representations force unbounded positive
representations. The proof uses the chord of two arbitrarily close points. -/
theorem unbounded_of_infinite {D : ℚ} (hD : 0<D)
    (hi : {y : ℚ | 0<y ∧ ∃ x : ℚ, 0<x ∧ x^3-y^3=D}.Infinite) (M : ℚ) :
    ∃ x y : ℚ, M<y ∧ 0<y ∧ 0<x ∧ x^3-y^3=D := by
  by_contra hnot
  have hbound : ∀ y∈{y : ℚ | 0<y ∧ ∃ x : ℚ, 0<x ∧ x^3-y^3=D}, y≤M := by
    rintro y ⟨hy,x,hx,he⟩
    by_contra hn
    exact hnot ⟨x,y,lt_of_not_ge hn,hy,hx,he⟩
  obtain ⟨y,hy⟩ := hi.nonempty
  have hM : 0<M := hy.1.trans_le (hbound y hy)
  let H := M+D+1
  have hH : 0<H := by dsimp [H]; positivity
  let δ := D^2/(3*(M+1)*H^4)
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨b,hb,d,hd,hbd,hclose⟩ := exists_close_pair hi (fun _ h => h.1) hbound hδ
  obtain ⟨hb,a,ha,h₁⟩ := hb
  obtain ⟨hd,c,hc,h₂⟩ := hd
  have hbM : b≤M := hbound b ⟨hb,a,ha,h₁⟩
  have hdM : d≤M := hbound d ⟨hd,c,hc,h₂⟩
  have haH : a≤H := (root_upper hD hb h₁).trans (by dsimp [H]; linarith)
  have hbH : b≤H := by dsimp [H]; linarith
  have hdH : d≤H := by dsimp [H]; linarith
  have hclose' : 3*(M+1)*H^4*(d-b)<D^2 := by
    have hpos : 0<3*(M+1)*H^4 := by positivity
    have ht := (lt_div_iff₀ hpos).mp hclose
    nlinarith only [ht]
  exact hnot (large_pair_of_close hD hM.le h₁ h₂ hb hbd haH hbH hdH hclose')

/-- Every positive rational difference of positive cubes has arbitrarily
large positive rational representations. No denominator estimate is claimed. -/
theorem unbounded_rational_difference {a b : ℚ} (hb : 0<b) (hab : b<a) (M : ℚ) :
    ∃ x y : ℚ, M<y ∧ 0<y ∧ 0<x ∧ x^3-y^3=a^3-b^3 := by
  exact unbounded_of_infinite (sub_pos.mpr
    ((Odd.strictMono_pow (by decide : Odd 3)) hab))
    (GeneralCubeDifferences.infinite_rational_difference hb hab) M

#print axioms unbounded_of_infinite
#print axioms unbounded_rational_difference
end Erdos1206.UnboundedCubeDifferences
