import Submission.RepeatedCubeDifferences

/-!
Quadratic chord maps for bounded families of repeated cubic differences.
This auxiliary development does not settle the positive-density conjecture.
-/

set_option maxHeartbeats 1000000

namespace Erdos1206.BoundedCubeDifferences
open scoped Classical

abbrev Point := Fin 3 → ℚ

def form (p : Point) : ℚ := p 0^3-p 1^3-7*p 2^3

def lin (q p : Point) : ℚ := q 0^2*p 0-q 1^2*p 1-7*q 2^2*p 2

def quad (q p : Point) : ℚ := q 0*p 0^2-q 1*p 1^2-7*q 2*p 2^2

/-- The third intersection of the line through `p,q` with the cubic. -/
def chord (q p : Point) : Point := lin q p • p - quad q p • q

lemma lin_chord (q p : Point) (hq : form q=0) :
    lin q (chord q p)=(lin q p)^2 := by
  simp only [lin, chord, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  dsimp [form] at hq
  linear_combination -(quad q p)*hq

lemma quad_chord (q p : Point) (hq : form q=0) :
    quad q (chord q p)=-(lin q p)^2*quad q p := by
  simp only [quad, chord, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  dsimp [form] at hq
  linear_combination (norm := (simp only [lin,quad]; ring_nf)) (quad q p)^2*hq

lemma chord_involution (q p : Point) (hq : form q=0) :
    chord q (chord q p)=(lin q p)^3 • p := by
  rw [chord, lin_chord q p hq, quad_chord q p hq]
  ext i
  simp only [chord, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma chord_form (q p : Point) (hq : form q=0) :
    form (chord q p)=(lin q p)^3*form p := by
  simp only [form, chord, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  dsimp [form] at hq
  linear_combination (norm := (simp only [lin,quad]; ring_nf)) -(quad q p)^3*hq

lemma chord_smul (q p : Point) (t : ℚ) :
    chord q (t • p)=t^2 • chord q p := by
  ext i
  simp only [chord, lin, quad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- On the affine chart, normalizing the chord map loses no points away
from its exceptional line. -/
lemma chord_normalized_injective (q p r : Point) (hq : form q=0)
    (hp : p 2=1) (hr : r 2=1)
    (hL : lin q p ≠ 0) (_hLr : lin q r ≠ 0)
    (hC : chord q p 2 ≠ 0) (_hCr : chord q r 2 ≠ 0)
    (he : (chord q p 2)⁻¹ • chord q p =
      (chord q r 2)⁻¹ • chord q r) : p=r := by
  have hh := congrArg (chord q) he
  rw [chord_smul, chord_smul, chord_involution q p hq,
    chord_involution q r hq] at hh
  have hs : (chord q p 2)⁻¹^2*(lin q p)^3 =
      (chord q r 2)⁻¹^2*(lin q r)^3 := by
    have h := congrFun hh 2
    simpa only [Pi.smul_apply, smul_eq_mul, hp, hr, mul_one] using h
  have hn : (chord q p 2)⁻¹^2*(lin q p)^3 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (inv_ne_zero hC)) (pow_ne_zero _ hL)
  ext i
  have h := congrFun hh i
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← hs] at h
  exact mul_left_cancel₀ hn h

def affine (a b : ℚ) : Point := ![a,b,1]

def upper (q : Point) (a b : ℚ) : ℚ :=
  -chord q (affine a b) 1 / chord q (affine a b) 2

def lower (q : Point) (a b : ℚ) : ℚ :=
  -chord q (affine a b) 0 / chord q (affine a b) 2

lemma mapped_identity (q : Point) (hq : form q=0) {a b : ℚ}
    (he : a^3-b^3=7) (hC : chord q (affine a b) 2 ≠ 0) :
    (upper q a b)^3-(lower q a b)^3=7 := by
  have hp : form (affine a b)=0 := by simp [form,affine]; linarith
  have hh := chord_form q (affine a b) hq
  rw [hp,mul_zero] at hh
  dsimp only [form] at hh
  dsimp only [upper,lower]
  field_simp
  nlinarith only [hh]

lemma mapped_lower_injective (q : Point) (hq : form q=0) {a b c d : ℚ}
    (he : a^3-b^3=7) (he' : c^3-d^3=7)
    (hL : lin q (affine a b) ≠ 0) (hL' : lin q (affine c d) ≠ 0)
    (hC : chord q (affine a b) 2 ≠ 0) (hC' : chord q (affine c d) 2 ≠ 0)
    (hf : lower q a b=lower q c d) : b=d := by
  have hu : upper q a b=upper q c d := by
    apply (Odd.strictMono_pow (by decide : Odd 3)).injective
    change (upper q a b)^3=(upper q c d)^3
    have h₁ := mapped_identity q hq he hC
    have h₂ := mapped_identity q hq he' hC'
    rw [hf] at h₁
    linarith
  have hn : (chord q (affine a b) 2)⁻¹ • chord q (affine a b) =
      (chord q (affine c d) 2)⁻¹ • chord q (affine c d) := by
    ext i
    fin_cases i
    · change (chord q (affine a b) 2)⁻¹*chord q (affine a b) 0 =
        (chord q (affine c d) 2)⁻¹*chord q (affine c d) 0
      have h := congrArg Neg.neg hf
      simpa only [lower, neg_div, neg_mul, neg_neg, div_eq_mul_inv, mul_comm] using h
    · change (chord q (affine a b) 2)⁻¹*chord q (affine a b) 1 =
        (chord q (affine c d) 2)⁻¹*chord q (affine c d) 1
      have h := congrArg Neg.neg hu
      simpa only [upper, neg_div, neg_mul, neg_neg, div_eq_mul_inv, mul_comm] using h
    · change (chord q (affine a b) 2)⁻¹*chord q (affine a b) 2 =
        (chord q (affine c d) 2)⁻¹*chord q (affine c d) 2
      rw [inv_mul_cancel₀ hC,inv_mul_cancel₀ hC']
  have h := chord_normalized_injective q (affine a b) (affine c d) hq
    (by simp [affine]) (by simp [affine]) hL hL' hC hC' hn
  exact congrFun h 1


def posQ : Point := ![73,17,38]
def negQ : Point := ![-17,-73,38]

lemma posQ_on_curve : form posQ=0 := by
  change (73 : ℚ)^3-17^3-7*38^3=0
  norm_num
lemma negQ_on_curve : form negQ=0 := by
  change (-17 : ℚ)^3-(-73)^3-7*38^3=0
  norm_num

lemma posQ_coordinates (a b : ℚ) :
    lin posQ (affine a b) = 5329*a-289*b-10108 ∧
    chord posQ (affine a b) 0 = -289*a*b+1241*b^2-10108*a+19418 ∧
    chord posQ (affine a b) 1 = 5329*a*b-1241*a^2-10108*b+4522 ∧
    chord posQ (affine a b) 2 = -2774*a^2+646*b^2+5329*a-289*b := by
  have hq0 : posQ 0=73 := rfl
  have hq1 : posQ 1=17 := rfl
  have hq2 : posQ 2=38 := rfl
  have hp0 : affine a b 0=a := rfl
  have hp1 : affine a b 1=b := rfl
  have hp2 : affine a b 2=1 := rfl
  refine ⟨?_,?_,?_,?_⟩ <;>
    simp only [chord,lin,quad,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
      hq0,hq1,hq2,hp0,hp1,hp2] <;> ring

lemma negQ_coordinates (a b : ℚ) :
    lin negQ (affine a b) = 289*a-5329*b-10108 ∧
    chord negQ (affine a b) 0 = -5329*a*b+1241*b^2-10108*a-4522 ∧
    chord negQ (affine a b) 1 = 289*a*b-1241*a^2-10108*b-19418 ∧
    chord negQ (affine a b) 2 = 646*a^2-2774*b^2+289*a-5329*b := by
  have hq0 : negQ 0=-17 := rfl
  have hq1 : negQ 1=-73 := rfl
  have hq2 : negQ 2=38 := rfl
  have hp0 : affine a b 0=a := rfl
  have hp1 : affine a b 1=b := rfl
  have hp2 : affine a b 2=1 := rfl
  refine ⟨?_,?_,?_,?_⟩ <;>
    simp only [chord,lin,quad,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
      hq0,hq1,hq2,hp0,hp1,hp2] <;> ring

lemma large_input_bounds {a b : ℚ} (_ha : 0<a) (hb : 100≤b)
    (he : a^3-b^3=7) :
    lin posQ (affine a b) ≠ 0 ∧ chord posQ (affine a b) 2 ≠ 0 ∧
    0 < upper posQ a b ∧ 1/100000 ≤ lower posQ a b ∧ lower posQ a b ≤ 100000 := by
  have hab : b<a := (Odd.pow_lt_pow (by decide : Odd 3)).mp (by linarith : b^3<a^3)
  have hab' : a<b+1 := by
    apply (Odd.pow_lt_pow (by decide : Odd 3)).mp
    nlinarith [sq_nonneg b]
  let h := a-b
  have hh0 : 0<h := by dsimp [h]; linarith
  have hh1 : h<1 := by dsimp [h]; linarith
  have hah : a=b+h := by dsimp [h]; ring
  have hbh0 : 0≤b*h := mul_nonneg (by linarith) hh0.le
  have hbh1 : b*h≤b := by nlinarith [mul_nonneg (by linarith : 0≤b) (by linarith : 0≤1-h)]
  have hh2 : h^2≤1 := by nlinarith
  have hb2 : 100*b≤b^2 := by nlinarith
  have hb20 : 0<b^2 := by positivity
  obtain ⟨hL,hX,hY,hZ⟩ := posQ_coordinates a b
  have hLp : 0<lin posQ (affine a b) := by rw [hL]; nlinarith
  have hXlo : b^2 ≤ chord posQ (affine a b) 0 := by
    rw [hX,hah]
    nlinarith
  have hXhi : chord posQ (affine a b) 0 ≤ 100000*b^2 := by
    rw [hX,hah]
    nlinarith
  have hYp : 0 < chord posQ (affine a b) 1 := by
    rw [hY,hah]
    nlinarith [sq_nonneg h]
  have hZlo : b^2 ≤ -chord posQ (affine a b) 2 := by
    rw [hZ,hah]
    nlinarith [sq_nonneg h]
  have hZhi : -chord posQ (affine a b) 2 ≤ 100000*b^2 := by
    rw [hZ,hah]
    nlinarith [sq_nonneg h]
  have hZp : 0 < -chord posQ (affine a b) 2 := hb20.trans_le hZlo
  have hXe : lower posQ a b = chord posQ (affine a b) 0 /
      (-chord posQ (affine a b) 2) := by simp [lower,div_neg,neg_div]
  have hYe : upper posQ a b = chord posQ (affine a b) 1 /
      (-chord posQ (affine a b) 2) := by simp [upper,div_neg,neg_div]
  refine ⟨hLp.ne',by linarith,hYe ▸ div_pos hYp hZp,?_,?_⟩
  · rw [hXe]
    apply (le_div_iff₀ hZp).mpr
    nlinarith
  · rw [hXe]
    apply (div_le_iff₀ hZp).mpr
    nlinarith

lemma small_input_bounds {a b : ℚ} (ha : 0<a) (hb : 0<b) (hb' : b≤1/100)
    (he : a^3-b^3=7) :
    lin negQ (affine a b) ≠ 0 ∧ chord negQ (affine a b) 2 ≠ 0 ∧
    0 < upper negQ a b ∧ 1/100000 ≤ lower negQ a b ∧ lower negQ a b ≤ 100000 := by
  have ha1 : 1≤a := by
    apply (Odd.pow_le_pow (by decide : Odd 3)).mp
    nlinarith [pow_nonneg hb.le 3]
  have ha2 : a≤2 := by
    apply (Odd.pow_le_pow (by decide : Odd 3)).mp
    have hb1 : b^3≤(1/100 : ℚ)^3 := pow_le_pow_left₀ hb.le hb' 3
    norm_num at hb1
    nlinarith
  have ha21 : 1≤a^2 := by nlinarith
  have ha24 : a^2≤4 := by nlinarith
  have hb2 : b^2≤1/10000 := by nlinarith
  have hab0 : 0≤a*b := mul_nonneg ha.le hb.le
  have hab2 : a*b≤2/100 := by nlinarith [mul_nonneg (by linarith : 0≤2-a) hb.le]
  obtain ⟨hL,hX,hY,hZ⟩ := negQ_coordinates a b
  have hLn : lin negQ (affine a b)<0 := by rw [hL]; linarith
  have hXlo : 1 ≤ -chord negQ (affine a b) 0 := by rw [hX]; nlinarith
  have hXhi : -chord negQ (affine a b) 0 ≤ 100000 := by rw [hX]; nlinarith [sq_nonneg b]
  have hYn : chord negQ (affine a b) 1<0 := by rw [hY]; nlinarith
  have hZlo : 1 ≤ chord negQ (affine a b) 2 := by rw [hZ]; nlinarith
  have hZhi : chord negQ (affine a b) 2 ≤ 100000 := by rw [hZ]; nlinarith [sq_nonneg b]
  have hZp : 0 < chord negQ (affine a b) 2 := by linarith
  refine ⟨hLn.ne,hZp.ne',div_pos (neg_pos.mpr hYn) hZp,?_,?_⟩
  · apply (le_div_iff₀ hZp).mpr
    nlinarith
  · apply (div_le_iff₀ hZp).mpr
    nlinarith



def roots : Set ℚ := {b | 0<b ∧ ∃ a : ℚ, 0<a ∧ a^3-b^3=7}

noncomputable def mate (b : ℚ) : ℚ :=
  if h : ∃ a : ℚ, 0<a ∧ a^3-b^3=7 then Classical.choose h else 0

lemma mate_spec {b : ℚ} (hb : b∈roots) :
    0 < mate b ∧ (mate b)^3-b^3=7 := by
  dsimp only [mate]
  rw [dif_pos hb.2]
  exact Classical.choose_spec hb.2

def boundedRoots : Set ℚ := {b | b∈roots ∧ 1/100000≤b ∧ b≤100000}

lemma bounded_image_infinite {S : Set ℚ} (hS : S.Infinite) (hSR : S⊆roots)
    (q : Point) (hq : form q=0)
    (hmap : ∀ b∈S, lin q (affine (mate b) b) ≠ 0 ∧
      chord q (affine (mate b) b) 2 ≠ 0 ∧
      0<upper q (mate b) b ∧
      1/100000≤lower q (mate b) b ∧ lower q (mate b) b≤100000) :
    boundedRoots.Infinite := by
  let f : ℚ → ℚ := fun b => lower q (mate b) b
  have hf : Set.InjOn f S := by
    intro b hb d hd he
    exact mapped_lower_injective q hq (mate_spec (hSR hb)).2 (mate_spec (hSR hd)).2
      (hmap b hb).1 (hmap d hd).1 (hmap b hb).2.1 (hmap d hd).2.1 he
  apply (hS.image hf).mono
  rintro _ ⟨b,hb,rfl⟩
  obtain ⟨hL,hC,ha,hlo,hhi⟩ := hmap b hb
  refine ⟨⟨lt_of_lt_of_le (by norm_num : (0 : ℚ)<1/100000) hlo,
    upper q (mate b) b,ha,?_⟩,hlo,hhi⟩
  exact mapped_identity q hq (mate_spec (hSR hb)).2 hC

/-- Infinitely many positive rational pairs with cubic difference seven
can be kept in a fixed compact range, bounded away from zero. -/
theorem bounded_roots_infinite : boundedRoots.Infinite := by
  have hR : roots.Infinite := RepeatedCubeDifferences.infinite_positive_cube_difference
  let S : Set ℚ := {b | b∈roots ∧ b≤1/100}
  let T : Set ℚ := {b | b∈roots ∧ 100≤b}
  by_cases hS : S.Infinite
  · apply bounded_image_infinite hS (fun _ h => h.1) negQ negQ_on_curve
    intro b hb
    exact small_input_bounds (mate_spec hb.1).1 hb.1.1 hb.2 (mate_spec hb.1).2
  by_cases hT : T.Infinite
  · apply bounded_image_infinite hT (fun _ h => h.1) posQ posQ_on_curve
    intro b hb
    exact large_input_bounds (mate_spec hb.1).1 hb.2 (mate_spec hb.1).2
  have hmid : (roots \ (S∪T)).Infinite :=
    hR.diff ((Set.not_infinite.mp hS).union (Set.not_infinite.mp hT))
  apply hmid.mono
  rintro b ⟨hb,hnot⟩
  have hsmall : ¬ b≤1/100 := fun h => hnot (Or.inl ⟨hb,h⟩)
  have hlarge : ¬ 100≤b := fun h => hnot (Or.inr ⟨hb,h⟩)
  exact ⟨hb,by linarith,by linarith⟩

#print axioms bounded_roots_infinite


end Erdos1206.BoundedCubeDifferences
