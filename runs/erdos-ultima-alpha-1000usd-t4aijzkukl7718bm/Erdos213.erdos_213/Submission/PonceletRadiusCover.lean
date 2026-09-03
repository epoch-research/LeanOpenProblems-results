import Submission.PonceletIntermediate

/-! Algebraic models for the first-rational-radius condition. No claims about
all rational points or about an Erdős configuration's existence are made. -/
namespace Erdos213.PonceletOctagon

def radiusQuartic (a t : ℚ) : ℚ := t^4+(4*a-2)*t^2+1

def productQuotientZero (a b x : ℚ) : ℚ :=
  (x^2+(4*a-2)*x+1)*(x^2+(4*b-2)*x+1)

def productQuotientPlus (a b x : ℚ) : ℚ := (x^2+4*a-4)*(x^2+4*b-4)
def productQuotientMinus (a b x : ℚ) : ℚ := (x^2+4*a)*(x^2+4*b)

lemma circle_parameter (s c : ℚ) (hc : c^2+s^2=1) (hc0 : 1+c ≠ 0) :
    c=(1-(s/(1+c))^2)/(1+(s/(1+c))^2) ∧
    s=2*(s/(1+c))/(1+(s/(1+c))^2) := by
  have hpos : 0<1+(s/(1+c))^2 := by positivity
  have hn : 1+(s/(1+c))^2 ≠ 0 := ne_of_gt hpos
  constructor
  · field_simp
    linear_combination (c+1)*hc
  · field_simp
    linear_combination s*hc

lemma quartic_cover_forward (q t y z : ℚ)
    (hy : y^2=radiusQuartic (q^4) t) (hz : z^2=radiusQuartic (q^2) t) :
    ((1-t^2)/(1+t^2))^2+(2*t/(1+t^2))^2=1 ∧
    (y/(1+t^2))^2+(1-q^4)*(2*t/(1+t^2))^2=1 ∧
    radiusSq (q^2) (2*t/(1+t^2)) ((1-t^2)/(1+t^2))=(z/(1+t^2))^2 := by
  have ht : 1+t^2 ≠ 0 := ne_of_gt (by positivity : 0<(1:ℚ)+t^2)
  dsimp [radiusQuartic] at hy hz
  dsimp [radiusSq]
  refine ⟨?_,?_,?_⟩
  · field_simp
    ring
  · field_simp
    linear_combination hy
  · field_simp
    linear_combination -hz

lemma quartic_cover_reverse (q t c s d e : ℚ)
    (hc : c=(1-t^2)/(1+t^2)) (hs : s=2*t/(1+t^2))
    (hd : d^2+(1-q^4)*s^2=1) (he : radiusSq (q^2) s c=e^2) :
    (d*(1+t^2))^2=radiusQuartic (q^4) t ∧
    (e*(1+t^2))^2=radiusQuartic (q^2) t := by
  have ht : 1+t^2 ≠ 0 := ne_of_gt (by positivity : 0<(1:ℚ)+t^2)
  subst c s
  dsimp [radiusSq] at he
  field_simp at hd he
  dsimp [radiusQuartic]
  constructor
  · linear_combination hd
  · linear_combination -he

/-- Every first-radius solution away from the omitted circle-chart point
has a point on the simultaneous quartic cover. -/
lemma first_radius_cover (q s c d e : ℚ) (hc : c^2+s^2=1)
    (hd : d^2+(1-q^4)*s^2=1) (he : radiusSq (q^2) s c=e^2)
    (hc0 : 1+c ≠ 0) :
    ∃ t y z : ℚ, y^2=radiusQuartic (q^4) t ∧ z^2=radiusQuartic (q^2) t := by
  obtain ⟨h1,h2⟩ := circle_parameter s c hc hc0
  exact ⟨s/(1+c),d*(1+(s/(1+c))^2),e*(1+(s/(1+c))^2),
    quartic_cover_reverse q (s/(1+c)) c s d e h1 h2 hd he⟩

lemma product_quotient_zero (a b t : ℚ) :
    productQuotientZero a b (t^2)=radiusQuartic a t*radiusQuartic b t := by
  dsimp [productQuotientZero,radiusQuartic]
  ring

lemma product_quotient_plus (a b t : ℚ) (ht : t ≠ 0) :
    productQuotientPlus a b (t+1/t)=radiusQuartic a t*radiusQuartic b t/t^4 := by
  dsimp [productQuotientPlus,radiusQuartic]
  field_simp
  ring

lemma product_quotient_minus (a b t : ℚ) (ht : t ≠ 0) :
    productQuotientMinus a b (t-1/t)=radiusQuartic a t*radiusQuartic b t/t^4 := by
  dsimp [productQuotientMinus,radiusQuartic]
  field_simp
  ring

lemma quotient_points (q t y z : ℚ) (ht : t ≠ 0)
    (hy : y^2=radiusQuartic (q^4) t) (hz : z^2=radiusQuartic (q^2) t) :
    (y*z)^2=productQuotientZero (q^4) (q^2) (t^2) ∧
    (y*z/t^2)^2=productQuotientPlus (q^4) (q^2) (t+1/t) ∧
    (y*z/t^2)^2=productQuotientMinus (q^4) (q^2) (t-1/t) := by
  rw [product_quotient_zero,product_quotient_plus _ _ _ ht,
    product_quotient_minus _ _ _ ht,← hy,← hz]
  constructor
  · ring
  constructor <;> ring

lemma minus_quotient_normalization (q u v : ℚ) (hq : q ≠ 0)
    (hv : v^2=productQuotientMinus (q^4) (q^2) u) :
    (v/(4*q^2))^2=(((u/(2*q))^2+q^2)*((u/(2*q))^2+1)) := by
  dsimp [productQuotientMinus] at hv
  field_simp
  linear_combination 16*hv

#print axioms first_radius_cover
#print axioms quartic_cover_forward
#print axioms quotient_points
#print axioms minus_quotient_normalization
end Erdos213.PonceletOctagon
