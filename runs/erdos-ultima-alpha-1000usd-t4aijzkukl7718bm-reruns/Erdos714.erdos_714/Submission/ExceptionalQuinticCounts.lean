import Submission.ExceptionalQuintic
import Submission.NoTwoCommon
import Submission.RobustPureFour

/-!
Exact finite-field root-count restrictions for the exceptional characteristic-three
quintic. These are necessary conditions on an all-root common-neighbor model,
not a graph construction or a proof of Erdős 714.
-/
noncomputable section
open Classical Finset Polynomial
set_option maxHeartbeats 4000000
namespace Erdos714ExceptionalCounts
variable {F : Type*} [Field F] [CharP F 3] [Finite F]

lemma linear_cubic_bijective (k : F) (hk : ¬ IsSquare (-k)) :
    Function.Bijective (fun x : F => x^3+k*x) := by
  have hi : Function.Injective (fun x : F => x^3+k*x) := by
    intro x y h
    have hz : (x-y)*((x-y)^2+k)=0 := by
      have h3 : (x-y)^3=x^3-y^3 := sub_pow_char x y
      linear_combination h+h3
    rcases mul_eq_zero.mp hz with hxy | hxy
    · exact sub_eq_zero.mp hxy
    · exact False.elim (hk ⟨x-y,by linear_combination -hxy⟩)
  exact ⟨hi,Finite.surjective_of_injective hi⟩

/-- The discriminant of a monic cubic, specialized to characteristic three. -/
def cubicDiscr (a b c : F) : F := a^2*b^2-b^3-a^3*c

/-- Over a finite characteristic-three field, a cubic with nonsquare
 discriminant has a rational root. No Galois-group theorem is assumed. -/
theorem cubic_has_root (a b c : F) (hD : ¬ IsSquare (cubicDiscr a b c)) :
    ∃ x : F, x^3+a*x^2+b*x+c=0 := by
  by_cases ha : a=0
  · have hb : ¬ IsSquare (-b) := by
      rintro ⟨t,ht⟩
      apply hD
      refine ⟨t^3,?_⟩
      simp only [cubicDiscr,ha,zero_pow (by decide : 2 ≠ 0),
        zero_pow (by decide : 3 ≠ 0),zero_mul,zero_sub,sub_zero]
      calc
        -b^3 = (-b)^3 := by ring
        _ = (t*t)^3 := by rw [ht]
        _ = _ := by ring
    obtain ⟨x,hx⟩ := (linear_cubic_bijective b hb).surjective (-c)
    refine ⟨x,?_⟩
    simp only [ha,zero_mul,add_zero]
    linear_combination hx
  let D := cubicDiscr a b c
  have hD0 : D ≠ 0 := by
    intro h
    apply hD
    change IsSquare D
    rw [h]
    exact ⟨0,by simp⟩
  have hk : ¬ IsSquare (-(-a^4/D)) := by
    simp only [neg_div,neg_neg]
    rintro ⟨u,hu⟩
    have hu' : a^4=u*u*D := (div_eq_iff hD0).mp hu
    have hu0 : u ≠ 0 := by
      intro hz
      rw [hz,zero_mul,zero_mul] at hu'
      exact pow_ne_zero 4 ha hu'
    apply hD
    refine ⟨a^2/u,?_⟩
    rw [← pow_two,div_pow,← pow_mul]
    apply (eq_div_iff (pow_ne_zero 2 hu0)).mpr
    convert hu'.symm using 1; ring
  obtain ⟨z,hz⟩ := (linear_cubic_bijective (-a^4/D) hk).surjective (a^3/D)
  have hz0 : z ≠ 0 := by
    intro h
    change z^3+(-a^4/D)*z=a^3/D at hz
    rw [h,zero_pow (by decide : 3 ≠ 0),mul_zero,add_zero] at hz
    exact div_ne_zero (pow_ne_zero 3 ha) hD0 hz.symm
  have heq : D*z^3-a^4*z-a^3=0 := by
    have h := congrArg (fun x : F => x*D) hz
    field_simp [hD0] at h
    linear_combination h
  have hid : a^3*z^3*((z⁻¹+b/a)^3+a*(z⁻¹+b/a)^2+b*(z⁻¹+b/a)+c) =
      a^3+a^4*z-D*z^3 := by
    dsimp [D,cubicDiscr]
    field_simp
    apply sub_eq_zero.mp
    ring_nf
    reduce_mod_char!
  refine ⟨z⁻¹+b/a,?_⟩
  apply (mul_eq_zero.mp (show (a^3*z^3)*
      ((z⁻¹+b/a)^3+a*(z⁻¹+b/a)^2+b*(z⁻¹+b/a)+c)=0 from ?_)).resolve_left
    (mul_ne_zero (pow_ne_zero 3 ha) (pow_ne_zero 3 hz0))
  rw [hid]
  linear_combination -heq


def coeffA (t : F) : F := -(2*t^4+t^3+t^2+2*t+1)
def coeffB (t : F) : F := t^3*(t+1)^3*(2*t+1)
def residual (t x : F) : F :=
  x^3+(1-t)*x^2+(t*(t-1)^2*(t+1))*x-t^2*(t+1)^2*(t-1)

omit [Finite F] in
lemma normalized_factor (t x : F) :
    x^5+coeffA t*x^3+coeffB t=(x-t)*(x-t-1)*residual t x := by
  dsimp [coeffA,coeffB,residual]
  apply sub_eq_zero.mp
  ring_nf
  reduce_mod_char!

omit [Finite F] in
lemma residual_discr (t : F) :
    cubicDiscr (1-t) (t*(t-1)^2*(t+1)) (-t^2*(t+1)^2*(t-1)) =
      -(t*(t-1)*(t+1))^4 := by
  dsimp [cubicDiscr]
  apply sub_eq_zero.mp
  ring_nf
  reduce_mod_char!

omit [Finite F] in
lemma residual_at_roots (t : F) : residual t t=t^4 ∧ residual t (t+1)=-(t+1)^4 := by
  constructor <;> dsimp [residual]
  all_goals apply sub_eq_zero.mp
  all_goals ring_nf
  all_goals reduce_mod_char!

omit [Finite F] in
lemma normalized_coefficients (a b t : F)
    (h0 : t^5+a*t^3+b=0) (h1 : (t+1)^5+a*(t+1)^3+b=0) :
    a=coeffA t ∧ b=coeffB t := by
  have ha : a=coeffA t := by
    dsimp [coeffA]
    apply sub_eq_zero.mp
    linear_combination (norm := ring_nf) h1-h0
    reduce_mod_char!
  refine ⟨ha,?_⟩
  rw [ha] at h0
  dsimp [coeffA] at h0
  dsimp [coeffB]
  linear_combination (norm := ring_nf) h0
  reduce_mod_char!

lemma normalized_third (t : F) (hns : ¬ IsSquare (-1 : F)) :
    ∃ x : F, x ≠ t ∧ x ≠ t+1 ∧ x^5+coeffA t*x^3+coeffB t=0 := by
  have h3 : (3 : F)=0 := CharP.cast_eq_zero F 3
  have hneg : (-1 : F) ≠ 1 := by
    intro h
    have h0 : (1 : F)=0 := by linear_combination h+h3
    exact one_ne_zero h0
  by_cases ht0 : t=0
  · subst t
    refine ⟨-1,by simp,by simpa using hneg,?_⟩
    norm_num [coeffA,coeffB]
  by_cases ht1 : t=1
  · subst t
    refine ⟨0,zero_ne_one,?_,?_⟩
    · intro h
      have h0 : (1 : F)=0 := by linear_combination h3+h
      exact one_ne_zero h0
    · norm_num [coeffA,coeffB]
      reduce_mod_char!
  by_cases htm : t = -1
  · subst t
    refine ⟨1,Ne.symm hneg,by simp,?_⟩
    norm_num [coeffA,coeffB]
  have hd : t*(t-1)*(t+1) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero ht0 (sub_ne_zero.mpr ht1))
      (by intro h; apply htm; linear_combination h)
  have hD : ¬ IsSquare (cubicDiscr (1-t) (t*(t-1)^2*(t+1)) (-t^2*(t+1)^2*(t-1))) := by
    rw [residual_discr]
    rintro ⟨v,hv⟩
    apply hns
    refine ⟨v/(t*(t-1)*(t+1))^2,?_⟩
    rw [← pow_two,div_pow,← pow_mul]
    apply (eq_div_iff (pow_ne_zero 4 hd)).mpr
    convert hv using 1 <;> ring
  obtain ⟨x,hx⟩ := cubic_has_root (1-t) (t*(t-1)^2*(t+1)) (-t^2*(t+1)^2*(t-1)) hD
  have hres : residual t x=0 := by dsimp [residual]; linear_combination hx
  refine ⟨x,?_,?_,?_⟩
  · intro h
    rw [h,(residual_at_roots t).1] at hres
    exact pow_ne_zero 4 ht0 hres
  · intro h
    rw [h,(residual_at_roots t).2,neg_eq_zero] at hres
    exact pow_ne_zero 4 (by intro h; apply htm; linear_combination h) hres
  · rw [normalized_factor,hres,mul_zero]

omit [Finite F] [CharP F 3] in
lemma scaled_eval (a b d x : F) (hd : d ≠ 0) :
    d^5*(x^5+(a/d^2)*x^3+b/d^5)=(d*x)^5+a*(d*x)^3+b := by
  field_simp

/-- Two distinct roots force a third distinct root, including constant term zero. -/
theorem third_root (a b r s : F) (hrs : r ≠ s)
    (hr : r^5+a*r^3+b=0) (hs : s^5+a*s^3+b=0) (hns : ¬ IsSquare (-1 : F)) :
    ∃ u : F, u ≠ r ∧ u ≠ s ∧ u^5+a*u^3+b=0 := by
  let d := r-s
  have hd : d ≠ 0 := sub_ne_zero.mpr hrs
  let t := s/d
  have hs' : d*t=s := by dsimp [t]; exact mul_div_cancel₀ _ hd
  have hr' : d*(t+1)=r := by rw [mul_add,hs',mul_one]; dsimp [d]; ring
  have h0 : t^5+(a/d^2)*t^3+b/d^5=0 := by
    apply (mul_eq_zero.mp (show d^5*(t^5+(a/d^2)*t^3+b/d^5)=0 from ?_)).resolve_left
      (pow_ne_zero 5 hd)
    rw [scaled_eval _ _ _ _ hd,hs',hs]
  have h1 : (t+1)^5+(a/d^2)*(t+1)^3+b/d^5=0 := by
    apply (mul_eq_zero.mp (show d^5*((t+1)^5+(a/d^2)*(t+1)^3+b/d^5)=0 from ?_)).resolve_left
      (pow_ne_zero 5 hd)
    rw [scaled_eval _ _ _ _ hd,hr',hr]
  obtain ⟨hA,hB⟩ := normalized_coefficients (a/d^2) (b/d^5) t h0 h1
  obtain ⟨x,hxt,hxt1,hx⟩ := normalized_third t hns
  refine ⟨d*x,?_,?_,?_⟩
  · intro h
    exact hxt1 (mul_left_cancel₀ hd (h.trans hr'.symm))
  · intro h
    exact hxt (mul_left_cancel₀ hd (h.trans hs'.symm))
  · rw [← scaled_eval _ _ _ _ hd,hA,hB,hx,mul_zero]

/-- The entire rational root set has cardinality zero, one, or three. -/
theorem root_count (a b : F) (hns : ¬ IsSquare (-1 : F)) :
    (Erdos714Exceptional.quintic a b).roots.toFinset.card=0 ∨
    (Erdos714Exceptional.quintic a b).roots.toFinset.card=1 ∨
    (Erdos714Exceptional.quintic a b).roots.toFinset.card=3 := by
  let T := (Erdos714Exceptional.quintic a b).roots.toFinset
  have hm (x : F) : x ∈ T ↔ x^5+a*x^3+b=0 := by
    dsimp only [T]
    rw [Multiset.mem_toFinset,Polynomial.mem_roots (Erdos714Exceptional.quintic_monic a b).ne_zero]
    simp [Polynomial.IsRoot,Erdos714Exceptional.quintic]
  have hle : T.card ≤ 3 := Erdos714Exceptional.distinct_roots_le_three a b hns
  have hn : T.card ≠ 2 := by
    intro h2
    obtain ⟨r,s,hrs,hT⟩ := Finset.card_eq_two.mp h2
    have hr : r ∈ T := by simp [hT]
    have hs : s ∈ T := by simp [hT]
    obtain ⟨u,hur,hus,hu⟩ := third_root a b r s hrs ((hm r).mp hr) ((hm s).mp hs) hns
    have hum : u ∈ T := (hm u).mpr hu
    simp only [hT,mem_insert,mem_singleton,hur,hus,or_self] at hum
  change T.card=0 ∨ T.card=1 ∨ T.card=3
  omega


abbrev roots (a b : F) : Finset F := (Erdos714Exceptional.quintic a b).roots.toFinset

omit [Finite F] in
lemma mem_roots (a b x : F) : x ∈ roots a b ↔ x^5+a*x^3+b=0 := by
  rw [roots,Multiset.mem_toFinset,Polynomial.mem_roots (Erdos714Exceptional.quintic_monic a b).ne_zero]
  simp [Polynomial.IsRoot,Erdos714Exceptional.quintic]

omit [Finite F] in
lemma two_root_parameters (r s : F) (hrs : r ≠ s) :
    ∃ a b : F, r ∈ roots a b ∧ s ∈ roots a b := by
  have hd : r^3-s^3 ≠ 0 := by rw [← sub_pow_char]; exact pow_ne_zero 3 (sub_ne_zero.mpr hrs)
  let a := -(r^5-s^5)/(r^3-s^3)
  refine ⟨a,-r^5-a*r^3,(mem_roots _ _ _).mpr (by ring),?_⟩
  apply (mem_roots _ _ _).mpr
  dsimp [a]
  field_simp
  ring

omit [Finite F] in
lemma parameters_unique (a b c d r s : F) (hrs : r ≠ s)
    (hr : r ∈ roots a b) (hs : s ∈ roots a b)
    (hr' : r ∈ roots c d) (hs' : s ∈ roots c d) : a=c ∧ b=d := by
  rw [mem_roots] at hr hs hr' hs'
  have hd : r^3-s^3 ≠ 0 := by rw [← sub_pow_char]; exact pow_ne_zero 3 (sub_ne_zero.mpr hrs)
  have h : (a-c)*(r^3-s^3)=0 := by linear_combination hr-hs-hr'+hs'
  have ha : a=c := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hd)
  refine ⟨ha,?_⟩
  rw [ha] at hr
  linear_combination hr-hr'

variable [Fintype F]

def rootProjection (p : Σ ab : F × F, roots ab.1 ab.2) : F × F := (p.1.1,p.2.val)

omit [Finite F] [Fintype F] in
lemma rootProjection_bijective : Function.Bijective (rootProjection (F := F)) := by
  constructor
  · rintro ⟨⟨a,b⟩,⟨x,hx⟩⟩ ⟨⟨c,d⟩,⟨y,hy⟩⟩ h
    have hac : a=c := congrArg Prod.fst h
    have hxy : x=y := congrArg Prod.snd h
    subst c
    subst y
    have hbd : b=d := by
      rw [mem_roots] at hx hy
      linear_combination hx-hy
    subst d
    rfl
  · rintro ⟨a,x⟩
    refine ⟨⟨(a,-x^5-a*x^3),⟨x,(mem_roots _ _ _).mpr (by ring)⟩⟩,rfl⟩

omit [Finite F] in
lemma first_moment : (∑ ab : F × F, (roots ab.1 ab.2).card)=Fintype.card F^2 := by
  have h := Fintype.card_congr (Equiv.ofBijective (rootProjection (F := F)) rootProjection_bijective)
  simpa only [Fintype.card_sigma,Fintype.card_coe,Fintype.card_prod,pow_two] using h

def pairProjection (p : Σ ab : F × F, Fin 2 ↪ roots ab.1 ab.2) : Fin 2 ↪ F :=
  p.2.trans (Function.Embedding.subtype _)

omit [Finite F] [Fintype F] in
lemma pairProjection_bijective : Function.Bijective (pairProjection (F := F)) := by
  constructor
  · rintro ⟨⟨a,b⟩,f⟩ ⟨⟨c,d⟩,g⟩ h
    have he (i : Fin 2) : (f i).val=(g i).val := congrArg (fun e : Fin 2 ↪ F => e i) h
    have hne : (f 0).val ≠ (f 1).val := by
      intro h01
      have hh := f.injective (Subtype.ext h01)
      exact (by decide : (0 : Fin 2) ≠ 1) hh
    have hr' : (f 0).val ∈ roots c d := by rw [he 0]; exact (g 0).property
    have hs' : (f 1).val ∈ roots c d := by rw [he 1]; exact (g 1).property
    obtain ⟨hac,hbd⟩ := parameters_unique a b c d _ _ hne
      (f 0).property (f 1).property hr' hs'
    subst c
    subst d
    have hfg : f=g := by ext i; exact he i
    subst g
    rfl
  · intro e
    have hne : e 0 ≠ e 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (e.injective h)
    obtain ⟨a,b,ha,hb⟩ := two_root_parameters (e 0) (e 1) hne
    have hm (i : Fin 2) : e i ∈ roots a b := by fin_cases i <;> assumption
    let f : Fin 2 ↪ roots a b :=
      ⟨fun i => ⟨e i,hm i⟩,fun i j h => e.injective (congrArg Subtype.val h)⟩
    exact ⟨⟨(a,b),f⟩,by ext i; rfl⟩

omit [Finite F] in
lemma second_factorial_moment :
    (∑ ab : F × F, (roots ab.1 ab.2).card.descFactorial 2)=
      (Fintype.card F).descFactorial 2 := by
  have h := Fintype.card_congr (Equiv.ofBijective (pairProjection (F := F)) pairProjection_bijective)
  simpa only [Fintype.card_sigma,Fintype.card_embedding_eq,Fintype.card_fin,Fintype.card_coe] using h

def countParameters (k : ℕ) : ℕ :=
  (univ.filter (fun ab : F × F => (roots ab.1 ab.2).card=k)).card

/-- Exact distribution over the ENTIRE two-parameter polynomial family.
In particular, counts one and three both have positive limiting density. -/
theorem parameter_distribution (hns : ¬ IsSquare (-1 : F)) :
    countParameters (F := F) 0=2*countParameters (F := F) 3 ∧
    2*countParameters (F := F) 1=Fintype.card F*(Fintype.card F+1) ∧
    6*countParameters (F := F) 3=Fintype.card F*(Fintype.card F-1) := by
  have htot : countParameters (F := F) 0+countParameters (F := F) 1+
      countParameters (F := F) 3=Fintype.card F^2 := by
    simp only [countParameters,card_filter,← sum_add_distrib]
    calc
      _ = ∑ _ab : F × F, 1 := by
        apply sum_congr rfl
        intro ab _
        rcases root_count ab.1 ab.2 hns with h | h | h <;> simp only [roots,h] <;> decide
      _ = _ := by simp [pow_two]
  have h1 : countParameters (F := F) 1+3*countParameters (F := F) 3=Fintype.card F^2 := by
    rw [← first_moment (F := F)]
    simp only [countParameters,card_filter,mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro ab _
    rcases root_count ab.1 ab.2 hns with h | h | h <;> simp only [roots,h] <;> decide
  have h2 : 6*countParameters (F := F) 3=(Fintype.card F).descFactorial 2 := by
    rw [← second_factorial_moment (F := F)]
    simp only [countParameters,card_filter,mul_sum]
    apply sum_congr rfl
    intro ab _
    rcases root_count ab.1 ab.2 hns with h | h | h <;> simp only [roots,h] <;> decide
  have h2' : 6*countParameters (F := F) 3=Fintype.card F*(Fintype.card F-1) := by
    simpa [Nat.descFactorial_succ,Nat.mul_comm] using h2
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have hq' := Nat.sub_add_cancel hq
  refine ⟨by omega,?_,h2'⟩
  nlinarith



/-- Division form of the exact parameter counts. -/
theorem parameter_counts (hns : ¬ IsSquare (-1 : F)) :
    countParameters (F := F) 0=Fintype.card F*(Fintype.card F-1)/3 ∧
    countParameters (F := F) 1=Fintype.card F*(Fintype.card F+1)/2 ∧
    countParameters (F := F) 3=Fintype.card F*(Fintype.card F-1)/6 := by
  obtain ⟨h0,h1,h3⟩ := parameter_distribution hns
  omega

omit [Fintype F] in
/-- The three-root polynomials form a Steiner triple system: every pair
of distinct field elements belongs to exactly one of these triples. -/
theorem steiner_triples (hns : ¬ IsSquare (-1 : F)) (r s : F) (hrs : r ≠ s) :
    ∃! ab : {p : F × F // (roots p.1 p.2).card=3},
      r ∈ roots ab.val.1 ab.val.2 ∧ s ∈ roots ab.val.1 ab.val.2 := by
  obtain ⟨a,b,hr,hs⟩ := two_root_parameters r s hrs
  have hlow : 2 ≤ (roots a b).card := by
    have hp : {r,s} ⊆ roots a b := by simp only [insert_subset_iff,singleton_subset_iff]; exact ⟨hr,hs⟩
    have h := card_le_card hp
    simpa only [card_pair hrs] using h
  have hc : (roots a b).card=3 := by
    have h := root_count a b hns
    change (roots a b).card=0 ∨ (roots a b).card=1 ∨ (roots a b).card=3 at h
    omega
  refine ⟨⟨(a,b),hc⟩,⟨hr,hs⟩,?_⟩
  rintro ⟨⟨c,d⟩,hcd⟩ ⟨hr',hs'⟩
  obtain ⟨hac,hbd⟩ := parameters_unique a b c d r s hrs hr hs hr' hs'
  exact Subtype.ext (Prod.ext hac.symm hbd.symm)

section Model
open SimpleGraph Erdos714Packing Erdos714RobustPureFour
variable {B V : Type*} [Fintype B] [Fintype V]

/-- This hypothesis identifies the number of common neighbors with the
ENTIRE root set, not an arbitrary subset or an injection into that set. -/
def FullRootModel (S : B → Finset V) : Prop :=
  ∀ T : Finset V, T.card=4 → ∃ a b : F, (blocksContaining S T).card=(roots a b).card

omit [Fintype F] [Fintype V] in
lemma model_counts (S : B → Finset V) (hmodel : FullRootModel (F := F) S)
    (hns : ¬ IsSquare (-1 : F)) (T : Finset V) (hT : T.card=4) :
    (blocksContaining S T).card=0 ∨ (blocksContaining S T).card=1 ∨
      (blocksContaining S T).card=3 := by
  obtain ⟨a,b,h⟩ := hmodel T hT
  rw [h]
  exact root_count a b hns

omit [Fintype F] in
lemma model_free (S : B → Finset V) (hmodel : FullRootModel (F := F) S)
    (hns : ¬ IsSquare (-1 : F)) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S) := by
  apply (free_iff_common_card S (by decide)).mpr
  apply (common_card_dual_iff S (by decide)).mpr
  intro g
  rw [common_dual_eq]
  have h := model_counts S hmodel hns (univ.map g) (by simp)
  omega

omit [Fintype F] in
/-- The exact no-two arithmetic gives the previously proved pair-intersection
alternative; this does not by itself imply a subcritical edge bound. -/
theorem model_pair_alternative (S : B → Finset V)
    (hmodel : FullRootModel (F := F) S) (hns : ¬ IsSquare (-1 : F))
    (b c : B) (hbc : b ≠ c) :
    ((S b ∩ S c).card-2)^2 ≤ 4*Fintype.card B ∨
      ((blocksContaining S (S b ∩ S c)).card=3 ∧
        ∃ d : B, d ≠ b ∧ d ≠ c ∧ S b ∩ S c ⊆ S d ∧
          ∀ a, ¬ S b ∩ S c ⊆ S a → ((S b ∩ S c) ∩ S a).card ≤ 3) := by
  apply Erdos714NoTwoCommon.pair_intersection_alternative S ?_ ?_ b c hbc
  · intro T hT
    have h := model_counts S hmodel hns T hT
    omega
  · intro T hT
    have h := model_counts S hmodel hns T hT
    omega

def singletonQuads (S : B → Finset V) : Finset (Quad V) :=
  univ.filter (fun p => (quadSet p).card=4 ∧ count S (quadSet p)=1)

omit [Fintype F] in
lemma model_impurity (S : B → Finset V) (hmodel : FullRootModel (F := F) S)
    (hns : ¬ IsSquare (-1 : F)) : impurity S=(singletonQuads S).card := by
  rw [impurity_eq_card]
  congr 1
  ext p
  simp only [impureQuads,singletonQuads,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨h4,hc⟩
    have h := model_counts S hmodel hns (quadSet p) h4
    change count S (quadSet p)=0 ∨ count S (quadSet p)=1 ∨ count S (quadSet p)=3 at h
    exact ⟨h4,by omega⟩
  · rintro ⟨h4,hc⟩
    exact ⟨h4,Or.inl hc⟩

omit [Fintype F] in
/-- Every critical all-root quintic model needs a positive density of
singleton common-neighbor fibers. There are no regularity hypotheses. -/
theorem critical_singletons (S : B → Finset V)
    (hmodel : FullRootModel (F := F) S) (hns : ¬ IsSquare (-1 : F))
    (q C : ℕ) (hC : 1 ≤ C) (hq : 82944*C^8 ≤ q)
    (hB : Fintype.card B ≤ q^4) (hV : Fintype.card V ≤ q^4)
    (he : q^7 ≤ C*(∑ b, (S b).card)) :
    q^16 ≤ 64*C^8*(singletonQuads S).card := by
  have h := critical_impurity S q C hC hq hB hV (model_free S hmodel hns) he
  rwa [model_impurity S hmodel hns] at h

end Model

#print axioms parameter_counts
#print axioms steiner_triples
#print axioms model_free
#print axioms model_pair_alternative
#print axioms critical_singletons
#print axioms first_moment
#print axioms second_factorial_moment
#print axioms parameter_distribution
#print axioms third_root
#print axioms root_count
#print axioms linear_cubic_bijective
#print axioms cubic_has_root
end Erdos714ExceptionalCounts
