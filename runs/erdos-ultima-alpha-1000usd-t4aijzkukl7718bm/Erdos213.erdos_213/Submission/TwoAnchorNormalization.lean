import Submission.TwoAnchorGeometry

/-! Normalizing a first-order collision of two quadratic rational-distance
motions. These hypotheses are identities over a rational-function field;
this file makes no claim about arbitrary individual integral-distance sets. -/
namespace Erdos213.TwoAnchorNormalization
open EuclideanGeometry Polynomial QuadraticMotion GeneralQuadraticType TwoAnchorGeometry
noncomputable section
set_option maxHeartbeats 2000000

lemma Compatible.square_polynomial (a b c : ℂ) (ha : a≠0) (h : Compatible a b c) :
    IsSquare (squaredNorm a b c) := by
  rcases h with hd | ⟨hb,hc⟩
  · let q : ℂ := b/(2*a)
    let P : ℝ[X] := C 1+C (2*q.re)*X+C (Complex.normSq q)*X^2
    have hP (t : ℝ) : P.eval t=‖1+q*t‖^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      simp only [P,eval_add,eval_mul,eval_C,eval_X,eval_pow,Complex.add_re,
        Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.one_re,Complex.one_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.normSq_apply]
      ring
    refine ⟨C ‖a‖*P,?_⟩
    apply Polynomial.funext
    intro t
    rw [squaredNorm_eval,repeated_root_form a b c ha hd t]
    simp only [eval_mul,eval_C,hP,norm_mul,norm_pow]
    dsimp only [q]
    ring
  · obtain ⟨u,v,he⟩ := constant_direction a b c ha hb hc
    refine ⟨C ‖a‖*CircleLineRigidity.quad v u 1,?_⟩
    apply Polynomial.funext
    intro t
    rw [squaredNorm_eval,he t,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    simp only [eval_mul,eval_C,CircleLineRigidity.quad,eval_add,eval_pow,eval_X]
    ring

lemma Compatible.square_ratFunc (a b c : ℂ) (ha : a≠0) (h : Compatible a b c) :
    IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (squaredNorm a b c)) := by
  obtain ⟨p,hp⟩ := Compatible.square_polynomial a b c ha h
  exact ⟨algebraMap ℝ[X] (RatFunc ℝ) p,by rw [hp,map_mul]⟩

/-- Real Möbius reparameterization preserves the quadratic square-type
classification. The discriminant is unchanged. -/
lemma Compatible.reparam (a b c : ℂ) (r : ℝ) (h : Compatible a b c) :
    Compatible a (b-2*r*a) (c-r*b+(r : ℂ)^2*a) := by
  rcases h with h | ⟨h,h'⟩
  · left
    linear_combination h
  · right
    simp only [cross,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.re_ofNat,Complex.im_ofNat,pow_two] at h h' ⊢
    constructor
    · linear_combination h
    · linear_combination h'-r*h

lemma reparam_identity (a b c : ℂ) (r t : ℝ) (ht : 1+r*t≠0) :
    ((1+r*t : ℝ) : ℂ)^2*
      (a+(b-2*r*a)*(t/(1+r*t) : ℝ)+
        (c-r*b+(r : ℂ)^2*a)*(t/(1+r*t) : ℝ)^2)=a+b*t+c*t^2 := by
  have ht' : (1+(r : ℂ)*t)≠0 := by exact_mod_cast ht
  push_cast
  field_simp
  ring

lemma collinear_similarity (z w : ℂ) {S : Set ℂ} (h : Collinear ℝ S) :
    Collinear ℝ ((fun p => z*p+w) '' S) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h ⊢
  obtain ⟨o,v,hv⟩ := h
  refine ⟨z*o+w,z*v,?_⟩
  rintro _ ⟨p,hp,rfl⟩
  obtain ⟨r,hr⟩ := hv p hp
  refine ⟨r,?_⟩
  rw [hr]
  simp only [vadd_eq_add,Complex.real_smul]
  ring

lemma cospherical_similarity (z w : ℂ) {S : Set ℂ} (h : Cospherical S) :
    Cospherical ((fun p => z*p+w) '' S) := by
  obtain ⟨o,r,hr⟩ := h
  refine ⟨z*o+w,‖z‖*r,?_⟩
  rintro _ ⟨p,hp,rfl⟩
  rw [dist_eq_norm,show z*p+w-(z*o+w)=z*(p-o) by ring,norm_mul,←dist_eq_norm,hr p hp]

/-- General-position conditions with two arbitrary complex anchors. -/
structure AnchoredGP {ι : Type*} (u v : ℂ) (p : ι → ℂ) : Prop where
  injective : Function.Injective p
  anchor_line : ∀ i, ¬Collinear ℝ {u,v,p i}
  left_line : ∀ i j, i≠j → ¬Collinear ℝ {u,p i,p j}
  right_line : ∀ i j, i≠j → ¬Collinear ℝ {v,p i,p j}
  outer_line : ∀ i j k, i≠j → i≠k → j≠k → ¬Collinear ℝ {p i,p j,p k}
  circle : ∀ i j, i≠j → ¬Cospherical ({u,v,p i,p j} : Set ℂ)

lemma AnchoredGP.pullback {ι : Type*} (u v z w : ℂ) (p : ι → ℂ)
    (h : AnchoredGP (z*u+w) (z*v+w) (fun i => z*p i+w)) : AnchoredGP u v p := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i j hij
    exact h.injective (by rw [hij])
  · intro i hc
    apply h.anchor_line i
    simpa only [Set.image_insert_eq,Set.image_singleton] using collinear_similarity z w hc
  · intro i j hij hc
    apply h.left_line i j hij
    simpa only [Set.image_insert_eq,Set.image_singleton] using collinear_similarity z w hc
  · intro i j hij hc
    apply h.right_line i j hij
    simpa only [Set.image_insert_eq,Set.image_singleton] using collinear_similarity z w hc
  · intro i j k hij hik hjk hc
    apply h.outer_line i j k hij hik hjk
    simpa only [Set.image_insert_eq,Set.image_singleton] using collinear_similarity z w hc
  · intro i j hij hc
    apply h.circle i j hij
    simpa only [Set.image_insert_eq,Set.image_singleton] using cospherical_similarity z w hc

lemma AnchoredGP.to_splitting {ι : Type*} (t : ℝ) (p : ι → ℂ)
    (h : AnchoredGP 0 t p) : SplittingGP t p :=
  ⟨h.injective,h.anchor_line,h.left_line,h.right_line,h.outer_line,h.circle⟩

lemma AnchoredGP.distinct_anchors {ι : Type*} [Nonempty ι] (u v : ℂ) (p : ι → ℂ)
    (h : AnchoredGP u v p) : u≠v := by
  intro hh
  obtain ⟨i⟩ := ‹Nonempty ι›
  apply h.anchor_line i
  rw [hh]
  simpa using collinear_pair ℝ v (p i)

/-- A version of the normalized obstruction using its purely algebraic
square-type conditions. -/
lemma no_five_exterior_types (a b c : Fin 5 → ℂ)
    (ha : ∀ i, a i≠0) (hinit : Function.Injective a)
    (h0 : ∀ i, Compatible (a i) (b i) (c i))
    (h1 : ∀ i, Compatible (a i) (b i-1) (c i))
    (hp : ∀ i j, i≠j → Compatible (a i-a j) (b i-b j) (c i-c j)) (t : ℝ) :
    ¬SplittingGP t (fun i => a i+b i*t+c i*t^2) :=
  no_five_exterior_quadratics a b c ha hinit
    (fun i => Compatible.square_ratFunc _ _ _ (ha i) (h0 i))
    (fun i => Compatible.square_ratFunc _ _ _ (ha i) (h1 i))
    (fun i j hij => Compatible.square_ratFunc _ _ _ (sub_ne_zero.mpr (hinit.ne hij)) (hp i j hij)) t

lemma SplittingGP.to_anchored {ι : Type*} (t : ℝ) (p : ι → ℂ)
    (h : SplittingGP t p) : AnchoredGP 0 t p :=
  ⟨h.injective,h.anchor_line,h.left_line,h.right_line,h.outer_line,h.circle⟩

/-- A curved splitting anchor `t+r*t²` is reduced to the linear anchor by
`τ=t/(1+r*t)` and common homothety `(1+r*t)²`. Its exceptional parameter
makes the two source anchors coincide, hence is incompatible with GP. -/
lemma no_five_curved_anchor_types (a b c : Fin 5 → ℂ) (r : ℝ)
    (ha : ∀ i, a i≠0) (hinit : Function.Injective a)
    (h0 : ∀ i, Compatible (a i) (b i) (c i))
    (h1 : ∀ i, Compatible (a i) (b i-1) (c i-r))
    (hp : ∀ i j, i≠j → Compatible (a i-a j) (b i-b j) (c i-c j)) (t : ℝ) :
    ¬SplittingGP (t+r*t^2) (fun i => a i+b i*t+c i*t^2) := by
  intro hg
  have ht : 1+r*t≠0 := by
    intro hh
    have hz : t+r*t^2=0 := by linear_combination t*hh
    have hne := AnchoredGP.distinct_anchors _ _ _ (SplittingGP.to_anchored _ _ hg)
    exact hne (by rw [hz]; simp)
  let B : Fin 5 → ℂ := fun i => b i-2*r*a i
  let C : Fin 5 → ℂ := fun i => c i-r*b i+(r : ℂ)^2*a i
  have h0' : ∀ i, Compatible (a i) (B i) (C i) := fun i =>
    Compatible.reparam (a i) (b i) (c i) r (h0 i)
  have h1' : ∀ i, Compatible (a i) (B i-1) (C i) := by
    intro i
    have hh := Compatible.reparam (a i) (b i-1) (c i-r) r (h1 i)
    convert hh using 1 <;> dsimp only [B,C] <;> ring
  have hp' : ∀ i j, i≠j → Compatible (a i-a j) (B i-B j) (C i-C j) := by
    intro i j hij
    have hh := Compatible.reparam (a i-a j) (b i-b j) (c i-c j) r (hp i j hij)
    convert hh using 1 <;> dsimp only [B,C] <;> ring
  let τ : ℝ := t/(1+r*t)
  let sc : ℂ := ((1+r*t : ℝ) : ℂ)^2
  have hanchor : sc*(τ : ℂ)=(t+r*t^2 : ℝ) := by
    have hh : (1+r*t)^2*(t/(1+r*t))=t+r*t^2 := by field_simp
    dsimp only [sc,τ]
    exact_mod_cast hh
  have hpoints : (fun i => sc*(a i+B i*τ+C i*(τ : ℂ)^2)+0)=
      (fun i => a i+b i*t+c i*t^2) := by
    funext i
    simpa only [B,C,τ,sc,add_zero] using reparam_identity (a i) (b i) (c i) r t ht
  apply no_five_exterior_types a B C ha hinit h0' h1' hp' τ
  apply AnchoredGP.to_splitting
  apply AnchoredGP.pullback 0 τ sc 0
  rw [mul_zero,add_zero,hanchor,add_zero,hpoints]
  exact SplittingGP.to_anchored _ _ hg

lemma no_first_order_collision_types (a₀ b₀ c₀ b₁ c₁ : ℂ) (a b c : Fin 5 → ℂ)
    (hw : b₁-b₀≠0) (hc : cross (b₁-b₀) (c₁-c₀)=0)
    (ha : ∀ i, a i≠a₀) (hinit : Function.Injective a)
    (h0 : ∀ i, Compatible (a i-a₀) (b i-b₀) (c i-c₀))
    (h1 : ∀ i, Compatible (a i-a₀) (b i-b₁) (c i-c₁))
    (hp : ∀ i j, i≠j → Compatible (a i-a j) (b i-b j) (c i-c j)) (t : ℝ) :
    ¬AnchoredGP (a₀+b₀*t+c₀*t^2) (a₀+b₁*t+c₁*t^2)
      (fun i => a i+b i*t+c i*t^2) := by
  intro hg
  obtain ⟨r,hr⟩ := (cross_zero_iff_real_mul hw).mp hc
  let w : ℂ := b₁-b₀
  let A : Fin 5 → ℂ := fun i => w⁻¹*(a i-a₀)
  let B : Fin 5 → ℂ := fun i => w⁻¹*(b i-b₀)
  let C : Fin 5 → ℂ := fun i => w⁻¹*(c i-c₀)
  have hw' : w≠0 := hw
  have hA (i) : w*A i=a i-a₀ := by simp [A,hw']
  have hB (i) : w*B i=b i-b₀ := by simp [B,hw']
  have hC (i) : w*C i=c i-c₀ := by simp [C,hw']
  have hna : ∀ i, A i≠0 := by
    intro i hh
    apply ha i
    have he := hA i
    rw [hh,mul_zero] at he
    exact sub_eq_zero.mp he.symm
  have hni : Function.Injective A := by
    intro i j hij
    apply hinit
    have hh := congrArg (fun z : ℂ => w*z) hij
    change w*A i=w*A j at hh
    rw [hA,hA] at hh
    linear_combination hh
  have ht0 : ∀ i, Compatible (A i) (B i) (C i) := fun i => (h0 i).mul w⁻¹
  have ht1 : ∀ i, Compatible (A i) (B i-1) (C i-r) := by
    intro i
    have hh := (h1 i).mul w⁻¹
    have hb : w⁻¹*(b i-b₁)=B i-1 := by
      rw [show b i-b₁=(b i-b₀)-w by dsimp [w]; ring,mul_sub,inv_mul_cancel₀ hw']
    have he : c i-c₁=(c i-c₀)-(r : ℂ)*w := by
      change c₁-c₀=(r : ℂ)*w at hr
      linear_combination -hr
    have hc' : w⁻¹*(c i-c₁)=C i-r := by
      rw [he,mul_sub]
      dsimp only [C]
      congr 1
      field_simp
    rwa [hb,hc'] at hh
  have htp : ∀ i j, i≠j → Compatible (A i-A j) (B i-B j) (C i-C j) := by
    intro i j hij
    have hh := (hp i j hij).mul w⁻¹
    convert hh using 1 <;> dsimp only [A,B,C] <;> ring
  apply no_five_curved_anchor_types A B C r hna hni ht0 ht1 htp t
  apply AnchoredGP.to_splitting
  apply AnchoredGP.pullback 0 (t+r*t^2 : ℝ) w (a₀+b₀*t+c₀*t^2)
  have hanchor : w*((t+r*t^2 : ℝ) : ℂ)+(a₀+b₀*t+c₀*t^2)=a₀+b₁*t+c₁*t^2 := by
    dsimp only [w]
    push_cast
    linear_combination -(t : ℂ)^2*hr
  have hpoints : (fun i => w*(A i+B i*t+C i*t^2)+(a₀+b₀*t+c₀*t^2))=
      (fun i => a i+b i*t+c i*t^2) := by
    funext i
    linear_combination hA i+(t : ℂ)*hB i+(t : ℂ)^2*hC i
  rwa [mul_zero,zero_add,hanchor,hpoints]

/-- A first-order two-point collision cannot split into seven GP points in
a quadratic rational-function-square family. The five exterior initial
positions are required to be distinct and different from the collision
point. Higher-order collisions and additional initial collisions are not
covered by this theorem. -/
theorem no_first_order_collision (a₀ b₀ c₀ b₁ c₁ : ℂ) (a b c : Fin 5 → ℂ)
    (hw : b₁-b₀≠0) (ha : ∀ i, a i≠a₀) (hinit : Function.Injective a)
    (hcc : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (squaredNorm 0 (b₁-b₀) (c₁-c₀))))
    (h0 : ∀ i, IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (squaredNorm (a i-a₀) (b i-b₀) (c i-c₀))))
    (h1 : ∀ i, IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (squaredNorm (a i-a₀) (b i-b₁) (c i-c₁))))
    (hp : ∀ i j, i≠j → IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (squaredNorm (a i-a j) (b i-b j) (c i-c j)))) (t : ℝ) :
    ¬AnchoredGP (a₀+b₀*t+c₀*t^2) (a₀+b₁*t+c₁*t^2)
      (fun i => a i+b i*t+c i*t^2) := by
  apply no_first_order_collision_types a₀ b₀ c₀ b₁ c₁ a b c hw ?_ ha hinit ?_ ?_ ?_ t
  · apply collision_type
    simpa only [squaredNorm,normPolynomial,Complex.zero_re,Complex.zero_im] using hcc
  · intro i
    exact GeneralQuadraticType.quadratic_type_ratFunc _ _ _ (sub_ne_zero.mpr (ha i)) (h0 i)
  · intro i
    exact GeneralQuadraticType.quadratic_type_ratFunc _ _ _ (sub_ne_zero.mpr (ha i)) (h1 i)
  · intro i j hij
    exact GeneralQuadraticType.quadratic_type_ratFunc _ _ _
      (sub_ne_zero.mpr (hinit.ne hij)) (hp i j hij)

lemma repeated_radial_velocity (a b c : ℂ) (ha : a≠0)
    (hd : b^2-4*a*c=0) (hb : cross a b=0) : cross a c=0 := by
  obtain ⟨r,hr⟩ := (cross_zero_iff_real_mul ha).mp hb
  rw [hr] at hd
  have hh : a*(((r : ℂ)^2/4)*a-c)=0 := by linear_combination hd/4
  have hc : c=((r^2/4 : ℝ) : ℂ)*a := by
    have he := (mul_eq_zero.mp hh).resolve_left ha
    push_cast
    linear_combination -he
  rw [hc]
  exact cross_real_mul a (r^2/4)

/-- Two anchors whose separation begins at order two allow no nonreal
quadratic exterior motion with nonzero initial position. -/
lemma second_order_real_coefficients (a b c : ℂ) (ha : a≠0)
    (h0 : Compatible a b c) (h1 : Compatible a b (c-1)) :
    a.im=0 ∧ b.im=0 ∧ c.im=0 := by
  have hh : cross a b=0 ∧ cross a c=0 ∧ cross a (c-1)=0 := by
    rcases h0 with h0 | ⟨hb,hc⟩
    · rcases h1 with h1 | ⟨hb,hc⟩
      · exfalso
        apply ha
        linear_combination (h1-h0)/4
      · exact ⟨hb,repeated_radial_velocity a b c ha h0 hb,hc⟩
    · rcases h1 with h1 | ⟨_,hc'⟩
      · exact ⟨hb,hc,repeated_radial_velocity a b (c-1) ha h1 hb⟩
      · exact ⟨hb,hc,hc'⟩
  have hi : a.im=0 := by
    have h := hh.2.1
    have h' := hh.2.2
    simp only [cross,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im] at h h'
    linear_combination h'-h
  have hr : a.re≠0 := by
    intro hr
    exact ha (Complex.ext hr hi)
  refine ⟨hi,?_,?_⟩
  · have hb := hh.1
    simp only [cross,hi,zero_mul,sub_zero] at hb
    exact (mul_eq_zero.mp hb).resolve_left hr
  · have hc := hh.2.1
    simp only [cross,hi,zero_mul,sub_zero] at hc
    exact (mul_eq_zero.mp hc).resolve_left hr

lemma second_order_collision_collinear (a₀ b₀ c₀ c₁ a b c : ℂ)
    (hw : c₁-c₀≠0) (ha : a≠a₀)
    (h0 : Compatible (a-a₀) (b-b₀) (c-c₀))
    (h1 : Compatible (a-a₀) (b-b₀) (c-c₁)) (t : ℝ) :
    Collinear ℝ {a₀+b₀*t+c₀*t^2,a₀+b₀*t+c₁*t^2,a+b*t+c*t^2} := by
  let w : ℂ := c₁-c₀
  let A : ℂ := w⁻¹*(a-a₀)
  let B : ℂ := w⁻¹*(b-b₀)
  let C : ℂ := w⁻¹*(c-c₀)
  have hw' : w≠0 := hw
  have hA : w*A=a-a₀ := by simp [A,hw']
  have hB : w*B=b-b₀ := by simp [B,hw']
  have hC : w*C=c-c₀ := by simp [C,hw']
  have hna : A≠0 := mul_ne_zero (inv_ne_zero hw') (sub_ne_zero.mpr ha)
  have ht0 : Compatible A B C := h0.mul w⁻¹
  have ht1 : Compatible A B (C-1) := by
    have hh := h1.mul w⁻¹
    have he : w⁻¹*(c-c₁)=C-1 := by
      rw [show c-c₁=(c-c₀)-w by dsimp [w]; ring,mul_sub,inv_mul_cancel₀ hw']
    rwa [he] at hh
  have hh := second_order_real_coefficients A B C hna ht0 ht1
  have hcol : Collinear ℝ {0,((t^2 : ℝ) : ℂ),A+B*t+C*t^2} := by
    apply SquaredBimedians.collinear_of_cross
    change cross (((t^2 : ℝ) : ℂ)-0) (A+B*t+C*t^2-0)=0
    simp [cross,pow_two,Complex.mul_re,Complex.mul_im,hh.1,hh.2.1,hh.2.2]
  have hc := collinear_similarity w (a₀+b₀*t+c₀*t^2) hcol
  have he1 : w*((t^2 : ℝ) : ℂ)+(a₀+b₀*t+c₀*t^2)=a₀+b₀*t+c₁*t^2 := by
    dsimp only [w]
    push_cast
    ring
  have he2 : w*(A+B*t+C*t^2)+(a₀+b₀*t+c₀*t^2)=a+b*t+c*t^2 := by
    linear_combination hA+(t : ℂ)*hB+(t : ℂ)^2*hC
  simpa only [Set.image_insert_eq,Set.image_singleton,mul_zero,zero_add,he1,he2] using hc

/-- Complete two-point initial-collision obstruction for quadratic motions.
No first-order assumption is needed. The exterior initial positions remain
required to be distinct and different from the common anchor position.
This is a construction-method obstruction, not an upper bound for arbitrary
rational-distance sets. -/
theorem no_two_point_collision (a₀ b₀ c₀ b₁ c₁ : ℂ) (a b c : Fin 5 → ℂ)
    (ha : ∀ i, a i≠a₀) (hinit : Function.Injective a)
    (hcc : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (squaredNorm 0 (b₁-b₀) (c₁-c₀))))
    (h0 : ∀ i, IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (squaredNorm (a i-a₀) (b i-b₀) (c i-c₀))))
    (h1 : ∀ i, IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (squaredNorm (a i-a₀) (b i-b₁) (c i-c₁))))
    (hp : ∀ i j, i≠j → IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (squaredNorm (a i-a j) (b i-b j) (c i-c j)))) (t : ℝ) :
    ¬AnchoredGP (a₀+b₀*t+c₀*t^2) (a₀+b₁*t+c₁*t^2)
      (fun i => a i+b i*t+c i*t^2) := by
  by_cases hw : b₁-b₀≠0
  · exact no_first_order_collision a₀ b₀ c₀ b₁ c₁ a b c hw ha hinit hcc h0 h1 hp t
  have hb : b₁=b₀ := sub_eq_zero.mp (not_ne_iff.mp hw)
  subst b₁
  intro hg
  by_cases hc : c₁-c₀≠0
  · apply hg.anchor_line 0
    apply second_order_collision_collinear a₀ b₀ c₀ c₁ (a 0) (b 0) (c 0) hc (ha 0)
    · exact GeneralQuadraticType.quadratic_type_ratFunc _ _ _ (sub_ne_zero.mpr (ha 0)) (h0 0)
    · exact GeneralQuadraticType.quadratic_type_ratFunc _ _ _ (sub_ne_zero.mpr (ha 0)) (h1 0)
  · have he : c₁=c₀ := sub_eq_zero.mp (not_ne_iff.mp hc)
    exact AnchoredGP.distinct_anchors _ _ _ hg (by rw [he])

lemma AnchoredGP.of_set {ι : Type*} (S : Set ℂ) (u v : ℂ) (p : ι → ℂ)
    (huv : u≠v) (hinj : Function.Injective p) (hpu : ∀ i, p i≠u)
    (hpv : ∀ i, p i≠v) (huS : u∈S) (hvS : v∈S) (hpS : ∀ i, p i∈S)
    (htri : NonTrilinear S)
    (hcirc : ∀ Q : Set ℂ, Q⊆S ∧ Q.ncard=4 → ¬Cospherical Q) :
    AnchoredGP u v p := by
  refine ⟨hinj,?_,?_,?_,?_,?_⟩
  · intro i
    exact htri huS hvS (hpS i) huv (hpv i).symm (hpu i).symm
  · intro i j hij
    exact htri huS (hpS i) (hpS j) (hpu i).symm (hinj.ne hij) (hpu j).symm
  · intro i j hij
    exact htri hvS (hpS i) (hpS j) (hpv i).symm (hinj.ne hij) (hpv j).symm
  · intro i j k hij hik hjk
    exact htri (hpS i) (hpS j) (hpS k) (hinj.ne hij) (hinj.ne hjk) (hinj.ne hik)
  · intro i j hij
    apply hcirc {u,v,p i,p j}
    constructor
    · rintro z (rfl | rfl | rfl | rfl)
      · exact huS
      · exact hvS
      · exact hpS i
      · exact hpS j
    · exact Set.ncard_eq_four.mpr ⟨u,v,p i,p j,huv,(hpu i).symm,
        (hpu j).symm,(hpv i).symm,(hpv j).symm,hinj.ne hij,rfl⟩

#print axioms Compatible.square_polynomial
#print axioms no_five_curved_anchor_types
#print axioms no_first_order_collision
#print axioms second_order_collision_collinear
#print axioms no_two_point_collision
#print axioms AnchoredGP.of_set
end
end Erdos213.TwoAnchorNormalization
