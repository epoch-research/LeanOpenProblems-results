import Submission.FermatCubicLines

/-!
Linear subspaces of the rational Fermat cubic and kernel restrictions.
These are auxiliary geometric statements, not density results.
-/

namespace Erdos1206.FermatCubicSubspaces
open Polynomial Module
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Four coordinates jointly separate vectors. -/
def JointlyInjective (a b c d : V →ₗ[ℚ] ℚ) : Prop :=
  ∀ x, a x=0 → b x=0 → c x=0 → d x=0 → x=0

private noncomputable def linePoly (f : V →ₗ[ℚ] ℚ) (u v : V) : ℚ[X] := C (f u)*X+C (f v)

private lemma linePoly_degree (f : V →ₗ[ℚ] ℚ) (u v : V) :
    (linePoly f u v).natDegree ≤ 1 := by dsimp [linePoly]; compute_degree

private lemma indep_coeffs {u v : V} (hi : LinearIndependent ℚ ![u,v])
    {r s : ℚ} (he : r • u+s • v=0) : r=0 ∧ s=0 := by
  have hh := Fintype.linearIndependent_iff.mp hi ![r,s]
    (by simpa [Fin.sum_univ_two] using he)
  exact ⟨by simpa using hh 0,by simpa using hh 1⟩

private lemma linePoly_common_false {a b c d : V →ₗ[ℚ] ℚ} {u v : V}
    (hj : JointlyInjective a b c d) (hi : LinearIndependent ℚ ![u,v]) :
    ¬ FermatCubicLines.CommonFactor
      (linePoly a u v) (linePoly b u v) (linePoly c u v) (linePoly d u v) := by
  rintro ⟨q,r,s,t,w,ha,hb,hc,hd⟩
  have coeffs (f : V →ₗ[ℚ] ℚ) (z : ℚ) (he : linePoly f u v=C z*q) :
      f u=z*q.coeff 1 ∧ f v=z*q.coeff 0 := by
    have h₁ := congrArg (fun p : ℚ[X] => p.coeff 1) he
    have h₀ := congrArg (fun p : ℚ[X] => p.coeff 0) he
    simpa [linePoly,coeff_C_mul_X,coeff_C_mul] using And.intro h₁ h₀
  obtain ⟨hau,hav⟩ := coeffs a r ha
  obtain ⟨hbu,hbv⟩ := coeffs b s hb
  obtain ⟨hcu,hcv⟩ := coeffs c t hc
  obtain ⟨hdu,hdv⟩ := coeffs d w hd
  have hz : (q.coeff 0) • u+(-q.coeff 1) • v=0 := by
    apply hj
    all_goals simp only [map_add,map_smul,smul_eq_mul,hau,hav,hbu,hbv,hcu,hcv,hdu,hdv]
    all_goals ring
  obtain ⟨_,hq₁⟩ := indep_coeffs hi hz
  have hq₁' : q.coeff 1=0 := neg_eq_zero.mp hq₁
  have hu : u=0 := hj u (by simp [hau,hq₁']) (by simp [hbu,hq₁'])
    (by simp [hcu,hq₁']) (by simp [hdu,hq₁'])
  exact hi.ne_zero 0 (by simpa using hu)

private lemma pair_eval_zero {a b : V →ₗ[ℚ] ℚ} {u v : V}
    (he : linePoly a u v+linePoly b u v=0) : (a+b) u=0 := by
  have hh := congrArg (fun p : ℚ[X] => p.coeff 1) he
  simpa [linePoly,coeff_C_mul_X] using hh

/-- An injectively embedded rational subspace of dimension at least two,
contained in the Fermat cubic, is contained in one of its three rational lines. -/
theorem subspace_opposite_pairs [FiniteDimensional ℚ V]
    {a b c d : V →ₗ[ℚ] ℚ} (hj : JointlyInjective a b c d)
    (hdim : 2 ≤ finrank ℚ V) (he : ∀ x, (a x)^3+(b x)^3+(c x)^3+(d x)^3=0) :
    (a+b=0 ∧ c+d=0) ∨ (a+c=0 ∧ b+d=0) ∨ (a+d=0 ∧ b+c=0) := by
  classical
  let fs : Fin 10 → (V →ₗ[ℚ] ℚ) := ![a,b,c,d,a+b,a+c,a+d,b+c,b+d,c+d]
  let I := {i : Fin 10 // fs i ≠ 0}
  obtain ⟨u,hu⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun i : I => fs i.val) (fun i => by
      obtain ⟨x,hx⟩ := DFunLike.ne_iff.mp i.property
      exact ⟨x,by simpa using hx⟩)
  have hgen (i : Fin 10) (hz : fs i u=0) : fs i=0 := by
    by_contra hn
    exact hu ⟨i,hn⟩ hz
  have hu0 : u ≠ 0 := by
    intro hz
    obtain ⟨v,hv⟩ := exists_linearIndependent_of_le_finrank hdim
    have ha : a=0 := hgen 0 (by simp [hz,fs])
    have hb : b=0 := hgen 1 (by simp [hz,fs])
    have hc : c=0 := hgen 2 (by simp [hz,fs])
    have hd : d=0 := hgen 3 (by simp [hz,fs])
    exact hv.ne_zero 0 (hj (v 0) (by simp [ha]) (by simp [hb]) (by simp [hc]) (by simp [hd]))
  obtain ⟨v,hv⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (show 1 < finrank ℚ V by omega) hu0
  have hpoly : (linePoly a u v)^3+(linePoly b u v)^3+
      (linePoly c u v)^3+(linePoly d u v)^3=0 := by
    apply Polynomial.funext
    intro t
    have hh := he (t • u+v)
    simp only [linePoly,eval_add,eval_pow,eval_mul,eval_C,eval_X,eval_zero]
    simp only [map_add,map_smul,smul_eq_mul] at hh
    simpa only [mul_comm] using hh
  rcases FermatCubicLines.rational_linear_family
      (linePoly_degree a u v) (linePoly_degree b u v)
      (linePoly_degree c u v) (linePoly_degree d u v) hpoly with hp | hp
  · rcases hp with ⟨hab,hcd⟩ | ⟨hac,hbd⟩ | ⟨had,hbc⟩
    · exact Or.inl ⟨hgen 4 (pair_eval_zero hab),hgen 9 (pair_eval_zero hcd)⟩
    · exact Or.inr (Or.inl ⟨hgen 5 (pair_eval_zero hac),hgen 8 (pair_eval_zero hbd)⟩)
    · exact Or.inr (Or.inr ⟨hgen 6 (pair_eval_zero had),hgen 7 (pair_eval_zero hbc)⟩)
  · exact (linePoly_common_false hj hv hp).elim

private lemma finrank_le_two_of_pairs [FiniteDimensional ℚ V]
    {a b c d : V →ₗ[ℚ] ℚ} (hj : JointlyInjective a b c d)
    (hab : a+b=0) (hcd : c+d=0) : finrank ℚ V ≤ 2 := by
  have hinj : Function.Injective (a.prod c) := by
    intro x y hxy
    have ha : a x=a y := congrArg Prod.fst hxy
    have hc : c x=c y := congrArg Prod.snd hxy
    have hb : b x=b y := by
      have hx := congrArg (fun f : V →ₗ[ℚ] ℚ => f x) hab
      have hy := congrArg (fun f : V →ₗ[ℚ] ℚ => f y) hab
      simp only [LinearMap.add_apply,LinearMap.zero_apply] at hx hy
      linarith
    have hd : d x=d y := by
      have hx := congrArg (fun f : V →ₗ[ℚ] ℚ => f x) hcd
      have hy := congrArg (fun f : V →ₗ[ℚ] ℚ => f y) hcd
      simp only [LinearMap.add_apply,LinearMap.zero_apply] at hx hy
      linarith
    apply sub_eq_zero.mp
    apply hj (x-y) <;> simp [map_sub,ha,hb,hc,hd]
  simpa [finrank_prod] using (LinearMap.finrank_le_finrank_of_injective hinj)

/-- In particular no rational projective plane lies in the Fermat cubic. -/
theorem subspace_finrank_le_two [FiniteDimensional ℚ V]
    {a b c d : V →ₗ[ℚ] ℚ} (hj : JointlyInjective a b c d)
    (he : ∀ x, (a x)^3+(b x)^3+(c x)^3+(d x)^3=0) : finrank ℚ V ≤ 2 := by
  by_cases hdim : 2 ≤ finrank ℚ V
  · rcases subspace_opposite_pairs hj hdim he with ⟨hab,hcd⟩ | ⟨hac,hbd⟩ | ⟨had,hbc⟩
    · exact finrank_le_two_of_pairs hj hab hcd
    · exact finrank_le_two_of_pairs (a := a) (b := c) (c := b) (d := d)
        (fun x ha hc hb hd => hj x ha hb hc hd) hac hbd
    · exact finrank_le_two_of_pairs (a := a) (b := d) (c := b) (d := c)
        (fun x ha hd hb hc => hj x ha hb hc hd) had hbc
  · omega

/-- Linear dependence of two coordinate forms, allowing one form to vanish. -/
def PairDependent (f g : V →ₗ[ℚ] ℚ) : Prop :=
  ∃ r s : ℚ, (r ≠ 0 ∨ s ≠ 0) ∧ r • f+s • g=0

private lemma scalar_of_ker_le {f L : V →ₗ[ℚ] ℚ}
    (hk : LinearMap.ker L ≤ LinearMap.ker f) : ∃ r : ℚ, f=r • L := by
  by_cases hL : L=0
  · refine ⟨0,?_⟩
    ext x
    have hx : L x=0 := by simp [hL]
    have hf : f x=0 := hk hx
    simpa using hf
  obtain ⟨w,hw⟩ := DFunLike.ne_iff.mp hL
  change L w ≠ 0 at hw
  refine ⟨f w/L w,?_⟩
  ext x
  have hz : L (x-(L x/L w) • w)=0 := by
    simp only [map_sub,map_smul,smul_eq_mul]
    field_simp
    ring
  have hh : f (x-(L x/L w) • w)=0 := hk hz
  simp only [map_sub,map_smul,smul_eq_mul] at hh
  change f x=(f w/L w)*L x
  calc
    f x=(L x/L w)*f w := sub_eq_zero.mp hh
    _ = _ := by ring

private lemma dependent_of_kernels {f g L : V →ₗ[ℚ] ℚ}
    (hf : LinearMap.ker L ≤ LinearMap.ker f)
    (hg : LinearMap.ker L ≤ LinearMap.ker g) : PairDependent f g := by
  obtain ⟨r,hr⟩ := scalar_of_ker_le hf
  obtain ⟨s,hs⟩ := scalar_of_ker_le hg
  by_cases hr0 : r=0
  · refine ⟨1,0,Or.inl one_ne_zero,?_⟩
    simp [hr,hr0]
  · refine ⟨s,-r,Or.inr (neg_ne_zero.mpr hr0),?_⟩
    rw [hr,hs]
    ext x
    simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.zero_apply,smul_eq_mul]
    ring

private lemma ker_le_of_restricted_pair {f g L : V →ₗ[ℚ] ℚ}
    (he : f.domRestrict (LinearMap.ker L)+g.domRestrict (LinearMap.ker L)=0) :
    LinearMap.ker L ≤ LinearMap.ker (f+g) := by
  intro x hx
  have hh := congrArg (fun k : (LinearMap.ker L) →ₗ[ℚ] ℚ => k ⟨x,hx⟩) he
  simpa using hh

/-- A hyperplane section of a three-dimensional linearized Fermat conic
supplies one of the three rational pair relations. -/
theorem residual_pair_dependency [FiniteDimensional ℚ V]
    {a b c d L : V →ₗ[ℚ] ℚ} (hj : JointlyInjective a b c d)
    (hdim : finrank ℚ V=3)
    (he : ∀ x, L x=0 → (a x)^3+(b x)^3+(c x)^3+(d x)^3=0) :
    PairDependent (a+b) (c+d) ∨ PairDependent (a+c) (b+d) ∨ PairDependent (a+d) (b+c) := by
  have hr := (LinearMap.range L).finrank_le
  rw [finrank_self] at hr
  have hn := L.finrank_range_add_finrank_ker
  have hk : 2 ≤ finrank ℚ (LinearMap.ker L) := by omega
  have hj' : JointlyInjective
      (a.domRestrict (LinearMap.ker L)) (b.domRestrict (LinearMap.ker L))
      (c.domRestrict (LinearMap.ker L)) (d.domRestrict (LinearMap.ker L)) := by
    intro x ha hb hc hd
    apply Subtype.ext
    exact hj x ha hb hc hd
  have he' : ∀ x : LinearMap.ker L,
      (a.domRestrict (LinearMap.ker L) x)^3+(b.domRestrict (LinearMap.ker L) x)^3+
      (c.domRestrict (LinearMap.ker L) x)^3+(d.domRestrict (LinearMap.ker L) x)^3=0 :=
    fun x => he x x.property
  rcases subspace_opposite_pairs hj' hk he' with ⟨hab,hcd⟩ | ⟨hac,hbd⟩ | ⟨had,hbc⟩
  · exact Or.inl (dependent_of_kernels
      (ker_le_of_restricted_pair hab) (ker_le_of_restricted_pair hcd))
  · exact Or.inr (Or.inl (dependent_of_kernels
      (ker_le_of_restricted_pair hac) (ker_le_of_restricted_pair hbd)))
  · exact Or.inr (Or.inr (dependent_of_kernels
      (ker_le_of_restricted_pair had) (ker_le_of_restricted_pair hbc)))

/-- Classification without an injectivity assumption: the coordinate maps
have one of the three opposite pairings, or all are multiples of one form. -/
theorem linear_forms_opposite_or_common {a b c d : V →ₗ[ℚ] ℚ}
    (he : ∀ x, (a x)^3+(b x)^3+(c x)^3+(d x)^3=0) :
    ((a+b=0 ∧ c+d=0) ∨ (a+c=0 ∧ b+d=0) ∨ (a+d=0 ∧ b+c=0)) ∨
    ∃ L : V →ₗ[ℚ] ℚ, ∃ r s t w : ℚ,
      a=r • L ∧ b=s • L ∧ c=t • L ∧ d=w • L := by
  classical
  by_cases hp : (a+b=0 ∧ c+d=0) ∨ (a+c=0 ∧ b+d=0) ∨ (a+d=0 ∧ b+c=0)
  · exact Or.inl hp
  right
  let fs : Fin 10 → (V →ₗ[ℚ] ℚ) := ![a,b,c,d,a+b,a+c,a+d,b+c,b+d,c+d]
  let I := {i : Fin 10 // fs i ≠ 0}
  obtain ⟨u,hu⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun i : I => fs i.val) (fun i => by
      obtain ⟨x,hx⟩ := DFunLike.ne_iff.mp i.property
      exact ⟨x,by simpa using hx⟩)
  have hgen (i : Fin 10) (hz : fs i u=0) : fs i=0 := by
    by_contra hn
    exact hu ⟨i,hn⟩ hz
  let f : Fin 4 → (V →ₗ[ℚ] ℚ) := ![a,b,c,d]
  have hcommon (v : V) : FermatCubicLines.CommonFactor
      (linePoly a u v) (linePoly b u v) (linePoly c u v) (linePoly d u v) := by
    have hpoly : (linePoly a u v)^3+(linePoly b u v)^3+
        (linePoly c u v)^3+(linePoly d u v)^3=0 := by
      apply Polynomial.funext
      intro t
      have hh := he (t • u+v)
      simp only [linePoly,eval_add,eval_pow,eval_mul,eval_C,eval_X,eval_zero]
      simp only [map_add,map_smul,smul_eq_mul] at hh
      simpa only [mul_comm] using hh
    rcases FermatCubicLines.rational_linear_family
        (linePoly_degree a u v) (linePoly_degree b u v)
        (linePoly_degree c u v) (linePoly_degree d u v) hpoly with hh | hh
    · exfalso
      apply hp
      rcases hh with ⟨hab,hcd⟩ | ⟨hac,hbd⟩ | ⟨had,hbc⟩
      · exact Or.inl ⟨hgen 4 (pair_eval_zero hab),hgen 9 (pair_eval_zero hcd)⟩
      · exact Or.inr (Or.inl ⟨hgen 5 (pair_eval_zero hac),hgen 8 (pair_eval_zero hbd)⟩)
      · exact Or.inr (Or.inr ⟨hgen 6 (pair_eval_zero had),hgen 7 (pair_eval_zero hbc)⟩)
    · exact hh
  have hcross (v : V) (i j : Fin 4) : f i u*f j v=f j u*f i v := by
    obtain ⟨q,r,s,t,w,ha,hb,hc,hd⟩ := hcommon v
    let z : Fin 4 → ℚ := ![r,s,t,w]
    have hh (i : Fin 4) : linePoly (f i) u v=C (z i)*q := by
      fin_cases i
      · exact ha
      · exact hb
      · exact hc
      · exact hd
    have hco (i : Fin 4) : f i u=z i*q.coeff 1 ∧ f i v=z i*q.coeff 0 := by
      have h₁ := congrArg (fun p : ℚ[X] => p.coeff 1) (hh i)
      have h₀ := congrArg (fun p : ℚ[X] => p.coeff 0) (hh i)
      simpa [linePoly,coeff_C_mul_X,coeff_C_mul] using And.intro h₁ h₀
    rw [(hco i).1,(hco i).2,(hco j).1,(hco j).2]
    ring
  have hi : ∃ i : Fin 4, f i u ≠ 0 := by
    by_contra! hh
    have ha : a=0 := hgen 0 (hh 0)
    have hb : b=0 := hgen 1 (hh 1)
    have hc : c=0 := hgen 2 (hh 2)
    have hd : d=0 := hgen 3 (hh 3)
    exact hp (Or.inl ⟨by simp [ha,hb],by simp [hc,hd]⟩)
  obtain ⟨i,hi⟩ := hi
  have hm (j : Fin 4) : f j=(f j u/f i u) • f i := by
    apply LinearMap.ext
    intro x
    change f j x=(f j u/f i u)*f i x
    have hx := hcross x i j
    field_simp
    nlinarith only [hx]
  exact ⟨f i,f 0 u/f i u,f 1 u/f i u,f 2 u/f i u,f 3 u/f i u,hm 0,hm 1,hm 2,hm 3⟩

#print axioms linear_forms_opposite_or_common

#print axioms residual_pair_dependency

#print axioms subspace_opposite_pairs
#print axioms subspace_finrank_le_two
end Erdos1206.FermatCubicSubspaces
