import Submission.FiniteInducedRamsey
import Submission.PaleyRamseyMargin

/-!
Finite Ramsey/Mycielski amplification of vector-coloring obstructions.
This auxiliary development does not settle Erdős 595.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open SimpleGraph Set
open scoped RealInnerProductSpace
namespace Erdos595MycielskiMargin
universe u

variable {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def UnitEdges (G : SimpleGraph V) (δ : ℝ) (v : V → E) : Prop :=
  (∀ a, ⟪v a,v a⟫ = 1) ∧ ∀ a b, G.Adj a b → ⟪v a,v b⟫ ≤ -δ

abbrev Vertex (V : Type*) := Option (V × Bool)
def graph (G : SimpleGraph V) : SimpleGraph (Vertex V) where
  Adj
    | none, none => False
    | none, some p => p.2 = true
    | some p, none => p.2 = true
    | some p, some q => G.Adj p.1 q.1 ∧ (p.2 = false ∨ q.2 = false)
  symm := by
    intro a b h
    cases a <;> cases b
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm,h.2.symm⟩
  loopless := by
    intro a h
    cases a with
    | none => exact h
    | some a => exact G.loopless _ h.1

lemma graph_cliqueFree (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    (graph G).CliqueFree 4 := by
  classical
  have no_four (a b c d : Vertex V)
      (hab : (graph G).Adj a b) (hac : (graph G).Adj a c)
      (had : (graph G).Adj a d) (hbc : (graph G).Adj b c)
      (hbd : (graph G).Adj b d) (hcd : (graph G).Adj c d) : False := by
    cases a <;> cases b <;> cases c <;> cases d
    all_goals simp only [graph] at hab hac had hbc hbd hcd
    all_goals first
      | contradiction
      | exact Erdos595Work.no_adj_common_neighbors hG hab.1 hac.1 hbc.1 had.1 hbd.1 hcd.1
      | aesop
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  exact no_four (e 0) (e 1) (e 2) (e 3)
    (e.map_rel_iff.mpr (by decide)) (e.map_rel_iff.mpr (by decide))
    (e.map_rel_iff.mpr (by decide)) (e.map_rel_iff.mpr (by decide))
    (e.map_rel_iff.mpr (by decide)) (e.map_rel_iff.mpr (by decide))

theorem finite_pair_ramsey {A : Type} [Finite A] (H : SimpleGraph A)
    (hH : H.CliqueFree 4) :
    ∃ (B : Type) (_ : Finite B) (R : SimpleGraph B), R.CliqueFree 4 ∧
      ∀ c : Sym2 B → Bool × Bool, ∃ (f : H ↪g R) (z : Bool × Bool),
        ∀ a b, H.Adj a b → c s(f a,f b) = z := by
  obtain ⟨B,hB,K,hK,h₁⟩ := Erdos595FiniteInducedRamsey.finite_induced_ramsey H hH
  letI := hB
  obtain ⟨D,hD,R,hR,h₂⟩ := Erdos595FiniteInducedRamsey.finite_induced_ramsey K hK
  refine ⟨D,hD,R,hR,?_⟩
  intro c
  obtain ⟨f,z,hf⟩ := h₂ (fun e => (c e).1)
  obtain ⟨g,w,hg⟩ := h₁ (fun e => (c (e.map f)).2)
  refine ⟨f.comp g,(z,w),?_⟩
  intro a b hab
  exact Prod.ext (hf _ _ (g.map_rel_iff.mpr hab)) (hg a b hab)

lemma norm_eq_one {v : E} (hv : ⟪v,v⟫ = 1) : ‖v‖ = 1 := by
  have hn : ‖v‖^2 = 1 := by simpa only [real_inner_self_eq_norm_sq] using hv
  nlinarith [norm_nonneg v]

noncomputable def normalized (w x : E) : E := by
  classical
  exact if x = 0 then w else ‖x‖⁻¹ • x

lemma normalized_unit {w x : E} (hw : ⟪w,w⟫ = 1) :
    ⟪normalized w x, normalized w x⟫ = 1 := by
  classical
  by_cases hx : x = 0
  · simpa [normalized,hx] using hw
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    simp only [normalized,if_neg hx,real_inner_smul_left,inner_smul_right,
      real_inner_self_eq_norm_sq]
    field_simp

lemma normalized_inner_le {w x y : E} {δ S : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hδ : 0 ≤ δ)
    (hprod : ‖x‖ * ‖y‖ ≤ S) (hxy : ⟪x,y⟫ ≤ -δ * S) :
    ⟪normalized w x, normalized w y⟫ ≤ -δ := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have h : ⟪x,y⟫ ≤ -δ * (‖x‖ * ‖y‖) :=
    hxy.trans (mul_le_mul_of_nonpos_left hprod (neg_nonpos.mpr hδ))
  simp only [normalized,if_neg hx,if_neg hy,real_inner_smul_left,inner_smul_right]
  have hid : ‖y‖⁻¹ * (‖x‖⁻¹ * ⟪x,y⟫) = ⟪x,y⟫ / (‖x‖ * ‖y‖) := by ring
  rw [hid]
  exact (div_le_iff₀ (mul_pos hxpos hypos)).mpr h

noncomputable def project (w x : E) : E := x - ⟪x,w⟫ • w

lemma project_inner {w x y : E} (hw : ⟪w,w⟫ = 1) :
    ⟪project w x,project w y⟫ = ⟪x,y⟫ - ⟪x,w⟫ * ⟪y,w⟫ := by
  simp only [project,inner_sub_left,inner_sub_right,real_inner_smul_left,inner_smul_right,hw]
  rw [real_inner_comm w y]
  ring

lemma project_norm_le {w x : E} (hw : ⟪w,w⟫ = 1) (hx : ⟪x,x⟫ = 1) :
    ‖project w x‖ ≤ 1 := by
  have h := project_inner (x := x) (y := x) hw
  rw [real_inner_self_eq_norm_sq,hx] at h
  nlinarith [norm_nonneg (project w x),sq_nonneg ⟪x,w⟫]

lemma negative_project_nonzero {w x y : E} {δ : ℝ}
    (hw : ⟪w,w⟫ = 1) (hδ : 0 < δ) (hxy : ⟪x,y⟫ ≤ -δ)
    (hx : ⟪x,w⟫ < -δ/2) (hy : ⟪y,w⟫ < -δ/2) : project w x ≠ 0 := by
  intro he
  have h := project_inner (x := x) (y := y) hw
  rw [he,inner_zero_left] at h
  have hp : 0 < ⟪x,w⟫ * ⟪y,w⟫ := mul_pos_of_neg_of_neg (by linarith) (by linarith)
  linarith

lemma negative_improves {w x y : E} {δ : ℝ}
    (hw : ⟪w,w⟫ = 1) (hxunit : ⟪x,x⟫ = 1) (hyunit : ⟪y,y⟫ = 1)
    (hδ : 0 < δ) (hxy : ⟪x,y⟫ ≤ -δ)
    (hx : ⟪x,w⟫ < -δ/2) (hy : ⟪y,w⟫ < -δ/2) :
    ⟪normalized w (project w x), normalized w (project w y)⟫ ≤ -(δ + δ^2/4) := by
  have hx0 := negative_project_nonzero hw hδ hxy hx hy
  have hy0 := negative_project_nonzero hw hδ (by simpa only [real_inner_comm] using hxy) hy hx
  apply normalized_inner_le hx0 hy0 (by positivity : 0 ≤ δ+δ^2/4) (S := 1)
  · exact (mul_le_mul (project_norm_le hw hxunit) (project_norm_le hw hyunit)
      (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  · rw [project_inner hw]
    have hprod : δ^2/4 ≤ ⟪x,w⟫ * ⟪y,w⟫ := by
      have hm := mul_le_mul (show δ/2 ≤ -⟪x,w⟫ by linarith)
        (show δ/2 ≤ -⟪y,w⟫ by linarith) (by positivity : 0 ≤ δ/2)
        (show 0 ≤ -⟪x,w⟫ by linarith)
      nlinarith
    nlinarith


noncomputable def mix (α : ℝ) (x y : E) : E := x + α • y

lemma mixed_self {x y : E} {α : ℝ} (hx : ⟪x,x⟫ = 1) (hy : ⟪y,y⟫ = 1) :
    ‖mix α x y‖^2 = 1 + 2*α*⟪x,y⟫ + α^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [mix,inner_add_left,inner_add_right,real_inner_smul_left,inner_smul_right,hx,hy]
  rw [real_inner_comm y x]
  ring

lemma mixed_nonzero {x y : E} {α : ℝ}
    (hx : ⟪x,x⟫ = 1) (hy : ⟪y,y⟫ = 1) (hα : 0 ≤ α) (hα1 : α < 1) :
    mix α x y ≠ 0 := by
  intro he
  have h := norm_add_le (mix α x y) (-α • y)
  have hi : mix α x y + -α • y = x := by simp [mix]
  rw [hi,he,norm_zero,zero_add,norm_smul,norm_eq_one hx,norm_eq_one hy] at h
  simp only [Real.norm_eq_abs,abs_neg,abs_of_nonneg hα,mul_one] at h
  linarith

lemma near_inner_bound {w x y : E} {δ : ℝ}
    (hw : ⟪w,w⟫ = 1) (hx : ⟪x,x⟫ = 1) (hy : ⟪y,y⟫ = 1)
    (hδ : 0 ≤ δ) (ht : -δ/2 ≤ ⟪x,w⟫) (hu : ⟪y,w⟫ ≤ -δ) :
    ⟪x,y⟫ ≤ 1-δ^2/8 := by
  have h := real_inner_mul_inner_self_le (x-y) w
  simp only [inner_sub_left,inner_sub_right,hx,hy,hw,mul_one] at h
  rw [real_inner_comm x y] at h
  have ht' : δ/2 ≤ ⟪x,w⟫ - ⟪y,w⟫ := by linarith
  have hs := mul_self_le_mul_self (by positivity : 0 ≤ δ/2) ht'
  nlinarith

lemma mixed_cross {x y x' y' : E} {δ α : ℝ}
    (hy : ⟪y,y⟫ = 1) (hy' : ⟪y',y'⟫ = 1) (hα : 0 ≤ α)
    (hxx : ⟪x,x'⟫ ≤ -δ) (hxy : ⟪x,y'⟫ ≤ -δ) (hyx : ⟪y,x'⟫ ≤ -δ) :
    ⟪mix α x y,mix α x' y'⟫ ≤ -δ*(1+2*α)+α^2 := by
  have hyy : ⟪y,y'⟫ ≤ 1 := by
    simpa only [norm_eq_one hy,norm_eq_one hy',mul_one] using real_inner_le_norm y y'
  have h₁ := mul_le_mul_of_nonneg_left hxy hα
  have h₂ := mul_le_mul_of_nonneg_left hyx hα
  have h₃ := mul_le_mul_of_nonneg_left hyy (sq_nonneg α)
  simp only [mix,inner_add_left,inner_add_right,real_inner_smul_left,inner_smul_right]
  nlinarith

lemma scalar_improvement {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    let α := δ^3/16;
    let S := (1+α)^2-α*δ^2/4;
    -δ*(1+2*α)+α^2 ≤ -(δ+δ^6/512)*S := by
  dsimp only
  let α := δ^3/16
  let S := (1+α)^2-α*δ^2/4
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hα16 : α ≤ 1/16 := by
    have h := pow_le_one₀ hδ hδ1 (n := 3)
    dsimp [α]
    linarith
  have hS : S ≤ 2 := by
    have hh : 0 ≤ α*δ^2 := mul_nonneg hα (sq_nonneg δ)
    have ha2 := mul_self_le_mul_self hα hα16
    dsimp [S]
    nlinarith
  have hδ3 : δ^3 = 16*α := by dsimp [α]; ring
  have hδ6 : δ^6/512 = α^2/2 := by dsimp [α]; ring
  have hid : -δ*(1+2*α)+α^2+δ*S = α^2*(1+δ)-α*δ^3/4 := by dsimp [S]; ring
  have hsum : -δ*(1+2*α)+α^2+δ*S ≤ -2*α^2 := by
    rw [hid,hδ3]
    nlinarith [mul_nonneg (sq_nonneg α) (sub_nonneg.mpr hδ1)]
  have he := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ α^2/2)
  change -δ*(1+2*α)+α^2 ≤ -(δ+δ^6/512)*S
  rw [hδ6]
  nlinarith

lemma positive_improves {w x y x' y' : E} {δ : ℝ}
    (hw : ⟪w,w⟫ = 1)
    (hx : ⟪x,x⟫ = 1) (hy : ⟪y,y⟫ = 1)
    (hx' : ⟪x',x'⟫ = 1) (hy' : ⟪y',y'⟫ = 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ht : -δ/2 ≤ ⟪x,w⟫) (hu : ⟪y,w⟫ ≤ -δ)
    (ht' : -δ/2 ≤ ⟪x',w⟫) (hu' : ⟪y',w⟫ ≤ -δ)
    (hxx : ⟪x,x'⟫ ≤ -δ) (hxy : ⟪x,y'⟫ ≤ -δ) (hyx : ⟪y,x'⟫ ≤ -δ) :
    ⟪normalized w (mix (δ^3/16) x y), normalized w (mix (δ^3/16) x' y')⟫
      ≤ -(δ+δ^6/512) := by
  let α := δ^3/16
  let S := (1+α)^2-α*δ^2/4
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hα1 : α < 1 := by
    have h := pow_le_one₀ hδ.le hδ1 (n := 3)
    dsimp [α]
    linarith
  have bound (a b : E) (ha : ⟪a,a⟫ = 1) (hb : ⟪b,b⟫ = 1)
      (ht : -δ/2 ≤ ⟪a,w⟫) (hu : ⟪b,w⟫ ≤ -δ) : ‖mix α a b‖^2 ≤ S := by
    rw [mixed_self ha hb]
    have h := near_inner_bound hw ha hb hδ.le ht hu
    have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2*α)
    dsimp [S]
    nlinarith
  apply normalized_inner_le (mixed_nonzero hx hy hα hα1)
    (mixed_nonzero hx' hy' hα hα1) (by positivity : 0 ≤ δ+δ^6/512) (S := S)
  · have h₁ := bound x y hx hy ht hu
    have h₂ := bound x' y' hx' hy' ht' hu'
    nlinarith [sq_nonneg (‖mix α x y‖-‖mix α x' y'‖)]
  · exact (mixed_cross hy hy' hα hxx hxy hyx).trans (scalar_improvement hδ.le hδ1)


lemma sixth_le_square {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) : δ^6 ≤ δ^2 := by
  calc
    δ^6 = δ^2*δ^4 := by ring
    _ ≤ δ^2*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hδ hδ1) (sq_nonneg δ)
    _ = δ^2 := mul_one _

/-- A finite host converts any unit-vector representation to a strictly
stronger representation of the target, in the same real inner-product space. -/
theorem finite_reflection {A : Type} [Finite A] (H : SimpleGraph A)
    (hH : H.CliqueFree 4) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1/2) :
    ∃ (D : Type) (_ : Finite D) (K : SimpleGraph D), K.CliqueFree 4 ∧
      ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E],
        ∀ v : D → E, UnitEdges K δ v →
          ∃ w : A → E, UnitEdges H (δ+δ^6/512) w := by
  classical
  obtain ⟨B,hB,R,hR,hRam⟩ := finite_pair_ramsey H hH
  letI := hB
  refine ⟨Vertex B,inferInstance,graph R,graph_cliqueFree R hR,?_⟩
  intro E _ _ v hv
  let w := v none
  let x : B → E := fun a => v (some (a,false))
  let y : B → E := fun a => v (some (a,true))
  have hw : ⟪w,w⟫ = 1 := hv.1 none
  have hx (a : B) : ⟪x a,x a⟫ = 1 := hv.1 _
  have hy (a : B) : ⟪y a,y a⟫ = 1 := hv.1 _
  have hyw (a : B) : ⟪y a,w⟫ ≤ -δ := hv.2 _ _ rfl
  have hxx {a b : B} (hab : R.Adj a b) : ⟪x a,x b⟫ ≤ -δ :=
    hv.2 _ _ ⟨hab,Or.inl rfl⟩
  have hxy {a b : B} (hab : R.Adj a b) : ⟪x a,y b⟫ ≤ -δ :=
    hv.2 _ _ ⟨hab,Or.inl rfl⟩
  have hyx {a b : B} (hab : R.Adj a b) : ⟪y a,x b⟫ ≤ -δ :=
    hv.2 _ _ ⟨hab,Or.inr rfl⟩
  let cut (a : B) : Bool := decide (⟪x a,w⟫ < -δ/2)
  let c : Sym2 B → Bool × Bool := Sym2.lift
    ⟨fun a b => (cut a && cut b, !cut a && !cut b), by
      intro a b
      simp only [Bool.and_comm]⟩
  obtain ⟨f,z,hf⟩ := hRam c
  have hδ1 : δ ≤ 1 := by linarith
  have hstep1 : δ+δ^6/512 ≤ 1 := by
    have h6 : δ^6 ≤ 1 := pow_le_one₀ hδ.le hδ1
    linarith
  by_cases hz : z.1 = true
  · refine ⟨fun a => normalized w (project w (x (f a))),?_,?_⟩
    · intro a; exact normalized_unit hw
    · intro a b hab
      have hh := congrArg Prod.fst (hf a b hab)
      change (cut (f a) && cut (f b)) = z.1 at hh
      rw [hz] at hh
      obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hh
      have ha' : ⟪x (f a),w⟫ < -δ/2 := of_decide_eq_true ha
      have hb' : ⟪x (f b),w⟫ < -δ/2 := of_decide_eq_true hb
      have hi := negative_improves hw (hx (f a)) (hx (f b)) hδ
        (hxx (f.map_rel_iff.mpr hab)) ha' hb'
      have h6 := sixth_le_square hδ.le hδ1
      nlinarith [sq_nonneg δ]
  · by_cases hz' : z.2 = true
    · refine ⟨fun a => normalized w (mix (δ^3/16) (x (f a)) (y (f a))),?_,?_⟩
      · intro a; exact normalized_unit hw
      · intro a b hab
        have hh := congrArg Prod.snd (hf a b hab)
        change (!cut (f a) && !cut (f b)) = z.2 at hh
        rw [hz'] at hh
        obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hh
        have ha0 : cut (f a) = false := by simpa only [Bool.not_eq_true'] using ha
        have hb0 : cut (f b) = false := by simpa only [Bool.not_eq_true'] using hb
        have ha' : -δ/2 ≤ ⟪x (f a),w⟫ := le_of_not_gt (of_decide_eq_false ha0)
        have hb' : -δ/2 ≤ ⟪x (f b),w⟫ := le_of_not_gt (of_decide_eq_false hb0)
        have hab' := f.map_rel_iff.mpr hab
        exact positive_improves hw (hx _) (hy _) (hx _) (hy _) hδ hδ1
          ha' (hyw _) hb' (hyw _) (hxx hab') (hxy hab') (hyx hab')
    · have hdiff {a b : A} (hab : H.Adj a b) : cut (f a) ≠ cut (f b) := by
        intro he
        have hh := hf a b hab
        have h₁ := congrArg Prod.fst hh
        have h₂ := congrArg Prod.snd hh
        change (cut (f a) && cut (f b)) = z.1 at h₁
        change (!cut (f a) && !cut (f b)) = z.2 at h₂
        rw [he] at h₁ h₂
        cases h : cut (f b) <;> simp_all
      let q : A → E := fun a => if cut (f a) then w else -w
      refine ⟨q,?_,?_⟩
      · intro a
        dsimp only [q]
        split_ifs <;> simp only [inner_neg_left,inner_neg_right,neg_neg,hw]
      · intro a b hab
        have he := hdiff hab
        have hh : ⟪q a,q b⟫ = -1 := by
          dsimp only [q]
          cases ha : cut (f a) <;> cases hb : cut (f b) <;> simp_all
        rw [hh]
        linarith

structure RealSpace where
  Carrier : Type u
  [normed : NormedAddCommGroup Carrier]
  [inner : InnerProductSpace ℝ Carrier]
attribute [instance] RealSpace.normed RealSpace.inner

def HasRep {A : Type} (H : SimpleGraph A) (δ : ℝ) : Prop :=
  ∃ S : RealSpace.{u}, ∃ v : A → S.Carrier, UnitEdges H δ v

def Universal (δ : ℝ) : Prop :=
  ∀ (A : Type) [Finite A] (H : SimpleGraph A), H.CliqueFree 4 → HasRep.{u} H δ

lemma universal_step {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1/2)
    (h : Universal.{u} δ) : Universal.{u} (δ+δ^6/512) := by
  intro A _ H hH
  obtain ⟨D,hD,K,hK,hRef⟩ := finite_reflection H hH hδ hδ2
  letI := hD
  obtain ⟨S,v,hv⟩ := h D K hK
  obtain ⟨w,hw⟩ := hRef S.Carrier v hv
  exact ⟨S,w,hw⟩


lemma universal_bound {δ : ℝ} (h : Universal.{u} δ) : δ ≤ 1/2 := by
  let T := (⊤ : SimpleGraph (Fin 3))
  have hT : T.CliqueFree 4 := (SimpleGraph.colorable_of_fintype T).cliqueFree (by decide)
  obtain ⟨S,v,hv⟩ := h (Fin 3) T hT
  have h₀ := hv.1 0
  have h₁ := hv.1 1
  have h₂ := hv.1 2
  have h01 := hv.2 0 1 (by decide : T.Adj 0 1)
  have h02 := hv.2 0 2 (by decide : T.Adj 0 2)
  have h12 := hv.2 1 2 (by decide : T.Adj 1 2)
  have hn : 0 ≤ ⟪v 0+v 1+v 2,v 0+v 1+v 2⟫ := real_inner_self_nonneg
  simp only [inner_add_left,inner_add_right,h₀,h₁,h₂] at hn
  rw [real_inner_comm (v 0) (v 1),real_inner_comm (v 0) (v 2),
    real_inner_comm (v 1) (v 2)] at hn
  linarith

lemma universal_mono {δ ε : ℝ} (h : Universal.{u} δ) (he : ε ≤ δ) : Universal.{u} ε := by
  intro A _ H hH
  obtain ⟨S,v,hv⟩ := h A H hH
  exact ⟨S,v,hv.1,fun a b hab => (hv.2 a b hab).trans (neg_le_neg he)⟩

/-- No fixed positive all-edge vector margin works on every finite K4-free graph. -/
theorem no_universal (δ : ℝ) (hδ : 0 < δ) : ¬Universal.{u} δ := by
  intro h
  let d := δ^6/512
  have hd : 0 < d := by dsimp [d]; positivity
  have hi (n : ℕ) : Universal.{u} (δ+(n : ℝ)*d) := by
    induction n with
    | zero => simpa using h
    | succ n ih =>
      have hle : δ ≤ δ+(n : ℝ)*d := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hd.le)
      have hpos : 0 < δ+(n : ℝ)*d := hδ.trans_le hle
      have hs := universal_step hpos (universal_bound ih) ih
      have hh := pow_le_pow_left₀ hδ.le hle 6
      have hstep : δ+(n+1 : ℕ)*d ≤
          (δ+(n : ℝ)*d)+(δ+(n : ℝ)*d)^6/512 := by
        rw [Nat.cast_add,Nat.cast_one]
        dsimp only [d] at *
        nlinarith
      exact universal_mono hs hstep
  obtain ⟨n,hn⟩ := exists_nat_gt ((1/2 : ℝ)/d)
  have hn' : (1/2 : ℝ) < (n : ℝ)*d := (div_lt_iff₀ hd).mp hn
  have hh := universal_bound (hi n)
  linarith

/-- One finite obstruction works simultaneously for every real inner-product
space in the chosen universe, with no bound on its dimension or separability. -/
theorem exists_no_unit_edges (δ : ℝ) (hδ : 0 < δ) :
    ∃ (A : Type) (_ : Finite A) (H : SimpleGraph A), H.CliqueFree 4 ∧
      ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E],
        ∀ v : A → E, ¬UnitEdges H δ v := by
  classical
  by_contra hn
  apply no_universal.{u} δ hδ
  intro A hA H hH
  by_contra hnot
  apply hn
  refine ⟨A,hA,H,hH,?_⟩
  intro E nE iE v hv
  let S : RealSpace.{u} := @RealSpace.mk E nE iE
  exact hnot ⟨S,v,hv⟩


lemma sum_cliqueFree {A B : Type*} (H : SimpleGraph A) (K : SimpleGraph B)
    (hH : H.CliqueFree 4) (hK : K.CliqueFree 4) : (H ⊕g K).CliqueFree 4 := by
  classical
  have hf (a b c d : A ⊕ B) (hab : (H ⊕g K).Adj a b)
      (hac : (H ⊕g K).Adj a c) (hbc : (H ⊕g K).Adj b c)
      (had : (H ⊕g K).Adj a d) (hbd : (H ⊕g K).Adj b d)
      (hcd : (H ⊕g K).Adj c d) : False := by
    cases a <;> cases b <;> cases c <;> cases d
    all_goals simp only [SimpleGraph.sum_adj] at hab hac hbc had hbd hcd
    all_goals first | contradiction |
      exact Erdos595Work.no_adj_common_neighbors hH hab hac hbc had hbd hcd |
      exact Erdos595Work.no_adj_common_neighbors hK hab hac hbc had hbd hcd
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  exact hf (e 0) (e 1) (e 2) (e 3)
    (e.map_rel_iff.mpr (by decide)) (e.map_rel_iff.mpr (by decide))
    (e.map_rel_iff.mpr (by decide)) (e.map_rel_iff.mpr (by decide))
    (e.map_rel_iff.mpr (by decide)) (e.map_rel_iff.mpr (by decide))

/-- Every fixed positive triangle-hitting margin already fails on some finite
K4-free graph. The space may have arbitrary dimension and need not be separable.
This does NOT exclude strictly negative margins varying from triangle to triangle. -/
theorem exists_no_uniform_triangle_hit (δ : ℝ) (hδ : 0 < δ) :
    ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V), G.CliqueFree 4 ∧
      ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E],
        ¬∃ v : V → E, Erdos595RamseyVector.UnitTriangleHit G (-δ) v := by
  obtain ⟨A,hA,H,hH,hbad⟩ := exists_no_unit_edges.{u} δ hδ
  letI := hA
  let T := (⊤ : SimpleGraph (Fin 3))
  have hT : T.CliqueFree 4 := (SimpleGraph.colorable_of_fintype T).cliqueFree (by decide)
  have htri : ∃ a b c, (H ⊕g T).Adj a b ∧ (H ⊕g T).Adj a c ∧ (H ⊕g T).Adj b c :=
    ⟨Sum.inr 0,Sum.inr 1,Sum.inr 2,by change (0 : Fin 3) ≠ 1; decide,
      by change (0 : Fin 3) ≠ 2; decide,by change (1 : Fin 3) ≠ 2; decide⟩
  obtain ⟨V,hV,G,hG,hRam⟩ := Erdos595PaleyRamseyMargin.finite_ramsey_against_triangle
    (H ⊕g T) (sum_cliqueFree H T hH hT) htri
  refine ⟨V,hV,G,hG,?_⟩
  intro E _ _
  apply Erdos595RamseyVector.no_triangle_hit_of_ramsey (H ⊕g T) G (-δ) ?_ hRam
  rintro ⟨v,hu,he⟩
  exact hbad E (fun a => v (Sum.inl a))
    ⟨fun a => hu (Sum.inl a),fun a b hab => he (Sum.inl a) (Sum.inl b) hab⟩

#print axioms graph_cliqueFree
#print axioms finite_pair_ramsey
#print axioms negative_improves
#print axioms positive_improves
#print axioms finite_reflection
#print axioms no_universal
#print axioms exists_no_unit_edges
#print axioms exists_no_uniform_triangle_hit
end Erdos595MycielskiMargin
