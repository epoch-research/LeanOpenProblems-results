import FormalConjecturesUtil
import Submission.FinitePermutationOccupancy
import Submission.FiniteNegCovOccupancy
import Submission.ThetaRandomSplitting

/-! Balanced random partitions of column neighborhoods preserve oriented
theta exclusion and retain heavy pairs with a deterministic degree cap. -/
open Finset
open scoped BigOperators Classical
namespace Erdos713ThetaBalancedRandomSplitting
open Erdos713ThetaGram Erdos713ThetaSplit Erdos713GlobalLight
open Erdos713ThetaC4Deletion Erdos713ThetaAffineStars
open Erdos713FiniteOccupancy Erdos713FinitePermutationOccupancy
variable {A B T U : Type*}
set_option maxHeartbeats 2000000

noncomputable def block [Fintype T] [Fintype U] (i : T) : Finset (T × U) :=
  univ.filter (fun z => z.1 = i)

lemma block_card [Fintype T] [Fintype U] (i : T) : (block (U := U) i).card = Fintype.card U := by
  have he : block (U := U) i = {i} ×ˢ (univ : Finset U) := by
    ext ⟨a,b⟩
    simp [block,eq_comm]
  rw [he,card_product,card_singleton,card_univ,one_mul]

lemma block_ratio [Fintype T] [Nonempty T] [Fintype U] [Nonempty U] (i : T) :
    ((block (U := U) i).card : ℝ)/Fintype.card (T × U) = 1/(Fintype.card T : ℝ) := by
  rw [block_card,Fintype.card_prod,Nat.cast_mul]
  have hT : (Fintype.card T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hU : (Fintype.card U : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

lemma block_mean [Fintype T] [Nonempty T] [Fintype U] [Nonempty U]
    (i : T) (z : T × U) :
    (𝔼 σ : Equiv.Perm (T × U), hit (block i) z σ) = 1/(Fintype.card T : ℝ) := by
  rw [expect_hit,block_ratio]

lemma block_pair_le [Fintype T] [Nonempty T] [Fintype U] [Nonempty U]
    (i : T) {z w : T × U} (hzw : z ≠ w) :
    (𝔼 σ : Equiv.Perm (T × U), hit (block i) z σ*hit (block i) w σ) ≤
      (1/(Fintype.card T : ℝ))^2 := by
  simpa only [block_ratio] using expect_pair_le (block i) hzw

def Inc (R : A → B → Prop) (e : ∀ b, {a // R a b} ≃ (T × U))
    (σ : B → Equiv.Perm (T × U)) (a : A) (b : B × T) : Prop :=
  ∃ h : R a b.1, (σ b.1 (e b.1 ⟨a,h⟩)).1 = b.2

lemma no_theta {R : A → B → Prop} (hR : ¬ HasTheta R)
    (e : ∀ b, {a // R a b} ≃ (T × U)) (σ : B → Equiv.Perm (T × U)) :
    ¬ HasTheta (Inc R e σ) := by
  apply mt (theta_of_projection Prod.fst (fun _ _ h => h.choose) ?_) hR
  intro a b c hb hc he
  obtain ⟨hb,hb'⟩ := hb
  obtain ⟨hc,hc'⟩ := hc
  rcases b with ⟨b,i⟩
  rcases c with ⟨c,j⟩
  change b = c at he
  subst c
  exact Prod.ext rfl (hb'.symm.trans hc')

noncomputable def rowEquiv (R : A → B → Prop)
    (e : ∀ b, {a // R a b} ≃ (T × U)) (σ : B → Equiv.Perm (T × U)) (a : A) :
    {b // R a b} ≃ {b // Inc R e σ a b} where
  toFun b := ⟨(b.val,(σ b.val (e b.val ⟨a,b.property⟩)).1),b.property,rfl⟩
  invFun b := ⟨b.val.1,b.property.choose⟩
  left_inv _ := rfl
  right_inv b := by
    apply Subtype.ext
    exact Prod.ext rfl b.property.choose_spec

lemma row_card (R : A → B → Prop)
    (e : ∀ b, {a // R a b} ≃ (T × U)) (σ : B → Equiv.Perm (T × U)) (a : A) :
    Nat.card {b // Inc R e σ a b} = Nat.card {b // R a b} :=
  (Nat.card_congr (rowEquiv R e σ a)).symm

noncomputable def columnEquiv (R : A → B → Prop)
    (e : ∀ b, {a // R a b} ≃ (T × U)) (σ : B → Equiv.Perm (T × U)) (b : B × T) :
    {a // Inc R e σ a b} ≃ U where
  toFun a := (σ b.1 (e b.1 ⟨a.val,a.property.choose⟩)).2
  invFun u := ⟨((e b.1).symm ((σ b.1).symm (b.2,u))).val,
    ((e b.1).symm ((σ b.1).symm (b.2,u))).property,by simp⟩
  left_inv a := by
    apply Subtype.ext
    have he : (b.2,(σ b.1 (e b.1 ⟨a.val,a.property.choose⟩)).2) =
        σ b.1 (e b.1 ⟨a.val,a.property.choose⟩) := by
      exact Prod.ext a.property.choose_spec.symm rfl
    simp only [he,Equiv.symm_apply_apply]
  right_inv u := by simp

lemma column_card (R : A → B → Prop)
    (e : ∀ b, {a // R a b} ≃ (T × U)) (σ : B → Equiv.Perm (T × U)) (b : B × T) :
    Nat.card {a // Inc R e σ a b} = Nat.card U := Nat.card_congr (columnEquiv R e σ b)

section Moments
variable [Fintype A] [Fintype B] [Fintype T] [Nonempty T] [Fintype U] [Nonempty U]
variable (R : A → B → Prop) (e : ∀ b, {a // R a b} ≃ (T × U))

abbrev PairRows (x y : B) := {a : A // R a x ∧ R a y}

noncomputable def pairHit (x y : B) (i j : T) (a : PairRows R x y)
    (σ : B → Equiv.Perm (T × U)) : ℝ :=
  hit (block i) (e x ⟨a.val,a.property.1⟩) (σ x) *
    hit (block j) (e y ⟨a.val,a.property.2⟩) (σ y)

omit [Fintype A] [Fintype B] [Nonempty T] [Nonempty U] in
lemma pairHit_sq (x y : B) (i j : T) (a : PairRows R x y)
    (σ : B → Equiv.Perm (T × U)) : (pairHit R e x y i j a σ)^2 = pairHit R e x y i j a σ := by
  simp only [pairHit,mul_pow,hit_sq]

omit [Fintype A] in
lemma pairHit_mean {x y : B} (hxy : x ≠ y) (i j : T) (a : PairRows R x y) :
    (𝔼 σ : B → Equiv.Perm (T × U), pairHit R e x y i j a σ) =
      1/(Fintype.card T : ℝ)^2 := by
  unfold pairHit
  rw [expect_eval_mul hxy,block_mean,block_mean]
  ring

omit [Fintype A] in
lemma pairHit_pair_le {x y : B} (hxy : x ≠ y) (i j : T)
    {a b : PairRows R x y} (hab : a ≠ b) :
    (𝔼 σ : B → Equiv.Perm (T × U), pairHit R e x y i j a σ*pairHit R e x y i j b σ) ≤
      (1/(Fintype.card T : ℝ)^2)^2 := by
  have hax : e x ⟨a.val,a.property.1⟩ ≠ e x ⟨b.val,b.property.1⟩ := by
    intro he
    apply hab
    exact Subtype.ext (congrArg (fun z : {a // R a x} => z.val) ((e x).injective he))
  have hay : e y ⟨a.val,a.property.2⟩ ≠ e y ⟨b.val,b.property.2⟩ := by
    intro he
    apply hab
    exact Subtype.ext (congrArg (fun z : {a // R a y} => z.val) ((e y).injective he))
  have he (σ : B → Equiv.Perm (T × U)) :
      pairHit R e x y i j a σ*pairHit R e x y i j b σ =
      (hit (block i) (e x ⟨a.val,a.property.1⟩) (σ x)*
        hit (block i) (e x ⟨b.val,b.property.1⟩) (σ x)) *
      (hit (block j) (e y ⟨a.val,a.property.2⟩) (σ y)*
        hit (block j) (e y ⟨b.val,b.property.2⟩) (σ y)) := by
    unfold pairHit
    ring
  simp_rw [he]
  rw [expect_eval_mul hxy
    (fun σ => hit (block i) (e x ⟨a.val,a.property.1⟩) σ*
      hit (block i) (e x ⟨b.val,b.property.1⟩) σ)
    (fun σ => hit (block j) (e y ⟨a.val,a.property.2⟩) σ*
      hit (block j) (e y ⟨b.val,b.property.2⟩) σ)]
  have hx := block_pair_le i hax
  have hy := block_pair_le j hay
  have hnonneg : 0 ≤ 𝔼 σ : Equiv.Perm (T × U),
      hit (block j) (e y ⟨a.val,a.property.2⟩) σ*hit (block j) (e y ⟨b.val,b.property.2⟩) σ :=
    expect_nonneg (fun σ _ => mul_nonneg (hit_nonneg _ _ _) (hit_nonneg _ _ _))
  calc
    _ ≤ (1/(Fintype.card T : ℝ))^2*(1/(Fintype.card T : ℝ))^2 :=
      mul_le_mul hx hy hnonneg (sq_nonneg _)
    _ = _ := by ring

omit [Fintype B] [Nonempty T] [Nonempty U] in
lemma codegree_sum (x y : B) (i j : T) (σ : B → Equiv.Perm (T × U)) :
    (codegree (Inc R e σ) (x,i) (y,j) : ℝ) =
      ∑ a : PairRows R x y, pairHit R e x y i j a σ := by
  let Q := {a : PairRows R x y //
    (σ x (e x ⟨a.val,a.property.1⟩)).1 = i ∧
    (σ y (e y ⟨a.val,a.property.2⟩)).1 = j}
  let f : {a : A // Inc R e σ a (x,i) ∧ Inc R e σ a (y,j)} ≃ Q :=
    { toFun := fun a => ⟨⟨a.val,a.property.1.choose,a.property.2.choose⟩,
        a.property.1.choose_spec,a.property.2.choose_spec⟩
      invFun := fun a => ⟨a.val.val,⟨a.val.property.1,a.property.1⟩,⟨a.val.property.2,a.property.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := Nat.card_congr f
  change codegree (Inc R e σ) (x,i) (y,j) = Nat.card Q at hc
  rw [hc]
  simp only [Q,Nat.card_eq_fintype_card,Fintype.card_subtype,← sum_boole]
  apply sum_congr rfl
  intro a _
  simp only [pairHit,hit,block,mem_filter,mem_univ,true_and]
  split_ifs <;> simp_all

lemma pair_heavy_expect {x y : B} (hxy : x ≠ y)
    (hc : 8*(Fintype.card T)^2 ≤ codegree R x y) (i j : T) :
    (1/2 : ℝ) ≤ 𝔼 σ : B → Equiv.Perm (T × U),
      if 3 ≤ codegree (Inc R e σ) (x,i) (y,j) then (1 : ℝ) else 0 := by
  let p : ℝ := 1/(Fintype.card T : ℝ)^2
  let L : ℝ := (codegree R x y : ℝ)*p
  have hT : (0 : ℝ) < Fintype.card T := Nat.cast_pos.mpr Fintype.card_pos
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hL : 8 ≤ L := by
    dsimp only [L,p]
    rw [mul_one_div,le_div_iff₀ (sq_pos_of_pos hT)]
    exact_mod_cast hc
  have hcard : Fintype.card (PairRows R x y) = codegree R x y := by
    simp only [PairRows,codegree,Nat.card_eq_fintype_card]
  have hv := Erdos713FiniteNegCovOccupancy.variance_le (univ : Finset (PairRows R x y))
    (pairHit R e x y i j) p (fun a _ => pairHit_sq R e x y i j a)
    (fun a _ => pairHit_mean R e hxy i j a)
    (fun a _ b _ hab => pairHit_pair_le R e hxy i j hab)
  simp only [card_univ,hcard,← codegree_sum] at hv
  have hv' : (𝔼 σ : B → Equiv.Perm (T × U),
      ((codegree (Inc R e σ) (x,i) (y,j) : ℝ)-L)^2) ≤ L := by
    apply hv.trans
    dsimp only [L]
    have hnonneg : 0 ≤ (codegree R x y : ℝ)*p := mul_nonneg (Nat.cast_nonneg _) hp
    nlinarith only [hp,hnonneg]
  have hh := heavy_of_variance
    (fun σ : B → Equiv.Perm (T × U) => (codegree (Inc R e σ) (x,i) (y,j) : ℝ)) L hL hv'
  convert hh using 1
  congr 1
  funext σ
  have he : (3 : ℝ) ≤ (codegree (Inc R e σ) (x,i) (y,j) : ℝ) ↔
      3 ≤ codegree (Inc R e σ) (x,i) (y,j) := by exact_mod_cast Iff.rfl
  simp only [he]

omit [Fintype A] [Nonempty T] [Fintype U] [Nonempty U] in
lemma heavy_sum (σ : B → Equiv.Perm (T × U)) :
    (heavyCount (Inc R e σ) : ℝ) = ∑ p : B × B, ∑ u : T × T,
      if 3 ≤ codegree (Inc R e σ) (p.1,u.1) (p.2,u.2) then (1 : ℝ) else 0 := by
  let rearrange : ((B × T) × (B × T)) ≃ ((B × B) × (T × T)) :=
    { toFun := fun p => ((p.1.1,p.2.1),(p.1.2,p.2.2))
      invFun := fun p => ((p.1.1,p.2.1),(p.1.2,p.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [heavyCount,Nat.card_eq_fintype_card,Fintype.card_subtype,← sum_boole]
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv rearrange _ _ (fun _ => rfl)

lemma heavy_expect_lower (P : Finset (B × B))
    (hP : ∀ p ∈ P, p.1 ≠ p.2 ∧ 8*(Fintype.card T)^2 ≤ codegree R p.1 p.2) :
    (P.card : ℝ)*(Fintype.card T : ℝ)^2/2 ≤
      𝔼 (σ : B → Equiv.Perm (T × U)), (heavyCount (Inc R e σ) : ℝ) := by
  simp_rw [heavy_sum,expect_sum_comm]
  calc
    _ = ∑ _p ∈ P, ∑ _u : T × T, (1/2 : ℝ) := by
      simp only [sum_const,card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul]
      ring
    _ ≤ ∑ p ∈ P, ∑ u : T × T,
        𝔼 (σ : B → Equiv.Perm (T × U)),
          if 3 ≤ codegree (Inc R e σ) (p.1,u.1) (p.2,u.2) then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro p hp
      apply sum_le_sum
      intro u _
      exact pair_heavy_expect R e (hP p hp).1 (hP p hp).2 u.1 u.2
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ P)
      intro p _ _
      apply sum_nonneg
      intro u _
      exact expect_nonneg (fun s _ => by split_ifs <;> positivity)

/-- A universal heavy-count bound on all assignments bounds one codegree band. -/
lemma band_mass_le (P : Finset (B × B))
    (hP : ∀ p ∈ P, p.1 ≠ p.2 ∧ 8*(Fintype.card T)^2 ≤ codegree R p.1 p.2 ∧
      codegree R p.1 p.2 < 32*(Fintype.card T)^2)
    (M : ℕ) (hM : ∀ σ : B → Equiv.Perm (T × U), heavyCount (Inc R e σ) ≤ M) :
    (∑ p ∈ P, codegree R p.1 p.2) ≤ 64*M := by
  have hlo := heavy_expect_lower (T := T) R e P (fun p hp => ⟨(hP p hp).1,(hP p hp).2.1⟩)
  have hhi : (𝔼 (σ : B → Equiv.Perm (T × U)), (heavyCount (Inc R e σ) : ℝ)) ≤ (M : ℝ) := by
    exact expect_le univ_nonempty (fun σ _ => by exact_mod_cast hM σ)
  have hw : (∑ p ∈ P, codegree R p.1 p.2) ≤ 32*(Fintype.card T)^2*P.card := by
    calc
      _ ≤ ∑ _p ∈ P, 32*(Fintype.card T)^2 := sum_le_sum (fun p hp => (hP p hp).2.2.le)
      _ = _ := by simp [Nat.mul_comm]
  have hwR : (∑ p ∈ P, (codegree R p.1 p.2 : ℝ)) ≤
      32*(Fintype.card T : ℝ)^2*P.card := by exact_mod_cast hw
  have hfin : (∑ p ∈ P, (codegree R p.1 p.2 : ℝ)) ≤ 64*(M : ℝ) := by
    nlinarith only [hwR,hlo,hhi]
  exact_mod_cast hfin

end Moments
#print axioms no_theta
#print axioms column_card
#print axioms pairHit_pair_le
#print axioms pair_heavy_expect
#print axioms band_mass_le
end Erdos713ThetaBalancedRandomSplitting
