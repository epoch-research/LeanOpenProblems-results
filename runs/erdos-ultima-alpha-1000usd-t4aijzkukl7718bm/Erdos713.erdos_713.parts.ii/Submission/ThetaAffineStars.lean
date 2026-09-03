import FormalConjecturesUtil
import Submission.ThetaTransversalCompletion

/-! Affine stars built from a local incidence system of girth at least eight.
These are auxiliary theta-free relations, not extremal graph examples. -/
namespace Erdos713ThetaAffineStars
open Erdos713ThetaGram Erdos713ThetaTransversal Erdos713GlobalLight
set_option maxHeartbeats 2000000
variable {A I F : Type*} [Field F]

abbrev Rows (A F : Type*) := (F × F) × A
abbrev Columns (I F : Type*) := (F × F) ⊕ (I × F)

def Inc (s : I → F) (L : A → I → Prop) : Rows A F → Columns I F → Prop
  | a, .inl p => a.1 = p
  | a, .inr b => L a.2 b.1 ∧ b.2 = a.1.1*s b.1+a.1.2

lemma common_two_center (s : I → F) (hs : Function.Injective s) (L : A → I → Prop)
    {a b : Rows A F} {x y : Columns I F} (hxy : x ≠ y)
    (hax : Inc s L a x) (hay : Inc s L a y)
    (hbx : Inc s L b x) (hby : Inc s L b y) : a.1 = b.1 := by
  cases x with
  | inl p => exact hax.trans hbx.symm
  | inr u =>
    cases y with
    | inl p => exact hay.trans hby.symm
    | inr v =>
      exact line_unique (A := A) s hs (fun he => hxy (congrArg Sum.inr he))
        hax.2 hay.2 hbx.2 hby.2

lemma leaf_eq_of_index (s : I → F) (L : A → I → Prop)
    {a b : Rows A F} {x y : I × F} (hab : a.1 = b.1)
    (hx : Inc s L a (.inr x)) (hy : Inc s L b (.inr y)) (hi : x.1 = y.1) : x = y := by
  apply Prod.ext hi
  calc
    x.2 = a.1.1*s x.1+a.1.2 := hx.2
    _ = b.1.1*s y.1+b.1.2 := by rw [hab,hi]
    _ = y.2 := hy.2.symm

lemma pair_contains_center (s : I → F) (hs : Function.Injective s) (L : A → I → Prop)
    (hfour : ∀ {a b : A} {i j : I}, a ≠ b → L a i → L a j → L b i → L b j → i = j)
    {a b : Rows A F} {x y : Columns I F} (hab : a ≠ b) (hxy : x ≠ y)
    (hax : Inc s L a x) (hay : Inc s L a y)
    (hbx : Inc s L b x) (hby : Inc s L b y) : x = .inl a.1 ∨ y = .inl a.1 := by
  have hc := common_two_center s hs L hxy hax hay hbx hby
  have ha : a.2 ≠ b.2 := fun he => hab (Prod.ext hc he)
  cases x with
  | inl p => exact Or.inl (congrArg Sum.inl hax.symm)
  | inr u =>
    cases y with
    | inl p => exact Or.inr (congrArg Sum.inl hay.symm)
    | inr v =>
      have hi := hfour ha hax.1 hay.1 hbx.1 hby.1
      exact (hxy (congrArg Sum.inr (leaf_eq_of_index s L rfl hax hay hi))).elim

lemma leaf_of_not_center (s : I → F) (L : A → I → Prop)
    {a : Rows A F} {x : Columns I F} (hx : Inc s L a x) (hne : x ≠ .inl a.1) :
    ∃ y : I × F, x = .inr y := by
  cases x with
  | inl p => exact (hne (congrArg Sum.inl hx.symm)).elim
  | inr y => exact ⟨y,rfl⟩

theorem no_theta (s : I → F) (hs : Function.Injective s) (L : A → I → Prop)
    (hfour : ∀ {a b : A} {i j : I}, a ≠ b → L a i → L a j → L b i → L b j → i = j)
    (hsix : ∀ {a b c : A} {i j k : I}, a ≠ b → a ≠ c → b ≠ c →
      L a i → L b i → L b j → L c j → L c k → L a k → i = j) :
    ¬ HasTheta (Inc s L) := by
  rintro ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩
  have hnA (i j : Fin 3) (hij : i ≠ j) : a i ≠ a j := fun h => hij (ha h)
  have hnB (i j : Fin 4) (hij : i ≠ j) : b i ≠ b j := fun h => hij (hb h)
  have hc := common_two_center s hs L (hnB 0 1 (by decide)) h00 h01 h10 h11
  have hcent := pair_contains_center s hs L hfour (hnA 0 1 (by decide))
    (hnB 0 1 (by decide)) h00 h01 h10 h11
  have hb2 : b 2 ≠ .inl (a 0).1 := by
    rcases hcent with h | h
    · exact fun he => hnB 2 0 (by decide) (he.trans h.symm)
    · exact fun he => hnB 2 1 (by decide) (he.trans h.symm)
  have hb3 : b 3 ≠ .inl (a 1).1 := by
    rw [← hc]
    rcases hcent with h | h
    · exact fun he => hnB 3 0 (by decide) (he.trans h.symm)
    · exact fun he => hnB 3 1 (by decide) (he.trans h.symm)
  obtain ⟨x,hx⟩ := leaf_of_not_center s L h02 hb2
  obtain ⟨y,hy⟩ := leaf_of_not_center s L h13 hb3
  rw [hx] at h02 h22
  rw [hy] at h13 h23
  have hxy : x ≠ y := fun h => hnB 2 3 (by decide) (hx.trans ((congrArg Sum.inr h).trans hy.symm))
  have hc2 : (a 0).1 = (a 2).1 := by
    apply line_unique (A := A) s hs hxy h02.2 _ h22.2 h23.2
    change y.2 = (a 0).1.1*s y.1+(a 0).1.2
    rw [hc]
    exact h13.2
  have hlocal (i j : Fin 3) (hij : i ≠ j) : (a i).2 ≠ (a j).2 := by
    have hall (i : Fin 3) : (a i).1 = (a 0).1 := by
      fin_cases i
      · rfl
      · exact hc.symm
      · exact hc2.symm
    exact fun he => hnA i j hij (Prod.ext ((hall i).trans (hall j).symm) he)
  have finish {z : I × F} {j : Fin 4} (hj : b j = .inr z)
      (h0 : Inc s L (a 0) (.inr z)) (h1 : Inc s L (a 1) (.inr z))
      (hj3 : j ≠ 3) : False := by
    have hi := hsix (hlocal 0 1 (by decide)) (hlocal 0 2 (by decide))
      (hlocal 1 2 (by decide)) h0.1 h1.1 h13.1 h23.1 h22.1 h02.1
    have he := leaf_eq_of_index s L hc h0 h13 hi
    exact hnB j 3 hj3 (hj.trans ((congrArg Sum.inr he).trans hy.symm))
  rcases hcent with h | h
  · have hb1 : b 1 ≠ .inl (a 0).1 := fun he => hnB 1 0 (by decide) (he.trans h.symm)
    obtain ⟨z,hz⟩ := leaf_of_not_center s L h01 hb1
    rw [hz] at h01 h11
    exact finish hz h01 h11 (by decide)
  · have hb0 : b 0 ≠ .inl (a 0).1 := fun he => hnB 0 1 (by decide) (he.trans h.symm)
    obtain ⟨z,hz⟩ := leaf_of_not_center s L h00 hb0
    rw [hz] at h00 h10
    exact finish hz h00 h10 (by decide)

lemma center_leaf_codegree [Fintype A] [Fintype F] (s : I → F) (L : A → I → Prop)
    (p : F × F) (i : I) :
    codegree (Inc s L) (.inl p) (.inr (i,p.1*s i+p.2)) = Nat.card {a // L a i} := by
  let e : {a : Rows A F // Inc s L a (.inl p) ∧ Inc s L a (.inr (i,p.1*s i+p.2))} ≃
      {a : A // L a i} :=
    { toFun := fun a => ⟨a.val.2,a.property.2.1⟩
      invFun := fun a => ⟨(p,a.val),rfl,a.property,rfl⟩
      left_inv := fun a => Subtype.ext (Prod.ext a.property.1.symm rfl)
      right_inv := fun _ => rfl }
  exact Nat.card_congr e

lemma center_degree [Fintype A] [Fintype F] (s : I → F) (L : A → I → Prop) (p : F × F) :
    Nat.card {a : Rows A F // Inc s L a (.inl p)} = Nat.card A := by
  let e : {a : Rows A F // Inc s L a (.inl p)} ≃ A :=
    { toFun := fun a => a.val.2
      invFun := fun a => ⟨(p,a),rfl⟩
      left_inv := fun a => Subtype.ext (Prod.ext a.property.symm rfl)
      right_inv := fun _ => rfl }
  exact Nat.card_congr e

lemma leaf_degree [Fintype A] [Fintype F] (s : I → F) (L : A → I → Prop) (b : I × F) :
    Nat.card {a : Rows A F // Inc s L a (.inr b)} = Nat.card F*Nat.card {a // L a b.1} := by
  let e : {a : Rows A F // Inc s L a (.inr b)} ≃ F × {a // L a b.1} :=
    { toFun := fun a => (a.val.1.1,⟨a.val.2,a.property.1⟩)
      invFun := fun a => ⟨((a.1,b.2-a.1*s b.1),a.2.val),a.2.property,by dsimp; ring⟩
      left_inv := by
        intro a
        apply Subtype.ext
        dsimp only
        refine Prod.ext ?_ rfl
        refine Prod.ext rfl ?_
        have hh := a.property.2
        change b.2-a.val.1.1*s b.1 = a.val.1.2
        linear_combination hh
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_prod]

noncomputable def heavyCount {U V : Type*} (R : U → V → Prop) : ℕ :=
  Nat.card {p : V × V // 3 ≤ codegree R p.1 p.2}

lemma heavy_lower [Fintype A] [Fintype I] [Fintype F] (s : I → F) (L : A → I → Prop)
    (hL : ∀ i, 3 ≤ Nat.card {a // L a i}) :
    (Nat.card F)^2*Nat.card I ≤ heavyCount (Inc s L) := by
  let f : (F × F) × I → {p : Columns I F × Columns I F // 3 ≤ codegree (Inc s L) p.1 p.2} :=
    fun p => ⟨(.inl p.1,.inr (p.2,p.1.1*s p.2+p.1.2)),by
      rw [center_leaf_codegree]; exact hL p.2⟩
  have hf : Function.Injective f := by
    intro p q he
    have h1 := Sum.inl.inj (congrArg (fun a => a.val.1) he)
    have h2 := congrArg Prod.fst (Sum.inr.inj (congrArg (fun a => a.val.2) he))
    exact Prod.ext h1 h2
  simpa only [Nat.card_prod,pow_two] using Nat.card_le_card_of_injective f hf

lemma center_center_codegree [Fintype A] [Fintype F] (s : I → F) (L : A → I → Prop)
    {p q : F × F} (hpq : p ≠ q) : codegree (Inc s L) (.inl p) (.inl q) = 0 := by
  classical
  haveI : IsEmpty {a : Rows A F // Inc s L a (.inl p) ∧ Inc s L a (.inl q)} :=
    ⟨fun a => hpq (a.property.1.symm.trans a.property.2)⟩
  simp only [codegree,Nat.card_eq_fintype_card,Fintype.card_of_isEmpty]

lemma light_lower [Fintype A] [Fintype I] [Fintype F] (s : I → F) (L : A → I → Prop) :
    (Nat.card F)^4-(Nat.card F)^2 ≤ Erdos713ThetaCross.lightCount (Inc s L) := by
  classical
  let f : ↥((Finset.univ : Finset (F × F)).offDiag) →
      {p : Columns I F × Columns I F // codegree (Inc s L) p.1 p.2 ≤ 2} :=
    fun p => ⟨(.inl p.val.1,.inl p.val.2),by
      rw [center_center_codegree s L (Finset.mem_offDiag.mp p.property).2.2]
      decide⟩
  have hf : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    exact Prod.ext (Sum.inl.inj (congrArg (fun a => a.val.1) he))
      (Sum.inl.inj (congrArg (fun a => a.val.2) he))
  have hh := Nat.card_le_card_of_injective f hf
  have hcard : Nat.card ↥((Finset.univ : Finset (F × F)).offDiag) =
      (Nat.card F)^4-(Nat.card F)^2 := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_coe,Finset.offDiag_card,
      Finset.card_univ,Fintype.card_prod]
    congr 1 <;> ring
  rwa [hcard] at hh

#print axioms no_theta
#print axioms center_leaf_codegree
#print axioms leaf_degree
#print axioms heavy_lower
#print axioms light_lower
end Erdos713ThetaAffineStars
