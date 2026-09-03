import FormalConjecturesUtil
import Submission.ThetaZeroPairs

/-! Linear transversal completion removes cross-copy zero pairs without
creating an oriented theta. This is not a counterexample to Erdős 713. -/
open Finset
namespace Erdos713ThetaTransversal
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaZeroPairs
variable {A I F : Type*} [Field F]
set_option maxHeartbeats 2000000

abbrev Rows (I A F : Type*) := (I × A) ⊕ (F × F)

def complete (s : I → F) (R : A → F → Prop) : Rows I A F → I × F → Prop
  | .inl a, b => a.1 = b.1 ∧ R a.2 b.2
  | .inr p, b => b.2 = p.1*s b.1+p.2

lemma line_unique (s : I → F) (hs : Function.Injective s)
    {p q : F × F} {x y : I × F} (hxy : x ≠ y)
    (hpx : complete s (fun (_ : A) (_ : F) => False) (.inr p) x)
    (hpy : complete s (fun (_ : A) (_ : F) => False) (.inr p) y)
    (hqx : complete s (fun (_ : A) (_ : F) => False) (.inr q) x)
    (hqy : complete s (fun (_ : A) (_ : F) => False) (.inr q) y) : p = q := by
  change x.2 = p.1*s x.1+p.2 at hpx
  change y.2 = p.1*s y.1+p.2 at hpy
  change x.2 = q.1*s x.1+q.2 at hqx
  change y.2 = q.1*s y.1+q.2 at hqy
  have hi : x.1 ≠ y.1 := by
    intro hi
    apply hxy
    exact Prod.ext hi (by rw [hpx,hpy,hi])
  have hz : (p.1-q.1)*(s x.1-s y.1) = 0 := by linear_combination -hpx+hpy+hqx-hqy
  have h1 : p.1 = q.1 := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right
    (sub_ne_zero.mpr (fun he => hi (hs he))))
  exact Prod.ext h1 (by rw [h1] at hpx; linear_combination hqx-hpx)

lemma old_of_same_block (s : I → F) (R : A → F → Prop)
    {a : Rows I A F} {x y : I × F} (hxy : x ≠ y) (hi : x.1 = y.1)
    (hx : complete s R a x) (hy : complete s R a y) : ∃ p : I × A, a = .inl p := by
  cases a with
  | inl p => exact ⟨p,rfl⟩
  | inr p => exact (hxy (Prod.ext hi (by change x.2 = _ at hx; change y.2 = _ at hy; rw [hx,hy,hi]))).elim

lemma branches_old (s : I → F) (hs : Function.Injective s) (R : A → F → Prop)
    {a b : Rows I A F} {x y : I × F} (hab : a ≠ b) (hxy : x ≠ y)
    (hax : complete s R a x) (hay : complete s R a y)
    (hbx : complete s R b x) (hby : complete s R b y) :
    (∃ p : I × A, a = .inl p) ∧ (∃ q : I × A, b = .inl q) := by
  cases a with
  | inl p =>
    have hi : x.1 = y.1 := hax.1.symm.trans hay.1
    exact ⟨⟨p,rfl⟩,old_of_same_block s R hxy hi hbx hby⟩
  | inr p =>
    cases b with
    | inl q =>
      have hi : x.1 = y.1 := hbx.1.symm.trans hby.1
      exact ⟨old_of_same_block s R hxy hi hax hay,⟨q,rfl⟩⟩
    | inr q =>
      have he := line_unique (A := A) s hs hxy hax hay hbx hby
      exact (hab (congrArg Sum.inr he)).elim

lemma complete_no_theta (s : I → F) (hs : Function.Injective s)
    {R : A → F → Prop} (hf : ¬ HasTheta R) : ¬ HasTheta (complete s R) := by
  rintro ⟨f,g,hfi,hgi,h00,h10,h01,h11,h02,h22,h13,h23⟩
  have hne (i j : Fin 4) (hij : i ≠ j) : g i ≠ g j := fun he => hij (hgi he)
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := branches_old s hs R
    (fun he => (by decide : (0 : Fin 3) ≠ 1) (hfi he))
    (hne 0 1 (by decide)) h00 h01 h10 h11
  rw [ha] at h00 h01 h02
  rw [hb] at h10 h11 h13
  have hab : a.1 = b.1 := h00.1.trans h10.1.symm
  have h23i : (g 2).1 = (g 3).1 := h02.1.symm.trans (hab.trans h13.1)
  obtain ⟨c,hc⟩ := old_of_same_block s R (hne 2 3 (by decide)) h23i h22 h23
  rw [hc] at h22 h23
  have hac : a.1 = c.1 := h02.1.trans h22.1.symm
  let f' : Fin 3 → A := ![a.2,b.2,c.2]
  let g' : Fin 4 → F := fun j => (g j).2
  have hmap (i : Fin 3) : f i = .inl (a.1,f' i) := by
    fin_cases i
    · simpa [f'] using ha
    · exact hb.trans (congrArg Sum.inl (Prod.ext hab.symm rfl))
    · exact hc.trans (congrArg Sum.inl (Prod.ext hac.symm rfl))
  have hmapg (i : Fin 4) : g i = (a.1,g' i) := by
    refine Prod.ext ?_ rfl
    fin_cases i
    · exact h00.1.symm
    · exact h01.1.symm
    · exact h02.1.symm
    · exact h13.1.symm.trans hab.symm
  have hfi' : Function.Injective f' := by
    intro i j he
    apply hfi
    rw [hmap,hmap,he]
  have hgi' : Function.Injective g' := by
    intro i j he
    apply hgi
    rw [hmapg,hmapg,he]
  exact hf ⟨f',g',hfi',hgi',h00.2,h10.2,h01.2,h11.2,h02.2,h22.2,h13.2,h23.2⟩

lemma cross_positive [Fintype A] [Fintype I] [Fintype F]
    (s : I → F) (hs : Function.Injective s) (R : A → F → Prop)
    (x y : I × F) (hi : x.1 ≠ y.1) : 0 < codegree (complete s R) x y := by
  classical
  let a : F := (x.2-y.2)/(s x.1-s y.1)
  let b : F := x.2-a*s x.1
  have hne : s x.1-s y.1 ≠ 0 := sub_ne_zero.mpr (fun he => hi (hs he))
  have ha : a*(s x.1-s y.1) = x.2-y.2 := div_mul_cancel₀ _ hne
  have hax : complete s R (.inr (a,b)) x := by dsimp [complete,b]; ring
  have hay : complete s R (.inr (a,b)) y := by dsimp [complete,b]; linear_combination ha
  have hp : 0 < Fintype.card {c : Rows I A F // complete s R c x ∧ complete s R c y} :=
    Fintype.card_pos_iff.mpr ⟨⟨.inr (a,b),hax,hay⟩⟩
  simpa only [codegree,Nat.card_eq_fintype_card] using hp

lemma zero_count_le [Fintype A] [Fintype I] [Fintype F]
    (s : I → F) (hs : Function.Injective s) (R : A → F → Prop) :
    (zeroSet (complete s R)).card ≤ Nat.card I*(Nat.card F)^2 := by
  classical
  have heq (p : ↥(zeroSet (complete s R))) : p.val.1.1 = p.val.2.1 := by
    by_contra hh
    have hc := cross_positive s hs R p.val.1 p.val.2 hh
    have hp : codegree (complete s R) p.val.1 p.val.2 = 0 := (mem_filter.mp p.property).2
    omega
  let f : ↥(zeroSet (complete s R)) → I × (F × F) :=
    fun p => (p.val.1.1,p.val.1.2,p.val.2.2)
  have hf : Function.Injective f := by
    intro p q hpq
    have hi := congrArg Prod.fst hpq
    have hj := congrArg (fun z : I × (F × F) => z.2.1) hpq
    have hk := congrArg (fun z : I × (F × F) => z.2.2) hpq
    apply Subtype.ext
    exact Prod.ext (Prod.ext hi hj) (Prod.ext ((heq p).symm.trans (hi.trans (heq q))) hk)
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,Fintype.card_prod,pow_two] using hh

omit [Field F] in
lemma rows_card [Fintype A] [Fintype I] [Fintype F] :
    Nat.card (Rows I A F) = Nat.card I*Nat.card A+(Nat.card F)^2 := by
  simp only [Rows,Nat.card_sum,Nat.card_prod,pow_two]

lemma edges_lower [Fintype A] [Fintype I] [Fintype F] (s : I → F) (R : A → F → Prop) :
    Nat.card I*Nat.card {p : A × F // R p.1 p.2} ≤
      Nat.card {p : Rows I A F × (I × F) // complete s R p.1 p.2} := by
  let f : I × {p : A × F // R p.1 p.2} →
      {p : Rows I A F × (I × F) // complete s R p.1 p.2} :=
    fun p => ⟨(.inl (p.1,p.2.val.1),(p.1,p.2.val.2)),rfl,p.2.property⟩
  have hf : Function.Injective f := by
    intro p q he
    have hrow := Sum.inl.inj (congrArg (fun z => z.val.1) he)
    have hcol := congrArg (fun z => z.val.2.2) he
    have hi : p.1 = q.1 := congrArg (fun z : I × A => z.1) hrow
    have hj : p.2.val.1 = q.2.val.1 := congrArg (fun z : I × A => z.2) hrow
    exact Prod.ext hi (Subtype.ext (Prod.ext hj hcol))
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf

lemma column_card [Fintype A] [Fintype I] [Fintype F] (s : I → F) (R : A → F → Prop)
    (c : I × F) : Nat.card {a : Rows I A F // complete s R a c} =
      Nat.card {a : A // R a c.2}+Nat.card F := by
  let e : {a : Rows I A F // complete s R a c} ≃ {a : A // R a c.2} ⊕ F :=
    { toFun := fun a => match a with
        | ⟨.inl p,hp⟩ => .inl ⟨p.2,hp.2⟩
        | ⟨.inr p,_⟩ => .inr p.1
      invFun := fun a => match a with
        | .inl a => ⟨.inl (c.1,a.val),rfl,a.property⟩
        | .inr t => ⟨.inr (t,c.2-t*s c.1),by dsimp [complete]; ring⟩
      left_inv := by
        rintro ⟨a,ha⟩
        apply Subtype.ext
        cases a with
        | inl p => exact congrArg Sum.inl (Prod.ext ha.1.symm rfl)
        | inr p =>
          apply congrArg Sum.inr
          refine Prod.ext (by rfl) ?_
          change c.2 = p.1*s c.1+p.2 at ha
          linear_combination ha
      right_inv := by intro a; cases a <;> rfl }
  rw [Nat.card_congr e,Nat.card_sum]

#print axioms complete_no_theta
#print axioms zero_count_le
#print axioms edges_lower
#print axioms column_card
end Erdos713ThetaTransversal
