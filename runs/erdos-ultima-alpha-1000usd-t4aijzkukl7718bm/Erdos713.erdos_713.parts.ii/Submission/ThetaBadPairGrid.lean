import FormalConjecturesUtil
import Submission.ThetaBadPairDeficiency
import Submission.ThetaPositiveCompletion

/-! A rigid theta-free grid of bad heavy pairs. Padding by allowed pair
rows controls the GLOBAL zero-pair count. This concerns an auxiliary
counting proposal, not a disproof of Erdos 713. -/
open Finset
open scoped Classical
namespace Erdos713ThetaBadPairGrid
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaHeavyMatching Erdos713ThetaRigidHeavyMatching
open Erdos713ThetaBadPairDeficiency
set_option maxHeartbeats 3000000

abbrev Book (N : ℕ) := Fin N × Fin N
abbrev Hub (N : ℕ) := (Fin 2 × Fin N) ⊕ Fin 2
abbrev Col (N : ℕ) := (Book N × Fin 2) ⊕ Hub N
abbrev Main (N : ℕ) := Book N × Fin 3
abbrev Rows (N : ℕ) := Main N ⊕ (Col N × Col N)

def anchor {N : ℕ} (p : Book N) (t : Fin 2) : Col N := .inl (p,t)
def leaf {N : ℕ} (s : Fin 2) (i : Fin N) : Col N := .inr (.inl (s,i))
def special {N : ℕ} (s : Fin 2) : Col N := .inr (.inr s)
def color {N : ℕ} : Hub N → Fin 3
  | .inl _ => 0
  | .inr s => ![1,2] s

def pick {N : ℕ} (p : Book N) (s : Fin 2) : Fin N := if s=0 then p.1 else p.2

def Base (N : ℕ) (a : Main N) : Col N → Prop
  | .inl p => a.1=p.1
  | .inr (.inl p) => a.2=0 ∧ pick a.1 p.1=p.2
  | .inr (.inr s) => a.2= ![1,2] s

def Zero {N : ℕ} : Col N → Col N → Prop
  | .inr x, .inr y => color x ≠ color y
  | _, _ => False

def Twin {N : ℕ} : Col N → Col N → Prop
  | .inl x, .inl y => x.1=y.1
  | _, _ => False

def Allowed {N : ℕ} (x y : Col N) : Prop := x ≠ y ∧ ¬ Zero x y ∧ ¬ Twin x y

def Inc (N : ℕ) : Rows N → Col N → Prop
  | .inl a, x => Base N a x
  | .inr p, x => Allowed p.1 p.2 ∧ (x=p.1 ∨ x=p.2)

lemma zero_symm {N : ℕ} {x y : Col N} (h : Zero x y) : Zero y x := by
  cases x <;> cases y <;> simp_all [Zero,ne_comm]
lemma not_zero_self {N : ℕ} (x : Col N) : ¬ Zero x x := by
  cases x <;> simp [Zero]
lemma twin_symm {N : ℕ} {x y : Col N} (h : Twin x y) : Twin y x := by
  cases x <;> cases y <;> simp_all [Twin]

lemma base_hub_color {N : ℕ} {a : Main N} {h : Hub N}
    (hh : Base N a (.inr h)) : a.2=color h := by
  cases h with
  | inl p => exact hh.1
  | inr s => exact hh

lemma base_common_unique {N : ℕ} {a b : Main N} (hab : a.1 ≠ b.1)
    {x y : Col N} (hax : Base N a x) (hbx : Base N b x)
    (hay : Base N a y) (hby : Base N b y) : x=y := by
  cases x with
  | inl p => exact (hab (hax.trans hbx.symm)).elim
  | inr x =>
    cases y with
    | inl p => exact (hab (hay.trans hby.symm)).elim
    | inr y =>
      cases x with
      | inl p =>
        cases y with
        | inl q =>
          obtain ⟨s,i⟩ := p
          obtain ⟨t,j⟩ := q
          fin_cases s <;> fin_cases t <;> simp only [Base,pick] at hax hbx hay hby
          · exact congrArg (fun i => (.inr (.inl (0,i)) : Col N)) (hax.2.symm.trans hay.2)
          · exact (hab (Prod.ext (hax.2.trans hbx.2.symm) (hay.2.trans hby.2.symm))).elim
          · exact (hab (Prod.ext (hay.2.trans hby.2.symm) (hax.2.trans hbx.2.symm))).elim
          · exact congrArg (fun i => (.inr (.inl (1,i)) : Col N)) (hax.2.symm.trans hay.2)
        | inr s =>
          have hc := base_hub_color hax
          have hd := base_hub_color hay
          fin_cases s <;> simp_all [color]
      | inr s =>
        cases y with
        | inl p =>
          have hc := base_hub_color hax
          have hd := base_hub_color hay
          fin_cases s <;> simp_all [color]
        | inr t =>
          have hc := base_hub_color hax
          have hd := base_hub_color hay
          fin_cases s <;> fin_cases t <;> simp_all [color]

lemma base_rigid (N : ℕ) (a b : Main N) (hab : a ≠ b) :
    (row (Base N) a ∩ row (Base N) b).card ≤ 2 := by
  by_cases hp : a.1=b.1
  · have hs : a.2 ≠ b.2 := fun he => hab (Prod.ext hp he)
    have hsub : row (Base N) a ∩ row (Base N) b ⊆ {anchor a.1 0,anchor a.1 1} := by
      intro x hx
      have hh : Base N a x ∧ Base N b x := by simpa only [mem_inter,mem_row] using hx
      cases x with
      | inl p =>
        obtain ⟨q,t⟩ := p
        have hq : a.1=q := hh.1
        fin_cases t <;> simp [anchor,hq]
      | inr h => exact (hs ((base_hub_color hh.1).trans (base_hub_color hh.2).symm)).elim
    exact (card_le_card hsub).trans card_le_two
  · apply (show (1 : ℕ) ≤ 2 by decide).trans' ?_
    apply card_le_one.mpr
    intro x hx y hy
    simp only [mem_inter,mem_row] at hx hy
    exact base_common_unique hp hx.1 hx.2 hy.1 hy.2

lemma new_card (N : ℕ) (p : Col N × Col N) : (row (Inc N) (.inr p)).card ≤ 2 := by
  apply (card_le_card (show row (Inc N) (.inr p) ⊆ {p.1,p.2} from ?_)).trans card_le_two
  intro x hx
  simpa only [mem_insert,mem_singleton] using ((mem_row (Inc N) (.inr p) x).mp hx).2

lemma rigid (N : ℕ) (a b : Rows N) (hab : a ≠ b) :
    (row (Inc N) a ∩ row (Inc N) b).card ≤ 2 := by
  cases a with
  | inl a =>
    cases b with
    | inl b => exact base_rigid N a b (fun he => hab (congrArg Sum.inl he))
    | inr b => exact (card_le_card inter_subset_right).trans (new_card N b)
  | inr a => exact (card_le_card inter_subset_left).trans (new_card N a)

lemma old_of_three {N : ℕ} {a : Rows N} {x y z : Col N}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : Inc N a x) (hy : Inc N a y) (hz : Inc N a z) : ∃ b, a=Sum.inl b := by
  cases a with
  | inl b => exact ⟨b,rfl⟩
  | inr p =>
    rcases hx.2 with hx | hx <;> rcases hy.2 with hy | hy <;>
      rcases hz.2 with hz | hz <;> simp_all

lemma no_zero_common {N : ℕ} {a : Rows N} {x y : Col N}
    (hx : Inc N a x) (hy : Inc N a y) : ¬ Zero x y := by
  cases a with
  | inl a =>
    cases x with
    | inl p => simp [Zero]
    | inr x =>
      cases y with
      | inl p => simp [Zero]
      | inr y => exact not_ne_iff.mpr ((base_hub_color hx).symm.trans (base_hub_color hy))
  | inr p =>
    have hn := hx.1.2.1
    rcases hx.2 with rfl | rfl <;> rcases hy.2 with rfl | rfl
    · exact not_zero_self _
    · exact hn
    · exact fun h => hn (zero_symm h)
    · exact not_zero_self _

lemma private_hub {N : ℕ} {a b : Main N} (hp : a.1=b.1) {x : Col N}
    (hx : Base N a x) (hn : ¬ Base N b x) :
    ∃ h : Hub N, x=.inr h ∧ a.2=color h := by
  cases x with
  | inl p => exact (hn (hp.symm.trans hx)).elim
  | inr h => exact ⟨h,rfl,base_hub_color hx⟩

/-- The padding never covers the private cross pairs of a double overlap. -/
theorem no_theta (N : ℕ) : ¬ HasTheta (Inc N) := by
  rintro ⟨f,g,hfi,hgi,h00,h10,h01,h11,h02,h22,h13,h23⟩
  have hn (i j : Fin 4) (hij : i ≠ j) : g i ≠ g j := fun he => hij (hgi he)
  obtain ⟨a,ha⟩ := old_of_three (hn 0 1 (by decide)) (hn 0 2 (by decide))
    (hn 1 2 (by decide)) h00 h01 h02
  obtain ⟨b,hb⟩ := old_of_three (hn 0 1 (by decide)) (hn 0 3 (by decide))
    (hn 1 3 (by decide)) h10 h11 h13
  rw [ha] at h00 h01 h02
  rw [hb] at h10 h11 h13
  have hab : a ≠ b := by
    intro he
    exact (by decide : (0 : Fin 3) ≠ 1) (hfi (ha.trans ((congrArg Sum.inl he).trans hb.symm)))
  have hp : a.1=b.1 := by
    by_contra hh
    exact hn 0 1 (by decide) (base_common_unique hh h00 h10 h01 h11)
  have hs : a.2 ≠ b.2 := fun he => hab (Prod.ext hp he)
  have hr : ∀ a b : Main N, a ≠ b → (row (Base N) a ∩ row (Base N) b).card ≤ 2 := base_rigid N
  have hx : ¬ Base N b (g 2) := by
    intro hx
    exact hab (Erdos713ThetaPositiveCompletion.eq_of_three (fun a b hab => by
      convert hr a b hab using 1
      congr 1
      ext x
      simp)
      (hn 0 1 (by decide)) (hn 0 2 (by decide)) (hn 1 2 (by decide))
      h00 h01 h02 h10 h11 hx)
  have hy : ¬ Base N a (g 3) := by
    intro hy
    exact hab (Erdos713ThetaPositiveCompletion.eq_of_three (fun a b hab => by
      convert hr a b hab using 1
      congr 1
      ext x
      simp)
      (hn 0 1 (by decide)) (hn 0 3 (by decide)) (hn 1 3 (by decide))
      h00 h01 hy h10 h11 h13)
  obtain ⟨x,hgx,hcx⟩ := private_hub hp h02 hx
  obtain ⟨y,hgy,hcy⟩ := private_hub hp.symm h13 hy
  apply no_zero_common h22 h23
  rw [hgx,hgy]
  exact fun he => hs (hcx.trans (he.trans hcy.symm))

noncomputable def anchorPair {N : ℕ} (p : Book N) : Pair (Col N) :=
  ⟨{anchor p 0,anchor p 1},mem_powersetCard.mpr ⟨subset_univ _,by simp [anchor]⟩⟩

lemma anchor_support {N : ℕ} (p : Book N) (s : Fin 3) :
    Sum.inl (p,s) ∈ supports (Inc N) (anchorPair p) := by
  simp [mem_supports,anchorPair,insert_subset_iff,singleton_subset_iff,mem_row,Inc,Base,anchor]

lemma anchor_heavy {N : ℕ} (p : Book N) : 3 ≤ (supports (Inc N) (anchorPair p)).card := by
  let f : Fin 3 → ↥(supports (Inc N) (anchorPair p)) :=
    fun s => ⟨.inl (p,s),anchor_support p s⟩
  have hi : Function.Injective f := by
    intro s t he
    exact congrArg Prod.snd (Sum.inl.inj (congrArg Subtype.val he))
  simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective f hi

lemma large_row {N : ℕ} (p : Book N) : (row (Inc N) (.inl (p,0))).card = 4 := by
  have he : row (Inc N) (.inl (p,0)) =
      {anchor p 0,anchor p 1,leaf 0 p.1,leaf 1 p.2} := by
    ext x
    cases x with
    | inl q =>
      obtain ⟨q,t⟩ := q
      fin_cases t <;> simp [mem_row,Inc,Base,anchor,leaf,eq_comm]
    | inr h =>
      cases h with
      | inl q =>
        obtain ⟨s,i⟩ := q
        fin_cases s <;> simp [mem_row,Inc,Base,anchor,leaf,pick,eq_comm]
      | inr s => fin_cases s <;> simp [mem_row,Inc,Base,anchor,leaf]
  rw [he]
  simp [anchor,leaf]

lemma new_no_twin {N : ℕ} {p : Col N × Col N} {x y : Col N}
    (hx : Inc N (.inr p) x) (hy : Inc N (.inr p) y) (hxy : x ≠ y) : ¬ Twin x y := by
  have hn := hx.1.2.2
  rcases hx.2 with rfl | rfl <;> rcases hy.2 with rfl | rfl
  · exact (hxy rfl).elim
  · exact hn
  · exact fun h => hn (twin_symm h)
  · exact (hxy rfl).elim

lemma no_exact_pair {N : ℕ} (p : Book N) (a : Rows N) :
    row (Inc N) a ≠ (anchorPair p).val := by
  intro he
  cases a with
  | inl a =>
    have hh : ∃ h : Hub N, Inc N (.inl a) (.inr h) := by
      obtain ⟨q,s⟩ := a
      fin_cases s
      · exact ⟨.inl (0,q.1),by simp [Inc,Base,pick]⟩
      · exact ⟨.inr 0,rfl⟩
      · exact ⟨.inr 1,rfl⟩
    obtain ⟨h,hh⟩ := hh
    have hm := (mem_row (Inc N) (.inl a) (.inr h)).mpr hh
    rw [he] at hm
    simp [anchorPair,anchor] at hm
  | inr q =>
    have h0 : Inc N (.inr q) (anchor p 0) := by
      apply (mem_row (Inc N) (.inr q) _).mp
      rw [he]
      simp [anchorPair]
    have h1 : Inc N (.inr q) (anchor p 1) := by
      apply (mem_row (Inc N) (.inr q) _).mp
      rw [he]
      simp [anchorPair]
    exact new_no_twin h0 h1 (by simp [anchor]) rfl

noncomputable def heavyAnchor {N : ℕ} (p : Book N) : HeavyPair (Inc N) :=
  ⟨anchorPair p,anchor_heavy p⟩

lemma bad_anchor {N : ℕ} (p : Book N) : Bad (Inc N) (heavyAnchor p) := by
  refine ⟨⟨.inl (p,0),anchor_support p 0,?_⟩,?_⟩
  · exact (large_row p).ge
  · rintro ⟨a,ha⟩
    exact no_exact_pair p a ha

lemma anchorPair_injective (N : ℕ) : Function.Injective (@anchorPair N) := by
  intro p q he
  have hm : anchor p 0 ∈ (anchorPair q).val := he ▸
    (show anchor p 0 ∈ (anchorPair p).val by simp [anchorPair])
  simpa [anchorPair,anchor] using hm

/-- The N^2 distinguished anchor pairs are all genuinely bad heavy pairs. -/
theorem bad_card_lower (N : ℕ) : N*N ≤ Nat.card (BadPair (Inc N)) := by
  let f : Book N → BadPair (Inc N) := fun p => ⟨heavyAnchor p,bad_anchor p⟩
  have hi : Function.Injective f := by
    intro p q he
    exact anchorPair_injective N (congrArg (fun x : BadPair (Inc N) => x.val.val) he)
  simpa only [Book,Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_fin] using
    Nat.card_le_card_of_injective f hi

lemma common_of_not_zero {N : ℕ} {x y : Col N} (hxy : x ≠ y) (hz : ¬ Zero x y) :
    ∃ a, Inc N a x ∧ Inc N a y := by
  by_cases ht : Twin x y
  · cases x with
    | inl p =>
      cases y with
      | inl q => exact ⟨.inl (p.1,1),rfl,ht⟩
      | inr q => exact ht.elim
    | inr p => exact ht.elim
  · exact ⟨.inr (x,y),⟨⟨hxy,hz,ht⟩,Or.inl rfl⟩,⟨⟨hxy,hz,ht⟩,Or.inr rfl⟩⟩

/-- Unordered distinct column pairs with no supporting row. -/
abbrev ZeroPair {A B : Type*} [Fintype A] [Fintype B] (R : A → B → Prop) :=
  {p : Pair B // (supports R p).card=0}

noncomputable def zeroChoices (N : ℕ) : Finset (Finset (Col N)) :=
  insert {special 0,special 1}
    ((univ : Finset ((Fin 2 × Fin N) × Fin 2)).image
      (fun p => {leaf p.1.1 p.1.2,special p.2}))

lemma zero_mem_choices {N : ℕ} {x y : Col N} (hz : Zero x y) : {x,y} ∈ zeroChoices N := by
  cases x with
  | inl p => exact hz.elim
  | inr x =>
    cases y with
    | inl p => exact hz.elim
    | inr y =>
      cases x with
      | inl p =>
        cases y with
        | inl q => exact (hz rfl).elim
        | inr s =>
          apply mem_insert_of_mem
          exact mem_image.mpr ⟨(p,s),mem_univ _,rfl⟩
      | inr s =>
        cases y with
        | inl p =>
          apply mem_insert_of_mem
          exact mem_image.mpr ⟨(p,s),mem_univ _,pair_comm _ _⟩
        | inr t =>
          fin_cases s <;> fin_cases t <;>
            simp_all [Zero,color,zeroChoices,special,pair_comm]

lemma zero_support_mem {N : ℕ} (p : ZeroPair (Inc N)) : p.val.val ∈ zeroChoices N := by
  obtain ⟨x,y,hxy,hpair⟩ := card_eq_two.mp (pair_card p.val)
  have hz : Zero x y := by
    by_contra hn
    obtain ⟨a,hax,hay⟩ := common_of_not_zero hxy hn
    have hm : a ∈ supports (Inc N) p.val := by
      rw [mem_supports,hpair]
      simp only [insert_subset_iff,singleton_subset_iff,mem_row]
      exact ⟨hax,hay⟩
    rw [card_eq_zero.mp p.property] at hm
    simp at hm
  rw [hpair]
  exact zero_mem_choices hz

lemma choices_card_le (N : ℕ) : (zeroChoices N).card ≤ 4*N+1 := by
  have hi := card_image_le (s := (univ : Finset ((Fin 2 × Fin N) × Fin 2)))
    (f := fun p => ({leaf p.1.1 p.1.2,special p.2} : Finset (Col N)))
  simp only [card_univ,Fintype.card_prod,Fintype.card_fin] at hi
  have hc := card_insert_le (special 0 |> fun x => ({x,special 1} : Finset (Col N)))
    ((univ : Finset ((Fin 2 × Fin N) × Fin 2)).image
      (fun p => {leaf p.1.1 p.1.2,special p.2}))
  change (zeroChoices N).card ≤ _ at hc
  omega

/-- This is a bound on ALL global zero pairs, not only chosen local witnesses. -/
theorem zero_card_upper (N : ℕ) : Nat.card (ZeroPair (Inc N)) ≤ 4*N+1 := by
  let f : ZeroPair (Inc N) → ↥(zeroChoices N) := fun p => ⟨p.val.val,zero_support_mem p⟩
  have hi : Function.Injective f := by
    intro p q he
    have hv : p.val.val=q.val.val := congrArg (fun r : ↥(zeroChoices N) => r.val) he
    apply Subtype.ext
    apply Subtype.ext
    exact hv
  have hh : Nat.card (ZeroPair (Inc N)) ≤ (zeroChoices N).card := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using
      Nat.card_le_card_of_injective f hi
  exact hh.trans (choices_card_le N)

/-- No fixed multiplicative charge of bad heavy pairs into global zero pairs
can hold under rigidity and theta exclusion alone. -/
theorem arbitrary_bad_zero_gap (C : ℕ) :
    ∃ N : ℕ, C*Nat.card (ZeroPair (Inc N)) < Nat.card (BadPair (Inc N)) := by
  let N := 8*C+8
  have hb := bad_card_lower N
  have hz := Nat.mul_le_mul_left C (zero_card_upper N)
  refine ⟨N,?_⟩
  have hp : C*(4*N+1) < N*N := by dsimp [N]; nlinarith
  exact (hz.trans_lt hp).trans_le hb

/-- The auxiliary failure holds with any real constant as well. -/
theorem arbitrary_real_bad_zero_gap (C : ℝ) :
    ∃ N : ℕ, C*(Nat.card (ZeroPair (Inc N)) : ℝ) < (Nat.card (BadPair (Inc N)) : ℝ) := by
  obtain ⟨K,hK⟩ := exists_nat_gt C
  obtain ⟨N,hN⟩ := arbitrary_bad_zero_gap K
  refine ⟨N,?_⟩
  have hn : (K : ℝ)*(Nat.card (ZeroPair (Inc N)) : ℝ) <
      (Nat.card (BadPair (Inc N)) : ℝ) := by exact_mod_cast hN
  exact (mul_le_mul_of_nonneg_right hK.le (Nat.cast_nonneg _)).trans_lt hn

/-- The counterexample's structural and counting properties hold on the
same finite relation. No bound on the number of rows is asserted. -/
theorem counterexample (C : ℕ) :
    ∃ N : ℕ, ¬ HasTheta (Inc N) ∧
      (∀ a b : Rows N, a ≠ b → (row (Inc N) a ∩ row (Inc N) b).card ≤ 2) ∧
      C*Nat.card (ZeroPair (Inc N)) < Nat.card (BadPair (Inc N)) := by
  obtain ⟨N,hN⟩ := arbitrary_bad_zero_gap C
  exact ⟨N,no_theta N,rigid N,hN⟩

/-- Negation of the proposed universal bad-pair/zero-pair estimate. This is
NOT the negation of the original graph-exponent conjecture. -/
theorem no_uniform_bad_zero_bound :
    ¬ ∃ C : ℕ, ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R →
      (∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2) →
      Nat.card (BadPair R) ≤ C*Nat.card (ZeroPair R) := by
  rintro ⟨C,hC⟩
  obtain ⟨N,hN⟩ := arbitrary_bad_zero_gap C
  have hh := hC (Rows N) (Col N) (Inc N) (no_theta N) (fun a b hab => by
    convert rigid N a b hab using 1
    congr 1
    ext x
    simp)
  exact (not_le_of_gt hN) hh

#print axioms arbitrary_real_bad_zero_gap
#print axioms counterexample
#print axioms no_uniform_bad_zero_bound

#print axioms bad_card_lower
#print axioms zero_card_upper
#print axioms arbitrary_bad_zero_gap

#print axioms rigid
#print axioms no_theta
end Erdos713ThetaBadPairGrid
