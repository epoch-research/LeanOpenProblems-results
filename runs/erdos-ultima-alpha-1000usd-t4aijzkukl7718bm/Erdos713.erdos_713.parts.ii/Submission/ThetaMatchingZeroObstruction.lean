import FormalConjecturesUtil
import Submission.ThetaHeavyMatching

/-! Zero pairs cannot pay for the deficiency of a matching of heavy pairs
into supporting rows. This is an auxiliary obstruction, not a disproof of
Erdős 713 or of the density gap using all codegree-at-most-two pairs. -/
open Finset
open scoped Classical
namespace Erdos713ThetaMatchingZeroObstruction
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaHeavyMatching
set_option maxHeartbeats 2000000

abbrev Rows (n : ℕ) := Option (Fin n × Fin 2)
abbrev Cols (n : ℕ) := Fin n × Fin 3

def Inc (n : ℕ) : Rows n → Cols n → Prop
  | none, _ => True
  | some a, b => a.1 = b.1

lemma four_in_one_block {n : ℕ} (b : Fin 4 → Cols n)
    (hb : Function.Injective b) (i : Fin n) (hi : ∀ j, (b j).1 = i) : False := by
  have hs : Function.Injective (fun j : Fin 4 => (b j).2) := by
    intro j k he
    exact hb (Prod.ext ((hi j).trans (hi k).symm) he)
  have hc := Fintype.card_le_of_injective _ hs
  norm_num at hc

theorem no_theta (n : ℕ) : ¬ HasTheta (Inc n) := by
  rintro ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩
  have h01a : a 0 ≠ a 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (ha h)
  have h02a : a 0 ≠ a 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (ha h)
  have h12a : a 1 ≠ a 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (ha h)
  cases h0 : a 0 with
  | none =>
    cases h1 : a 1 with
    | none => exact h01a (h0.trans h1.symm)
    | some u =>
      cases h2 : a 2 with
      | none => exact h02a (h0.trans h2.symm)
      | some v =>
        simp only [h1,h2,Inc] at h10 h11 h22 h13 h23
        have huv : u.1 = v.1 := h13.trans h23.symm
        apply four_in_one_block b hb u.1
        intro j
        fin_cases j
        · exact h10.symm
        · exact h11.symm
        · exact h22.symm.trans huv.symm
        · exact h13.symm
  | some u =>
    cases h1 : a 1 with
    | none =>
      cases h2 : a 2 with
      | none => exact h12a (h1.trans h2.symm)
      | some v =>
        simp only [h0,h2,Inc] at h00 h01 h02 h22 h23
        have huv : u.1 = v.1 := h02.trans h22.symm
        apply four_in_one_block b hb u.1
        intro j
        fin_cases j
        · exact h00.symm
        · exact h01.symm
        · exact h02.symm
        · exact h23.symm.trans huv.symm
    | some v =>
      simp only [h0,h1,Inc] at h00 h10 h01 h02 h13
      have huv : u.1 = v.1 := h00.trans h10.symm
      apply four_in_one_block b hb u.1
      intro j
      fin_cases j
      · exact h00.symm
      · exact h01.symm
      · exact h02.symm
      · exact h13.symm.trans huv.symm

lemma codegree_eq {n : ℕ} (x y : Cols n) :
    codegree (Inc n) x y = if x.1 = y.1 then 3 else 1 := by
  classical
  by_cases he : x.1 = y.1
  · let e : {a : Rows n // Inc n a x ∧ Inc n a y} ≃ Option (Fin 2) := {
      toFun := fun a => a.val.map Prod.snd
      invFun := fun z => match z with
        | none => ⟨none,trivial,trivial⟩
        | some s => ⟨some (x.1,s),rfl,he⟩
      left_inv := by
        intro a
        rcases a with ⟨a,hax,hay⟩
        cases a with
        | none => rfl
        | some a =>
          apply Subtype.ext
          simp only [Option.map_some,Option.some.injEq]
          exact Prod.ext hax.symm rfl
      right_inv := by intro z; cases z <;> rfl }
    change Nat.card _ = _
    rw [Nat.card_congr e]
    simp [he,Nat.card_eq_fintype_card]
  · let e : {a : Rows n // Inc n a x ∧ Inc n a y} ≃ Unit := {
      toFun := fun _ => ()
      invFun := fun _ => ⟨none,trivial,trivial⟩
      left_inv := by
        intro a
        rcases a with ⟨a,hax,hay⟩
        cases a with
        | none => rfl
        | some a => exact (he (hax.symm.trans hay)).elim
      right_inv := by intro z; cases z; rfl }
    change Nat.card _ = _
    rw [Nat.card_congr e]
    simp [he,Nat.card_eq_fintype_card]

lemma no_zero_pairs {n : ℕ} (x y : Cols n) : 0 < codegree (Inc n) x y := by
  rw [codegree_eq]
  split_ifs <;> norm_num

/-- The three unordered pairs within each block, without repetitions. -/
def anchor {n : ℕ} (z : Fin n × Fin 3) : Pair (Cols n) :=
  ⟨{(z.1,z.2),(z.1,z.2+1)}, mem_powersetCard.mpr ⟨subset_univ _,by
    have h : z.2 ≠ z.2+1 := (by decide : ∀ j : Fin 3, j ≠ j+1) z.2
    exact Finset.card_pair (fun he => h (congrArg Prod.snd he))⟩⟩

lemma anchor_injective {n : ℕ} : Function.Injective (@anchor n) := by
  intro z w h
  have he : (anchor z).val = (anchor w).val := congrArg Subtype.val h
  have hm : (z.1,z.2) ∈ (anchor w).val := he ▸ (by simp [anchor])
  have hfirst : z.1 = w.1 := by
    simp only [anchor,mem_insert,mem_singleton,Prod.mk.injEq] at hm
    rcases hm with hm | hm <;> exact hm.1
  have hsecond := congrArg (Finset.image Prod.snd) he
  have hs : ({z.2,z.2+1} : Finset (Fin 3)) = {w.2,w.2+1} := by
    simpa only [anchor,image_insert,image_singleton] using hsecond
  have hi : Function.Injective (fun j : Fin 3 => ({j,j+1} : Finset (Fin 3))) := by decide
  exact Prod.ext hfirst (hi hs)

lemma anchor_heavy {n : ℕ} (z : Fin n × Fin 3) :
    3 ≤ (supports (Inc n) (anchor z)).card := by
  have he : supports (Inc n) (anchor z) =
      univ.filter (fun a => Inc n a (z.1,z.2) ∧ Inc n a (z.1,z.2+1)) := by
    ext a
    simp [mem_supports,anchor,insert_subset_iff,singleton_subset_iff,mem_row]
  rw [he]
  have hh := codegree_eq (z.1,z.2) (z.1,z.2+1)
  simpa only [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype] using hh.ge

lemma rows_card (n : ℕ) : Nat.card (Rows n) = 2*n+1 := by
  simp [Rows,Nat.card_eq_fintype_card,Nat.mul_comm]

lemma cols_card (n : ℕ) : Nat.card (Cols n) = 3*n := by
  simp [Cols,Nat.card_eq_fintype_card,Nat.mul_comm]

lemma light_iff {n : ℕ} (x y : Cols n) :
    codegree (Inc n) x y ≤ 2 ↔ x.1 ≠ y.1 := by
  rw [codegree_eq]
  split_ifs <;> simp_all

/-- The ordered light-pair count, with diagonals included in the domain.
It is large, so these examples do not refute the <=2-light density gap. -/
theorem light_card (n : ℕ) :
    Nat.card {p : Cols n × Cols n // codegree (Inc n) p.1 p.2 ≤ 2} =
      9*(n*n-n) := by
  let P := (univ : Finset (Fin n)).offDiag
  let e : {p : Cols n × Cols n // codegree (Inc n) p.1 p.2 ≤ 2} ≃
      P × (Fin 3 × Fin 3) := {
    toFun := fun p =>
      (⟨(p.val.1.1,p.val.2.1),mem_offDiag.mpr ⟨mem_univ _,mem_univ _,
        (light_iff _ _).mp p.property⟩⟩,(p.val.1.2,p.val.2.2))
    invFun := fun p => ⟨((p.1.val.1,p.2.1),(p.1.val.2,p.2.2)),
      (light_iff _ _).mpr (mem_offDiag.mp p.1.property).2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simp only [P,Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_coe,
    offDiag_card,card_univ,Fintype.card_fin]
  omega

/-- Triple-intersection rigidity is deliberately NOT present in this
example: the universal row and a block row share three columns. -/
lemma not_rigid (n : ℕ) (hn : 0 < n) :
    ¬ (∀ a b : Rows n, a ≠ b →
      (row (Inc n) a ∩ row (Inc n) b).card ≤ 2) := by
  intro h
  let b : Rows n := some (⟨0,hn⟩,0)
  have hb : (none : Rows n) ≠ b := by simp [b]
  have hi : Function.Injective (fun j : Fin 3 => ((⟨0,hn⟩ : Fin n),j)) := by
    intro i j he
    exact congrArg Prod.snd he
  have hs : univ.image (fun j : Fin 3 => ((⟨0,hn⟩ : Fin n),j)) ⊆
      row (Inc n) none ∩ row (Inc n) b := by
    intro x hx
    obtain ⟨j,_,rfl⟩ := mem_image.mp hx
    simp [mem_row,Inc,b]
  have hc := (card_le_card hs).trans (h none b hb)
  rw [card_image_of_injective _ hi,card_univ,Fintype.card_fin] at hc
  omega

/-- Any partial injective assignment misses at least n-1 of these heavy
pairs, regardless of which supporting rows it chooses. -/
theorem matching_deficit (n : ℕ) (S : Finset (Fin n × Fin 3))
    (f : S → Rows n) (hf : Function.Injective f) :
    n-1 ≤ 3*n-S.card := by
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe,Fintype.card_option,Fintype.card_prod,Fintype.card_fin] at hc
  omega

/-- Arbitrarily many heavy pairs must be left unmatched even though every
pair of columns has a common row. No small <=2-light-pair count is claimed. -/
theorem arbitrary_deficit (D : ℕ) :
    let n := D+2
    ¬ HasTheta (Inc n) ∧
      (∀ x y, 0 < codegree (Inc n) x y) ∧
      Function.Injective (@anchor n) ∧
      (∀ z, 3 ≤ (supports (Inc n) (anchor z)).card) ∧
      ∀ (S : Finset (Fin n × Fin 3)) (f : S → Rows n),
        Function.Injective f → D < 3*n-S.card := by
  dsimp only
  refine ⟨no_theta _,no_zero_pairs,anchor_injective,anchor_heavy,?_⟩
  intro S f hf
  have hh := matching_deficit (D+2) S f hf
  omega

#print axioms no_theta
#print axioms codegree_eq
#print axioms light_card
#print axioms not_rigid
#print axioms arbitrary_deficit
end Erdos713ThetaMatchingZeroObstruction
