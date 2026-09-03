import FormalConjecturesUtil
import Submission.ThetaBadPairGrid

/-! Positive-light completion preserves old bad heavy pairs and the global
unordered zero-pair count. Thus the bad/zero bound fails even after every
positive codegree is at least three. The density gap remains unresolved. -/
open Finset
open scoped Classical
namespace Erdos713ThetaBadPairCompletion
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaHeavyMatching Erdos713ThetaRigidHeavyMatching
open Erdos713ThetaBadPairDeficiency
open Erdos713ThetaBadPairGrid (ZeroPair)
open Erdos713ThetaPositiveCompletion
set_option maxHeartbeats 2000000
variable {A B : Type*} [Fintype A] [Fintype B]

lemma supports_card_eq_codegree (R : A → B → Prop) (p : Pair B) {x y : B}
    (hp : p.val={x,y}) : (supports R p).card=codegree R x y := by
  rw [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype]
  congr 1
  ext a
  simp [mem_supports,hp,insert_subset_iff,singleton_subset_iff,mem_row]

lemma supports_mono (R : A → B → Prop) (p : Pair B) :
    (supports R p).card ≤ (supports (fill R) p).card := by
  obtain ⟨x,y,_hxy,hp⟩ := card_eq_two.mp (pair_card p)
  rw [supports_card_eq_codegree R p hp,supports_card_eq_codegree (fill R) p hp]
  exact codegree_mono R x y

noncomputable def filledHeavy {R : A → B → Prop} (p : HeavyPair R) : HeavyPair (fill R) :=
  ⟨p.val,p.property.trans (supports_mono R p.val)⟩

/-- Completion does not add an exact-pair row for an already heavy pair. -/
theorem preserve_bad {R : A → B → Prop} {p : HeavyPair R} (h : Bad R p) :
    Bad (fill R) (filledHeavy p) := by
  obtain ⟨⟨a,ha,hd⟩,hn⟩ := h
  refine ⟨⟨.inl a,?_,hd⟩,?_⟩
  · exact (mem_supports (fill R) _ _).mpr ((mem_supports R _ _).mp ha)
  · rintro ⟨a,he⟩
    cases a with
    | inl a => exact hn ⟨a,he⟩
    | inr q =>
      have hp : p.val.val={q.1.val.1,q.1.val.2} := he.symm.trans (new_row R q)
      have h3 := p.property
      rw [supports_card_eq_codegree R p.val hp] at h3
      have h2 := q.1.property.2
      omega

/-- This monotonicity does not require theta exclusion or rigidity. -/
theorem bad_card_mono (R : A → B → Prop) :
    Nat.card (BadPair R) ≤ Nat.card (BadPair (fill R)) := by
  let f : BadPair R → BadPair (fill R) := fun p => ⟨filledHeavy p.val,preserve_bad p.property⟩
  have hi : Function.Injective f := by
    intro p q he
    have hv : p.val.val=q.val.val := congrArg (fun r : BadPair (fill R) => r.val.val) he
    apply Subtype.ext
    apply Subtype.ext
    exact hv
  exact Nat.card_le_card_of_injective f hi

/-- Completion preserves unordered distinct zero pairs exactly. -/
theorem zero_pair_card_eq (R : A → B → Prop) :
    Nat.card (ZeroPair (fill R))=Nat.card (ZeroPair R) := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro p
  obtain ⟨x,y,_hxy,hp⟩ := card_eq_two.mp (pair_card p)
  rw [supports_card_eq_codegree (fill R) p hp,supports_card_eq_codegree R p hp]
  exact zero_iff R x y

/-- The unbounded bad/zero ratio survives normalization. -/
theorem completed_gap (C : ℕ) :
    ∃ N : ℕ,
      C*Nat.card (ZeroPair (fill (Erdos713ThetaBadPairGrid.Inc N))) <
        Nat.card (BadPair (fill (Erdos713ThetaBadPairGrid.Inc N))) := by
  obtain ⟨N,hN⟩ := Erdos713ThetaBadPairGrid.arbitrary_bad_zero_gap C
  refine ⟨N,?_⟩
  rw [zero_pair_card_eq]
  exact hN.trans_le (bad_card_mono _)

/-- All normalized hypotheses and the failed charge hold on one relation. -/
theorem completed_counterexample (C : ℕ) :
    ∃ N : ℕ, ¬ HasTheta (fill (Erdos713ThetaBadPairGrid.Inc N)) ∧
      (∀ a b : Rows (Erdos713ThetaBadPairGrid.Inc N), a ≠ b →
        (row (fill (Erdos713ThetaBadPairGrid.Inc N)) a ∩
          row (fill (Erdos713ThetaBadPairGrid.Inc N)) b).card ≤ 2) ∧
      (∀ x y, codegree (fill (Erdos713ThetaBadPairGrid.Inc N)) x y=0 ∨
        3 ≤ codegree (fill (Erdos713ThetaBadPairGrid.Inc N)) x y) ∧
      C*Nat.card (ZeroPair (fill (Erdos713ThetaBadPairGrid.Inc N))) <
        Nat.card (BadPair (fill (Erdos713ThetaBadPairGrid.Inc N))) := by
  obtain ⟨N,hN⟩ := completed_gap C
  have hf := no_theta (Erdos713ThetaBadPairGrid.no_theta N) (fun a b hab => by
    convert Erdos713ThetaBadPairGrid.rigid N a b hab using 1
    congr 1
    ext x
    simp)
  refine ⟨N,hf,?_,zero_or_heavy _,hN⟩
  intro a b hab
  have hh := rigid (R := Erdos713ThetaBadPairGrid.Inc N) (fun a b hab => by
    convert Erdos713ThetaBadPairGrid.rigid N a b hab using 1
    congr 1
    ext x
    simp) a b hab
  convert hh using 1
  congr 1
  ext x
  simp

/-- This negates an auxiliary completed-case bound, not Erdos 713. -/
theorem no_completed_bad_zero_bound :
    ¬ ∃ C : ℕ, ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R →
      (∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2) →
      (∀ x y, codegree R x y=0 ∨ 3 ≤ codegree R x y) →
      Nat.card (BadPair R) ≤ C*Nat.card (ZeroPair R) := by
  rintro ⟨C,hC⟩
  obtain ⟨N,hf,hr,hheavy,hgap⟩ := completed_counterexample C
  exact (not_le_of_gt hgap)
    (hC (Rows (Erdos713ThetaBadPairGrid.Inc N)) (Erdos713ThetaBadPairGrid.Col N)
      (fill (Erdos713ThetaBadPairGrid.Inc N)) hf (fun a b hab => by
        convert hr a b hab using 1
        congr 1
        ext x
        simp) hheavy)

/-- With no zero diagonal, every ordered zero pair maps injectively to an
unordered zero pair together with one of its two endpoints. -/
theorem ordered_zero_le_twice (R : A → B → Prop)
    (hd : ∀ x, 0 < codegree R x x) : zeroCount R ≤ 2*Nat.card (ZeroPair R) := by
  let Z := {p : B × B // codegree R p.1 p.2=0}
  have hne (p : Z) : p.val.1 ≠ p.val.2 := by
    intro he
    have hh := p.property
    rw [← he] at hh
    exact (Nat.ne_of_gt (hd p.val.1)) hh
  let P : Z → ZeroPair R := fun p =>
    ⟨⟨{p.val.1,p.val.2},mem_powersetCard.mpr ⟨subset_univ _,card_pair (hne p)⟩⟩,by
      rw [supports_card_eq_codegree R _ rfl]
      exact p.property⟩
  let f : Z → (Σ p : ZeroPair R, ↥p.val.val) :=
    fun p => ⟨P p,⟨p.val.1,by simp [P]⟩⟩
  have hi : Function.Injective f := by
    intro p q he
    have hset : ({p.val.1,p.val.2} : Finset B)={q.val.1,q.val.2} :=
      congrArg (fun r : (Σ p : ZeroPair R, ↥p.val.val) => r.1.val.val) he
    have hfst : p.val.1=q.val.1 :=
      congrArg (fun r : (Σ p : ZeroPair R, ↥p.val.val) => r.2.val) he
    have hm : p.val.2 ∈ ({q.val.1,q.val.2} : Finset B) := hset ▸ (by simp)
    simp only [mem_insert,mem_singleton] at hm
    rcases hm with he2 | he2
    · exact (hne p (hfst.trans he2.symm)).elim
    · exact Subtype.ext (Prod.ext hfst he2)
  have hc : Nat.card (Σ p : ZeroPair R, ↥p.val.val)=2*Nat.card (ZeroPair R) := by
    rw [Nat.card_sigma]
    have hh (p : ZeroPair R) : Nat.card ↥p.val.val=2 := by
      rw [Nat.card_eq_fintype_card,Fintype.card_coe,pair_card]
    simp_rw [hh]
    simp [mul_comm,Nat.card_eq_fintype_card]
  change Nat.card Z ≤ _
  exact (Nat.card_le_card_of_injective f hi).trans hc.le

lemma grid_column_nonempty {N : ℕ} (hN : 0 < N) (x : Erdos713ThetaBadPairGrid.Col N) :
    ∃ a, Erdos713ThetaBadPairGrid.Inc N a x := by
  cases x with
  | inl p => exact ⟨.inl (p.1,1),rfl⟩
  | inr h =>
    cases h with
    | inl p =>
      refine ⟨.inl ((p.2,p.2),0),rfl,?_⟩
      dsimp [Erdos713ThetaBadPairGrid.pick]
      split <;> rfl
    | inr s =>
      let i : Fin N := ⟨0,hN⟩
      fin_cases s
      · exact ⟨.inl ((i,i),1),rfl⟩
      · exact ⟨.inl ((i,i),2),rfl⟩

lemma grid_diagonal_pos {N : ℕ} (hN : 0 < N) (x : Erdos713ThetaBadPairGrid.Col N) :
    0 < codegree (Erdos713ThetaBadPairGrid.Inc N) x x := by
  obtain ⟨a,ha⟩ := grid_column_nonempty hN x
  haveI : Nonempty {a : Erdos713ThetaBadPairGrid.Rows N //
      Erdos713ThetaBadPairGrid.Inc N a x ∧ Erdos713ThetaBadPairGrid.Inc N a x} := ⟨⟨a,ha,ha⟩⟩
  exact Nat.card_pos

/-- The ordered count includes diagonals; their absence here is proved,
not silently assumed. -/
theorem grid_ordered_zero_upper {N : ℕ} (hN : 0 < N) :
    zeroCount (fill (Erdos713ThetaBadPairGrid.Inc N)) ≤ 8*N+2 := by
  rw [zeroCount_eq]
  have hh := ordered_zero_le_twice (Erdos713ThetaBadPairGrid.Inc N) (grid_diagonal_pos hN)
  have hz := Nat.mul_le_mul_left 2 (Erdos713ThetaBadPairGrid.zero_card_upper N)
  omega

/-- Bad pairs also have unbounded ratio to the ordered zero count used by
the completed density-gap formulation. The row term is not controlled. -/
theorem ordered_completed_gap (C : ℕ) :
    ∃ N : ℕ, C*zeroCount (fill (Erdos713ThetaBadPairGrid.Inc N)) <
      Nat.card (BadPair (fill (Erdos713ThetaBadPairGrid.Inc N))) := by
  let N := 16*C+16
  have hN : 0 < N := by dsimp [N]; omega
  have hz := Nat.mul_le_mul_left C (grid_ordered_zero_upper hN)
  have hb := (Erdos713ThetaBadPairGrid.bad_card_lower N).trans
    (bad_card_mono (Erdos713ThetaBadPairGrid.Inc N))
  have hp : C*(8*N+2) < N*N := by dsimp [N]; nlinarith
  exact ⟨N,(hz.trans_lt hp).trans_le hb⟩

/-- The failed bound cannot be rescued merely by changing to the ordered
zero-count convention of CompletedGap. -/
theorem no_completed_ordered_bad_zero_bound :
    ¬ ∃ C : ℕ, ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R →
      (∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2) →
      (∀ x y, codegree R x y=0 ∨ 3 ≤ codegree R x y) →
      Nat.card (BadPair R) ≤ C*zeroCount R := by
  rintro ⟨C,hC⟩
  obtain ⟨N,hgap⟩ := ordered_completed_gap C
  have hf := no_theta (Erdos713ThetaBadPairGrid.no_theta N) (fun a b hab => by
    convert Erdos713ThetaBadPairGrid.rigid N a b hab using 1
    congr 1
    ext x
    simp)
  have hr := rigid (R := Erdos713ThetaBadPairGrid.Inc N) (fun a b hab => by
    convert Erdos713ThetaBadPairGrid.rigid N a b hab using 1
    congr 1
    ext x
    simp)
  exact (not_le_of_gt hgap)
    (hC (Rows (Erdos713ThetaBadPairGrid.Inc N)) (Erdos713ThetaBadPairGrid.Col N)
      (fill (Erdos713ThetaBadPairGrid.Inc N)) hf hr (zero_or_heavy _))

#print axioms ordered_zero_le_twice
#print axioms grid_diagonal_pos
#print axioms grid_ordered_zero_upper
#print axioms ordered_completed_gap
#print axioms no_completed_ordered_bad_zero_bound

#print axioms preserve_bad
#print axioms bad_card_mono
#print axioms zero_pair_card_eq
#print axioms completed_counterexample
#print axioms no_completed_bad_zero_bound
end Erdos713ThetaBadPairCompletion
