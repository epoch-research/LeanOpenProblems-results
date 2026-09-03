import Submission.StaticShearerBarrier

/-!
A limitation of static graph polynomials AFTER pure-prime conditioning.
This is not a covering-system theorem.
-/
namespace Erdos7ConditionedStarPolynomial
open scoped BigOperators
open Erdos7StaticShearerBarrier
set_option maxHeartbeats 2000000

lemma prime_sums_after_cutoff (B : ℝ) (N : ℕ) :
    ∃ s : Finset Nat.Primes, (∀ p ∈ s, N < (p : ℕ)) ∧
      B < ∑ p ∈ s, (1 / (p : ℝ)) := by
  classical
  let t : Finset Nat.Primes := (Finset.range (N+1)).subtype Nat.Prime
  obtain ⟨u, hu⟩ := prime_reciprocal_sums_unbounded
    (B + ∑ p ∈ t, (1/(p : ℝ)))
  refine ⟨u \ t, ?_, ?_⟩
  · intro p hp
    have hn := (Finset.mem_sdiff.mp hp).2
    have hh : ¬ (p : ℕ) < N+1 := by
      intro h
      exact hn (Finset.mem_subtype.mpr (Finset.mem_range.mpr h))
    omega
  · have he := Finset.sum_sdiff (Finset.inter_subset_left (s₁ := u) (s₂ := t))
      (f := fun p : Nat.Primes => (1/(p : ℝ)))
    have hle : (∑ p ∈ u ∩ t, (1/(p : ℝ))) ≤ ∑ p ∈ t, (1/(p : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (by intros; positivity)
    have hd : u \ (u ∩ t) = u \ t := by ext p; simp
    rw [hd] at he
    linarith

noncomputable def polynomial (s : Finset Nat.Primes) : ℝ :=
  (∑ t ∈ s.powerset, ∏ p ∈ t, -(1/(8*((p : ℝ)-1)))) - 1/8

lemma polynomial_eq (s : Finset Nat.Primes) :
    polynomial s = (∏ p ∈ s, (1-1/(8*((p : ℝ)-1)))) - 1/8 := by
  unfold polynomial
  rw [← Finset.prod_one_add]
  simp only [sub_eq_add_neg]

theorem exists_negative :
    ∃ s : Finset Nat.Primes, (∀ p ∈ s, 15 < (p : ℕ)) ∧ polynomial s < 0 := by
  obtain ⟨s, hs, hsum⟩ := prime_sums_after_cutoff 64 15
  let w : Nat.Primes → ℝ := fun p => 1/(8*((p : ℝ)-1))
  have hw : ∀ p ∈ s, 0 ≤ w p ∧ w p ≤ 1 := by
    intro p hp
    have hh : (15 : ℝ) < (p : ℕ) := by exact_mod_cast hs p hp
    dsimp [w]
    constructor
    · exact div_nonneg (by norm_num) (by linarith)
    · apply (div_le_iff₀ (by linarith : 0 < 8*((p : ℝ)-1))).mpr
      linarith
  have hsumle : (∑ p ∈ s, (1/(p : ℝ))) / 8 ≤ ∑ p ∈ s, w p := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro p hp
    have hh : (15 : ℝ) < (p : ℕ) := by exact_mod_cast hs p hp
    dsimp [w]
    rw [div_div]
    apply one_div_le_one_div_of_le (by linarith) (by linarith)
  have ht : 8 < ∑ p ∈ s, w p := by linarith
  have hb := product_complement_bound s w hw
  have hn : 0 ≤ ∏ p ∈ s, (1-w p) :=
    Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (hw p hp).2)
  refine ⟨s, hs, ?_⟩
  rw [polynomial_eq]
  change (∏ p ∈ s, (1-w p)) - 1/8 < 0
  by_contra! h
  nlinarith

abbrev Fibers (s : Finset Nat.Primes) := (p : s) → Fin ((p.val : ℕ)-1)
abbrev Space (s : Finset Nat.Primes) := Fin 2 × Fin 4 × Fibers s

def center {s : Finset Nat.Primes} (x : Space s) : Prop := x.1=0 ∧ x.2.1=0

def leaf {s : Finset Nat.Primes} (p : s) (x : Space s) : Prop :=
  x.1=1 ∧ x.2.1=1 ∧ (x.2.2 p).val=0

instance {s : Finset Nat.Primes} (x : Space s) : Decidable (center x) := by
  unfold center; infer_instance
instance {s : Finset Nat.Primes} (p : s) (x : Space s) : Decidable (leaf p x) := by
  unfold leaf; infer_instance

noncomputable def probability {s : Finset Nat.Primes} (P : Space s → Prop)
    [DecidablePred P] : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / Fintype.card (Space s)

lemma fiber_card (s : Finset Nat.Primes) :
    Fintype.card (Fibers s) = ∏ p : s, ((p.val : ℕ)-1) := by
  simp [Fibers, Fintype.card_pi]

lemma space_card (s : Finset Nat.Primes) :
    Fintype.card (Space s) = 8 * Fintype.card (Fibers s) := by
  simp [Space, Fintype.card_prod]; omega

lemma fibers_nonempty (s : Finset Nat.Primes) : Nonempty (Fibers s) := by
  refine ⟨fun p => ⟨0, ?_⟩⟩
  have := p.val.property.two_le
  omega

lemma center_count (s : Finset Nat.Primes) :
    (Finset.univ.filter (@center s)).card = Fintype.card (Fibers s) := by
  let e : {x : Space s // center x} ≃ Fibers s :=
    { toFun := fun x => x.val.2.2
      invFun := fun f => ⟨(0,0,f), rfl, rfl⟩
      left_inv := by
        intro x
        apply Subtype.ext
        rcases x with ⟨⟨a,b,f⟩,ha,hb⟩
        dsimp at ha hb ⊢
        subst a; subst b; rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_subtype] using Fintype.card_congr e

lemma center_probability (s : Finset Nat.Primes) : probability (@center s) = 1/8 := by
  letI := fibers_nonempty s
  have hc : (Fintype.card (Fibers s) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Fibers s) ≠ 0)
  unfold probability
  rw [center_count, space_card, Nat.cast_mul]
  norm_num only [Nat.cast_ofNat]
  field_simp [hc]

lemma fiber_slice_count (s : Finset Nat.Primes) (p : s) :
    (Finset.univ.filter (fun f : Fibers s => (f p).val=0)).card =
      ∏ q ∈ (Finset.univ : Finset s).erase p, ((q.val : ℕ)-1) := by
  classical
  let z : Fin ((p.val : ℕ)-1) := ⟨0, by have := p.val.property.two_le; omega⟩
  have he (f : Fibers s) : (f p).val=0 ↔ f p=z := by
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp_rw [he]
  simpa using Fintype.card_filter_piFinset_eq_of_mem
    (fun q : s => (Finset.univ : Finset (Fin ((q.val : ℕ)-1)))) p (Finset.mem_univ z)

lemma leaf_count (s : Finset Nat.Primes) (p : s) :
    (Finset.univ.filter (leaf p)).card =
      (Finset.univ.filter (fun f : Fibers s => (f p).val=0)).card := by
  let e : {x : Space s // leaf p x} ≃ {f : Fibers s // (f p).val=0} :=
    { toFun := fun x => ⟨x.val.2.2, x.property.2.2⟩
      invFun := fun f => ⟨(1,1,f.val), rfl, rfl, f.property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        rcases x with ⟨⟨a,b,f⟩,ha,hb,hf⟩
        dsimp at ha hb ⊢
        subst a; subst b; rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_subtype] using Fintype.card_congr e

lemma leaf_probability (s : Finset Nat.Primes) (p : s) :
    probability (leaf p) = 1/(8*((p.val : ℝ)-1)) := by
  classical
  let n : ℕ := ∏ q ∈ (Finset.univ : Finset s).erase p, ((q.val : ℕ)-1)
  have hnp : 0 < n := Finset.prod_pos (fun q _ => by have := q.val.property.two_le; omega)
  have hpr := Finset.mul_prod_erase (Finset.univ : Finset s)
    (fun q => ((q.val : ℕ)-1)) (Finset.mem_univ p)
  have hf : Fintype.card (Fibers s) = ((p.val : ℕ)-1)*n := by
    rw [fiber_card]; exact hpr.symm
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hnp.ne'
  have hp : (p.val : ℝ)-1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ (p.val : ℕ) := by exact_mod_cast p.val.property.two_le
    linarith
  unfold probability
  rw [leaf_count, fiber_slice_count, space_card, hf]
  change (n : ℝ) / ((8 * (((p.val : ℕ)-1)*n) : ℕ) : ℝ) = _
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub p.val.property.one_le]
  norm_num only [Nat.cast_ofNat, Nat.cast_one]
  field_simp [hp, hn]

lemma incompatibility_star (s : Finset Nat.Primes) (i j : Option s) :
    (¬ ∃ x : Space s, (match i with | none => center x | some p => leaf p x) ∧
      (match j with | none => center x | some p => leaf p x)) ↔
      (i=none ∧ j≠none) ∨ (j=none ∧ i≠none) := by
  let z : Fibers s := fun p => ⟨0, by have := p.val.property.two_le; omega⟩
  cases i <;> cases j
  · apply iff_of_false ?_ (by simp)
    intro h; exact h ⟨(0,0,z), ⟨rfl,rfl⟩, ⟨rfl,rfl⟩⟩
  · apply iff_of_true ?_ (by simp)
    rintro ⟨x,hc,hl⟩
    have h := hc.1.symm.trans hl.1
    exact (by decide : (0 : Fin 2) ≠ 1) h
  · apply iff_of_true ?_ (by simp)
    rintro ⟨x,hl,hc⟩
    have h := hc.1.symm.trans hl.1
    exact (by decide : (0 : Fin 2) ≠ 1) h
  · apply iff_of_false ?_ (by simp)
    intro h; exact h ⟨(1,1,z), ⟨rfl,rfl,rfl⟩, ⟨rfl,rfl,rfl⟩⟩

#print axioms exists_negative
#print axioms center_probability
#print axioms leaf_probability
#print axioms incompatibility_star
end Erdos7ConditionedStarPolynomial
