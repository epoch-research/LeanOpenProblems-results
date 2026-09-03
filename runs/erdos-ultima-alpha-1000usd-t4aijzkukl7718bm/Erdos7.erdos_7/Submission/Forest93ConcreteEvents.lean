import Submission.Forest93ConcreteData
import Submission.Forest93Events

/-! Actual residue boxes for the forest certificate. -/
namespace Erdos7Forest93Concrete
open scoped BigOperators
open Erdos7Forest93Certificate Erdos7Forest93Shapes Erdos7ForestRestricted
open Erdos7ForestUnion Erdos7RootOverlapCompensation Erdos7ForestProduct
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option autoImplicit false

abbrev Space := ∀ j,Coord j
noncomputable def measure (b : Fin 9) : Space → ℚ := productWeight Coord (law b)
def residueBox (i : Index) (r : Space) : Space → Prop := box Coord (fun j x => x ∈ boxSection i r j)
def good (i : Index) (r : Space) : Prop :=
  (exponent i 0 ≠ 0 → (r 0).val%3 ≠ 0) ∧
  (∀ j : Fin 7,exponent i j.succ ≠ 0 → r j.succ ≠ zeroLeaf j)
noncomputable def rootProbability (b r : Fin 9) : ℚ :=
  (branch 0 b ⟨r.val%3,Nat.mod_lt _ (by decide)⟩).card/5

lemma measure_nonneg (b : Fin 9) (x : Space) : 0 ≤ measure b x :=
  productWeight_nonneg Coord (law b) (law_nonneg b) x
lemma measure_full (b : Fin 9) (hb : b.val%3 ≠ 0) : mass (measure b) (fun _ => True) = 1 :=
  productWeight_mass Coord (law b) (law_sum b hb)
lemma residueBox_mass (b : Fin 9) (i : Index) (r : Space) :
    mass (measure b) (residueBox i r) = ∏ j,mass (law b j) (fun x => x ∈ boxSection i r j) :=
  box_mass Coord (law b) _
lemma residueBox_mass_le (b : Fin 9) (hb : b.val%3 ≠ 0) (i : Index) (hi : mixed i) (r : Space) :
    mass (measure b) (residueBox i r) ≤ weight i := by
  rw [residueBox_mass,weight_product i hi]
  exact Finset.prod_le_prod (fun j _ => mass_nonneg _ (law_nonneg b j) _)
    (fun j _ => section_mass_le b hb i r j)
lemma residueBox_independent (b : Fin 9) (hb : b.val%3 ≠ 0) (i k : Index) (r s : Space)
    (hd : ∀ j,exponent i j = 0 ∨ exponent k j = 0) :
    mass (measure b) (fun x => residueBox i r x ∧ residueBox k s x) =
      mass (measure b) (residueBox i r)*mass (measure b) (residueBox k s) := by
  apply disjoint_box_independent Coord (law b) (law_sum b hb)
  intro j
  rcases hd j with h | h
  · left; intro a; rw [section_zero i r j h]; exact Finset.mem_univ _
  · right; intro a; rw [section_zero k s j h]; exact Finset.mem_univ _

lemma section_mass_zero_exp (b : Fin 9) (hb : b.val%3 ≠ 0) (i : Index) (r : Space)
    (j : Fin 8) (hj : exponent i j = 0) :
    mass (law b j) (fun x => x ∈ boxSection i r j) = 1 := by
  rw [section_zero i r j hj]
  simpa [mass,bit] using law_sum b hb j
lemma root_mass_one_exp (b : Fin 9) (i : Index) (r : Space) (hi : exponent i 0 = 1) :
    mass (law b 0) (fun x => x ∈ boxSection i r 0) =
      (branch 0 b ⟨(r 0).val%3,Nat.mod_lt _ (by decide)⟩).card/(root b).card := by
  have h0 : exponent i 0 ≠ 0 := by omega
  change mass (restricted (root b)) (fun x => x ∈ rootSection i (r 0)) = _
  rw [rootSection,if_neg h0,if_pos hi]
  erw [restricted_mass]
  rw [root_fiber]
lemma root_mass_probability (b : Fin 9) (hb : b.val%3 ≠ 0) (i : Index) (r : Space)
    (hi : exponent i 0 = 1) :
    mass (law b 0) (fun x => x ∈ boxSection i r 0) = rootProbability b (r 0) := by
  rw [root_mass_one_exp b i r hi,root_card b hb]
  rfl
lemma leaf_mass_eq (b : Fin 9) (i : Index) (r : Space) (j : Fin 7)
    (hi : exponent i j.succ ≠ 0) (hr : r j.succ ≠ zeroLeaf j) :
    mass (law b j.succ) (fun x => x ∈ boxSection i r j.succ) = 1/(primes j.succ-1:ℕ) := by
  have hh := restricted_singleton_eq (leaf j) (r j.succ) (by simp [leaf,hr])
  rw [leaf_card] at hh
  simpa [law,allowed,boxSection,hi] using hh
lemma rootProbability_cases (b r : Fin 9) (hb : b.val%3 ≠ 0) (hr : r.val%3 ≠ 0) :
    rootProbability b r = 2/5 ∨ rootProbability b r = 3/5 := by
  unfold rootProbability
  rw [branch_card 0 b _ hb (by simpa only [ne_eq,Fin.ext_iff,Fin.val_zero] using hr)]
  split_ifs <;> simp
lemma rootProbability_eq_iff (b r s : Fin 9) (hb : b.val%3 ≠ 0)
    (hr : r.val%3 ≠ 0) (hs : s.val%3 ≠ 0) :
    rootProbability b r = rootProbability b s ↔ r.val%3 = s.val%3 := by
  constructor
  · intro h
    have hc : (branch 0 b ⟨r.val%3,Nat.mod_lt _ (by decide)⟩).card =
        (branch 0 b ⟨s.val%3,Nat.mod_lt _ (by decide)⟩).card := by
      have hh : ((branch 0 b ⟨r.val%3,Nat.mod_lt _ (by decide)⟩).card:ℚ) =
          (branch 0 b ⟨s.val%3,Nat.mod_lt _ (by decide)⟩).card := by
        unfold rootProbability at h
        linarith
      exact_mod_cast hh
    have he := equal_size_branch 0 b _ _ hb
      (by simpa only [ne_eq,Fin.ext_iff,Fin.val_zero] using hr)
      (by simpa only [ne_eq,Fin.ext_iff,Fin.val_zero] using hs) hc
    exact congrArg Fin.val he
  · intro h
    unfold rootProbability
    simp only [h]

lemma pivot192_mass (b : Fin 9) (hb : b.val%3 ≠ 0) (r : Space) (hr : good 192 r) :
    mass (measure b) (residueBox 192 r) = rootProbability b (r 0)/4 := by
  have he := pivot_exponents.1
  have h0 := root_mass_probability b hb 192 r (by rw [he]; rfl)
  have h1 := leaf_mass_eq b 192 r 0 (by rw [he]; decide)
    (hr.2 0 (by rw [he]; decide))
  have hz (j : Fin 8) (hj : j ≠ 0 ∧ j ≠ 1) :
      mass (law b j) (fun x => x ∈ boxSection 192 r j) = 1 := by
    apply section_mass_zero_exp b hb
    rw [he]
    fin_cases j <;> simp_all
  rw [residueBox_mass]
  calc
    _ = ∏ j,(![rootProbability b (r 0),1/4,1,1,1,1,1,1] : Fin 8 → ℚ) j := by
      apply Finset.prod_congr rfl
      intro j _
      fin_cases j
      · exact h0
      · convert h1 using 1 <;> norm_num [primes]
      all_goals exact hz _ (by decide)
    _ = _ := by norm_num [Fin.prod_univ_succ]; ring
lemma pivot160_mass (b : Fin 9) (hb : b.val%3 ≠ 0) (r : Space) (hr : good 160 r) :
    mass (measure b) (residueBox 160 r) = rootProbability b (r 0)/6 := by
  have he := pivot_exponents.2
  have h0 := root_mass_probability b hb 160 r (by rw [he]; rfl)
  have h2 := leaf_mass_eq b 160 r 1 (by rw [he]; decide)
    (hr.2 1 (by rw [he]; decide))
  have hz (j : Fin 8) (hj : j ≠ 0 ∧ j ≠ 2) :
      mass (law b j) (fun x => x ∈ boxSection 160 r j) = 1 := by
    apply section_mass_zero_exp b hb
    rw [he]
    fin_cases j <;> simp_all
  rw [residueBox_mass]
  calc
    _ = ∏ j,(![rootProbability b (r 0),1,1/6,1,1,1,1,1] : Fin 8 → ℚ) j := by
      apply Finset.prod_congr rfl
      intro j _
      fin_cases j
      · exact h0
      · exact hz _ (by decide)
      · convert h2 using 1 <;> norm_num [primes]
      all_goals exact hz _ (by decide)
    _ = _ := by norm_num [Fin.prod_univ_succ]; ring

lemma intersection_mass (b : Fin 9) (i k : Index) (r s : Space) :
    mass (measure b) (fun x => residueBox i r x ∧ residueBox k s x) =
      ∏ j,mass (law b j) (fun x => x ∈ boxSection i r j ∩ boxSection k s j) := by
  have he : (fun x => residueBox i r x ∧ residueBox k s x) =
      box Coord (fun j x => x ∈ boxSection i r j ∩ boxSection k s j) := by
    funext x
    exact propext (by simp only [residueBox,box,Finset.mem_inter,forall_and])
  rw [he]
  exact box_mass Coord (law b) _

lemma pivot_intersection_eq (b : Fin 9) (hb : b.val%3 ≠ 0) (r s : Space)
    (hr : good 192 r) (hs : good 160 s) (hroot : (r 0).val%3 = (s 0).val%3) :
    mass (measure b) (fun x => residueBox 160 s x ∧ residueBox 192 r x) =
      rootProbability b (r 0)/24 := by
  have h0 : boxSection 160 s 0 = boxSection 192 r 0 := by
    simp [boxSection,rootSection,pivot_exponents,hroot]
  have hl : boxSection 160 s 1 = Finset.univ :=
    section_zero 160 s 1 (by rw [pivot_exponents.2]; rfl)
  have hk : boxSection 192 r 2 = Finset.univ :=
    section_zero 192 r 2 (by rw [pivot_exponents.1]; rfl)
  have hz (j : Fin 8) (hj : j ≠ 0 ∧ j ≠ 1 ∧ j ≠ 2) :
      mass (law b j) (fun x => x ∈ boxSection 160 s j ∩ boxSection 192 r j) = 1 := by
    have he : exponent 160 j = 0 ∧ exponent 192 j = 0 := by
      rw [pivot_exponents.1,pivot_exponents.2]
      fin_cases j <;> simp_all
    rw [section_zero 160 s j he.1,section_zero 192 r j he.2,Finset.inter_self]
    simpa [mass,bit] using law_sum b hb j
  rw [intersection_mass]
  calc
    _ = ∏ j,(![rootProbability b (r 0),1/4,1/6,1,1,1,1,1] : Fin 8 → ℚ) j := by
      apply Finset.prod_congr rfl
      intro j _
      fin_cases j
      · change mass (law b 0) (fun x => x ∈ boxSection 160 s 0 ∩ boxSection 192 r 0) = _
        rw [h0,Finset.inter_self]
        exact root_mass_probability b hb 192 r (by rw [pivot_exponents.1]; rfl)
      · change mass (law b 1) (fun x => x ∈ boxSection 160 s 1 ∩ boxSection 192 r 1) = _
        rw [hl,Finset.univ_inter]
        exact leaf_mass_eq b 192 r 0 (by rw [pivot_exponents.1]; decide)
          (hr.2 0 (by rw [pivot_exponents.1]; decide))
      · change mass (law b 2) (fun x => x ∈ boxSection 160 s 2 ∩ boxSection 192 r 2) = _
        rw [hk,Finset.inter_univ]
        exact leaf_mass_eq b 160 s 1 (by rw [pivot_exponents.2]; decide)
          (hs.2 1 (by rw [pivot_exponents.2]; decide))
      all_goals exact hz _ (by decide)
    _ = _ := by norm_num [Fin.prod_univ_succ]; ring

lemma pivot_intersection_lower (b : Fin 9) (hb : b.val%3 ≠ 0) (r s : Space)
    (hr : good 192 r) (hs : good 160 s) :
    (if rootProbability b (r 0) = rootProbability b (s 0) then rootProbability b (r 0)/24 else 0) ≤
      mass (measure b) (fun x => residueBox 160 s x ∧ residueBox 192 r x) := by
  split_ifs with h
  · have he := (rootProbability_eq_iff b (r 0) (s 0) hb
      (hr.1 (by rw [pivot_exponents.1]; decide))
      (hs.1 (by rw [pivot_exponents.2]; decide))).mp h
    exact le_of_eq (pivot_intersection_eq b hb r s hr hs he).symm
  · exact mass_nonneg _ (measure_nonneg b) _

#print axioms pivot192_mass
#print axioms pivot160_mass
#print axioms pivot_intersection_lower
end Erdos7Forest93Concrete
