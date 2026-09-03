import Submission.UnbalancedBounds

/-!
A local star-count refinement for the fourth balanced Zarankiewicz case.
These are necessary degree bounds, not a solution of Erdős 714.
-/
noncomputable section
open Finset SimpleGraph Classical
set_option maxHeartbeats 2000000
namespace Erdos714FourthLocal
open Erdos714Packing
variable {A B : Type*} [Fintype A] [Fintype B]

abbrev PairCommon (S : A → Finset B) (a b : A) := ↥(S a ∩ S b)

/-- Restrict to two rows' common columns, and remove those two rows. -/
def localRows (S : A → Finset B) (a b c : A) : Finset (PairCommon S a b) :=
  if c = a ∨ c = b then ∅ else univ.filter (fun x => x.val ∈ S c)

omit [Fintype A] [Fintype B] in
lemma mem_localRows (S : A → Finset B) (a b c : A) (x : PairCommon S a b) :
    x ∈ localRows S a b c ↔ c ≠ a ∧ c ≠ b ∧ x.val ∈ S c := by
  simp only [localRows]
  split_ifs with h
  · simp only [notMem_empty, false_iff]
    tauto
  · simp_all

/-- Four common columns admit at most one row other than the two already fixed. -/
theorem local_common_le_one (S : A → Finset B) (a b : A) (hab : a ≠ b)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (f : Fin 4 ↪ PairCommon S a b) :
    (common (dual (localRows S a b)) f).card ≤ 1 := by
  let g : Fin 4 ↪ B := f.trans ⟨Subtype.val, Subtype.val_injective⟩
  let D := common (dual S) g
  let E := common (dual (localRows S a b)) f
  have hD : D.card < 4 :=
    (common_card_dual_iff S (by decide)).mp
      ((free_iff_common_card S (by decide)).mp hfree) g
  have haD : a ∈ D := by
    simp only [D, mem_common, mem_dual]
    exact fun i => (mem_inter.mp (f i).property).1
  have hbD : b ∈ D := by
    simp only [D, mem_common, mem_dual]
    exact fun i => (mem_inter.mp (f i).property).2
  have hE (c : A) (hc : c ∈ E) : c ≠ a ∧ c ≠ b ∧ c ∈ D := by
    have hc' : ∀ i, f i ∈ localRows S a b c := by
      simpa only [E, mem_common, mem_dual] using hc
    have h₀ := (mem_localRows S a b c (f 0)).mp (hc' 0)
    refine ⟨h₀.1, h₀.2.1, ?_⟩
    simp only [D, mem_common, mem_dual]
    exact fun i => ((mem_localRows S a b c (f i)).mp (hc' i)).2.2
  have haE : a ∉ E := fun h => (hE a h).1 rfl
  have hbE : b ∉ E := fun h => (hE b h).2.1 rfl
  have hsub : insert a (insert b E) ⊆ D := by
    simp only [insert_subset_iff]
    exact ⟨haD, hbD, fun c hc => (hE c hc).2.2⟩
  have hcard := card_le_card hsub
  rw [card_insert_of_notMem (by simp [hab, haE]), card_insert_of_notMem hbE] at hcard
  change E.card ≤ 1
  omega

/-- The local ordered-star bound has coefficient one, rather than three. -/
theorem local_fourth_moment (S : A → Finset B) (a b : A) (hab : a ≠ b)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ c : A, ((localRows S a b c).card - 3)^4) ≤ (S a ∩ S b).card^4 := by
  have hcount := Fintype.card_congr (Erdos714Unbalanced.starEquiv (localRows S a b) 4)
  simp only [Fintype.card_sigma, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_coe] at hcount
  calc
    _ ≤ ∑ c : A, (localRows S a b c).card.descFactorial 4 :=
      sum_le_sum (fun c _ => Nat.pow_sub_le_descFactorial _ 4)
    _ = ∑ f : Fin 4 ↪ PairCommon S a b, (common (dual (localRows S a b)) f).card := hcount
    _ ≤ ∑ _f : Fin 4 ↪ PairCommon S a b, 1 :=
      sum_le_sum (fun f _ => local_common_le_one S a b hab hfree f)
    _ = (S a ∩ S b).card.descFactorial 4 := by simp
    _ ≤ _ := Nat.descFactorial_le_pow _ _

/-- A purely integer version of the local fourth-root estimate. -/
theorem local_edge_bound (S : A → Finset B) (a b : A) (hab : a ≠ b)
    (q : ℕ) (hA : Fintype.card A ≤ q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ c : A, (localRows S a b c).card) ≤
      q^3*(S a ∩ S b).card + 3*Fintype.card A := by
  have hp := pow_sum_le_card_mul_sum_pow (s := (univ : Finset A))
    (f := fun c => (localRows S a b c).card - 3) (by intros; omega) 3
  simp only [card_univ] at hp
  have hpow : (∑ c : A, ((localRows S a b c).card - 3))^4 ≤
      (q^3*(S a ∩ S b).card)^4 := by
    calc
      _ ≤ Fintype.card A^3 * ∑ c : A, ((localRows S a b c).card-3)^4 := hp
      _ ≤ (q^4)^3 * (S a ∩ S b).card^4 := by
        gcongr
        exact local_fourth_moment S a b hab hfree
      _ = _ := by ring
  have hsum := (Nat.pow_le_pow_iff_left (by decide : 4 ≠ 0)).mp hpow
  calc
    _ ≤ ∑ c : A, ((localRows S a b c).card - 3 + 3) :=
      sum_le_sum (fun c _ => by omega)
    _ = (∑ c : A, ((localRows S a b c).card - 3)) + 3*Fintype.card A := by
      simp [sum_add_distrib, mul_comm]
    _ ≤ _ := Nat.add_le_add_right hsum _

lemma local_dual (S : A → Finset B) (a b : A) (x : PairCommon S a b) :
    dual (localRows S a b) x = ((dual S x.val).erase a).erase b := by
  ext c
  simp only [mem_dual, mem_localRows, mem_erase]
  tauto

/-- Reinsert the two fixed rows in each column count. -/
lemma local_column_count (S : A → Finset B) (a b : A) (hab : a ≠ b)
    (x : PairCommon S a b) :
    (dual (localRows S a b) x).card + 2 = (dual S x.val).card := by
  rw [local_dual]
  have ha : a ∈ dual S x.val := (mem_dual S a x.val).mpr (mem_inter.mp x.property).1
  have hb : b ∈ (dual S x.val).erase a := by
    simp only [mem_erase, mem_dual]
    exact ⟨Ne.symm hab, (mem_inter.mp x.property).2⟩
  have h₁ := card_erase_add_one ha
  have h₂ := card_erase_add_one hb
  omega

/-- Exact degree sum over the fixed pair's common columns. -/
theorem local_degree_sum (S : A → Finset B) (a b : A) (hab : a ≠ b)
    (q : ℕ) (hA : Fintype.card A ≤ q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ x : PairCommon S a b, (dual S x.val).card) ≤
      (q^3+2)*(S a ∩ S b).card + 3*Fintype.card A := by
  have he := local_edge_bound S a b hab q hA hfree
  have hcount' : (∑ c, (localRows S a b c).card) = ∑ x, (dual (localRows S a b) x).card := by
    have hc (c : A) : (localRows S a b c).card =
        ∑ x : PairCommon S a b, if x ∈ localRows S a b c then 1 else 0 := by
      rw [sum_boole]
      congr 1
      ext x
      simp
    simp_rw [hc]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    simp only [sum_boole, Nat.cast_id, dual]
    congr 1
    ext c
    simp
  have hsum : (∑ x : PairCommon S a b, (dual S x.val).card) =
      (∑ c : A, (localRows S a b c).card) + 2*(S a ∩ S b).card := by
    rw [hcount']
    simp_rw [← local_column_count S a b hab]
    simp [sum_add_distrib, mul_comm]
  rw [hsum]
  nlinarith

/-- Under a uniform column-degree lower bound, every pair intersection is small. -/
theorem pair_degree_bound (S : A → Finset B) (a b : A) (hab : a ≠ b)
    (q d : ℕ) (hA : Fintype.card A ≤ q^4)
    (hd : ∀ x : B, d ≤ (dual S x).card)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    d*(S a ∩ S b).card ≤ (q^3+2)*(S a ∩ S b).card + 3*Fintype.card A := by
  calc
    _ = ∑ _x : PairCommon S a b, d := by simp [mul_comm]
    _ ≤ ∑ x : PairCommon S a b, (dual S x.val).card := sum_le_sum (fun x _ => hd x.val)
    _ ≤ _ := local_degree_sum S a b hab q hA hfree

lemma pair_count (S : A → Finset B) :
    (∑ x : B, (dual S x).card.descFactorial 2) =
      ∑ f : Fin 2 ↪ A, (S (f 0) ∩ S (f 1)).card := by
  have h := Fintype.card_congr (Erdos714Unbalanced.starEquiv (dual S) 2)
  simp only [Fintype.card_sigma, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_coe] at h
  have hdual : dual (dual S) = S := by
    funext a
    ext x
    simp only [mem_dual]
  rw [hdual] at h
  have hc (f : Fin 2 ↪ A) : common S f = S (f 0) ∩ S (f 1) := by
    ext x
    simp only [mem_common, Fin.forall_fin_two, mem_inter]
  simpa only [hc] using h

/-- A high column minimum degree forces a pair with at least q² common columns. -/
theorem exists_large_pair (S : A → Finset B) (q : ℕ) (hq : 0 < q)
    (hA : Fintype.card A ≤ q^4) (hB : Fintype.card B = q^4)
    (hd : ∀ x : B, q^3+1 ≤ (dual S x).card) :
    ∃ a b : A, a ≠ b ∧ q^2 ≤ (S a ∩ S b).card := by
  have hbase : q^6 ≤ (q^3+1).descFactorial 2 := by
    calc
      _ = (q^3)^2 := by ring
      _ ≤ _ := by simpa using Nat.pow_sub_le_descFactorial (q^3+1) 2
  have hlo : q^10 ≤ ∑ f : Fin 2 ↪ A, (S (f 0) ∩ S (f 1)).card := by
    rw [← pair_count]
    calc
      _ = ∑ _x : B, q^6 := by simp [hB]; ring
      _ ≤ _ := sum_le_sum (fun x _ => hbase.trans (Nat.descFactorial_le 2 (hd x)))
  have hnum : Fintype.card (Fin 2 ↪ A) ≤ q^8 := by
    calc
      _ = (Fintype.card A).descFactorial 2 := by simp
      _ ≤ Fintype.card A^2 := Nat.descFactorial_le_pow _ _
      _ ≤ (q^4)^2 := Nat.pow_le_pow_left hA 2
      _ = _ := by ring
  by_contra! hn
  have hsmall (f : Fin 2 ↪ A) : (S (f 0) ∩ S (f 1)).card < q^2 :=
    hn (f 0) (f 1) (fun h => by have := f.injective h; exact (by decide : (0 : Fin 2) ≠ 1) this)
  have hp : 0 < ∑ f : Fin 2 ↪ A, (S (f 0) ∩ S (f 1)).card := (pow_pos hq _).trans_le hlo
  obtain ⟨f, hf, _⟩ := sum_pos_iff.mp hp
  have hlt := sum_lt_sum_of_nonempty (s := (univ : Finset (Fin 2 ↪ A)))
    ⟨f, hf⟩ (fun f _ => hsmall f)
  have hhi : (∑ f : Fin 2 ↪ A, (S (f 0) ∩ S (f 1)).card) < q^10 := by
    calc
      _ < ∑ _f : Fin 2 ↪ A, q^2 := hlt
      _ = Fintype.card (Fin 2 ↪ A)*q^2 := by simp
      _ ≤ q^8*q^2 := Nat.mul_le_mul_right _ hnum
      _ = _ := by ring
  omega

/-- A fourth-case packing on at most q⁴ rows and exactly q⁴ columns has
column minimum degree at most q³ + 3q² + 2. -/
theorem column_minimum_bound (S : A → Finset B) (q d : ℕ) (hq : 0 < q)
    (hA : Fintype.card A ≤ q^4) (hB : Fintype.card B = q^4)
    (hd : ∀ x : B, d ≤ (dual S x).card)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    d ≤ q^3 + 3*q^2 + 2 := by
  by_contra! hlarge
  obtain ⟨a,b,hab,hm⟩ := exists_large_pair S q hq hA hB (fun x => by have := hd x; omega)
  have hpair := pair_degree_bound S a b hab q d hA hd hfree
  have hmult : (q^3+3*q^2+3)*(S a ∩ S b).card ≤ d*(S a ∩ S b).card :=
    Nat.mul_le_mul_right _ (by omega)
  have hq2 : 0 < q^2 := pow_pos hq _
  have hmul : q^2*q^2 ≤ q^2*(S a ∩ S b).card := Nat.mul_le_mul_left _ hm
  have heq : q^2*q^2 = q^4 := by ring
  nlinarith

/-- The same result without choosing a minimum in advance. -/
theorem exists_small_column (S : A → Finset B) (q : ℕ) (hq : 0 < q)
    (hA : Fintype.card A ≤ q^4) (hB : Fintype.card B = q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    ∃ x : B, (dual S x).card ≤ q^3 + 3*q^2 + 2 := by
  by_contra! h
  have hh := column_minimum_bound S q (q^3+3*q^2+3) hq hA hB
    (fun x => by have := h x; omega) hfree
  omega

#print axioms pair_count
#print axioms exists_large_pair
#print axioms column_minimum_bound
#print axioms exists_small_column
#print axioms local_common_le_one
#print axioms local_fourth_moment
#print axioms local_edge_bound
#print axioms local_degree_sum
#print axioms pair_degree_bound
end Erdos714FourthLocal
