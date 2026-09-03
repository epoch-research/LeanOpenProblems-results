import Submission.DfaCountingExplore

/-! Ordinary-integer representation peaks inside Cartesian digit boxes.
The digits at different positions need not use the same allowed set. -/
namespace Erdos66DigitBoxEnergy
open AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 2600000
variable {b k : ℕ}

def encode (x : Fin k → Fin b) : ℕ :=
  Nat.ofDigits b (List.ofFn (fun i ↦ (x i).val))

lemma encode_injective (hb : 1<b) : Function.Injective (@encode b k) := by
  intro x y h
  have he := Nat.ofDigits_inj_of_len_eq hb
    (by simp : (List.ofFn (fun i ↦ (x i).val)).length=(List.ofFn (fun i ↦ (y i).val)).length)
    (by intro a ha; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha; exact (x i).isLt)
    (by intro a ha; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha; exact (y i).isLt) h
  have hf := List.ofFn_injective he
  funext i
  exact Fin.ext (congrFun hf i)

lemma encode_lt (hb : 1<b) (x : Fin k → Fin b) : encode x<b^k := by
  have he := Nat.ofDigits_lt_base_pow_length hb (l := List.ofFn (fun i ↦ (x i).val))
    (by intro a ha; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha; exact (x i).isLt)
  simpa only [List.length_ofFn] using he

lemma encode_pair_sum (x y a d : Fin k → Fin b)
    (h : ∀ i, (x i).val+(y i).val=(a i).val+(d i).val) :
    encode x+encode y=encode a+encode d := by
  unfold encode
  rw [Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq (by simp),
    Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq (by simp)]
  congr 1
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_zipWith,List.getElem_ofFn]
  exact h _

noncomputable def box (D : Fin k → Finset (Fin b)) : Finset ℕ :=
  (Fintype.piFinset D).image encode

lemma box_card (hb : 1<b) (D : Fin k → Finset (Fin b)) :
    (box D).card=∏ i : Fin k, (D i).card := by
  rw [box,Finset.card_image_of_injective _ (encode_injective hb),Fintype.card_piFinset]

lemma mem_box (D : Fin k → Finset (Fin b)) (x : Fin k → Fin b)
    (hx : ∀ i, x i∈D i) : encode x∈box D :=
  Finset.mem_image.mpr ⟨x,Fintype.mem_piFinset.mpr hx,rfl⟩

lemma two_point_power_bound (D : Finset (Fin b)) (hD : D.Nonempty) :
    ∃ a∈D, ∃ d∈D, D.card≤({a,d} : Finset (Fin b)).card^b := by
  by_cases hcard : D.card≤1
  · obtain ⟨a,ha⟩ := hD
    exact ⟨a,ha,a,ha,by simpa using hcard⟩
  · obtain ⟨a,ha,d,hd,had⟩ := Finset.one_lt_card.mp (by omega : 1<D.card)
    refine ⟨a,ha,d,hd,?_⟩
    rw [Finset.card_pair had]
    have hbound : D.card≤b := by simpa using Finset.card_le_univ D
    exact hbound.trans Nat.lt_two_pow_self.le

/-- A two-point subbox is centrally symmetric in ORDINARY integer
addition. Carries are identical in all the complementary pairs. -/
theorem two_point_box_peak (hb : 1<b) (A : Set ℕ) (a d : Fin k → Fin b)
    (hA : (box (fun i ↦ {a i,d i}) : Set ℕ)⊆A) :
    (Fintype.piFinset (fun i ↦ ({a i,d i} : Finset (Fin b)))).card ≤
      sumRep A (encode a+encode d) := by
  let comp : (Fin k → Fin b) → Fin k → Fin b := fun x i ↦ if x i=a i then d i else a i
  have hcomp (x : Fin k → Fin b) (hx : ∀ i, x i∈({a i,d i} : Finset (Fin b))) :
      (∀ i, comp x i∈({a i,d i} : Finset (Fin b))) ∧
        encode x+encode (comp x)=encode a+encode d := by
    constructor
    · intro i
      dsimp only [comp]
      split_ifs <;> simp
    · apply encode_pair_sum
      intro i
      rcases Finset.mem_insert.mp (hx i) with hi | hi
      · simp [comp,hi]
      · have hi := Finset.mem_singleton.mp hi
        by_cases hd : d i=a i
        · simp [comp,hi,hd]
        · simp [comp,hi,hd,Nat.add_comm]
  rw [sumRep_def]
  apply Finset.card_le_card_of_injOn
    (s := Fintype.piFinset (fun i ↦ ({a i,d i} : Finset (Fin b))))
    (t := (Finset.antidiagonal (encode a+encode d)).filter (fun p ↦ p.1∈A ∧ p.2∈A))
    (f := fun x ↦ (encode x,encode (comp x)))
  · intro x hx
    have hx := Fintype.mem_piFinset.mp hx
    have hc := hcomp x hx
    change (encode x,encode (comp x))∈
      (Finset.antidiagonal (encode a+encode d)).filter (fun p ↦ p.1∈A ∧ p.2∈A)
    exact Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr hc.2,
      hA (mem_box _ _ hx),hA (mem_box _ _ hc.1)⟩
  · intro x hx y hy he
    exact encode_injective hb (congrArg Prod.fst he)

/-- A uniform representation cap M below 2*b^k restricts EVERY contained
base-b Cartesian digit box to at most M^b points, independently of k. -/
theorem box_card_le_cap_power (hb : 1<b) (A : Set ℕ) (D : Fin k → Finset (Fin b))
    (hA : (box D : Set ℕ)⊆A) (M : ℕ)
    (hM : ∀ n<2*b^k, sumRep A n≤M) :
    (box D).card≤M^b := by
  by_cases hD : ∀ i, (D i).Nonempty
  · choose a ha d hd hc using fun i ↦ two_point_power_bound (D i) (hD i)
    have hsub : (box (fun i ↦ ({a i,d i} : Finset (Fin b))) : Set ℕ)⊆A := by
      intro n hn
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hn
      apply hA
      apply mem_box
      intro i
      have hi := Fintype.mem_piFinset.mp hx i
      rcases Finset.mem_insert.mp hi with hi | hi
      · simpa only [hi] using ha i
      · simpa only [Finset.mem_singleton.mp hi] using hd i
    have hpeak := (two_point_box_peak hb A a d hsub).trans
      (hM _ (by have h1 := encode_lt hb a; have h2 := encode_lt hb d; omega))
    have hprod : (box D).card≤
        (Fintype.piFinset (fun i ↦ ({a i,d i} : Finset (Fin b)))).card^b := by
      rw [box_card hb,Fintype.card_piFinset,←Finset.prod_pow]
      exact Finset.prod_le_prod (fun i _ ↦ Nat.zero_le _) (fun i _ ↦ hc i)
    exact hprod.trans (Nat.pow_le_pow_left hpeak b)
  · have he : Fintype.piFinset D=∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      simpa only [Fintype.piFinset_nonempty] using hD
    simp only [box,he,Finset.image_empty,Finset.card_empty]
    exact Nat.zero_le _

end Erdos66DigitBoxEnergy
