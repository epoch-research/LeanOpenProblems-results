import Submission.OctahedralLocal
import Submission.OctahedralCodes
import Submission.TetrahedralArithmetic

namespace Erdos213.OctahedralLocal
/-- The local-profile certificate gives a cardinality bound once the
normalized edge requirements have been placed in that profile. -/
lemma card_le_eight_of_profile (a b c : ZMod 16)
    (hp : a.val%2=1 ∨ b.val%2=1 ∨ c.val%2=1)
    (q : Fin 8) (T : Finset (Fin 48))
    (h : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      (refinedProfile a b c q).testBit (edgeCode i j).val = true) : T.card ≤ 8 := by
  obtain ⟨k,hk⟩ := profile_cover a b c hp q
  apply card_le_eight_of_mask T k
  intro i hi j hj hij
  have he := congrArg (fun n : ℕ => n.testBit (edgeCode i j).val) hk
  simpa [Nat.testBit_land,h i hi j hj hij] using he

#print axioms card_le_eight_of_mask
#print axioms card_le_eight_of_profile

private lemma fold_bits_keep (f : Fin 44 → Bool) (l : List (Fin 44))
    (m n : ℕ) (hm : m.testBit n = true) :
    (l.foldl (fun acc k => if f k then acc ||| (2^k.val) else acc) m).testBit n = true := by
  induction l generalizing m with
  | nil => simpa using hm
  | cons k l ih =>
    simp only [List.foldl_cons]
    apply ih
    split_ifs <;> simp [Nat.testBit_lor,hm]

private lemma fold_bits_member (f : Fin 44 → Bool) (l : List (Fin 44))
    (m : ℕ) (k : Fin 44) (hk : k ∈ l) (hf : f k = true) :
    (l.foldl (fun acc j => if f j then acc ||| (2^j.val) else acc) m).testBit k.val = true := by
  induction l generalizing m with
  | nil => simp at hk
  | cons j l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hk with h | h
    · subst j
      apply fold_bits_keep
      simp [hf,Nat.testBit_lor,Nat.testBit_two_pow_self]
    · apply ih
      exact h

lemma profile_contains (a b c : ZMod 16) (k : Fin 44)
    (h : IsSquare (codeValue a b c k)) : (profile a b c).testBit k.val = true := by
  apply fold_bits_member (fun j => square16 (codeValue a b c j)) (List.finRange 44) 0 k
  · simp
  · exact (square16_iff _).mpr h

lemma card_le_eight_of_local_squares (a b c : ZMod 16)
    (hp : a.val%2=1 ∨ b.val%2=1 ∨ c.val%2=1)
    (q : Fin 8) (T : Finset (Fin 48))
    (hc : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      ((2^44-1)-choiceMask q).testBit (edgeCode i j).val = true)
    (hs : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → IsSquare (codeValue a b c (edgeCode i j))) :
    T.card ≤ 8 := by
  apply card_le_eight_of_profile a b c hp q T
  intro i hi j hj hij
  simp only [refinedProfile,Nat.testBit_land,profile_contains a b c _ (hs i hi j hj hij),
    hc i hi j hj hij,Bool.and_self]

#print axioms card_le_eight_of_local_squares
def faceIndex (j : Fin 3) : Fin 22 := ⟨j.val+1, by omega⟩

def ChoiceValid (a b c : ℤ) (q : Fin 8) : Prop :=
  ∀ j : Fin 3, q.val.testBit j.val = true ↔ ¬IsSquare (forms a b c (faceIndex j))

lemma choice_exists (a b c : ℤ) : ∃ q : Fin 8, ChoiceValid a b c q := by
  classical
  by_cases h1 : IsSquare (forms a b c 1) <;>
    by_cases h2 : IsSquare (forms a b c 2) <;>
      by_cases h3 : IsSquare (forms a b c 3)
  · refine ⟨0, ?_⟩; intro j; fin_cases j <;> simp [faceIndex,h1,h2,h3] <;> decide
  · refine ⟨4, ?_⟩; intro j; fin_cases j <;> simp [faceIndex,h1,h2,h3] <;> decide
  · refine ⟨2, ?_⟩; intro j; fin_cases j <;> simp [faceIndex,h1,h2,h3] <;> decide
  · refine ⟨6, ?_⟩; intro j; fin_cases j <;> simp [faceIndex,h1,h2,h3] <;> decide
  · refine ⟨1, ?_⟩; intro j; fin_cases j <;> simp [faceIndex,h1,h2,h3] <;> decide
  · refine ⟨5, ?_⟩; intro j; fin_cases j <;> simp [faceIndex,h1,h2,h3] <;> decide
  · refine ⟨3, ?_⟩; intro j; fin_cases j <;> simp [faceIndex,h1,h2,h3] <;> decide
  · refine ⟨7, ?_⟩; intro j; fin_cases j <;> simp [faceIndex,h1,h2,h3] <;> decide

lemma choice_mask_rule : ∀ q : Fin 8, ∀ k : Fin 44,
    ((2^44-1)-choiceMask q).testBit k.val = true ↔
      ∀ j : Fin 3, k.val ≠ j.val+1+(if q.val.testBit j.val then 0 else 22) := by
  decide

lemma int_code_low (a b c : ℤ) (j : Fin 3) :
    intCodeValue a b c ⟨j.val+1, by omega⟩ = forms a b c (faceIndex j) := by
  have h : j.val+1 < 22 := by omega
  simp [intCodeValue,h,Nat.mod_eq_of_lt h,faceIndex]

lemma int_code_high (a b c : ℤ) (j : Fin 3) :
    intCodeValue a b c ⟨j.val+23, by omega⟩ = 2*forms a b c (faceIndex j) := by
  have h : ¬j.val+23 < 22 := by omega
  have hh : (j.val+23)%22=j.val+1 := by omega
  simp [intCodeValue,h,hh,faceIndex]

lemma integer_squareclass_conflict {x : ℤ} (hx : x ≠ 0)
    (hs : IsSquare x) : ¬IsSquare (2*x) := by
  intro ht
  apply TetrahedralArithmetic.squareclass_conflict (show (x : ℚ) ≠ 0 by exact_mod_cast hx)
    (Rat.isSquare_intCast_iff.mpr hs)
  simpa using (Rat.isSquare_intCast_iff.mpr ht)

lemma choice_allows_square (a b c : ℤ) (q : Fin 8) (hq : ChoiceValid a b c q)
    (hn : ∀ j : Fin 3, forms a b c (faceIndex j) ≠ 0)
    (k : Fin 44) (hs : IsSquare (intCodeValue a b c k)) :
    ((2^44-1)-choiceMask q).testBit k.val = true := by
  rw [choice_mask_rule]
  intro j he
  by_cases hb : q.val.testBit j.val = true
  · have hk : k = ⟨j.val+1, by omega⟩ := by apply Fin.ext; simpa [hb] using he
    rw [hk,int_code_low] at hs
    exact (hq j).mp hb hs
  · have hf : IsSquare (forms a b c (faceIndex j)) := by
      by_contra h
      exact hb ((hq j).mpr h)
    have hk : k = ⟨j.val+23, by omega⟩ := by apply Fin.ext; simpa [hb,Nat.add_assoc] using he
    rw [hk,int_code_high] at hs
    exact integer_squareclass_conflict (hn j) hf hs

lemma cast_forms (a b c : ℤ) (k : Fin 22) :
    ((forms a b c k : ℤ) : ZMod 16) = forms (a : ZMod 16) (b : ZMod 16) (c : ZMod 16) k := by
  fin_cases k <;> simp [forms]

lemma cast_codeValue (a b c : ℤ) (k : Fin 44) :
    (intCodeValue a b c k : ZMod 16) = codeValue (a : ZMod 16) (b : ZMod 16) (c : ZMod 16) k := by
  unfold intCodeValue codeValue
  rw [Int.cast_mul,cast_forms]
  split_ifs <;> norm_num

lemma primitive_mod_sixteen (a b c : ℤ) (hp : TetrahedralArithmetic.Primitive a b c) :
    (a : ZMod 16).val%2=1 ∨ (b : ZMod 16).val%2=1 ∨ (c : ZMod 16).val%2=1 := by
  by_contra hh
  push_neg at hh
  have div_two : ∀ z : ℤ, (z : ZMod 16).val%2 ≠ 1 → (2 : ℤ) ∣ z := by
    intro z hz
    have hz0 : (z : ZMod 16).val%2=0 := by omega
    have he : (((z : ZMod 16).val : ℤ)%2)=0 := by exact_mod_cast hz0
    rw [ZMod.val_intCast] at he
    norm_num only [Nat.cast_ofNat] at he
    rw [Int.emod_emod_of_dvd _ (by norm_num : (2 : ℤ) ∣ 16)] at he
    exact Int.dvd_of_emod_eq_zero he
  obtain ⟨r,s,t,hp⟩ := hp
  have hd : (2 : ℤ) ∣ 1 := by
    rw [← hp]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right (div_two a hh.1) r)
      (dvd_mul_of_dvd_right (div_two b hh.2.1) s))
      (dvd_mul_of_dvd_right (div_two c hh.2.2) t)
  norm_num at hd

/-- A verified bound for the normalized square-class-one requirements. The
geometric connection from a signed-permutation orbit to these codes is not
part of this theorem. -/
lemma normalized_squareclass_one_bound (a b c : ℤ)
    (hp : TetrahedralArithmetic.Primitive a b c)
    (hn : ∀ j : Fin 3, forms a b c (faceIndex j) ≠ 0)
    (T : Finset (Fin 48))
    (hs : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → IsSquare (intCodeValue a b c (edgeCode i j))) :
    T.card ≤ 8 := by
  obtain ⟨q,hq⟩ := choice_exists a b c
  apply card_le_eight_of_local_squares (a : ZMod 16) (b : ZMod 16) (c : ZMod 16)
    (primitive_mod_sixteen a b c hp) q T
  · intro i hi j hj hij
    exact choice_allows_square a b c q hq hn _ (hs i hi j hj hij)
  · intro i hi j hj hij
    rw [← cast_codeValue]
    exact (hs i hi j hj hij).map (Int.castRingHom (ZMod 16))

#print axioms normalized_squareclass_one_bound

end Erdos213.OctahedralLocal
