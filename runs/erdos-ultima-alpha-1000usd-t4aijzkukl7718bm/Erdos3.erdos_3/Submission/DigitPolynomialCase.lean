import Submission.BinarySymmetryCase
import Submission.FiniteKernelCase

/-! Complement-doubling gives long progressions with identical finite binary-digit jets.
This is an auxiliary construction, not a proof of the unrestricted conjecture. -/
namespace Erdos3DigitPolynomialCase
open Polynomial Erdos3BinarySymmetryCase
set_option maxHeartbeats 2000000

/-- The binary word is read least significant digit first. -/
noncomputable def wordPoly : List ℕ → ℤ[X]
  | [] => 0
  | b :: w => C (b : ℤ) + X * wordPoly w

lemma wordPoly_append (u v : List ℕ) :
    wordPoly (u ++ v) = wordPoly u + X^u.length * wordPoly v := by
  induction u with
  | nil => simp [wordPoly]
  | cons b u ih => simp only [List.cons_append, wordPoly, List.length_cons, ih, pow_succ]; ring

lemma wordPoly_complement (w : List ℕ) (hw : ∀ b ∈ w, b < 2) :
    wordPoly (w.map (fun b ↦ 1-b)) + wordPoly w = wordPoly (List.replicate w.length 1) := by
  induction w with
  | nil => simp [wordPoly]
  | cons b w ih =>
    have hb := hw b (by simp)
    have ht : ∀ c ∈ w, c < 2 := fun c hc ↦ hw c (by simp [hc])
    have hi := ih ht
    have hb' : b = 0 ∨ b = 1 := by omega
    rcases hb' with rfl | rfl <;>
      simp only [List.map_cons, List.length_cons, List.replicate_succ, wordPoly,
        Nat.sub_zero, Nat.sub_self, Nat.cast_zero, Nat.cast_one, map_zero, map_one] <;>
      linear_combination X * hi

/-- Complement in the lower block, original word in the upper block. -/
def doubleWord (w : List ℕ) : List ℕ := w.map (fun b ↦ 1-b) ++ w

lemma doubleWord_length (w : List ℕ) : (doubleWord w).length = 2*w.length := by
  simp [doubleWord]; omega

lemma doubleWord_binary (w : List ℕ) (hw : ∀ b ∈ w, b < 2) :
    ∀ b ∈ doubleWord w, b < 2 := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    omega
  · exact hw b hb

lemma doubleWord_poly (w : List ℕ) (hw : ∀ b ∈ w, b < 2) :
    wordPoly (doubleWord w) = wordPoly (List.replicate w.length 1) +
      (X^w.length-1)*wordPoly w := by
  rw [doubleWord, wordPoly_append, List.length_map]
  linear_combination wordPoly_complement w hw

lemma doubleWord_value (w : List ℕ) (hw : ∀ b ∈ w, b < 2) :
    Nat.ofDigits 2 (doubleWord w) = (2^w.length-1)*(Nat.ofDigits 2 w+1) := by
  have h := complement_value w hw
  have hp : 1 ≤ 2^w.length := one_le_pow₀ (by norm_num)
  have hp' := Nat.sub_add_cancel hp
  simp only [doubleWord, Nat.ofDigits_append, List.length_map]
  have hcv : Nat.ofDigits 2 (w.map (fun b ↦ 1-b)) + Nat.ofDigits 2 w = 2^w.length-1 := by omega
  conv_lhs => rw [← hp']
  nlinarith

def encode : ℕ → List ℕ → List ℕ
  | 0, w => w
  | r+1, w => doubleWord (encode r w)

lemma encode_length (r : ℕ) (w : List ℕ) : (encode r w).length = 2^r*w.length := by
  induction r with
  | zero => simp [encode]
  | succ r ih => rw [encode, doubleWord_length, ih, pow_succ]; ring

lemma encode_binary (r : ℕ) (w : List ℕ) (hw : ∀ b ∈ w, b < 2) :
    ∀ b ∈ encode r w, b < 2 := by
  induction r with
  | zero => exact hw
  | succ r ih => exact doubleWord_binary _ ih

/-- The first r Taylor coefficients at X=1 agree after r complement-doublings. -/
lemma encode_jet (r : ℕ) (u v : List ℕ) (hu : ∀ b ∈ u, b < 2)
    (hv : ∀ b ∈ v, b < 2) (hlen : u.length = v.length) :
    (X-1 : ℤ[X])^r ∣ wordPoly (encode r u)-wordPoly (encode r v) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have he : (encode r u).length = (encode r v).length := by simp [encode_length, hlen]
    have hd : (X-1 : ℤ[X]) ∣ X^(encode r u).length-1 := by
      simpa using sub_dvd_pow_sub_pow (X : ℤ[X]) 1 (encode r u).length
    have hp := mul_dvd_mul hd ih
    rw [pow_succ']
    convert hp using 1
    rw [encode, encode, doubleWord_poly _ (encode_binary r u hu),
      doubleWord_poly _ (encode_binary r v hv), ← he]
    ring

def start (r m : ℕ) : ℕ := Nat.ofDigits 2 (encode r (Nat.digitsAppend 2 m 0))

def step : ℕ → ℕ → ℕ
  | 0, _ => 1
  | r+1, m => (2^(2^r*m)-1)*step r m

lemma step_pos (r : ℕ) {m : ℕ} (hm : 0 < m) : 0 < step r m := by
  induction r with
  | zero => simp [step]
  | succ r ih =>
    apply Nat.mul_pos _ ih
    have hexp : 0 < 2^r*m := by positivity
    have hpow : 1 < 2^(2^r*m) := one_lt_pow₀ (by norm_num) hexp.ne'
    omega

lemma encode_value_affine (r m i : ℕ) (hi : i < 2^m) :
    Nat.ofDigits 2 (encode r (Nat.digitsAppend 2 m i)) = start r m + i*step r m := by
  have hzero : (0 : ℕ) < 2^m := by positivity
  have hwi := Nat.lt_of_mem_digitsAppend (by norm_num : 1 < 2) m (n := i)
  have hwz := Nat.lt_of_mem_digitsAppend (by norm_num : 1 < 2) m (n := 0)
  induction r with
  | zero => simp [encode, start, step, padded_value]
  | succ r ih =>
    have hz : start (r+1) m = (2^(2^r*m)-1)*(start r m+1) := by
      unfold start
      rw [encode, doubleWord_value _ (encode_binary r _ hwz), encode_length,
        Nat.length_digitsAppend (by norm_num : 1 < 2) m hzero]
    rw [encode, doubleWord_value _ (encode_binary r _ hwi), encode_length,
      Nat.length_digitsAppend (by norm_num : 1 < 2) m hi, ih, hz, step]
    ring

/-- Explicit AP template: binary words of common length, positive step, and equal r-jets. -/
theorem binary_jet_progression (r k : ℕ) :
    ∃ L a d : ℕ, 0 < L ∧ 0 < d ∧
      ∃ w : Fin k → List ℕ,
        (∀ i, (w i).length = L) ∧
        (∀ i, ∀ b ∈ w i, b < 2) ∧
        (∀ i, Nat.ofDigits 2 (w i) = a+i.val*d) ∧
        (∀ i j, (X-1 : ℤ[X])^r ∣ wordPoly (w i)-wordPoly (w j)) := by
  let m := k+1
  let w : Fin k → List ℕ := fun i ↦ encode r (Nat.digitsAppend 2 m i.val)
  have hm : 0 < m := by dsimp [m]; omega
  have hi (i : Fin k) : i.val < 2^m :=
    i.isLt.trans_le ((Nat.le_succ k).trans (Nat.le_of_lt ((Nat.lt_two_pow_self (n := m)))))
  have hw (i : Fin k) : ∀ b ∈ Nat.digitsAppend 2 m i.val, b < 2 :=
    Nat.lt_of_mem_digitsAppend (by norm_num : 1 < 2) m
  have hlen (i : Fin k) : (Nat.digitsAppend 2 m i.val).length = m :=
    Nat.length_digitsAppend (by norm_num : 1 < 2) m (hi i)
  refine ⟨2^r*m,start r m,step r m,by positivity,step_pos r hm,w,?_,?_,?_,?_⟩
  · intro i
    dsimp [w]
    rw [encode_length, hlen]
  · intro i
    exact encode_binary r _ (hw i)
  · intro i
    exact encode_value_affine r m i.val (hi i)
  · intro i j
    exact encode_jet r _ _ (hw i) (hw j) ((hlen i).trans (hlen j).symm)

open Erdos3FiniteKernelCase

/-- Invariance under binary-word replacements preserving a fixed finite jet at X=1.
This is an additional structural hypothesis, not a property of arbitrary sets. -/
def JetInvariant (A : Set ℕ) (r : ℕ) : Prop :=
  ∀ u v : List ℕ, (∀ b ∈ u, b < 2) → (∀ b ∈ v, b < 2) →
    u.length = v.length → (X-1 : ℤ[X])^r ∣ wordPoly v-wordPoly u →
    Nat.ofDigits 2 u ∈ A → Nat.ofDigits 2 v ∈ A

lemma wordPoly_sandwich (u v w z : List ℕ) (hlen : w.length = z.length) :
    wordPoly (u ++ w ++ v)-wordPoly (u ++ z ++ v) =
      X^u.length*(wordPoly w-wordPoly z) := by
  simp only [wordPoly_append, List.length_append, hlen]
  ring

lemma template_hole {A : Set ℕ} {r k : ℕ} (hk : 0 < k)
    (hA : JetInvariant A r) (hfree : ¬ HasAP A k)
    (L a d : ℕ) (hd : 0 < d) (w : Fin k → List ℕ)
    (hlen : ∀ i, (w i).length = L)
    (hbin : ∀ i, ∀ b ∈ w i, b < 2)
    (hval : ∀ i, Nat.ofDigits 2 (w i) = a+i.val*d)
    (hjet : ∀ i j, (X-1 : ℤ[X])^r ∣ wordPoly (w i)-wordPoly (w j))
    (m s : ℕ) (hs : s < 2^m) :
    sectionSet (sectionSet A (2^m) s) (2^L) a = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  change 2^m*(2^L*t+a)+s ∈ A at ht
  let lo := Nat.digitsAppend 2 m s
  let hi := Nat.digits 2 t
  let zero : Fin k := ⟨0,hk⟩
  let v : Fin k → List ℕ := fun i ↦ lo ++ w i ++ hi
  have hlo : lo.length = m := Nat.length_digitsAppend (by norm_num : 1 < 2) m hs
  have hlow : ∀ b ∈ lo, b < 2 := Nat.lt_of_mem_digitsAppend (by norm_num : 1 < 2) m
  have hhigh : ∀ b ∈ hi, b < 2 := fun b hb ↦ Nat.digits_lt_base (by norm_num) hb
  have hvbin (i : Fin k) : ∀ b ∈ v i, b < 2 := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact (List.mem_append.mp hb).elim (hlow b) (hbin i b)
    · exact hhigh b hb
  have hvlen (i : Fin k) : (v zero).length = (v i).length := by
    simp only [v, List.length_append, hlen]
  have hvjet (i : Fin k) : (X-1 : ℤ[X])^r ∣ wordPoly (v i)-wordPoly (v zero) := by
    rw [wordPoly_sandwich lo hi (w i) (w zero) ((hlen i).trans (hlen zero).symm)]
    exact dvd_mul_of_dvd_right (hjet i zero) _
  have hvval (i : Fin k) : Nat.ofDigits 2 (v i) =
      (2^m*(2^L*t+a)+s) + i.val*(2^m*d) := by
    simp only [v, Nat.ofDigits_append, List.length_append, hlo, hlen, hval]
    rw [show Nat.ofDigits 2 lo = s from padded_value m s,
      show Nat.ofDigits 2 hi = t from Nat.ofDigits_digits 2 t, pow_add]
    ring
  have hz : Nat.ofDigits 2 (v zero) ∈ A := by simpa only [hvval, zero, Nat.zero_mul, Nat.add_zero] using ht
  apply hfree
  refine ⟨2^m*(2^L*t+a)+s,2^m*d,by positivity,?_⟩
  intro i hi'
  have hv := hA (v zero) (v ⟨i,hi'⟩) (hvbin zero) (hvbin _) (hvlen _) (hvjet _) hz
  simpa only [hvval] using hv

/-- AP avoidance under finite-jet invariance gives a uniform missing binary block. -/
theorem jet_invariant_uniform_holes {A : Set ℕ} {r k : ℕ} (hk : 0 < k)
    (hA : JetInvariant A r) (hfree : ¬ HasAP A k) :
    ∃ L : ℕ, 0 < L ∧ ∀ B ∈ dyadicKernel A,
      ∃ a < 2^L, sectionSet B (2^L) a = ∅ := by
  obtain ⟨L,a,d,hL,hd,w,hlen,hbin,hval,hjet⟩ := binary_jet_progression r k
  let zero : Fin k := ⟨0,hk⟩
  have ha : a < 2^L := by
    have hb := Nat.ofDigits_lt_base_pow_length (by norm_num : 1 < 2) (hbin zero)
    simpa only [hval, zero, Nat.zero_mul, Nat.add_zero, hlen] using hb
  refine ⟨L,hL,?_⟩
  rintro B ⟨m,s,hs,rfl⟩
  exact ⟨a,ha,template_hole hk hA hfree L a d hd w hlen hbin hval hjet m s hs⟩

/-- A positive special case for every progression length, under the explicit invariance. -/
theorem jet_invariant_noAP_summable {A : Set ℕ} {r k : ℕ} (hk : 0 < k)
    (hA : JetInvariant A r) (hfree : ¬ HasAP A k) :
    Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  obtain ⟨L,hL,hholes⟩ := jet_invariant_uniform_holes hk hA hfree
  apply summable_of_count_pow_bound (one_lt_pow₀ one_lt_two hL.ne')
  intro j
  exact count_pow_le_of_holes (dyadicKernel A) (2^L)
    (fun B hB a ha ↦ kernel_closed hB ha) hholes j A (self_mem_kernel A)

theorem jet_invariant_contains_ap {A : Set ℕ} {r : ℕ} (hA : JetInvariant A r)
    (hs : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) (k : ℕ) :
    ∃ S ⊆ A, S.IsAPOfLength k := by
  by_cases hk : k = 0
  · subst k
    exact ⟨∅,Set.empty_subset _,by simp⟩
  have hap : HasAP A k := by
    by_contra h
    exact hs (jet_invariant_noAP_summable (Nat.pos_of_ne_zero hk) hA h)
  obtain ⟨a,d,hd,hmem⟩ := hap
  let g : ℕ → ℕ := fun i ↦ a+i*d
  have hgi : Function.Injective g := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
  refine ⟨g '' Set.Iio k,?_,a,d,?_,?_⟩
  · rintro x ⟨i,hi,rfl⟩
    exact hmem i hi
  · change (g '' Set.Iio k).encard = (k : ℕ∞)
    rw [hgi.encard_image]
    exact Set.Nat.encard_range k
  · ext x
    simp [g]

/-- The original conclusion with the additional finite binary-jet invariance hypothesis. -/
theorem jet_invariant_case {A : Set ℕ} {r : ℕ} (hA : JetInvariant A r)
    (hs : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) :
    ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k := by
  apply Filter.frequently_atTop.mpr
  intro k
  exact ⟨k,le_rfl,jet_invariant_contains_ap hA hs k⟩

#print axioms binary_jet_progression
#print axioms jet_invariant_noAP_summable
#print axioms jet_invariant_case
end Erdos3DigitPolynomialCase
