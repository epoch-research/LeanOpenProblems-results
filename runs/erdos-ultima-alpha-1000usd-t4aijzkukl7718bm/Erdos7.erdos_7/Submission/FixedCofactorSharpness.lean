import Submission.RootMarginalSharpness

/-! Fixed-cofactor partial families. Deep projected ternary classes are
separated inside one complementary residue rather than given new colors.
The family has private integers and an explicit hole; it is not a cover. -/
namespace Erdos7FixedCofactorSharpness
open scoped BigOperators
open Erdos7PrimePowerCombFamily Erdos7PrimePowerBoxRealization
open Erdos7PresentCylinderArithmetic Erdos7PresentCylinderLower
open Erdos7RootMarginalSharpness (Label bases caps exps bases_prime bases_injective exps_bound
  one_not_exit stem_not_exit good good_card nested_good cylinder_nested cylinder_congr
  moduli_injective moduli_odd_gt_one divisor_closed arithmeticGood arithmeticCount)
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The late exits are disjoint, but stay below every earlier nested prefix. -/
def residue (q e : ℕ) : ℤ := if e < q-1 then 1 else 2+exitValue 3 e 1

def color (q e : ℕ) : ℕ := min e (q-1)

def target {E : ℕ} (q : ℕ) : Label E → Fin 2 → ℤ
  | Sum.inl j => ![exitValue 3 (j.val+1) 1,0]
  | Sum.inr j => ![residue q j.val,(color q j.val : ℤ)]
def witness {E : ℕ} (q : ℕ) : Label E → Fin 2 → ℤ
  | Sum.inl j => ![exitValue 3 (j.val+1) 1,1]
  | Sum.inr j => ![if j.val = 0 then -1 else residue q j.val,(color q j.val : ℤ)]
def hole : Fin 2 → ℤ := ![-1,1]

lemma residue_mod_three {q e : ℕ} (hq : 3 < q) : (3 : ℤ) ∣ residue q e-1 := by
  by_cases he : e < q-1
  · simp [residue,he]
  · have hp : (3 : ℤ) ∣ (3 : ℤ)^(e-1) := by
      exact (by simpa using pow_dvd_pow (3 : ℤ) (show 1 ≤ e-1 by omega))
    convert hp using 1 <;> simp [residue,he,exitValue] <;> ring

lemma color_lt {q e : ℕ} (hq : 0 < q) : color q e < q := by
  simp only [color]
  omega

lemma late_residue_separated {q e f : ℕ} (he : q-1 ≤ e) (hf : q-1 ≤ f)
    (hqe : 1 < q) (hd : (3 : ℤ)^min e f ∣ residue q e-residue q f) : e = f := by
  have h : (3 : ℤ)^min e f ∣ exitValue 3 e 1-exitValue 3 f 1 := by
    convert hd using 1 <;> simp [residue,show ¬e<q-1 by omega,show ¬f<q-1 by omega]
  exact ((exit_congruent_iff (by omega : 0 < (3:ℕ)) (by omega : 0 < e)
    (by omega : 0 < f) (by omega : 0 < (1:ℕ)) (by omega : 0 < (1:ℕ))
    (by omega : 1 < (3:ℕ)) (by omega : 1 < (3:ℕ))).mp h).1

lemma residue_not_pure {q e f : ℕ} (hq : 3 < q) (hf : 0 < f) :
    ¬ (3 : ℤ) ∣ residue q e-exitValue 3 f 1 := by
  intro h
  apply one_not_exit f hf
  convert dvd_sub h (residue_mod_three (e := e) hq) using 1 <;> ring

lemma stem_not_residue {q e : ℕ} (hq : 3 < q) :
    ¬ (3 : ℤ) ∣ -1-residue q e := by
  intro h
  have hh : (3 : ℤ) ∣ -2 := by
    convert dvd_add h (residue_mod_three (e := e) hq) using 1 <;> ring
  norm_num at hh

lemma private_coordinates {E q : ℕ} (hq : 3 < q) (j k : Label E) :
    (∀ i, (bases q i : ℤ)^exps k i ∣ witness q j i-target q k i) ↔ k = j := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    cases j with
    | inl j => cases k with
      | inl k =>
        simp only [bases,exps,witness,target,Matrix.cons_val_zero] at h0
        have hh := (exit_congruent_iff (by omega : 0 < (3:ℕ))
          (Nat.succ_pos j.val) (Nat.succ_pos k.val) (by omega : 0 < (1:ℕ))
          (by omega : 0 < (1:ℕ)) (by omega : 1 < (3:ℕ))
          (by omega : 1 < (3:ℕ))).mp
          ((pow_dvd_pow (3:ℤ) (min_le_right _ _)).trans h0)
        congr 1; apply Fin.ext; omega
      | inr k =>
        simp only [bases,exps,witness,target,Matrix.cons_val_one,Matrix.cons_val_zero,
          pow_one] at h0 h1
        by_cases hk : k.val = 0
        · simp [color,hk] at h1
          have := Int.le_of_dvd (by norm_num : (0:ℤ)<1) h1
          omega
        · apply False.elim
          apply residue_not_pure (e := k.val) hq (Nat.succ_pos j.val)
          have hd := (pow_dvd_pow (3:ℤ) (show 1 ≤ k.val by omega)).trans h0
          convert dvd_neg.mpr hd using 1 <;> ring
    | inr j => cases k with
      | inl k =>
        simp only [bases,exps,witness,target,Matrix.cons_val_zero] at h0
        by_cases hj : j.val = 0
        · rw [if_pos hj] at h0
          exact (stem_not_exit (k.val+1) (by omega) h0).elim
        · rw [if_neg hj] at h0
          exact (residue_not_pure hq (Nat.succ_pos k.val)
            ((pow_dvd_pow (3:ℤ) (by omega : 1 ≤ k.val+1)).trans h0)).elim
      | inr k =>
        simp only [bases,exps,witness,target,Matrix.cons_val_one,Matrix.cons_val_zero,
          pow_one] at h0 h1
        have hh := bounded_congruent_eq (by positivity : (0:ℤ) ≤ color q j.val)
          (by positivity : (0:ℤ) ≤ color q k.val)
          (by exact_mod_cast color_lt (e := j.val) (by omega : 0<q))
          (by exact_mod_cast color_lt (e := k.val) (by omega : 0<q)) h1
        have hcol : color q j.val = color q k.val := by exact_mod_cast hh
        have heq : j.val = k.val := by
          by_cases hj : j.val < q-1
          · simp only [color] at hcol
            omega
          · have hk : q-1 ≤ k.val := by simp only [color] at hcol; omega
            rw [if_neg (by omega : j.val ≠ 0)] at h0
            apply late_residue_separated (by omega) hk (by omega : 1<q)
            exact (pow_dvd_pow (3:ℤ) (min_le_right _ _)).trans h0
        congr 1; apply Fin.ext; exact heq.symm
  · rintro rfl i
    cases k with
    | inl j => fin_cases i <;> simp [bases,exps,witness,target]
    | inr j =>
      fin_cases i
      · by_cases hj : j.val = 0 <;> simp [bases,exps,witness,target,hj]
      · simp [bases,exps,witness,target]

lemma hole_coordinates {E q : ℕ} (hq : 3 < q) (k : Label E) :
    ¬ ∀ i, (bases q i : ℤ)^exps k i ∣ hole i-target q k i := by
  intro h
  cases k with
  | inl k =>
    exact stem_not_exit (k.val+1) (by omega) (by simpa [bases,exps,hole,target] using h 0)
  | inr k =>
    by_cases hk : k.val = 0
    · have hh : (q : ℤ) ∣ 1 := by simpa [bases,exps,hole,target,color,hk] using h 1
      have := Int.le_of_dvd (by norm_num : (0:ℤ)<1) hh
      omega
    · have hh : (3 : ℤ)^k.val ∣ -1-residue q k.val := by
        simpa [bases,exps,hole,target] using h 0
      exact stem_not_residue hq ((pow_dvd_pow (3:ℤ) (show 1≤k.val by omega)).trans hh)

/-- Unlike the original rank-colored construction, q is fixed and E is
arbitrary. The private points and the hole are actual integer residues. -/
theorem arithmetic_family (E q : ℕ) (hq : q.Prime) (h3 : 3 < q) :
    ∃ (a z : Label E → ℤ) (v : ℤ),
      (∀ j i, (bases q i : ℤ)^caps E i ∣ a j-target q j i) ∧
      (∀ j k, (modulus (bases q) (exps k) : ℤ) ∣ z j-a k ↔ k = j) ∧
      (∀ k, ¬ (modulus (bases q) (exps k) : ℤ) ∣ v-a k) := by
  exact realize_partial_family (bases q) (bases_prime hq) (bases_injective h3)
    (caps E) exps exps_bound (target q) (witness q) hole
    (private_coordinates h3) (hole_coordinates h3)

noncomputable def active (E q : ℕ) (x : ZMod (3^E)) : Finset ℕ :=
  (Finset.range E).filter (fun j => x ∈ cylinder 3 E (j+1) (residue q (j+1)))
noncomputable def rootCount (E q : ℕ) (x : ZMod (3^E)) : ℕ := 1+(active E q x).card

lemma projection_good {E q e : ℕ} (hq : 3<q) (he : 0<e) :
    cylinder 3 E e (residue q e) ⊆ good E := by
  intro x hx
  apply nested_good (a := 1) (by omega)
  rw [mem_cylinder] at hx ⊢
  simp only [Nat.cast_pow,Nat.cast_ofNat,pow_one] at hx ⊢
  have h := (pow_dvd_pow (3:ℤ) (show 1≤e by omega)).trans hx
  convert dvd_add h (residue_mod_three (e := e) hq) using 1 <;> ring

lemma projection_prefix {E q b e : ℕ} (hb : b<q-1) (hbe : b<e) :
    cylinder 3 E e (residue q e) ⊆ cylinder 3 E b 1 := by
  intro x hx
  rw [mem_cylinder] at hx ⊢
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hx ⊢
  have h := (pow_dvd_pow (3:ℤ) hbe.le).trans hx
  have hd : (3:ℤ)^b ∣ residue q e-1 := by
    by_cases he : e<q-1
    · simp [residue,he]
    · have hp := pow_dvd_pow (3:ℤ) (show b≤e-1 by omega)
      convert hp using 1 <;> simp [residue,he,exitValue] <;> ring
  convert dvd_add h hd using 1 <;> ring

/-- A finite-set hinge identity, using only downward closure below the cutoff. -/
lemma hinge_filter (S : Finset ℕ) (s : ℕ)
    (hdown : ∀ j ∈ S, s≤j → Finset.range s ⊆ S) :
    max ((S.card : ℚ)-s) 0 = ((S.filter (fun j => s≤j)).card : ℚ) := by
  classical
  by_cases hn : (S.filter (fun j => s≤j)).Nonempty
  · obtain ⟨j,hj⟩ := hn
    obtain ⟨hj,hsj⟩ := Finset.mem_filter.mp hj
    have he : S.filter (fun j => j<s) = Finset.range s := by
      ext k
      simp only [Finset.mem_filter,Finset.mem_range]
      exact and_iff_right_of_imp (fun hk => hdown j hj hsj (Finset.mem_range.mpr hk))
    have hh := S.card_filter_add_card_filter_not (fun j => j<s)
    simp only [not_lt] at hh
    rw [he,Finset.card_range] at hh
    have hh' : (S.card:ℚ)-s = ((S.filter (fun j => s≤j)).card:ℚ) := by
      exact_mod_cast (show (S.card:ℤ)-s = (S.filter (fun j => s≤j)).card by omega)
    rw [hh',max_eq_left (by positivity)]
  · have he : S.filter (fun j => s≤j) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hs : S ⊆ Finset.range s := by
      intro j hj
      apply Finset.mem_range.mpr
      by_contra h
      have hm := Finset.mem_filter.mpr ⟨hj,(by omega : s≤j)⟩
      rw [he] at hm
      exact Finset.notMem_empty j hm
    have hc := Finset.card_le_card hs
    rw [Finset.card_range] at hc
    rw [he,Finset.card_empty,Nat.cast_zero,max_eq_right]
    exact sub_nonpos.mpr (by exact_mod_cast hc)

lemma root_hinge_identity {E q t : ℕ} (ht : 0<t) (htq : t<q) (htE : t≤E+1)
    (x : ZMod (3^E)) :
    max ((rootCount E q x : ℚ)-t) 0 =
      (((active E q x).filter (fun j => t-1≤j)).card : ℚ) := by
  have hh := hinge_filter (active E q x) (t-1) (by
    intro j hj hsj k hk
    have hk' := Finset.mem_range.mp hk
    have hx := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega),?_⟩
    have hp := projection_prefix (E := E) (q := q) (b := k+1) (e := j+1)
      (by omega) (by omega) hx
    simpa only [residue,if_pos (show k+1<q-1 by omega)] using hp)
  have hcast : ((t-1:ℕ):ℚ) = (t:ℚ)-1 := by exact_mod_cast (show ((t-1:ℕ):ℤ) = (t:ℤ)-1 by omega)
  rw [hcast] at hh
  convert hh using 1 <;> simp [rootCount] <;> ring

/-- All low integer hinge sums equal their unrestricted geometric values.
No exponent tail is omitted, and q is independent of E. -/
theorem root_hinge_sum {E q t : ℕ} (hq : 3<q) (ht : 0<t) (htq : t<q)
    (htE : t≤E+1) :
    (∑ x ∈ good E, max ((rootCount E q x : ℚ)-t) 0) =
      Fintype.card (ZMod (3^E)) *
        ∑ j ∈ (Finset.range E).filter (fun j => t-1≤j), (1/3:ℚ)^(j+1) := by
  classical
  let J := (Finset.range E).filter (fun j => t-1≤j)
  have he (x : ZMod (3^E)) : (active E q x).filter (fun j => t-1≤j) =
      J.filter (fun j => x ∈ cylinder 3 E (j+1) (residue q (j+1))) := by
    ext j
    simp [active,J,and_left_comm,and_assoc,and_comm]
  simp_rw [root_hinge_identity ht htq htE,he]
  have hh (x : ZMod (3^E)) :
      ((J.filter (fun j => x ∈ cylinder 3 E (j+1) (residue q (j+1)))).card : ℚ) =
      ∑ j ∈ J, if x ∈ cylinder 3 E (j+1) (residue q (j+1)) then (1:ℚ) else 0 := by simp
  simp_rw [hh]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjE : j+1≤E := by have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1; omega
  have hs : (good E).filter (fun x => x ∈ cylinder 3 E (j+1) (residue q (j+1))) =
      cylinder 3 E (j+1) (residue q (j+1)) := by
    exact Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (projection_good hq (by omega)))
  calc
    _ = (((good E).filter (fun x => x ∈ cylinder 3 E (j+1) (residue q (j+1)))).card:ℚ) := by simp [Finset.filter_mem_eq_inter]
    _ = _ := by rw [hs,cylinder_card 3 E (j+1) hjE]; norm_num

/-- The actual projected count is bounded by the fixed cofactor q. -/
theorem root_count_le {E q : ℕ} (hq : 3<q) (x : ZMod (3^E)) : rootCount E q x ≤ q := by
  classical
  have hlate : ((active E q x).filter (fun j => q-2≤j)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro j hj k hk
    obtain ⟨hja,hj⟩ := Finset.mem_filter.mp hj
    obtain ⟨hka,hk⟩ := Finset.mem_filter.mp hk
    have hx := (Finset.mem_filter.mp hja).2
    have hy := (Finset.mem_filter.mp hka).2
    rw [mem_cylinder] at hx hy
    simp only [Nat.cast_pow,Nat.cast_ofNat] at hx hy
    have hd : (3:ℤ)^min (j+1) (k+1) ∣ residue q (j+1)-residue q (k+1) := by
      convert dvd_sub ((pow_dvd_pow (3:ℤ) (min_le_right _ _)).trans hy)
        ((pow_dvd_pow (3:ℤ) (min_le_left _ _)).trans hx) using 1 <;> ring
    have he := late_residue_separated (by omega : q-1≤j+1) (by omega : q-1≤k+1)
      (by omega : 1<q) hd
    omega
  have hearly : ((active E q x).filter (fun j => j<q-2)).card ≤ q-2 := by
    have hs : (active E q x).filter (fun j => j<q-2) ⊆ Finset.range (q-2) := by
      intro j hj
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
    simpa only [Finset.card_range] using Finset.card_le_card hs
  have hh := (active E q x).card_filter_add_card_filter_not (fun j => j<q-2)
  simp only [not_lt] at hh
  dsimp only [rootCount]
  omega

lemma arithmeticGood_eq {E q : ℕ} (a : Label E → ℤ)
    (ha : ∀ j i, (bases q i : ℤ)^caps E i ∣ a j-target q j i) :
    arithmeticGood a = good E := by
  have hh (j : Fin E) : cylinder 3 E (j.val+1) (a (Sum.inl j)) =
      Erdos7RootMarginalSharpness.pure E j.val := by
    apply cylinder_congr (by omega)
    simpa [bases,caps,target] using ha (Sum.inl j) 0
  ext x
  simp only [arithmeticGood,good,Finset.mem_sdiff,Finset.mem_univ,true_and,
    Finset.mem_biUnion,hh]
  simp only [Fin.exists_iff,Finset.mem_range, exists_prop]

lemma arithmeticCount_eq {E q : ℕ} (a : Label E → ℤ)
    (ha : ∀ j i, (bases q i : ℤ)^caps E i ∣ a j-target q j i) (x : ZMod (3^E)) :
    arithmeticCount a x = rootCount E q x := by
  have hh (j : Fin (E+1)) : cylinder 3 E j.val (a (Sum.inr j)) =
      cylinder 3 E j.val (residue q j.val) := by
    apply cylinder_congr (by omega)
    simpa [bases,caps,target] using ha (Sum.inr j) 0
  simp only [arithmeticCount,hh]
  rw [Fin.sum_univ_succ]
  have hz : x ∈ cylinder 3 E 0 (residue q 0) := by rw [mem_cylinder]; simp
  simp only [Fin.val_zero,if_pos hz,Fin.val_succ,rootCount]
  congr 1
  rw [Fin.sum_univ_eq_sum_range
    (fun j => if x ∈ cylinder 3 E (j+1) (residue q (j+1)) then (1:ℕ) else 0)]
  exact Finset.sum_boole _ _

/-- Fixed q, arbitrary E, with the geometric low-hinge law on the actual
pure-complement sampling space. This is an equality, not a numerical bound. -/
theorem arithmetic_hinge_law {E q t : ℕ} (hq : 3<q) (ht : 0<t) (htq : t<q)
    (htE : t≤E+1) (a : Label E → ℤ)
    (ha : ∀ j i, (bases q i : ℤ)^caps E i ∣ a j-target q j i) :
    (∑ x ∈ arithmeticGood a, max ((arithmeticCount a x : ℚ)-t) 0) /
        (arithmeticGood a).card =
      (2/(1+(1/3:ℚ)^E)) *
        ∑ j ∈ (Finset.range E).filter (fun j => t-1≤j), (1/3:ℚ)^(j+1) := by
  simp only [arithmeticGood_eq a ha,arithmeticCount_eq a ha]
  rw [root_hinge_sum hq ht htq htE,good_card]
  have hcard : (Fintype.card (ZMod (3^E)):ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0<Fintype.card (ZMod (3^E))))
  have hden : 1+(1/3:ℚ)^E ≠ 0 := by positivity
  field_simp

/-- A complete arithmetic sharpness package with fixed complementary prime.
The explicit uncovered integer prevents this from being a covering witness. -/
theorem exists_fixed_cofactor_sharpness (E q : ℕ) (hq : q.Prime) (h3 : 3<q) :
    ∃ (a z : Label E → ℤ) (v : ℤ),
      Function.Injective (fun j : Label E => modulus (bases q) (exps j)) ∧
      (∀ j : Label E, 1 < modulus (bases q) (exps j) ∧ Odd (modulus (bases q) (exps j))) ∧
      (∀ j : Label E, ∀ d : ℕ, d ∣ modulus (bases q) (exps j) → 1<d →
        ∃ k : Label E, modulus (bases q) (exps k) = d) ∧
      (∀ j k, (modulus (bases q) (exps k) : ℤ) ∣ z j-a k ↔ k = j) ∧
      (∀ k, ¬ (modulus (bases q) (exps k) : ℤ) ∣ v-a k) ∧
      (∀ x, arithmeticCount a x ≤ q) ∧
      (∀ t, 0<t → t<q → t≤E+1 →
        (∑ x ∈ arithmeticGood a, max ((arithmeticCount a x : ℚ)-t) 0) /
          (arithmeticGood a).card = (2/(1+(1/3:ℚ)^E)) *
            ∑ j ∈ (Finset.range E).filter (fun j => t-1≤j), (1/3:ℚ)^(j+1)) := by
  obtain ⟨a,z,v,ha,hz,hv⟩ := arithmetic_family E q hq h3
  refine ⟨a,z,v,moduli_injective E q hq h3,moduli_odd_gt_one hq h3,
    divisor_closed hq h3,hz,hv,?_,?_⟩
  · intro x
    rw [arithmeticCount_eq a ha]
    exact root_count_le h3 x
  · intro t ht htq htE
    exact arithmetic_hinge_law h3 ht htq htE a ha

#print axioms exists_fixed_cofactor_sharpness
#print axioms arithmetic_hinge_law
#print axioms root_count_le
#print axioms root_hinge_sum
#print axioms arithmetic_family
end Erdos7FixedCofactorSharpness
