import Submission.Capped19Metadata
import Submission.FiniteGeometricBudget

/-! Real-valued interpretation and continuum checks for the finite capped-19
scalar table. This module does not yet assert an arithmetic covering theorem. -/
namespace Erdos7Capped19Real
open scoped BigOperators
open Erdos7Capped19Rows Erdos7Capped19Metadata
set_option maxHeartbeats 2500000

lemma map_range_sum {α : Type*} [AddCommMonoid α] (f : ℕ → α) (N : ℕ) :
    ((List.range N).map f).sum = ∑ j ∈ Finset.range N, f j := by
  simpa only [List.toFinset_range] using (List.sum_toFinset f (List.nodup_range (n := N))).symm

noncomputable def evalR (f : List ℚ) : ℝ → ℝ := Erdos7FiniteHingeFunctions.eval (fun j => (coeff f j : ℝ)) 8
noncomputable def ret (s : Stage) (k : ℝ) : ℝ :=
  max 0 (min 1 ((s.cap:ℝ)*(1-k/((s.p:ℝ)-1))))

lemma coeff_nonneg (f : List ℚ) (hf : Good f) (j : ℕ) : 0 ≤ coeff f j := by
  dsimp only [coeff]
  cases he : f[j]? with
  | none => simp
  | some a => exact hf.1 a (List.mem_of_getElem? he)

lemma evalR_convex (f : List ℚ) (hf : Good f) : ConvexOn ℝ Set.univ (evalR f) :=
  Erdos7FiniteHingeFunctions.eval_convex _ _ (fun j _ => Rat.cast_nonneg.mpr (coeff_nonneg f hf (j+2)))

lemma evalR_monotone (f : List ℚ) (hf : Good f) : Monotone (evalR f) :=
  Erdos7FiniteHingeFunctions.eval_monotone _ _ (Rat.cast_nonneg.mpr (coeff_nonneg f hf 1))
    (fun j _ => Rat.cast_nonneg.mpr (coeff_nonneg f hf (j+2)))

lemma evalR_nonneg (f : List ℚ) (hf : Good f) (x : ℝ) (hx : 1 ≤ x) : 0 ≤ evalR f x :=
  Erdos7FiniteHingeFunctions.eval_nonneg _ _ (Rat.cast_nonneg.mpr (coeff_nonneg f hf 0))
    (Rat.cast_nonneg.mpr (coeff_nonneg f hf 1))
    (fun j _ => Rat.cast_nonneg.mpr (coeff_nonneg f hf (j+2))) x hx

lemma evalR_cast (f : List ℚ) (x : ℚ) : evalR f (x:ℝ) = (evaluate f x : ℝ) := by
  rw [evaluate, map_range_sum]
  simp only [evalR, Erdos7FiniteHingeFunctions.eval, Erdos7FiniteHingeFunctions.hinge, coeff, Rat.cast_add, Rat.cast_mul, Rat.cast_sub,
    Rat.cast_one, Rat.cast_sum, Rat.cast_max, Rat.cast_zero, Rat.cast_natCast, Rat.cast_ofNat]

lemma slope_cast (f : List ℚ) (hf : Good f) :
    (Erdos7Capped19Rows.slope f : ℝ) = Erdos7FiniteHingeFunctions.slope (fun j => (coeff f j : ℝ)) 8 := by
  rw [hf.2, map_range_sum]
  simp only [Rat.cast_add, Rat.cast_sum, Erdos7FiniteHingeFunctions.slope]

lemma slope_nonneg (f : List ℚ) (hf : Good f) : 0 ≤ (Erdos7Capped19Rows.slope f : ℝ) := by
  rw [slope_cast f hf]
  exact add_nonneg (Rat.cast_nonneg.mpr (coeff_nonneg f hf 1))
    (Finset.sum_nonneg (fun j _ => Rat.cast_nonneg.mpr (coeff_nonneg f hf (j+2))))

lemma evalR_tail (f : List ℚ) (hf : Good f) (x : ℝ) (hx : 9 ≤ x) :
    evalR f x = evalR f 9+(Erdos7Capped19Rows.slope f:ℝ)*(x-9) := by
  rw [slope_cast f hf]
  simpa only [evalR, Nat.cast_ofNat, show (8:ℝ)+1=9 by norm_num] using
    Erdos7FiniteHingeFunctions.eval_affine_tail (fun j => (coeff f j:ℝ)) 8 x (by norm_num; exact hx)

lemma ret_cast (s : Stage) (k : ℚ) : ret s (k:ℝ) = (retention s.p s.cap k:ℝ) := by
  simp only [ret, retention, Rat.cast_max, Rat.cast_min, Rat.cast_zero, Rat.cast_one,
    Rat.cast_mul, Rat.cast_sub, Rat.cast_div]

lemma mixture_cast (p c h : ℚ) (f : List ℚ) (n : ℚ) :
    Erdos7FiniteGeometricBudget.budget (p:ℝ) c h (evalR f) (Erdos7Capped19Rows.slope f:ℝ) 9 n =
      (mixture p c h f n:ℝ) := by
  rw [mixture, map_range_sum]
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_sub,
    Rat.cast_min, Rat.cast_sum, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one,
    ← evalR_cast, Erdos7FiniteGeometricBudget.budget, Erdos7FiniteGeometricBudget.op, Erdos7FiniteGeometricBudget.q, Erdos7FiniteGeometricBudget.tail]

lemma moment_cast (p c h : ℚ) : Erdos7FiniteGeometricBudget.moment (p:ℝ) c h 4 = (firstMoment p c h:ℝ) := by
  rw [firstMoment, map_range_sum]
  simp only [Erdos7FiniteGeometricBudget.moment, Erdos7FiniteGeometricBudget.q, Erdos7FiniteGeometricBudget.tail, Rat.cast_add, Rat.cast_sum, Rat.cast_min,
    Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat, Rat.cast_mul]

lemma evalR_unit_cell (f : List ℚ) (j : ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    evalR f (a*(j+1)+b*(j+2))=a*evalR f (j+1)+b*evalR f (j+2) :=
  Erdos7FiniteHingeFunctions.eval_on_unit_interval _ _ j a b ha hb hab


noncomputable def cost (s : Stage) (future : List ℚ) (k n : ℝ) : ℝ :=
  1-ret s k + Erdos7FiniteGeometricBudget.budget s.p s.cap (ret s k)
    (evalR future) (Erdos7Capped19Rows.slope future) 9 n

lemma cost_cast (s : Stage) (future : List ℚ) (k n : ℚ) :
    cost s future k n = ((1-retention s.p s.cap k +
      mixture s.p s.cap (retention s.p s.cap k) future n : ℚ):ℝ) := by
  rw [cost, ret_cast, mixture_cast]
  push_cast
  rfl

lemma row_all_counts (s : Stage) (future : List ℚ) (hv : Valid s future)
    (hm : Metadata s future) (k : ℚ) (hk : k ∈ s.rows) (n : ℝ) (hn : 1 ≤ n) :
    cost s future k n ≤ evalR s.U k+evalR s.V n := by
  rcases hv with ⟨_,_,_,_,_,hrows⟩
  rcases hm with ⟨hp,hc,hU,hV,hF,hG,_,_,_,_⟩
  have hp' : (1:ℝ)<s.p := by exact_mod_cast hp
  have hc' : (0:ℝ)≤s.cap := by exact_mod_cast hc
  have hh : 0 ≤ ret s (k:ℝ) := le_max_left _ _
  have hconv : ConvexOn ℝ Set.univ (cost s future (k:ℝ)) :=
    (convexOn_const _ (convex_univ : Convex ℝ (Set.univ : Set ℝ))).add
      (Erdos7FiniteGeometricBudget.budget_convex _ _ _ hp' hc' hh _ (evalR_convex future hG) _ _)
  have hend (j : ℕ) (hj : j<9) :
      cost s future k ((j:ℝ)+1) ≤ evalR s.U k+evalR s.V ((j:ℝ)+1) := by
    have hq : cost s future k (Rat.cast ((j:ℚ)+1):ℝ) ≤ evalR s.U k+evalR s.V (Rat.cast ((j:ℚ)+1):ℝ) := by
      rw [cost_cast, evalR_cast, evalR_cast, ← Rat.cast_add]
      exact_mod_cast (hrows k hk).2.2 j (List.mem_range.mpr hj)
    simpa only [Rat.cast_add, Rat.cast_one, Rat.cast_natCast] using hq
  by_cases hn9 : n ≤ 9
  · obtain ⟨j,hj,hjn⟩ := Erdos7FiniteHingeFunctions.exists_unit_interval 8 (by norm_num) n hn (by norm_num; exact hn9)
    obtain ⟨a,b,ha,hb,hab,he⟩ := Erdos7FiniteHingeFunctions.interval_combination _ _ n hjn
    rw [he]
    apply Erdos7FiniteHingeFunctions.convex_below_affine_cell (cost s future k)
      (fun x => evalR s.U k+evalR s.V x) hconv _ _ a b ha hb hab
    · rw [evalR_unit_cell s.V j a b ha hb hab]
      have hh : (a+b)*evalR s.U k=evalR s.U k := by rw [hab, one_mul]
      nlinarith
    · exact hend j (by omega)
    · simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hend (j+1) (by omega)
  · have hn' : 9 ≤ n := le_of_lt (lt_of_not_ge hn9)
    have hS : (Erdos7Capped19Rows.slope future:ℝ)*
        Erdos7FiniteGeometricBudget.moment s.p s.cap (ret s k) 9 ≤
        (Erdos7Capped19Rows.slope s.V:ℝ) := by
      calc
        _ ≤ (Erdos7Capped19Rows.slope future:ℝ)*
            Erdos7FiniteGeometricBudget.moment s.p s.cap (ret s k) 4 :=
          mul_le_mul_of_nonneg_left (Erdos7FiniteGeometricBudget.moment_antitone _ _ _ hp' hc' (by omega))
            (slope_nonneg future hG)
        _ ≤ _ := by
          rw [ret_cast, moment_cast, ← Rat.cast_mul]
          exact_mod_cast (hrows k hk).2.1
    have htail := Erdos7FiniteGeometricBudget.budget_affine_tail
      (s.p:ℝ) s.cap (ret s k) (evalR future) 9 (Erdos7Capped19Rows.slope future)
      (by norm_num) (evalR_tail future hG) 9 n hn'
    have hvTail := evalR_tail s.V hV n hn'
    have hbase : cost s future k 9 ≤ evalR s.U k+evalR s.V 9 := by
      simpa only [Nat.cast_ofNat, show (8:ℝ)+1=9 by norm_num] using hend 8 (by omega)
    have hprod := mul_le_mul_of_nonneg_right hS (sub_nonneg.mpr hn')
    dsimp only [cost] at hbase ⊢
    rw [htail, hvTail]
    nlinarith


noncomputable def rawR (s : Stage) (k : ℝ) : ℝ := (s.cap:ℝ)*(1-k/((s.p:ℝ)-1))

lemma raw_cast (s : Stage) (k : ℚ) : rawR s k=(raw s k:ℝ) := by
  simp only [rawR, raw, Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_div]

lemma min_on_segment (A B T a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (hcell : (A ≤ T ∧ B ≤ T) ∨ (T ≤ A ∧ T ≤ B)) :
    min (a*A+b*B) T=a*min A T+b*min B T := by
  have he : (a+b)*T=T := by rw [hab, one_mul]
  rcases hcell with h | h
  · have h₁ := mul_le_mul_of_nonneg_left h.1 ha
    have h₂ := mul_le_mul_of_nonneg_left h.2 hb
    have hh : a*A+b*B ≤ T := by nlinarith
    rw [min_eq_left hh, min_eq_left h.1, min_eq_left h.2]
  · have h₁ := mul_le_mul_of_nonneg_left h.1 ha
    have h₂ := mul_le_mul_of_nonneg_left h.2 hb
    have hh : T ≤ a*A+b*B := by nlinarith
    rw [min_eq_right hh, min_eq_right h.1, min_eq_right h.2]
    nlinarith

lemma ret_of_raw_nonneg (s : Stage) (x : ℝ) (hx : 0 ≤ rawR s x) :
    ret s x=min (rawR s x) 1 := by
  change max 0 (min 1 (rawR s x)) = min (rawR s x) 1
  rw [max_eq_right (le_min zero_le_one hx), min_comm]

lemma ret_on_cell (s : Stage) (A B : ℚ) (hc : Cell s (A,B)) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    ret s (a*A+b*B)=a*ret s A+b*ret s B := by
  rcases hc with ⟨_,hA,hB,hcase,_,_⟩
  have hA' : 0 ≤ rawR s A := by rw [raw_cast]; exact_mod_cast hA
  have hB' : 0 ≤ rawR s B := by rw [raw_cast]; exact_mod_cast hB
  have he : rawR s (a*A+b*B)=a*rawR s A+b*rawR s B := by
    dsimp only [rawR]
    have hh : (a+b)*(s.cap:ℝ)=(s.cap:ℝ) := by rw [hab, one_mul]
    simp only [div_eq_mul_inv]
    nlinarith
  have hraw : 0 ≤ rawR s (a*A+b*B) := by rw [he]; positivity
  rw [ret_of_raw_nonneg s _ hraw, he, ret_of_raw_nonneg s _ hA', ret_of_raw_nonneg s _ hB']
  apply min_on_segment _ _ _ a b ha hb hab
  simp only [raw_cast]
  rcases hcase with hl | hr
  · left; constructor
    · exact_mod_cast hl.1
    · exact_mod_cast hl.2
  · right; constructor
    · exact_mod_cast hr.1
    · exact_mod_cast hr.2

lemma q_on_cell (s : Stage) (A B : ℚ) (hc : Cell s (A,B)) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (j : ℕ) (hj : j<9) :
    Erdos7FiniteGeometricBudget.q s.p s.cap (ret s (a*A+b*B)) j =
      a*Erdos7FiniteGeometricBudget.q s.p s.cap (ret s A) j+
      b*Erdos7FiniteGeometricBudget.q s.p s.cap (ret s B) j := by
  have he := ret_on_cell s A B hc a b ha hb hab
  dsimp only [Erdos7FiniteGeometricBudget.q]
  rw [he]
  apply min_on_segment _ _ _ a b ha hb hab
  have ht := hc.2.2.2.2.2 j (List.mem_range.mpr hj)
  rcases ht with hl | hr
  · left; constructor
    · rw [ret_cast]; exact_mod_cast hl.1
    · rw [ret_cast]; exact_mod_cast hl.2
  · right; constructor
    · rw [ret_cast]; exact_mod_cast hr.1
    · rw [ret_cast]; exact_mod_cast hr.2

lemma U_on_cell (s : Stage) (A B : ℚ) (hc : Cell s (A,B)) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    evalR s.U (a*A+b*B)=a*evalR s.U A+b*evalR s.U B := by
  apply Erdos7FiniteHingeFunctions.eval_on_segment _ _ _ _ a b ha hb hab
  intro j hj
  have ht := hc.2.2.2.2.1 j (List.mem_range.mpr hj)
  rcases ht with hz | hl | hr
  · left; exact_mod_cast hz
  · right; left; constructor
    · exact_mod_cast hl.1
    · exact_mod_cast hl.2
  · right; right; constructor
    · exact_mod_cast hr.1
    · exact_mod_cast hr.2

lemma cost_on_cell (s : Stage) (future : List ℚ) (A B : ℚ) (hc : Cell s (A,B))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (n : ℝ) :
    cost s future (a*A+b*B) n=a*cost s future A n+b*cost s future B n := by
  have hr := ret_on_cell s A B hc a b ha hb hab
  have hq := q_on_cell s A B hc a b ha hb hab
  have hsum : (∑ j ∈ Finset.range 9,
      Erdos7FiniteGeometricBudget.q s.p s.cap (ret s (a*A+b*B)) j *
        (evalR future ((j+2)*n)-evalR future ((j+1)*n))) =
    a*(∑ j ∈ Finset.range 9, Erdos7FiniteGeometricBudget.q s.p s.cap (ret s A) j *
        (evalR future ((j+2)*n)-evalR future ((j+1)*n)))+
    b*(∑ j ∈ Finset.range 9, Erdos7FiniteGeometricBudget.q s.p s.cap (ret s B) j *
        (evalR future ((j+2)*n)-evalR future ((j+1)*n))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hq j (Finset.mem_range.mp hj)]
    ring
  dsimp only [cost, Erdos7FiniteGeometricBudget.budget, Erdos7FiniteGeometricBudget.op]
  rw [hsum, hr]
  have ht : (a+b)*(Erdos7FiniteGeometricBudget.tail s.p s.cap 9*
      (Erdos7Capped19Rows.slope future:ℝ)*n)=
      Erdos7FiniteGeometricBudget.tail s.p s.cap 9*(Erdos7Capped19Rows.slope future:ℝ)*n := by
    rw [hab, one_mul]
  nlinarith

/-- Transfer interval bounds along a finite list of rational nodes. -/
lemma bound_along_rows (a : ℚ) (l : List ℚ) (H : ℝ → ℝ) (L : ℝ)
    (hrow : ∀ r ∈ a::l, H r ≤ L)
    (hcell : ∀ ab ∈ (a::l).zip l, ∀ x ∈ Set.Icc (ab.1:ℝ) (ab.2:ℝ),
      H ab.1 ≤ L → H ab.2 ≤ L → H x ≤ L)
    (x : ℝ) (hx : (a:ℝ) ≤ x) (hlast : x ≤ (Rat.cast (lastValue a l):ℝ)) : H x ≤ L := by
  induction l generalizing a with
  | nil =>
    have he : x=(a:ℝ) := le_antisymm hlast hx
    rw [he]
    exact hrow a (by simp)
  | cons b l ih =>
    by_cases hxb : x ≤ (b:ℝ)
    · apply hcell (a,b) (by simp) x ⟨hx,hxb⟩
      · exact hrow a (by simp)
      · exact hrow b (by simp)
    · apply ih b (fun r hr => hrow r (by simp only [List.mem_cons] at hr ⊢; tauto))
        (fun ab hab y hy hA hB => hcell ab (by simp only [List.zip_cons_cons, List.mem_cons]; exact Or.inr hab) y hy hA hB)
        (le_of_lt (lt_of_not_ge hxb))
      exact hlast

theorem live_dual (s : Stage) (future : List ℚ) (hv : Valid s future)
    (hm : Metadata s future) (k n : ℝ) (hk : 1 ≤ k) (hkcut : k ≤ s.cut) (hn : 1 ≤ n) :
    cost s future k n ≤ evalR s.U k+evalR s.V n := by
  have hr := hm.2.2.2.2.2.2.1
  have hlast := hm.2.2.2.2.2.2.2.1
  have hcells := hm.2.2.2.2.2.2.2.2.2
  have hb : cost s future k n-evalR s.U k ≤ evalR s.V n := by
    apply bound_along_rows 1 s.rows.tail (fun x => cost s future x n-evalR s.U x)
      (evalR s.V n)
    · intro r hmem
      have hh := row_all_counts s future hv hm r (by rw [hr]; exact hmem) n hn
      linarith
    · intro ab hmem x hx hA hB
      have hcell : Cell s ab := hcells ab (by rw [hr]; exact hmem)
      obtain ⟨a,b,ha,hb,hab,he⟩ := Erdos7FiniteHingeFunctions.interval_combination _ _ x hx
      rw [he, cost_on_cell s future ab.1 ab.2 hcell a b ha hb hab n,
        U_on_cell s ab.1 ab.2 hcell a b ha hb hab]
      have h₁ := mul_le_mul_of_nonneg_left hA ha
      have h₂ := mul_le_mul_of_nonneg_left hB hb
      have hh : (a+b)*evalR s.V n=evalR s.V n := by rw [hab, one_mul]
      nlinarith
    · simpa only [Rat.cast_one] using hk
    · rw [hlast]
      exact hkcut
  linarith

#print axioms live_dual
#print axioms row_all_counts
#print axioms evalR_convex
#print axioms evalR_tail
#print axioms mixture_cast
end Erdos7Capped19Real
