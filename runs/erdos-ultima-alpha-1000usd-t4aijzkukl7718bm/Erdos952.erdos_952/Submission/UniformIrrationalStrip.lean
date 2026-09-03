import Submission.PeriodicCompositePatches
import Submission.OneSidedIrrationalApproximation
import Submission.UniformRationalStrip

/-! Uniform bounds for finite prime paths in translated irrational strips.
The location of the strip is arbitrary; its slope and width are fixed. -/
namespace Erdos952Investigation
namespace UniformIrrationalStrip

set_option maxHeartbeats 0

lemma uniform_irrational_crosscut {α : ℝ} (hα : Irrational α) (B : ℝ) (W : ℕ) :
    ∃ H D : ℤ, 0 < D ∧ ∀ w : GaussianInt,
      ∃ A : ℤ, 0 < A ∧ A ≤ D ∧ ∀ z : GaussianInt,
        H < z.norm → |(z-w).re-A| ≤ W →
        |((z-w).im : ℝ)-α*((z-w).re : ℝ)| ≤ B → ¬ Prime z := by
  classical
  obtain ⟨V,hV⟩ := exists_nat_gt (B+|α| *(W : ℝ)+1)
  obtain ⟨a,P,hP,hpatch⟩ := PeriodicCompositePatches.periodic_rectangle W V
  letI : NeZero P := ⟨hP.ne'⟩
  let R := ZMod P × ZMod P
  have hcenter (r : R) : ∃ k l : ℤ,
      0 < (a : ℤ)-(r.1.val : ℤ)+(P : ℤ)*k ∧
      |α*(((a : ℤ)-(r.1.val : ℤ)+(P : ℤ)*k : ℤ) : ℝ)-
        (((P : ℤ)*l : ℤ) : ℝ)-(-(r.2.val : ℝ))| < 1 :=
    IrrationalLatticeApproximation.arbitrarily_large_affine_grid_center hα
      ((a : ℤ)-(r.1.val : ℤ)) P 0 (-(r.2.val : ℝ)) (by exact_mod_cast hP)
  choose k l hk hl using hcenter
  let u : R → ℤ := fun r => (a : ℤ)-(r.1.val : ℤ)+(P : ℤ)*k r
  let v : R → ℤ := fun r => (P : ℤ)*l r-(r.2.val : ℤ)
  have hu (r : R) : 0 < u r := hk r
  have hnear (r : R) : |α*(u r : ℝ)-(v r : ℝ)| < 1 := by
    convert hl r using 1
    congr 1
    dsimp [u,v]
    push_cast
    ring
  let D : ℤ := ((Finset.univ.sup (fun r : R => (u r).natAbs) : ℕ) : ℤ)+1
  have huD (r : R) : u r ≤ D := by
    have hsup : (u r).natAbs ≤ Finset.univ.sup (fun r : R => (u r).natAbs) :=
      Finset.le_sup (f := fun r : R => (u r).natAbs) (Finset.mem_univ r)
    have hsup' : ((u r).natAbs : ℤ) ≤
        ((Finset.univ.sup (fun r : R => (u r).natAbs) : ℕ) : ℤ) := by exact_mod_cast hsup
    have hle : u r ≤ ((u r).natAbs : ℤ) := Int.le_natAbs
    dsimp [D]
    omega
  refine ⟨P,D,by dsimp [D]; positivity,?_⟩
  intro w
  let r : R := ((w.re : ZMod P),(w.im : ZMod P))
  have hwr : (P : ℤ) ∣ w.re-(r.1.val : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ P).mp
    simp [r]
  have hwi : (P : ℤ) ∣ w.im-(r.2.val : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ P).mp
    simp [r]
  obtain ⟨wr,hwr⟩ := hwr
  obtain ⟨wi,hwi⟩ := hwi
  refine ⟨u r,hu r,huD r,?_⟩
  intro z hn hr hs
  have hrreal : |((z-w).re : ℝ)-(u r : ℝ)| ≤ W := by exact_mod_cast hr
  have hcalc : |((z-w).im : ℝ)-(v r : ℝ)| < V := by
    have he : ((z-w).im : ℝ)-(v r : ℝ) =
        (((z-w).im : ℝ)-α*((z-w).re : ℝ)) +
        α*(((z-w).re : ℝ)-(u r : ℝ)) + (α*(u r : ℝ)-(v r : ℝ)) := by ring
    rw [he]
    have ht := abs_add_le (((z-w).im : ℝ)-α*((z-w).re : ℝ))
      (α*(((z-w).re : ℝ)-(u r : ℝ)))
    have ht' := abs_add_le ((((z-w).im : ℝ)-α*((z-w).re : ℝ)) +
      α*(((z-w).re : ℝ)-(u r : ℝ))) (α*(u r : ℝ)-(v r : ℝ))
    have hm : |α*(((z-w).re : ℝ)-(u r : ℝ))| ≤ |α| *(W : ℝ) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hrreal (abs_nonneg α)
    have hh := hnear r
    linarith
  have hi : |(z-w).im-v r| ≤ V := by exact_mod_cast hcalc.le
  have hre : z.re-((a : ℤ)+(P : ℤ)*(wr+k r)) = (z-w).re-u r := by
    dsimp [u]
    linear_combination hwr
  have him : z.im-(P : ℤ)*(wi+l r) = (z-w).im-v r := by
    dsimp [v]
    linear_combination hwi
  exact hpatch (wr+k r) (wi+l r) z (by rw [hre]; exact hr) (by rw [him]; exact hi) hn

theorem uniform_large_prime_strip_bound {α : ℝ} (hα : Irrational α)
    (C : ℤ) (B : ℝ) :
    ∃ H R : ℤ, ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      (∀ n ≤ L, Prime (x n) ∧ H < (x n).norm) →
      (∀ n < L, (x (n+1)-x n).norm < C) →
      (∀ n ≤ L, |((x n-x 0).im : ℝ)-α*((x n-x 0).re : ℝ)| ≤ B) →
      ∀ n ≤ L, (x n-x 0).norm ≤ R := by
  let E : ℤ := max C 1
  have hE : 0 < E := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hW : (E.toNat : ℤ) = E := Int.toNat_of_nonneg hE.le
  obtain ⟨H,D,hD,hcut⟩ := uniform_irrational_crosscut hα B E.toNat
  obtain ⟨V,hV⟩ := exists_nat_gt (B+|α| *(D : ℝ))
  refine ⟨H,D^2+(V : ℤ)^2,?_⟩
  intro x L hp hs hstrip n hn
  let y : ℕ → GaussianInt := fun j => x j-x 0
  obtain ⟨A,hA,hAD,hfree⟩ := hcut (x 0)
  obtain ⟨A',hA',hAD',hfree'⟩ := hcut (-x 0)
  have hstep (j : ℕ) (hj : j < L) : |(y (j+1)).re-(y j).re| < E := by
    have he : y (j+1)-y j = x (j+1)-x j := by dsimp [y]; abel
    calc
      _ ≤ (y (j+1)-y j).norm := abs_re_le_gaussian_norm _
      _ = (x (j+1)-x j).norm := congrArg Zsqrtd.norm he
      _ < E := (hs j hj).trans_le (le_max_left _ _)
  have hneg (j : ℕ) : -x j- -x 0 = -(y j) := by dsimp [y]; abel
  have hbounds : ∀ j ≤ L, -A' < (y j).re ∧ (y j).re < A := by
    intro j hj
    induction j with
    | zero => simp [y,hA,hA']
    | succ j ih =>
      have hjL : j < L := by omega
      obtain ⟨hil,hiu⟩ := ih (by omega)
      have hdelta := abs_lt.mp (hstep j hjL)
      constructor
      · by_contra! hbad
        apply hfree' (-x (j+1)) (by simpa using (hp (j+1) hj).2) ?_ ?_
          (hp (j+1) hj).1.neg
        · rw [hneg,hW]
          simp only [Zsqrtd.re_neg]
          apply abs_le.mpr
          omega
        · rw [hneg]
          have he : (((-(y (j+1))).im : ℤ) : ℝ)-α*(((-(y (j+1))).re : ℤ) : ℝ) =
              -(((y (j+1)).im : ℝ)-α*((y (j+1)).re : ℝ)) := by simp; ring
          rw [he,abs_neg]
          exact hstrip (j+1) hj
      · by_contra! hbad
        apply hfree (x (j+1)) (hp (j+1) hj).2 ?_ (hstrip (j+1) hj) (hp (j+1) hj).1
        rw [hW]
        change |(y (j+1)).re-A| ≤ E
        apply abs_le.mpr
        omega
  obtain ⟨hl,hu⟩ := hbounds n hn
  have hr : |(y n).re| ≤ D := abs_le.mpr ⟨by omega,by omega⟩
  have hrreal : |((y n).re : ℝ)| ≤ (D : ℝ) := by exact_mod_cast hr
  have hi : |(y n).im| ≤ (V : ℤ) := by
    have ht := abs_add_le (((y n).im : ℝ)-α*((y n).re : ℝ)) (α*((y n).re : ℝ))
    rw [sub_add_cancel] at ht
    have hm : |α*((y n).re : ℝ)| ≤ |α| *(D : ℝ) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hrreal (abs_nonneg α)
    have hh := hstrip n hn
    change |((y n).im : ℝ)-α*((y n).re : ℝ)| ≤ B at hh
    have hib : |((y n).im : ℝ)| ≤ (V : ℝ) := by linarith
    exact_mod_cast hib
  have hr2 : (y n).re^2 ≤ D^2 := sq_le_sq.mpr (by rw [abs_of_pos hD]; exact hr)
  have hi2 : (y n).im^2 ≤ (V : ℤ)^2 := sq_le_sq.mpr (by
    rw [abs_of_nonneg (Int.natCast_nonneg V)]; exact hi)
  change (y n).norm ≤ _
  rw [gaussian_norm_sq]
  omega

/-- Uniform finite length bound outside a fixed finite norm ball. -/
theorem uniform_large_prime_segment_bound {α : ℝ} (hα : Irrational α)
    (C : ℤ) (B : ℝ) :
    ∃ H : ℤ, ∃ K : ℕ, ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      Set.InjOn x (Set.Iic L) →
      (∀ n ≤ L, Prime (x n) ∧ H < (x n).norm) →
      (∀ n < L, (x (n+1)-x n).norm < C) →
      (∀ n ≤ L, |((x n-x 0).im : ℝ)-α*((x n-x 0).re : ℝ)| ≤ B) → L < K := by
  classical
  obtain ⟨H,R,hR⟩ := uniform_large_prime_strip_bound hα C B
  let T := {z : GaussianInt | z.norm ≤ R}
  letI : Fintype T := (norm_sublevel_finite R).fintype
  refine ⟨H,Fintype.card T,?_⟩
  intro x L hx hp hs hstrip
  let f : Fin (L+1) → T := fun i => ⟨x i.val-x 0, hR x L hp hs hstrip i.val (by omega)⟩
  have hfi : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply hx (by change i.val ≤ L; omega) (by change j.val ≤ L; omega)
    exact sub_left_injective (congrArg Subtype.val hij)
  have hcard := Fintype.card_le_of_injective f hfi
  simp only [Fintype.card_fin] at hcard
  omega

/-- There is a uniform bound on the length of *every* injective finite prime
walk contained in a translated irrational strip. No lower bound on the norms is
required: injectivity bounds the total number of small-prime exceptions. -/
theorem uniform_prime_segment_bound {α : ℝ} (hα : Irrational α)
    (C : ℤ) (B : ℝ) :
    ∃ K : ℕ, ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      Set.InjOn x (Set.Iic L) →
      (∀ n ≤ L, Prime (x n)) →
      (∀ n < L, (x (n+1)-x n).norm < C) →
      (∀ n ≤ L, |((x n-x 0).im : ℝ)-α*((x n-x 0).re : ℝ)| ≤ B) → L < K := by
  classical
  obtain ⟨H, K, hK⟩ := uniform_large_prime_segment_bound hα C (2*B)
  let T := {z : GaussianInt | z.norm ≤ H}
  letI : Fintype T := (norm_sublevel_finite H).fintype
  let M := Fintype.card T
  let Q := K+1
  refine ⟨(M+1)*Q, ?_⟩
  intro x L hx hp hs hstrip
  by_contra! hlong
  have hindex (j : Fin (M+1)) (i : ℕ) (hi : i ≤ K) : j.val*Q+i < L := by
    have hm := Nat.mul_le_mul_right Q (show j.val+1 ≤ M+1 by omega)
    dsimp [Q] at hm ⊢ hlong
    nlinarith
  have hsmall (j : Fin (M+1)) : ∃ i ≤ K, (x (j.val*Q+i)).norm ≤ H := by
    by_contra! hn
    have hbad : K < K := by
      apply hK (fun i => x (j.val*Q+i)) K
      · intro i hi l hl he
        change i ≤ K at hi
        change l ≤ K at hl
        exact Nat.add_left_cancel
          (hx (hindex j i hi).le (hindex j l hl).le he)
      · intro i hi
        exact ⟨hp _ (hindex j i hi).le, hn i hi⟩
      · intro i hi
        simpa only [Nat.add_assoc] using hs _ (hindex j i hi.le)
      · intro i hi
        have hr := hstrip _ (hindex j i hi).le
        have hl := hstrip _ (hindex j 0 (Nat.zero_le _)).le
        let proj : GaussianInt → ℝ := fun z => (z.im : ℝ)-α*(z.re : ℝ)
        have he : proj (x (j.val*Q+i)-x (j.val*Q+0)) =
            proj (x (j.val*Q+i)-x 0)-proj (x (j.val*Q+0)-x 0) := by
          simp only [proj,Zsqrtd.re_sub,Zsqrtd.im_sub,Int.cast_sub]
          ring
        change |proj (x (j.val*Q+i)-x (j.val*Q+0))| ≤ 2*B
        rw [he]
        have ht := abs_add_le (proj (x (j.val*Q+i)-x 0))
          (-proj (x (j.val*Q+0)-x 0))
        simp only [abs_neg, ← sub_eq_add_neg] at ht
        change |proj (x (j.val*Q+i)-x 0)| ≤ B at hr
        change |proj (x (j.val*Q+0)-x 0)| ≤ B at hl
        linarith
    omega
  choose i hi hnorm using hsmall
  let f : Fin (M+1) → T := fun j => ⟨x (j.val*Q+i j), hnorm j⟩
  have hfi : Function.Injective f := by
    intro j k he
    have hpos := hx (hindex j (i j) (hi j)).le (hindex k (i k) (hi k)).le
      (congrArg Subtype.val he)
    have hdiv (l : Fin (M+1)) : (l.val*Q+i l)/Q = l.val := by
      rw [Nat.mul_comm l.val Q, Nat.mul_add_div (by dsimp [Q]; omega),
        Nat.div_eq_of_lt (by have := hi l; dsimp [Q]; omega), Nat.add_zero]
    apply Fin.ext
    rw [← hdiv j, ← hdiv k, hpos]
  have hcard := Fintype.card_le_of_injective f hfi
  simp only [Fintype.card_fin] at hcard
  change M+1 ≤ M at hcard
  omega

#print axioms uniform_prime_segment_bound
#print axioms uniform_irrational_crosscut
#print axioms uniform_large_prime_strip_bound
#print axioms uniform_large_prime_segment_bound

end UniformIrrationalStrip
end Erdos952Investigation
