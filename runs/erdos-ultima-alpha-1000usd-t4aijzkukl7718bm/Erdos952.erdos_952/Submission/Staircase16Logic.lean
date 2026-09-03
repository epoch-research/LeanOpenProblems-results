import Submission.Staircase16Data

/-! Soundness of the finite staircase certificate. The numerical row checks
are hypotheses here and are discharged by separate kernel computations. -/
namespace Erdos952Investigation.Staircase16
set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma height_antitone (hRows : ∀ r : Fin (radius+1), RowCheck r) : Antitone height := by
  apply antitone_nat_of_succ_le
  intro n
  by_cases hn : n ≤ radius
  · exact (hRows ⟨n,by omega⟩).1
  · simp only [height,if_neg hn,if_neg (show ¬ n+1 ≤ radius by omega),le_refl]

lemma inside_octant_bound {z : GaussianInt} (hz : InsideOctant z) :
    0 ≤ z.re ∧ z.re ≤ (radius : ℤ) ∧ 0 ≤ z.im ∧ z.im ≤ (radius : ℤ) := by
  have hr0 : 0 ≤ z.re := hz.1.trans hz.2.1
  have hr1 : z.re ≤ (radius : ℤ) := by
    by_contra! hr
    have hnat : ¬ z.re.toNat ≤ radius := by omega
    have hh := hz.2.2
    rw [height,if_neg hnat] at hh
    have hi := hz.1
    omega
  exact ⟨hr0,hr1,hz.1,hz.2.1.trans hr1⟩

lemma inside_coordinate_bound {z : GaussianInt} (hz : Inside z) :
    -(radius : ℤ) ≤ z.re ∧ z.re ≤ radius ∧ -(radius : ℤ) ≤ z.im ∧ z.im ≤ radius := by
  have hh : max |z.re| |z.im| ≤ (radius : ℤ) := (inside_octant_bound hz).2.1
  have hr := abs_le.mp ((le_max_left _ _).trans hh)
  have hi := abs_le.mp ((le_max_right _ _).trans hh)
  exact ⟨hr.1,hr.2,hi.1,hi.2⟩

lemma inside_finite : {z | Inside z}.Finite := by
  apply (norm_sublevel_finite (2*(radius : ℤ)^2)).subset
  intro z hz
  obtain ⟨hr0,hr1,hi0,hi1⟩ := inside_coordinate_bound hz
  have hr : z.re^2 ≤ (radius : ℤ)^2 := sq_le_sq.mpr (by
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    exact abs_le.mpr ⟨hr0,hr1⟩)
  have hi : z.im^2 ≤ (radius : ℤ)^2 := sq_le_sq.mpr (by
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    exact abs_le.mpr ⟨hi0,hi1⟩)
  simp only [Set.mem_setOf_eq,gaussian_norm_sq]
  omega

lemma three_inside : Inside (3 : GaussianInt) := by decide +kernel

lemma inside_octant_closed (hRows : ∀ r : Fin (radius+1), RowCheck r) {z w : GaussianInt} (hz : InsideOctant z)
    (hzP : Prime z) (hwP : Prime w) (hd : (w-z).norm < 16)
    (hwO : OctantReduction.InOctant w) : InsideOctant w := by
  by_cases hwin : InsideOctant w
  · exact hwin
  have hwout : height w.re.toNat < w.im := by
    exact lt_of_not_ge (fun hh => hwin ⟨hwO.1,hwO.2,hh⟩)
  have hwre : 0 ≤ w.re := hwO.1.trans hwO.2
  obtain ⟨hzre0,hzre1,hzim0,hzim1⟩ := inside_octant_bound hz
  have hd' : (w.re-z.re)^2+(w.im-z.im)^2 < 16 := by
    simpa only [gaussian_norm_sq,Zsqrtd.re_sub,Zsqrtd.im_sub] using hd
  have hdr : -3 ≤ w.re-z.re ∧ w.re-z.re ≤ 3 := by
    constructor <;> nlinarith [sq_nonneg (w.im-z.im)]
  have hdi : -3 ≤ w.im-z.im ∧ w.im-z.im ≤ 3 := by
    constructor <;> nlinarith [sq_nonneg (w.re-z.re)]
  let r : Fin (radius+1) := ⟨z.re.toNat,by omega⟩
  have hr : (r.val : ℤ) = z.re := by dsimp [r]; omega
  have hwsmall : w.re.toNat ≤ r.val+3 := by omega
  have hheight := height_antitone hRows hwsmall
  have hlower : lower r.val ≤ z.im := by dsimp [lower]; omega
  have hupper : z.im ≤ height r.val := hz.2.2
  let s : Fin (width r.val) := ⟨(z.im-lower r.val).toNat,by dsimp [width]; omega⟩
  have hs : lower r.val+(s.val : ℤ) = z.im := by dsimp [s]; omega
  let a : Fin 7 := ⟨(w.re-z.re+3).toNat,by omega⟩
  let b : Fin 7 := ⟨(w.im-z.im+3).toNat,by omega⟩
  have ha : (a.val : ℤ)-3 = w.re-z.re := by dsimp [a]; omega
  have hb : (b.val : ℤ)-3 = w.im-z.im := by dsimp [b]; omega
  have hrow := (hRows r).2 s
  dsimp only at hrow
  rw [hr,hs] at hrow
  have hstep := hrow hz a b
  rw [ha,hb] at hstep
  have heq : (⟨z.re+(w.re-z.re),z.im+(w.im-z.im)⟩ : GaussianInt) = w := by
    ext <;> simp
  have hh : InsideOctant w ∨ Blocked z ∨ Blocked w := by
    simpa only [heq] using hstep hd' (by simpa only [heq] using hwO)
  exact ((hh.resolve_left hwin).elim (prime_not_blocked hzP) (prime_not_blocked hwP)).elim

lemma inside_closed (hRows : ∀ r : Fin (radius+1), RowCheck r) {z w : GaussianInt} (hz : Inside z)
    (hzP : Prime z) (hwP : Prime w) (hd : (w-z).norm < 16) : Inside w :=
  inside_octant_closed hRows hz (OctantReduction.prime_fold hzP)
    (OctantReduction.prime_fold hwP)
    (lt_of_le_of_lt (OctantReduction.fold_contract _ _) hd)
    (OctantReduction.fold_in_octant _)

/-- Any successful row data constitute a genuine finite moat around 3. -/
theorem certificate_of_rows (hRows : ∀ r : Fin (radius+1), RowCheck r) : ∃ S : Finset GaussianInt, MoatCertificate 16 S := by
  classical
  refine ⟨inside_finite.toFinset,?_,?_⟩
  · simpa only [Set.Finite.mem_toFinset,Set.mem_setOf_eq] using three_inside
  · intro z hz w hw
    simp only [Set.Finite.mem_toFinset,Set.mem_setOf_eq] at hz ⊢
    exact inside_closed hRows hz hw.1 hw.2.1 hw.2.2.2

theorem component_finite_of_rows (hRows : ∀ r : Fin (radius+1), RowCheck r) :
    {w | (primeGraph 16).Reachable (3 : GaussianInt) w}.Finite :=
  (fixed_component_finite_iff_certificate 16).mpr (certificate_of_rows hRows)

theorem step_bound_gt_sixteen_of_rows (hRows : ∀ r : Fin (radius+1), RowCheck r) (x : ℕ → GaussianInt) (C : ℤ)
    (hx0 : x 0 = 3) (hx : Function.Injective x)
    (hp : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) : 16 < C := by
  by_contra! hC
  have hin (n : ℕ) : Inside (x n) := by
    induction n with
    | zero => simpa only [hx0] using three_inside
    | succ n ih =>
      exact inside_closed hRows ih (hp n).1 (hp (n+1)).1 ((hp n).2.trans_le hC)
  exact (Set.infinite_range_of_injective hx)
    (inside_finite.subset (by rintro z ⟨n,rfl⟩; exact hin n))

/-- An explicit bound for finite prime paths from 3. The bound comes from
an enclosing square, not a claim about the exact component cardinality. -/
theorem finite_path_length_bound_of_rows (hRows : ∀ r : Fin (radius+1), RowCheck r)
    (x : ℕ → GaussianInt) (L : ℕ) (hx0 : x 0 = 3)
    (hx : Set.InjOn x (Set.Iic L)) (hp : ∀ n ≤ L, Prime (x n))
    (hs : ∀ n < L, (x (n+1)-x n).norm < 16) : L < (2*radius+1)^2 := by
  have hin (n : ℕ) (hn : n ≤ L) : Inside (x n) := by
    induction n with
    | zero => simpa only [hx0] using three_inside
    | succ n ih =>
      exact inside_closed hRows (ih (by omega)) (hp n (by omega)) (hp (n+1) hn)
        (hs n (by omega))
  let f : Fin (L+1) → Fin (2*radius+1) × Fin (2*radius+1) := fun i =>
    (⟨((x i.val).re+(radius : ℤ)).toNat,by
      have hh := inside_coordinate_bound (hin i.val (by omega)); omega⟩,
     ⟨((x i.val).im+(radius : ℤ)).toNat,by
      have hh := inside_coordinate_bound (hin i.val (by omega)); omega⟩)
  have hfi : Function.Injective f := by
    intro i j hij
    have hri := inside_coordinate_bound (hin i.val (by omega))
    have hrj := inside_coordinate_bound (hin j.val (by omega))
    have hr := congrArg (fun t => t.1.val) hij
    have hi := congrArg (fun t => t.2.val) hij
    dsimp [f] at hr hi
    apply Fin.ext
    apply hx (by change i.val ≤ L; omega) (by change j.val ≤ L; omega)
    apply Zsqrtd.ext <;> omega
  have hh := Fintype.card_le_of_injective f hfi
  simp only [Fintype.card_fin,Fintype.card_prod] at hh
  nlinarith

#print axioms finite_path_length_bound_of_rows

#print axioms certificate_of_rows
#print axioms step_bound_gt_sixteen_of_rows
end Erdos952Investigation.Staircase16
