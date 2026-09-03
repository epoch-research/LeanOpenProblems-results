import Submission.RationalStripObstruction
import Submission.FiniteSieveReduction

/-! A uniform finite-sieve obstruction for finite-width rational strips.
The constants are independent of the location of the strip or the walk. -/
namespace Erdos952Investigation
namespace UniformRationalStrip

open RationalStrip FiniteSieveReduction
set_option maxHeartbeats 0

lemma periodic_scaled_sieve_patch {ι : Type*} [Fintype ι]
    (d : GaussianInt) (hd0 : d ≠ 0) (f : ι → GaussianInt) :
    ∃ P : ℕ, 0 < P ∧ ∀ b : GaussianInt,
      ∃ A : ℕ, A < P ∧ ∀ k : ℤ, ∀ i, ∀ z : GaussianInt,
        d * z = b + ((A : ℤ) + (P : ℤ)*k : ℤ) + f i → ¬ Allowed P z := by
  classical
  let B := d.norm.natAbs
  have hB : 0 < B := Int.natAbs_pos.mpr (GaussianInt.norm_pos.mpr hd0).ne'
  let e : ι → ℕ := fun i => (Fintype.equivFin ι i).val
  have he : Function.Injective e := Fin.val_injective.comp (Fintype.equivFin ι).injective
  let t : ι → ℕ := fun i => euclidT B (e i)
  let m : ι → ℕ := fun i => euclidM B (e i)
  have hm (i : ι) : (m i : ℤ) = (t i : ℤ)^2 + 1 := by
    simp [m, t, euclidM]
  have hmpos (i : ι) : 0 < m i := by dsimp [m, euclidM]; positivity
  have hmone (i : ι) : 1 < m i := by
    have ht := t_pos hB (e i)
    dsimp [m, euclidM]
    nlinarith
  have hmB (i : ι) : (m i).Coprime B := coprime_m_base B (e i)
  have hcop : ((Finset.univ : Finset ι) : Set ι).Pairwise (Function.onFun Nat.Coprime m) := by
    intro i _ j _ hij
    exact pairwise_coprime_m B (fun h => hij (he h))
  let P : ℕ := ∏ i, m i
  have hP : 0 < P := Finset.prod_pos fun i _ => hmpos i
  refine ⟨P, hP, ?_⟩
  intro b
  let r : ι → ℕ := fun i =>
    (((t i : ℤ) * (b.im + (f i).im) - (b.re + (f i).re)) % (m i : ℤ)).toNat
  let a := Nat.chineseRemainderOfFinset r m Finset.univ
    (fun i _ => (hmpos i).ne') hcop
  let A := a.val % P
  refine ⟨A, Nat.mod_lt _ hP, ?_⟩
  intro k i z hz hzallowed
  have hdP : m i ∣ P := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  have hmod : A ≡ r i [MOD m i] := by
    change (a.val % P) % m i = r i % m i
    rw [Nat.mod_mod_of_dvd _ hdP]
    exact a.property i (Finset.mem_univ i)
  have hr : (r i : ℤ) =
      ((t i : ℤ) * (b.im + (f i).im) - (b.re + (f i).re)) % m i := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast (hmpos i).ne'))
  have hmod' : (A : ℤ) ≡
      (t i : ℤ) * (b.im + (f i).im) - (b.re + (f i).re) [ZMOD m i] := by
    calc
      _ = (r i : ℤ) % m i := Int.natCast_modEq_iff.mpr hmod
      _ = _ := by rw [hr, Int.emod_emod]
  have hdiv : (m i : ℤ) ∣
      (b.re + ((A : ℤ) + (P : ℤ)*k) + (f i).re) -
        (t i : ℤ)*(b.im + (f i).im) := by
    have hbase := dvd_neg.mpr (Int.modEq_iff_dvd.mp hmod')
    have hper : (m i : ℤ) ∣ (P : ℤ)*k :=
      dvd_mul_of_dvd_left (by exact_mod_cast hdP) k
    convert dvd_add hbase hper using 1
    ring
  let g : GaussianInt := ⟨t i, 1⟩
  have hg : g.norm = (m i : ℤ) := by simp [g, gaussian_norm_sq, hm]
  have hgy : g ∣ d * z := by
    apply gaussian_linear_divisor
    rw [hz, ← hm]
    simpa using hdiv
  have hnormdiv : (m i : ℤ) ∣ d.norm * z.norm := by
    have hdv := map_dvd (Zsqrtd.normMonoidHom (d := -1)) hgy
    change g.norm ∣ (d * z).norm at hdv
    rwa [hg, Zsqrtd.norm_mul] at hdv
  have hnatdiv : m i ∣ B * z.norm.natAbs := by
    simpa only [Int.natAbs_natCast, Int.natAbs_mul, B] using
      (Int.natAbs_dvd_natAbs.mpr hnormdiv)
  have hmz : m i ∣ z.norm.natAbs := (hmB i).dvd_of_dvd_mul_left hnatdiv
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (ne_of_gt (hmone i))
  exact hzallowed p (Nat.le_of_dvd hP (hpm.trans hdP)) hp
    (Int.natCast_dvd.mpr (hpm.trans hmz))

lemma periodic_scaled_sieve_rectangle (d : GaussianInt) (hd : d ≠ 0)
    (B W : ℕ) :
    ∃ P : ℕ, 0 < P ∧ ∀ b : GaussianInt, ∃ A : ℕ, A < P ∧
      ∀ k : ℤ, ∀ z : GaussianInt,
        (A : ℤ) + P*k ≤ (d*z-b).re →
        (d*z-b).re ≤ (A : ℤ) + P*k + W →
        |(d*z-b).im| ≤ B → ¬ Allowed P z := by
  let f : Fin (W + 1) × Fin (2*B + 1) → GaussianInt :=
    fun i => ⟨i.1.val, (i.2.val : ℤ) - B⟩
  obtain ⟨P, hP, hpatch⟩ := periodic_scaled_sieve_patch d hd f
  refine ⟨P, hP, ?_⟩
  intro b
  obtain ⟨A, hA, hf⟩ := hpatch b
  refine ⟨A, hA, ?_⟩
  intro k z hrl hru hi
  let u : Fin (W+1) := ⟨((d*z-b).re - ((A : ℤ) + P*k)).toNat, by omega⟩
  let v : Fin (2*B+1) := ⟨((d*z-b).im + B).toNat, by have := abs_le.mp hi; omega⟩
  apply hf k (u,v) z
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_mul, Zsqrtd.im_mul,
    neg_mul, one_mul] at hrl hru hi
  have := abs_le.mp hi
  apply Zsqrtd.ext <;> simp [f, u, v] <;> omega

/-- A finite sieve bounds the diameter of every surviving finite walk in a
rational strip relative to its starting point. All translates use the same
sieve and diameter bound. -/
theorem uniform_sieve_strip_bound (d : GaussianInt) (hd : d ≠ 0)
    (C : ℤ) (B : ℕ) :
    ∃ P : ℕ, 0 < P ∧ ∃ R : ℤ, ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      (∀ n ≤ L, Allowed P (x n)) →
      (∀ n < L, (x (n+1)-x n).norm < C) →
      (∀ n ≤ L, |(d*(x n-x 0)).im| ≤ B) →
      ∀ n ≤ L, (x n-x 0).norm ≤ R := by
  let D := d.norm * max C 1
  have hdn : 0 < d.norm := GaussianInt.norm_pos.mpr hd
  have hD : 0 < D := mul_pos hdn (lt_of_lt_of_le (by norm_num) (le_max_right _ _))
  have hW : (D.toNat : ℤ) = D := Int.toNat_of_nonneg hD.le
  obtain ⟨P, hP, hrect⟩ := periodic_scaled_sieve_rectangle d hd B D.toNat
  refine ⟨P, hP, (2*(P : ℤ))^2 + (B : ℤ)^2, ?_⟩
  intro x L ha hs hstrip n hn
  let y : ℕ → GaussianInt := fun n => d*(x n-x 0)
  have hstep (j : ℕ) (hj : j < L) : |(y (j+1)).re-(y j).re| < D := by
    have he : y (j+1)-y j = d*(x (j+1)-x j) := by dsimp [y]; ring
    calc
      _ ≤ (y (j+1)-y j).norm := abs_re_le_gaussian_norm _
      _ = d.norm * (x (j+1)-x j).norm := by rw [he, Zsqrtd.norm_mul]
      _ < D := (mul_lt_mul_of_pos_left (hs j hj) hdn).trans_le
        (mul_le_mul_of_nonneg_left (le_max_left C 1) hdn.le)
  obtain ⟨A, hA, hfree⟩ := hrect (d*x 0)
  obtain ⟨A', hA', hfree'⟩ := hrect (-d*x 0)
  have hsame (j : ℕ) : d*x j - d*x 0 = y j := by dsimp [y]; ring
  have hneg (j : ℕ) : d*(-x j) - -d*x 0 = -(y j) := by dsimp [y]; ring
  have hbounds : ∀ j ≤ L,
      -((A' : ℤ)+P) < (y j).re ∧ (y j).re < (A : ℤ)+P := by
    intro j hj
    induction j with
    | zero => simp [y]; omega
    | succ j ih =>
      have hjL : j < L := by omega
      obtain ⟨hil, hiu⟩ := ih (by omega)
      have hdelta := abs_lt.mp (hstep j hjL)
      constructor
      · by_contra! hbad
        apply hfree' 1 (-x (j+1)) ?_ ?_ ?_ ?_
        · rw [hneg]; simp only [Zsqrtd.re_neg]; omega
        · rw [hneg, hW]; simp only [Zsqrtd.re_neg]; omega
        · rw [hneg]; simp only [Zsqrtd.im_neg, abs_neg]
          exact hstrip (j+1) hj
        · intro p hpP hp hdiv
          exact ha (j+1) hj p hpP hp (by simpa using hdiv)
      · by_contra! hbad
        apply hfree 1 (x (j+1)) ?_ ?_ ?_ (ha (j+1) hj)
        · rw [hsame]; omega
        · rw [hsame, hW]; omega
        · rw [hsame]; exact hstrip (j+1) hj
  obtain ⟨hl, hu⟩ := hbounds n hn
  have hre : |(y n).re| ≤ 2*(P : ℤ) := by
    apply abs_le.mpr
    constructor <;> omega
  have him : |(y n).im| ≤ B := hstrip n hn
  have hre2 : (y n).re^2 ≤ (2*(P : ℤ))^2 := sq_le_sq.mpr (by
    rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2*P)]; exact hre)
  have him2 : (y n).im^2 ≤ (B : ℤ)^2 := sq_le_sq.mpr (by
    rw [abs_of_nonneg (Int.natCast_nonneg _)]; exact him)
  have hynorm : (y n).norm ≤ (2*(P : ℤ))^2 + (B : ℤ)^2 := by
    rw [gaussian_norm_sq]; omega
  have hxy : (x n-x 0).norm ≤ (y n).norm := by
    dsimp [y]
    rw [Zsqrtd.norm_mul]
    have := GaussianInt.norm_nonneg (x n-x 0)
    nlinarith
  exact hxy.trans hynorm

/-- Uniform cardinality bound for finite prime paths in translated rational
strips, once the finitely many small-norm exceptions have been removed. -/
theorem uniform_large_prime_segment_bound (d : GaussianInt) (hd : d ≠ 0)
    (C : ℤ) (B : ℕ) :
    ∃ H : ℤ, ∃ K : ℕ, ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      Set.InjOn x (Set.Iic L) →
      (∀ n ≤ L, Prime (x n) ∧ H < (x n).norm) →
      (∀ n < L, (x (n+1)-x n).norm < C) →
      (∀ n ≤ L, |(d*(x n-x 0)).im| ≤ B) → L < K := by
  classical
  obtain ⟨P, hP, R, hR⟩ := uniform_sieve_strip_bound d hd C B
  let T := {z : GaussianInt | z.norm ≤ R}
  letI : Fintype T := (norm_sublevel_finite R).fintype
  refine ⟨(P : ℤ)^2, Fintype.card T, ?_⟩
  intro x L hx hp hs hstrip
  have ha (n : ℕ) (hn : n ≤ L) : Allowed P (x n) := by
    intro p hpP hpprime hdiv
    have hsmall := prime_norm_divisor_bound (hp n hn).1 hpprime hdiv
    have hpP' : (p : ℤ) ≤ P := by exact_mod_cast hpP
    have hp0 : (0 : ℤ) ≤ p := Int.natCast_nonneg p
    have hlarge := (hp n hn).2
    nlinarith
  let f : Fin (L+1) → T := fun i => ⟨x i.val-x 0, hR x L ha hs hstrip i.val (by omega)⟩
  have hfi : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply hx (by change i.val ≤ L; omega) (by change j.val ≤ L; omega)
    exact sub_left_injective (congrArg Subtype.val hij)
  have hcard := Fintype.card_le_of_injective f hfi
  simp only [Fintype.card_fin] at hcard
  omega

/-- Any hypothetical prime ray must leave each fixed-width rational strip
within a uniformly bounded number of steps, on every sufficiently late segment.
The bound depends on the width and direction, not on the segment's location. -/
theorem uniform_rational_transverse_escape (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C)
    (d : GaussianInt) (hd : d ≠ 0) (B : ℕ) :
    ∃ K N : ℕ, ∀ n ≥ N, ∃ i ≤ K, (B : ℤ) < |(d*(x (n+i)-x n)).im| := by
  obtain ⟨H, K, hK⟩ := uniform_large_prime_segment_bound d hd C B
  obtain ⟨N, hN⟩ := injective_escapes_norm x hx H
  refine ⟨K, N, ?_⟩
  intro n hn
  by_contra! hstrip
  have hbad := hK (fun i => x (n+i)) K
    (fun i _ j _ he => Nat.add_left_cancel (hx he))
    (fun i hi => ⟨(h (n+i)).1, hN (n+i) (by omega)⟩)
    (fun i hi => by simpa only [Nat.add_assoc] using (h (n+i)).2)
    (by simpa only [Nat.add_zero] using hstrip)
  omega

/-- There is a uniform bound on the length of *every* injective finite prime
walk contained in a translated rational strip. No lower bound on the norms is
required: injectivity bounds the total number of small-prime exceptions. -/
theorem uniform_prime_segment_bound (d : GaussianInt) (hd : d ≠ 0)
    (C : ℤ) (B : ℕ) :
    ∃ K : ℕ, ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      Set.InjOn x (Set.Iic L) →
      (∀ n ≤ L, Prime (x n)) →
      (∀ n < L, (x (n+1)-x n).norm < C) →
      (∀ n ≤ L, |(d*(x n-x 0)).im| ≤ B) → L < K := by
  classical
  obtain ⟨H, K, hK⟩ := uniform_large_prime_segment_bound d hd C (2*B)
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
        have he : d*(x (j.val*Q+i)-x (j.val*Q+0)) =
            d*(x (j.val*Q+i)-x 0) - d*(x (j.val*Q+0)-x 0) := by ring
        rw [he, Zsqrtd.im_sub]
        have ht := abs_add_le (d*(x (j.val*Q+i)-x 0)).im
          (-(d*(x (j.val*Q+0)-x 0)).im)
        simp only [abs_neg, ← sub_eq_add_neg] at ht
        push_cast
        omega
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

#print axioms periodic_scaled_sieve_patch
#print axioms uniform_prime_segment_bound
#print axioms uniform_large_prime_segment_bound
#print axioms uniform_rational_transverse_escape
#print axioms uniform_sieve_strip_bound

end UniformRationalStrip
end Erdos952Investigation
