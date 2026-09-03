import Submission.BinaryNormBound

/-! Subpolynomial bounds for quartic representations on a Pythagorean-relation
locus. These bounds do not cover arbitrary representations. -/
namespace Erdos322Research.QuarticPythagorean

private def reps (n : ℕ) : Finset (Fin 4 → Fin (n+1)) :=
  Finset.univ.filter (fun a ↦ (∑ i, (a i : ℕ)^4 = n) ∧
    ((a 0 : ℕ)+(a 1 : ℕ))^2 = (a 2 : ℕ)^2+(a 3 : ℕ)^2)

/-- Count with the displayed ordering of the Pythagorean relation. -/
def fixedCount (n : ℕ) : ℕ := (reps n).card

private def normPair {n : ℕ} (a : Fin 4 → Fin (n+1)) : ℕ :=
  (a 0 : ℕ)^2+(a 0 : ℕ)*(a 1 : ℕ)+(a 1 : ℕ)^2

private def lowFactor {n : ℕ} (a : Fin 4 → Fin (n+1)) : ℕ :=
  normPair a-(a 2 : ℕ)*(a 3 : ℕ)

private def highFactor {n : ℕ} (a : Fin 4 → Fin (n+1)) : ℕ :=
  normPair a+(a 2 : ℕ)*(a 3 : ℕ)

private lemma product_le_norm {n : ℕ} {a : Fin 4 → Fin (n+1)} (ha : a ∈ reps n) :
    (a 2 : ℕ)*(a 3 : ℕ) ≤ normPair a := by
  have hp := (Finset.mem_filter.mp ha).2.2
  dsimp [normPair]
  nlinarith [two_mul_le_add_sq (a 2 : ℕ) (a 3 : ℕ)]

/-- Exact factorization of the represented target on this locus. -/
private theorem factorization {n : ℕ} {a : Fin 4 → Fin (n+1)} (ha : a ∈ reps n) :
    n=2*lowFactor a*highFactor a := by
  have hp := (Finset.mem_filter.mp ha).2.2
  have hs := (Finset.mem_filter.mp ha).2.1
  simp only [Fin.sum_univ_four] at hs
  have hle := product_le_norm ha
  dsimp only [lowFactor, highFactor]
  zify [hle] at hp hs ⊢
  dsimp only [normPair] at *
  have he := congrArg (fun z : ℤ ↦ z^2) hp
  push_cast at he ⊢
  nlinarith [he]

private lemma low_pos {n : ℕ} (hn : 0 < n) {a : Fin 4 → Fin (n+1)}
    (ha : a ∈ reps n) : 0 < lowFactor a := by
  have he := factorization ha
  by_contra hh
  have hz : lowFactor a=0 := by omega
  simp [hz] at he
  omega

private lemma norm_le_target {n : ℕ} (hn : 0 < n) {a : Fin 4 → Fin (n+1)}
    (ha : a ∈ reps n) : normPair a ≤ n := by
  have hd : highFactor a ∣ n := by
    exact ⟨2*lowFactor a, (factorization ha).trans (by ring)⟩
  exact (by dsimp [highFactor]; omega : normPair a ≤ highFactor a).trans
    (Nat.le_of_dvd hn hd)

private lemma low_mem_divisors {n : ℕ} (hn : 0 < n) {a : Fin 4 → Fin (n+1)}
    (ha : a ∈ reps n) : lowFactor a ∈ n.divisors := by
  apply Nat.mem_divisors.mpr
  refine ⟨?_,hn.ne'⟩
  exact ⟨2*highFactor a, (factorization ha).trans (by ring)⟩

private def recoveredNorm (n u : ℕ) : ℕ := (u+n/(2*u))/2

private lemma recoveredNorm_eq {n : ℕ} (hn : 0 < n)
    {a : Fin 4 → Fin (n+1)} (ha : a ∈ reps n) :
    recoveredNorm n (lowFactor a)=normPair a := by
  have hu := low_pos hn ha
  have hv : n/(2*lowFactor a)=highFactor a := by
    exact Nat.div_eq_of_eq_mul_left (by omega) ((factorization ha).trans (by ring))
  have he : lowFactor a+highFactor a=2*normPair a := by
    have hle := product_le_norm ha
    dsimp [lowFactor,highFactor]
    omega
  dsimp only [recoveredNorm]
  rw [hv,he]
  omega

private def innerTag {n : ℕ} (a : Fin 4 → Fin (n+1)) : (ℕ × ℕ) × Bool :=
  ((2*(a 0 : ℕ)+(a 1 : ℕ),(a 1 : ℕ)),decide ((a 2 : ℕ)≤(a 3 : ℕ)))

private lemma pair_unique (a b c d : ℕ) (hs : a^2+b^2=c^2+d^2)
    (hp : a*b=c*d) (ho : decide (a≤b)=decide (c≤d)) : a=c ∧ b=d := by
  have hsum : a+b=c+d := Nat.pow_left_injective (by decide : 2 ≠ 0)
    (by nlinarith : (a+b)^2=(c+d)^2)
  have hf : ((a : ℤ)-c)*((a : ℤ)-d)=0 := by
    zify at hp hsum
    nlinarith [hp]
  rcases mul_eq_zero.mp hf with h | h
  · have ha : a=c := by omega
    exact ⟨ha,by omega⟩
  · have ha : a=d := by omega
    have hb : b=c := by omega
    have he : a=b := by
      subst c; subst d
      by_cases hab : a≤b
      · have hh : b≤a := by simpa [hab] using ho.symm
        omega
      · have hh : ¬ b≤a := by simpa [hab] using ho.symm
        omega
    omega

private lemma innerTag_fiber_injective (n u : ℕ) (_hn : 0 < n) :
    Set.InjOn innerTag ((reps n).filter (fun a ↦ lowFactor a=u) :
      Set (Fin 4 → Fin (n+1))) := by
  intro a ha b hb he
  obtain ⟨ha,hau⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb,hbu⟩ := Finset.mem_filter.mp hb
  have h0 := congrArg (fun z : (ℕ × ℕ) × Bool ↦ z.1.1) he
  have h1 := congrArg (fun z : (ℕ × ℕ) × Bool ↦ z.1.2) he
  have ho := congrArg (fun z : (ℕ × ℕ) × Bool ↦ z.2) he
  dsimp only [innerTag] at h0 h1 ho
  have ha0 : (a 0 : ℕ)=(b 0 : ℕ) := by omega
  have hnorm : normPair a=normPair b := by simp [normPair,ha0,h1]
  have hla : lowFactor a=lowFactor b := hau.trans hbu.symm
  have hprod : (a 2 : ℕ)*(a 3 : ℕ)=(b 2 : ℕ)*(b 3 : ℕ) := by
    have hleA := product_le_norm ha
    have hleB := product_le_norm hb
    dsimp only [lowFactor] at hla
    omega
  have hsA := (Finset.mem_filter.mp ha).2.2
  have hsB := (Finset.mem_filter.mp hb).2.2
  have hs : (a 2 : ℕ)^2+(a 3 : ℕ)^2=(b 2 : ℕ)^2+(b 3 : ℕ)^2 := by
    rw [←hsA,←hsB,ha0,h1]
  obtain ⟨h2,h3⟩ := pair_unique _ _ _ _ hs hprod ho
  funext i
  apply Fin.ext
  fin_cases i <;> assumption

private lemma fiber_card_le (n u : ℕ) (hn : 0 < n) :
    ((reps n).filter (fun a ↦ lowFactor a=u)).card ≤
      2*(binaryNormSolutions 3 (4*recoveredNorm n u)).card := by
  classical
  have hc := Finset.card_le_card_of_injOn innerTag
    (s := (reps n).filter (fun a ↦ lowFactor a=u))
    (t := binaryNormSolutions 3 (4*recoveredNorm n u) ×ˢ (Finset.univ : Finset Bool))
    (by
      intro a ha
      obtain ⟨ha,hu⟩ := Finset.mem_filter.mp ha
      apply Finset.mem_product.mpr
      refine ⟨?_,Finset.mem_univ _⟩
      have he := recoveredNorm_eq hn ha
      rw [hu] at he
      rw [he]
      apply (mem_binaryNormSolutions (by decide) _).mpr
      dsimp [innerTag,normPair]
      ring)
    (innerTag_fiber_injective n u hn)
  simpa [Finset.card_product,mul_comm] using hc

/-- Uniform subpolynomial bound on the fixed-order Pythagorean locus. -/
theorem fixed_count_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n → (fixedCount n : ℝ) ≤ C*(n : ℝ)^ε := by
  classical
  have hδ : 0 < ε/2 := by linarith
  obtain ⟨A,hA,hdiv⟩ := divisor_count_subpolynomial (ε/2) hδ
  obtain ⟨B,hB,hnorm⟩ := binary_norm_subpolynomial_up_to (by decide : 2 ≤ 3) (ε/2) hδ
  refine ⟨2*A*B*(5:ℝ)^(ε/2),by positivity,fun n hn ↦ ?_⟩
  let I := (reps n).image lowFactor
  have hnr : (0:ℝ)<n := by exact_mod_cast hn
  have himage : (I.card : ℝ) ≤ A*(n:ℝ)^(ε/2) := by
    have hi : I ⊆ n.divisors := by
      intro u hu
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
      exact low_mem_divisors hn ha
    have hc : (I.card : ℝ) ≤ n.divisors.card := by
      exact_mod_cast Finset.card_le_card hi
    exact hc.trans (hdiv n hn)
  have hfiber (u : ℕ) (hu : u ∈ I) :
      (((reps n).filter (fun a ↦ lowFactor a=u)).card : ℝ) ≤
        2*B*(4*n+1:ℝ)^(ε/2) := by
    have hq : recoveredNorm n u ≤ n := by
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
      rw [recoveredNorm_eq hn ha]
      exact norm_le_target hn ha
    have hcard : (((reps n).filter (fun a ↦ lowFactor a=u)).card : ℝ) ≤
        2*(binaryNormSolutions 3 (4*recoveredNorm n u)).card := by
      exact_mod_cast fiber_card_le n u hn
    have hb := hnorm (4*n) (4*recoveredNorm n u) (by omega)
    push_cast at hb
    exact hcard.trans (by nlinarith [hb])
  have hpow : (4*n+1:ℝ)^(ε/2) ≤ (5:ℝ)^(ε/2)*(n:ℝ)^(ε/2) := by
    rw [← Real.mul_rpow (by norm_num : (0:ℝ)≤5) hnr.le]
    apply Real.rpow_le_rpow (by positivity) _ hδ.le
    have h1 : (1:ℝ)≤n := by exact_mod_cast hn
    linarith
  have hp : (n:ℝ)^(ε/2)*(n:ℝ)^(ε/2)=(n:ℝ)^ε := by
    rw [←Real.rpow_add hnr]
    congr 1
    ring
  calc
    (fixedCount n : ℝ) =
        ∑ u ∈ I, (((reps n).filter (fun a ↦ lowFactor a=u)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image lowFactor (reps n)
    _ ≤ ∑ _u ∈ I, 2*B*(4*n+1:ℝ)^(ε/2) := Finset.sum_le_sum hfiber
    _ = (I.card : ℝ)*(2*B*(4*n+1:ℝ)^(ε/2)) := by simp
    _ ≤ (A*(n:ℝ)^(ε/2))*(2*B*((5:ℝ)^(ε/2)*(n:ℝ)^(ε/2))) := by
      exact mul_le_mul himage (mul_le_mul_of_nonneg_left hpow (by positivity))
        (by positivity) (by positivity)
    _ = (2*A*B*(5:ℝ)^(ε/2))*(n:ℝ)^ε := by
      calc
        _ = (2*A*B*(5:ℝ)^(ε/2))*((n:ℝ)^(ε/2)*(n:ℝ)^(ε/2)) := by ring
        _ = _ := by rw [hp]

private def permReps (n : ℕ) (σ : Equiv.Perm (Fin 4)) : Finset (Fin 4 → Fin (n+1)) :=
  Finset.univ.filter (fun a ↦ (∑ i, (a i : ℕ)^4=n) ∧
    ((a (σ 0) : ℕ)+(a (σ 1) : ℕ))^2=(a (σ 2) : ℕ)^2+(a (σ 3) : ℕ)^2)

private lemma permReps_card (n : ℕ) (σ : Equiv.Perm (Fin 4)) :
    (permReps n σ).card=fixedCount n := by
  classical
  apply Finset.card_nbij (fun a i ↦ a (σ i))
  · intro a ha
    simp only [Finset.mem_coe,permReps,reps,Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
    exact ⟨(Equiv.sum_comp σ (fun i ↦ (a i : ℕ)^4)).trans ha.1,ha.2⟩
  · intro a _ b _ he
    funext i
    have hi := congrArg (fun f ↦ f (σ.symm i)) he
    simpa using hi
  · intro a ha
    simp only [Finset.mem_coe,reps,Finset.mem_filter,Finset.mem_univ,true_and] at ha
    refine ⟨fun i ↦ a (σ.symm i),?_,?_⟩
    · simp only [Finset.mem_coe,permReps,Finset.mem_filter,Finset.mem_univ,true_and,
        Equiv.symm_apply_apply]
      exact ⟨(Equiv.sum_comp σ.symm (fun i ↦ (a i : ℕ)^4)).trans ha.1,ha.2⟩
    · funext i
      simp

/-- Some permutation of the coordinates obeys `(a+b)^2=c^2+d^2`. -/
def HasPythagoreanRelation {n : ℕ} (a : Fin 4 → Fin (n+1)) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4),
    ((a (σ 0) : ℕ)+(a (σ 1) : ℕ))^2=(a (σ 2) : ℕ)^2+(a (σ 3) : ℕ)^2

instance {n : ℕ} (a : Fin 4 → Fin (n+1)) : Decidable (HasPythagoreanRelation a) :=
  inferInstanceAs (Decidable (∃ σ : Equiv.Perm (Fin 4),
    ((a (σ 0) : ℕ)+(a (σ 1) : ℕ))^2=(a (σ 2) : ℕ)^2+(a (σ 3) : ℕ)^2))

/-- Count the entire Pythagorean-relation locus, allowing all permutations. -/
def pythagoreanCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun a : Fin 4 → Fin (n+1) ↦
    (∑ i, (a i : ℕ)^4=n) ∧ HasPythagoreanRelation a)).card

private lemma count_le_fixed (n : ℕ) : pythagoreanCount n ≤ 24*fixedCount n := by
  classical
  have he : Finset.univ.filter (fun a : Fin 4 → Fin (n+1) ↦
      (∑ i, (a i : ℕ)^4=n) ∧ HasPythagoreanRelation a) =
      Finset.univ.biUnion (permReps n) := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_biUnion,
      permReps,HasPythagoreanRelation]
    tauto
  unfold pythagoreanCount
  rw [he]
  have hc := Finset.card_biUnion_le (s := (Finset.univ : Finset (Equiv.Perm (Fin 4))))
    (t := permReps n)
  simp only [permReps_card,Finset.sum_const,Finset.card_univ,Fintype.card_perm,
    Fintype.card_fin,smul_eq_mul] at hc
  norm_num at hc
  exact hc

/-- All quartic representations obeying any such Pythagorean relation have
a uniform subpolynomial count. This is a bound on a subset, not the full count. -/
theorem pythagorean_count_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n → (pythagoreanCount n : ℝ) ≤ C*(n:ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := fixed_count_subpolynomial ε hε
  refine ⟨24*C,by positivity,fun n hn ↦ ?_⟩
  calc
    (pythagoreanCount n : ℝ) ≤ 24*(fixedCount n : ℝ) := by exact_mod_cast count_le_fixed n
    _ ≤ 24*(C*(n:ℝ)^ε) := mul_le_mul_of_nonneg_left (hbound n hn) (by norm_num)
    _ = (24*C)*(n:ℝ)^ε := by ring

/-- The complementary count, on which the quartic problem remains open here. -/
def nonPythagoreanCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun a : Fin 4 → Fin (n+1) ↦
    (∑ i, (a i : ℕ)^4=n) ∧ ¬ HasPythagoreanRelation a)).card

lemma count_split (n : ℕ) :
    pythagoreanCount n+nonPythagoreanCount n=Erdos322.representationCount 4 n := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter
    (fun a : Fin 4 → Fin (n+1) ↦ ∑ i, (a i : ℕ)^4=n)) HasPythagoreanRelation
  simpa only [Finset.filter_filter,pythagoreanCount,nonPythagoreanCount,
    Erdos322.representationCount] using h

/-- Removing the entire Pythagorean-relation locus leaves exactly the same
question about existence of positive-power quartic peaks. -/
theorem quartic_peaks_iff_nonPythagorean_peaks :
    (∃ c > (0:ℝ), {n : ℕ | (n:ℝ)^c < Erdos322.representationCount 4 n}.Infinite) ↔
    (∃ c > (0:ℝ), {n : ℕ | (n:ℝ)^c < nonPythagoreanCount n}.Infinite) := by
  constructor
  · rintro ⟨c,hc,hi⟩
    have hh : 0<c/2 := by linarith
    obtain ⟨C,hC,hsmall⟩ := pythagorean_count_subpolynomial (c/2) hh
    have ht : Filter.Tendsto (fun n : ℕ ↦ (n:ℝ)^(c/2)) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop hh).comp tendsto_natCast_atTop_atTop
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop (C+1))
    refine ⟨c/2,hh,(hi.diff (Set.finite_Iio (max N 1))).mono ?_⟩
    intro n hn
    have hlarge : max N 1≤n := by simpa only [Set.mem_Iio,not_lt] using hn.2
    have hnpos : 0<n := by omega
    have hnr : (0:ℝ)<n := by exact_mod_cast hnpos
    have hbound := hsmall n hnpos
    have hdom := hN n (by omega)
    have hsplit : (pythagoreanCount n : ℝ)+nonPythagoreanCount n =
        Erdos322.representationCount 4 n := by exact_mod_cast count_split n
    have hp : ((n:ℝ)^(c/2))^2=(n:ℝ)^c := by
      rw [pow_two,←Real.rpow_add hnr]
      congr 1
      ring
    have hmain := hn.1
    change (n:ℝ)^c < (Erdos322.representationCount 4 n : ℝ) at hmain
    change (n:ℝ)^(c/2) < (nonPythagoreanCount n : ℝ)
    nlinarith [mul_nonneg (show 0≤(n:ℝ)^(c/2) by positivity)
      (show 0≤(n:ℝ)^(c/2)-(C+1) by linarith)]
  · rintro ⟨c,hc,hi⟩
    refine ⟨c,hc,hi.mono fun n hn ↦ ?_⟩
    have hle : (nonPythagoreanCount n : ℝ)≤Erdos322.representationCount 4 n := by
      exact_mod_cast (show nonPythagoreanCount n≤Erdos322.representationCount 4 n from
        by have := count_split n; omega)
    exact hn.trans_le hle

end Erdos322Research.QuarticPythagorean
