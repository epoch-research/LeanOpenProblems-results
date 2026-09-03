import Submission.FinitePatternAdmissibility

/-! Exact local translate counts for split primes. These are local factors
for a possible path-counting sieve, not uniform estimates for prime paths. -/
namespace Erdos952Investigation.FinitePatternLocalCounts
open AdmissibleRay
set_option maxHeartbeats 0

noncomputable def splitEquiv {K : Type*} [Field K]
    (r : K) (hr : r ≠ 0) (h2 : (2 : K) ≠ 0) : K × K ≃ K × K where
  toFun ab := (ab.1+r*ab.2,ab.1-r*ab.2)
  invFun uv := ((uv.1+uv.2)/2,(uv.1-uv.2)/(2*r))
  left_inv ab := by
    apply Prod.ext <;> dsimp <;> field_simp <;> ring
  right_inv uv := by
    apply Prod.ext <;> dsimp <;> field_simp <;> ring

lemma card_avoiding {ι K : Type*} [Fintype ι] [Fintype K] (f : ι → K) :
    Nat.card {a : K // ∀ i, a ≠ f i} = Fintype.card K-Nat.card (Set.range f) := by
  classical
  calc
    Nat.card {a : K // ∀ i, a ≠ f i} = Nat.card {a : K // a ∉ Set.range f} := by
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro a
      simp [Set.mem_range,eq_comm]
    _ = Fintype.card K-Nat.card (Set.range f) := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]

lemma sum_squares_ne_zero_iff {K : Type*} [Field K] (r : K) (hr : r^2 = -1)
    (a b u v : K) :
    (a+u)^2+(b+v)^2 ≠ 0 ↔
      a+r*b ≠ -u-r*v ∧ a-r*b ≠ -u+r*v := by
  have he : (a+u)^2+(b+v)^2 =
      ((a+r*b)-(-u-r*v))*((a-r*b)-(-u+r*v)) := by
    linear_combination (b+v)^2*hr
  rw [he,mul_ne_zero_iff,sub_ne_zero,sub_ne_zero]

theorem finite_field_split_count {ι K : Type*} [Fintype ι] [Fintype K] [Field K]
    (r : K) (hr : r^2 = -1) (h2 : (2 : K) ≠ 0) (u v : ι → K) :
    Nat.card {ab : K × K // ∀ i, (ab.1+u i)^2+(ab.2+v i)^2 ≠ 0} =
      (Fintype.card K-Nat.card (Set.range (fun i => -u i-r*v i)))*
      (Fintype.card K-Nat.card (Set.range (fun i => -u i+r*v i))) := by
  classical
  have hr0 : r ≠ 0 := by
    intro he
    rw [he,zero_pow (by decide : 2 ≠ 0)] at hr
    exact one_ne_zero (neg_eq_zero.mp hr.symm)
  let e := splitEquiv r hr0 h2
  have he (ab : K × K) :
      (∀ i, (ab.1+u i)^2+(ab.2+v i)^2 ≠ 0) ↔
      (∀ i, (e ab).1 ≠ -u i-r*v i) ∧ (∀ i, (e ab).2 ≠ -u i+r*v i) := by
    rw [← forall_and]
    apply forall_congr'
    intro i
    exact sum_squares_ne_zero_iff r hr _ _ _ _
  let ee : {ab : K × K // ∀ i, (ab.1+u i)^2+(ab.2+v i)^2 ≠ 0} ≃
      {ab : K × K // (∀ i, ab.1 ≠ -u i-r*v i) ∧
        (∀ i, ab.2 ≠ -u i+r*v i)} := e.subtypeEquiv he
  have hh := Nat.card_congr (ee.trans (Equiv.subtypeProdEquivProd
    (p := fun a => ∀ i, a ≠ -u i-r*v i)
    (q := fun b => ∀ i, b ≠ -u i+r*v i)))
  rw [Nat.card_prod,card_avoiding,card_avoiding] at hh
  exact hh

noncomputable def localCount {ι : Type*} (z : ι → GaussianInt) (p : ℕ) : ℕ :=
  Nat.card {ab : ZMod p × ZMod p // ∀ i, Good p ab.1 ab.2 (z i)}

def project {p : ℕ} (r : ZMod p) (z : GaussianInt) : ZMod p :=
  (z.re : ZMod p)+r*(z.im : ZMod p)

lemma two_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro he
  have hd := (ZMod.natCast_eq_zero_iff 2 p).mp he
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)

/-- Each of the two projections excludes its distinct values, independently
of the other projection. Collisions are counted exactly. -/
theorem split_local_count {ι : Type*} [Fintype ι] (z : ι → GaussianInt)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (r : ZMod p) (hr : r^2 = -1) :
    localCount z p =
      (p-Nat.card (Set.range (fun i => -((z i).re : ZMod p)-r*((z i).im : ZMod p))))*
      (p-Nat.card (Set.range (fun i => -((z i).re : ZMod p)+r*((z i).im : ZMod p)))) := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa only [localCount,Good,ZMod.card] using finite_field_split_count
    r hr (two_ne_zero hp hp2) (fun i => ((z i).re : ZMod p))
    (fun i => ((z i).im : ZMod p))

/-- If the prime exceeds every squared difference, neither split projection
can identify two distinct vertices. -/
theorem projection_injective_of_norm_bound {ι : Type*} (z : ι → GaussianInt)
    (hz : Function.Injective z) {p : ℕ} (r : ZMod p) (hr : r^2 = -1)
    (hbound : ∀ i j, (z i-z j).norm < (p : ℤ)) :
    Function.Injective (fun i => project r (z i)) := by
  intro i j he
  have hproj : (((z i-z j).re : ℤ) : ZMod p)+
      r*((((z i-z j).im : ℤ) : ZMod p)) = 0 := by
    simp only [Zsqrtd.re_sub,Zsqrtd.im_sub,Int.cast_sub]
    dsimp [project] at he
    linear_combination he
  have hnorm : ((z i-z j).norm : ZMod p) = 0 := by
    rw [gaussian_norm_sq]
    push_cast
    have hf : ((((z i-z j).re : ℤ) : ZMod p))^2+
        ((((z i-z j).im : ℤ) : ZMod p))^2 =
        (((((z i-z j).re : ℤ) : ZMod p))+r*((((z i-z j).im : ℤ) : ZMod p)))*
        (((((z i-z j).re : ℤ) : ZMod p))-r*((((z i-z j).im : ℤ) : ZMod p))) := by
      linear_combination ((((z i-z j).im : ℤ) : ZMod p))^2*hr
    rw [hf,hproj,zero_mul]
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (z i-z j).norm p).mp hnorm
  have hn := Int.eq_zero_of_dvd_of_nonneg_of_lt (GaussianInt.norm_nonneg _) (hbound i j) hd
  exact hz (sub_eq_zero.mp (GaussianInt.norm_eq_zero.mp hn))

lemma card_range_of_injective {ι K : Type*} [Fintype ι]
    (f : ι → K) (hf : Function.Injective f) :
    Nat.card (Set.range f) = Fintype.card ι := by
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (Equiv.ofInjective f hf)).symm

/-- In the collision-free range, a k-vertex pattern has exactly (p-k)^2
surviving translates at a split prime. This is not a global sieve estimate. -/
theorem split_local_count_of_norm_bound {ι : Type*} [Fintype ι]
    (z : ι → GaussianInt) (hz : Function.Injective z)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (r : ZMod p) (hr : r^2 = -1)
    (hbound : ∀ i j, (z i-z j).norm < (p : ℤ)) :
    localCount z p = (p-Fintype.card ι)^2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hplus := projection_injective_of_norm_bound z hz r hr hbound
  have hminus := projection_injective_of_norm_bound z hz (-r)
    (by simpa only [neg_sq] using hr) hbound
  have hpi : Function.Injective
      (fun i => -((z i).re : ZMod p)-r*((z i).im : ZMod p)) := by
    intro i j he
    apply hplus
    dsimp [project]
    linear_combination -he
  have hmi : Function.Injective
      (fun i => -((z i).re : ZMod p)+r*((z i).im : ZMod p)) := by
    intro i j he
    apply hminus
    dsimp [project]
    linear_combination -he
  rw [split_local_count z hp hp2 r hr,card_range_of_injective _ hpi,
    card_range_of_injective _ hmi,pow_two]


/-- Projection collisions can only increase the local count from (p-k)^2.
This lower bound does not require a bound on the configuration's diameter. -/
theorem split_local_count_lower {ι : Type*} [Fintype ι]
    (z : ι → GaussianInt) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (r : ZMod p) (hr : r^2 = -1) :
    (p-Fintype.card ι)^2 ≤ localCount z p := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hplus : Nat.card (Set.range
      (fun i => -((z i).re : ZMod p)-r*((z i).im : ZMod p))) ≤ Fintype.card ι := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_range_le _
  have hminus : Nat.card (Set.range
      (fun i => -((z i).re : ZMod p)+r*((z i).im : ZMod p))) ≤ Fintype.card ι := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_range_le _
  rw [split_local_count z hp hp2 r hr,pow_two]
  exact Nat.mul_le_mul (Nat.sub_le_sub_left hplus p) (Nat.sub_le_sub_left hminus p)

#print axioms split_local_count_lower

#print axioms finite_field_split_count
#print axioms split_local_count
#print axioms projection_injective_of_norm_bound
#print axioms split_local_count_of_norm_bound
end Erdos952Investigation.FinitePatternLocalCounts
