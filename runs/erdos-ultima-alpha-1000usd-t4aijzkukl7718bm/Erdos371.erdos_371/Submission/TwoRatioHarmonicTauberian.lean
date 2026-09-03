import Submission.HarmonicWindowTauberian

/-! Two multiplicatively independent harmonic-window cancellations suffice
for ordinary Cesaro cancellation. This supplies a criterion, not its arithmetic
hypotheses for the largest-prime comparison. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

lemma irrational_log_two_div_log_three : Irrational (Real.log 2/Real.log 3) := by
  rintro ⟨q,hq⟩
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0<Real.log 3 := Real.log_pos (by norm_num)
  have hqpos : 0<q := Rat.cast_pos.mp (hq.symm ▸ div_pos hlog2 hlog3)
  have hnum : 0<q.num := Rat.num_pos.mpr hqpos
  have hnumcast : (q.num : ℝ)=(q.num.natAbs : ℝ) := by
    have he := Int.natCast_natAbs q.num
    rw [abs_of_pos hnum] at he
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) he.symm
  rw [Rat.cast_def,hnumcast] at hq
  have hden : (0 : ℝ)<q.den := by exact_mod_cast q.den_pos
  have he : (q.den : ℝ)*Real.log 2=(q.num.natAbs : ℝ)*Real.log 3 := by
    have h := (div_eq_div_iff hden.ne' hlog3.ne').mp hq
    nlinarith
  have hp : (2 : ℝ)^q.den=(3 : ℝ)^q.num.natAbs := by
    calc
      _ = Real.exp ((q.den : ℝ)*Real.log 2) := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
      _ = Real.exp ((q.num.natAbs : ℝ)*Real.log 3) := congrArg Real.exp he
      _ = _ := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  have hpN : (2 : ℕ)^q.den=3^q.num.natAbs := by exact_mod_cast hp
  have hd : 2 ∣ (2 : ℕ)^q.den := dvd_pow_self 2 q.den_pos.ne'
  rw [hpN] at hd
  have hbad := Nat.prime_two.dvd_of_dvd_pow hd
  norm_num at hbad

/-- Positive integer dilations under which the raw harmonic primitive has
asymptotically zero increment. -/
def GoodHarmonicMultiplier (H : ℕ → ℝ) (a : ℕ) : Prop :=
  0<a ∧ Tendsto (fun N => H (a*N)-H N) atTop (𝓝 0)

lemma goodHarmonicMultiplier_one (H : ℕ → ℝ) : GoodHarmonicMultiplier H 1 := by
  exact ⟨by omega,by simp only [one_mul,sub_self]; exact tendsto_const_nhds⟩

lemma goodHarmonicMultiplier_mul (H : ℕ → ℝ) (a b : ℕ)
    (ha : GoodHarmonicMultiplier H a) (hb : GoodHarmonicMultiplier H b) :
    GoodHarmonicMultiplier H (a*b) := by
  have ht : Tendsto (fun N : ℕ => b*N) atTop atTop :=
    tendsto_atTop_mono (fun N => by
      simpa only [id_eq,one_mul] using Nat.mul_le_mul_right N (show 1≤b from hb.1)) tendsto_id
  refine ⟨Nat.mul_pos ha.1 hb.1,?_⟩
  have h := (ha.2.comp ht).add hb.2
  simpa only [Function.comp_apply,sub_add_sub_cancel,zero_add,mul_assoc] using h

noncomputable def harmonicPeriodLogGroup (H : ℕ → ℝ) : AddSubgroup ℝ where
  carrier := {t | ∃ a b : ℕ, GoodHarmonicMultiplier H a ∧ GoodHarmonicMultiplier H b ∧
    t=Real.log a-Real.log b}
  zero_mem' := ⟨1,1,goodHarmonicMultiplier_one H,goodHarmonicMultiplier_one H,by simp⟩
  add_mem' := by
    rintro x y ⟨a,b,ha,hb,rfl⟩ ⟨c,d,hc,hd,rfl⟩
    refine ⟨a*c,b*d,goodHarmonicMultiplier_mul H a c ha hc,
      goodHarmonicMultiplier_mul H b d hb hd,?_⟩
    have har : (a : ℝ)≠0 := by exact_mod_cast ha.1.ne'
    have hbr : (b : ℝ)≠0 := by exact_mod_cast hb.1.ne'
    have hcr : (c : ℝ)≠0 := by exact_mod_cast hc.1.ne'
    have hdr : (d : ℝ)≠0 := by exact_mod_cast hd.1.ne'
    rw [Nat.cast_mul,Nat.cast_mul,Real.log_mul har hcr,Real.log_mul hbr hdr]
    ring
  neg_mem' := by
    rintro x ⟨a,b,ha,hb,rfl⟩
    exact ⟨b,a,hb,ha,by ring⟩

lemma harmonicPeriodLogGroup_dense (H : ℕ → ℝ)
    (h2 : GoodHarmonicMultiplier H 2) (h3 : GoodHarmonicMultiplier H 3) :
    Dense (harmonicPeriodLogGroup H : Set ℝ) := by
  have hsub : AddSubgroup.closure {Real.log 2,Real.log 3} ≤ harmonicPeriodLogGroup H := by
    apply (AddSubgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      exact ⟨2,1,h2,goodHarmonicMultiplier_one H,by simp⟩
    · have hx' := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨3,1,h3,goodHarmonicMultiplier_one H,by simp⟩
  exact (dense_addSubgroupClosure_pair_iff.mpr irrational_log_two_div_log_three).mono hsub

/-- Integer ratios arbitrarily close to one are available from the two
zero-increment multipliers; negative powers are implemented using a denominator. -/
lemma narrow_good_harmonic_multipliers (H : ℕ → ℝ)
    (h2 : GoodHarmonicMultiplier H 2) (h3 : GoodHarmonicMultiplier H 3)
    (ε : ℝ) (hε : 0<ε) :
    ∃ a b : ℕ, GoodHarmonicMultiplier H a ∧ GoodHarmonicMultiplier H b ∧
      b<a ∧ ((a : ℝ)-b)/b<ε := by
  have hlog : 0<Real.log (1+ε) := Real.log_pos (by linarith)
  obtain ⟨t,ht,htI⟩ := (harmonicPeriodLogGroup_dense H h2 h3).exists_mem_open
    isOpen_Ioo (Set.nonempty_Ioo.mpr hlog)
  obtain ⟨a,b,ha,hb,rfl⟩ := ht
  have har : (0 : ℝ)<a := by exact_mod_cast ha.1
  have hbr : (0 : ℝ)<b := by exact_mod_cast hb.1
  have hab : (b : ℝ)<a := by
    apply (Real.log_lt_log_iff hbr har).mp
    linarith [htI.1]
  have he : (a : ℝ)/b<1+ε := by
    apply (Real.log_lt_log_iff (div_pos har hbr) (by linarith)).mp
    rw [Real.log_div har.ne' hbr.ne']
    exact htI.2
  refine ⟨a,b,ha,hb,by exact_mod_cast hab,?_⟩
  have he' : ((a : ℝ)-b)/b=(a : ℝ)/b-1 := by field_simp
  rw [he']
  linarith

/-- Two fixed ratios suffice. This is strictly a conditional analytic
criterion; the two window limits for factorSign remain to be established. -/
theorem prefixMean_zero_of_two_harmonic_windows (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1)
    (h2 : Tendsto (fun N => rawHarmonicSum f (2*N)-rawHarmonicSum f N) atTop (𝓝 0))
    (h3 : Tendsto (fun N => rawHarmonicSum f (3*N)-rawHarmonicSum f N) atTop (𝓝 0)) :
    Tendsto (fun N => prefixMean N f) atTop (𝓝 0) := by
  apply prefixMean_zero_of_narrow_harmonic_windows f hf
  intro ε hε
  obtain ⟨a,b,ha,hb,hba,he⟩ := narrow_good_harmonic_multipliers (rawHarmonicSum f)
    ⟨by omega,h2⟩ ⟨by omega,h3⟩ ε hε
  refine ⟨a,b,hb.1,hba,he,?_⟩
  simpa only [sub_sub_sub_cancel_right,sub_zero] using ha.2.sub hb.2

/-- A weaker alternative to unnormalized prime-current l1 tightness. The
arithmetic hypotheses are not provided by normalized harmonic cancellation. -/
theorem density_of_two_harmonic_windows
    (h2 : Tendsto (fun N => rawHarmonicSum factorSign (2*N)-rawHarmonicSum factorSign N) atTop (𝓝 0))
    (h3 : Tendsto (fun N => rawHarmonicSum factorSign (3*N)-rawHarmonicSum factorSign N) atTop (𝓝 0)) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) := by
  rw [density_iff_signed_count]
  simpa only [prefixMean,factorSign_sum_eq_count_difference] using
    prefixMean_zero_of_two_harmonic_windows factorSign (fun n => by simpa only [← Real.norm_eq_abs,factorSign_norm] using (le_refl (1 : ℝ))) h2 h3

#print axioms irrational_log_two_div_log_three
#print axioms prefixMean_zero_of_two_harmonic_windows
#print axioms density_of_two_harmonic_windows
end Erdos371
