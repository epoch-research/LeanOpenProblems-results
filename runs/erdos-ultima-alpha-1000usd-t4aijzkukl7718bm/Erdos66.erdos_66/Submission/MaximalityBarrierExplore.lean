import Submission.Explore

/-! Asymptotic upper bounds alone do not support an inclusion-maximality
argument: finite insertions preserve them, and increasing unions need not.
This diagnoses a proposed proof strategy, not the conjecture itself. -/
namespace Erdos66MaximalityBarrier
open Filter AdditiveCombinatorics Erdos66Explore
open scoped Topology Classical

def UpperTail (A : Set ℕ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (sumRep A n : ℝ)/Real.log n ≤ c+ε

lemma upperTail_insert {A : Set ℕ} {c : ℝ} (h : UpperTail A c) (a : ℕ) :
    UpperTail (insert a A) c := by
  intro ε hε
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := (hlog.const_div_atTop (2:ℝ)).eventually_lt_const (half_pos hε)
  filter_upwards [h (ε/2) (half_pos hε),hsmall,eventually_ge_atTop 2] with n hn hsmalln hn2
  have hl : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn2)
  have hb : (sumRep (insert a A) n : ℝ) ≤ (sumRep A n : ℝ)+2 := by
    exact_mod_cast sumRep_insert_le A a n
  have hh := div_le_div_of_nonneg_right hb hl.le
  rw [add_div] at hh
  linarith

lemma upperTail_sublinear {A : Set ℕ} {c : ℝ} (h : UpperTail A c) :
    Tendsto (fun n ↦ (sumRep A n : ℝ)/(n:ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n/(n:ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun n : ℕ ↦ (|c|+1)*(Real.log n/(n:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlog.const_mul (|c|+1)
  refine squeeze_zero' (Eventually.of_forall (fun n ↦ by positivity)) ?_ hu
  filter_upwards [h 1 (by norm_num),eventually_ge_atTop 2] with n hn hn2
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn2)
  have hb : (sumRep A n : ℝ) ≤ (|c|+1)*Real.log n := by
    have hh := (div_le_iff₀ hl).mp hn
    have hm := mul_le_mul_of_nonneg_right (show c+1 ≤ |c|+1 by linarith [le_abs_self c]) hl.le
    exact hh.trans hm
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hb hnp.le

lemma sumRep_univ (n : ℕ) : sumRep (Set.univ : Set ℕ) n=n+1 := by
  simp [sumRep_def,Finset.Nat.card_antidiagonal]

lemma not_upperTail_univ (c : ℝ) : ¬ UpperTail (Set.univ : Set ℕ) c := by
  intro h
  have hh := upperTail_sublinear h
  have hb : ∀ᶠ n : ℕ in atTop, (1:ℝ) ≤ (sumRep (Set.univ : Set ℕ) n : ℝ)/(n:ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    rw [sumRep_univ,Nat.cast_add,Nat.cast_one]
    exact (le_div_iff₀ hnp).mpr (by linarith)
  have hf : (1:ℝ) ≤ 0 := ge_of_tendsto hh hb
  norm_num at hf

/-- Every set with the asymptotic upper bound has a strictly larger set with
that same bound. Hence ordinary inclusion-maximality is unavailable. -/
theorem upperTail_has_strict_extension {A : Set ℕ} {c : ℝ} (h : UpperTail A c) :
    ∃ B : Set ℕ, A ⊂ B ∧ UpperTail B c := by
  have hne : A ≠ Set.univ := by
    intro he
    exact not_upperTail_univ c (he ▸ h)
  have hex : ∃ a, a ∉ A := by
    by_contra hh
    push_neg at hh
    exact hne (Set.eq_univ_iff_forall.mpr hh)
  obtain ⟨a,ha⟩ := hex
  exact ⟨insert a A,Set.ssubset_insert ha,upperTail_insert h a⟩

lemma finite_upperTail {A : Set ℕ} (hA : A.Finite) {c : ℝ} (hc : 0 ≤ c) :
    UpperTail A c := by
  intro ε hε
  exact ((finite_limit_zero hA).eventually_lt_const (show 0<c+ε by linarith)).mono
    (fun _ hh ↦ hh.le)

/-- Even an increasing sequence of finite admissible sets can have an
inadmissible union. Thus the asymptotic upper-bound class is not chain-closed. -/
theorem increasing_union_counterexample (c : ℝ) (hc : 0 ≤ c) :
    ∃ S : ℕ → Set ℕ, Monotone S ∧ (∀ k, UpperTail (S k) c) ∧
      ¬ UpperTail (⋃ k, S k) c := by
  let S : ℕ → Set ℕ := fun k ↦ Set.Iio k
  have hS : (⋃ k, S k)=Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro n
    exact Set.mem_iUnion.mpr ⟨n+1,by simp [S]⟩
  refine ⟨S,?_,?_,?_⟩
  · intro i j hij n hn
    exact lt_of_lt_of_le hn hij
  · intro k
    exact finite_upperTail (Set.finite_Iio k) hc
  · rw [hS]
    exact not_upperTail_univ c

end Erdos66MaximalityBarrier
