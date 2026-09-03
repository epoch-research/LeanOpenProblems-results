import FormalConjecturesUtil

/-! Finite product sampling and a second-moment bound for sparse families of
coordinate events. All expectations are finite averages. -/
namespace Erdos1206.FiniteProductSampling
open Finset
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} [NeZero k]

noncomputable def event (e : Finset V) (ω : V → Fin k) : ℝ :=
  if ∀ v ∈ e, ω v=0 then 1 else 0

lemma event_nonneg (e : Finset V) (ω : V → Fin k) : 0 ≤ event e ω := by
  dsimp [event]; split_ifs <;> norm_num

lemma event_le_one (e : Finset V) (ω : V → Fin k) : event e ω ≤ 1 := by
  dsimp [event]; split_ifs <;> norm_num

lemma event_mul (e f : Finset V) (ω : V → Fin k) :
    event e ω*event f ω=event (e∪f) ω := by
  have hiff : (∀ v ∈ e∪f, ω v=0) ↔ (∀ v ∈ e, ω v=0) ∧ (∀ v ∈ f, ω v=0) := by
    simp only [mem_union,or_imp,forall_and]
  simp only [event,hiff]
  split_ifs <;> simp_all

omit [NeZero k] in
private lemma expect_product (f : V → Fin k → ℝ) :
    (𝔼 ω : V → Fin k, ∏ v, f v (ω v))=∏ v, (𝔼 a : Fin k, f v a) := by
  simp only [Fintype.expect_eq_sum_div_card,←Fintype.prod_sum,Fintype.card_fun,Fintype.card_fin]
  rw [prod_div_distrib,prod_const,card_univ,Nat.cast_pow]

lemma event_mean (e : Finset V) :
    (𝔼 ω : V → Fin k, event e ω)=(1/(k:ℝ))^e.card := by
  have hprod (ω : V → Fin k) : event e ω=∏ v, (if v∈e then (if ω v=0 then (1:ℝ) else 0) else 1) := by
    rw [prod_ite_mem,univ_inter]
    dsimp only [event]
    split_ifs with h
    ·
      symm
      apply prod_eq_one
      intro v hv
      simp [h v hv]
    · have hex : ∃ v∈e, ω v≠0 := by push_neg at h; exact h
      obtain ⟨v,hv,hv0⟩ := hex
      symm
      exact prod_eq_zero hv (by simp [hv0])
  simp_rw [hprod]
  rw [expect_product (fun v a => if v∈e then (if a=0 then (1:ℝ) else 0) else 1)]
  have hmean (v : V) : (𝔼 a : Fin k, if v∈e then (if a=0 then (1:ℝ) else 0) else 1)=
      if v∈e then 1/(k:ℝ) else 1 := by
    by_cases hv : v∈e
    · simp only [hv,if_true,Fintype.expect_eq_sum_div_card,Fintype.card_fin]
      simp
    · simp [hv]
  simp_rw [hmean]
  rw [prod_ite_mem,univ_inter,prod_const]

noncomputable def centered (e : Finset V) (ω : V → Fin k) : ℝ :=
  event e ω-(1/(k:ℝ))^e.card

lemma event_covariance (e f : Finset V) :
    (𝔼 ω : V → Fin k, centered e ω*centered f ω)=
      (1/(k:ℝ))^(e∪f).card-(1/(k:ℝ))^e.card*(1/(k:ℝ))^f.card := by
  have he (ω : V → Fin k) : centered e ω*centered f ω=
      event (e∪f) ω-event e ω*(1/(k:ℝ))^f.card-
        (1/(k:ℝ))^e.card*event f ω+(1/(k:ℝ))^e.card*(1/(k:ℝ))^f.card := by
    rw [←event_mul]
    dsimp [centered]
    ring
  simp_rw [he]
  rw [expect_add_distrib,expect_sub_distrib,expect_sub_distrib,←expect_mul,←mul_expect,
    event_mean,event_mean,event_mean,Fintype.expect_const]
  ring

lemma covariance_zero_of_disjoint {e f : Finset V} (h : Disjoint e f) :
    (𝔼 ω : V → Fin k, centered e ω*centered f ω)=0 := by
  rw [event_covariance,card_union_of_disjoint h,pow_add,sub_self]

lemma covariance_le_one (e f : Finset V) :
    (𝔼 ω : V → Fin k, centered e ω*centered f ω) ≤ 1 := by
  rw [event_covariance]
  have hk : (1:ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  have hp : 1/(k:ℝ) ≤ 1 := (div_le_one (by positivity : (0:ℝ) < k)).mpr hk
  have hh : (1/(k:ℝ))^(e∪f).card ≤ 1 := pow_le_one₀ (by positivity) hp
  have hn : 0 ≤ (1/(k:ℝ))^e.card*(1/(k:ℝ))^f.card := by positivity
  linarith

#print axioms event_mean
#print axioms event_covariance
end Erdos1206.FiniteProductSampling
