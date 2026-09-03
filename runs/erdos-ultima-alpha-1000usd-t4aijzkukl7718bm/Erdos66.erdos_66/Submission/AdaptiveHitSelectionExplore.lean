import Submission.UniformSelectionExplore

/-! Sequential selection from history-dependent candidate sets. A common
exponential potential controls all accumulated hits; availability is charged
at each step, not by a union bound over all pairs of steps. -/
namespace Erdos66AdaptiveHitSelection
open Erdos66UniformSelection
open scoped Classical
set_option maxHeartbeats 2200000

lemma subtype_hit_card {α : Type*} [Fintype α] (U S : Finset α) :
    (Finset.univ.filter (fun a : ↥U ↦ a.val∈S)).card ≤ S.card := by
  apply Finset.card_le_card_of_injOn Subtype.val
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · intro a ha b hb he
    exact Subtype.ext he

/-- One conditional hit has an exponential cost bounded using the number
of currently available choices, without independence from the past. -/
lemma restricted_hit_mgf {α : Type*} [Fintype α]
    (U S : Finset α) (hU : U.Nonempty) (q K t b : ℝ)
    (hq : 0<q) (hcard : q ≤ U.card) (hS : (S.card : ℝ) ≤ K)
    (hb : Real.exp t*K/q ≤ b) :
    mean (fun a : ↥U ↦ Real.exp (t*(if a.val∈S then (1 : ℝ) else 0))) ≤ Real.exp b := by
  letI : Nonempty ↥U := hU.to_subtype
  let S' : Finset ↥U := Finset.univ.filter (fun a ↦ a.val∈S)
  have hS' : (S'.card : ℝ) ≤ K := by
    have hc : (S'.card : ℝ) ≤ S.card := by exact_mod_cast subtype_hit_card U S
    exact hc.trans hS
  have hK : 0 ≤ K := (Nat.cast_nonneg S'.card).trans hS'
  have hden : (0 : ℝ)<U.card := hq.trans_le hcard
  have hc : Fintype.card ↥U=U.card := Fintype.card_coe U
  have he : mean (fun a : ↥U ↦ Real.exp (t*(if a.val∈S then (1 : ℝ) else 0))) =
      1+(Real.exp t-1)*S'.card/U.card := by
    have hh := mean_exp_hit S' t
    simpa only [S',Finset.mem_filter,Finset.mem_univ,true_and,hc] using hh
  rw [he]
  have hnum : (Real.exp t-1)*S'.card ≤ Real.exp t*K := by
    have hh := mul_le_mul_of_nonneg_left hS' (Real.exp_pos t).le
    have hn := Nat.cast_nonneg (α := ℝ) S'.card
    nlinarith
  have hfrac : (Real.exp t-1)*S'.card/U.card ≤ Real.exp t*K/q :=
    (div_le_div_of_nonneg_right hnum hden.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg (Real.exp_pos t).le hK) hq hcard)
  have h := Real.add_one_le_exp b
  linarith

variable {α γ ζ : Type*} [Fintype α]

/-- State-dependent finite selection with arbitrary target-dependent budgets.
The invariant and all candidate-degree estimates are explicit hypotheses. -/
theorem exists_adaptive_small_hits
    (m : ℕ) (s₀ : γ) (Inv : ℕ → γ → Prop)
    (choices : ℕ → γ → Finset α) (next : ℕ → γ → α → γ)
    (load : γ → ζ → ℝ) (hit : ℕ → γ → ζ → Finset α)
    (T : Finset ζ) (q t : ℝ) (K b R : ζ → ℝ)
    (hq : 0<q) (ht : 0<t) (h₀ : Inv 0 s₀)
    (hload₀ : ∀ z ∈ T, load s₀ z=0)
    (hchoices : ∀ k < m, ∀ s, Inv k s → q ≤ (choices k s).card)
    (hnext : ∀ k < m, ∀ s, Inv k s → ∀ a∈choices k s, Inv (k+1) (next k s a))
    (hhit : ∀ k < m, ∀ s, Inv k s → ∀ z∈T, ((hit k s z).card : ℝ) ≤ K z)
    (hload : ∀ k < m, ∀ s, Inv k s → ∀ a∈choices k s, ∀ z∈T,
      load (next k s a) z ≤ load s z+(if a∈hit k s z then 1 else 0))
    (hrate : ∀ z∈T, Real.exp t*K z/q ≤ b z)
    (hsmall : (∑ z∈T, Real.exp ((m : ℝ)*b z-t*R z))<1) :
    ∃ s, Inv m s ∧ ∀ z∈T, load s z<R z := by
  let potential (k : ℕ) (s : γ) : ℝ :=
    ∑ z∈T, Real.exp (t*load s z+((m : ℝ)-k)*b z-t*R z)
  have hstart : potential 0 s₀<1 := by
    have he : potential 0 s₀=∑ z∈T, Real.exp ((m : ℝ)*b z-t*R z) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hload₀ z hz]
      simp
    rwa [he]
  have hstep : ∀ k < m, ∀ s, Inv k s → potential k s<1 →
      ∃ s', Inv (k+1) s' ∧ potential (k+1) s'<1 := by
    intro k hk s hs hpot
    let U := choices k s
    have hcard : q ≤ (U.card : ℝ) := hchoices k hk s hs
    have hU : U.Nonempty := by
      apply Finset.card_pos.mp
      exact_mod_cast (hq.trans_le hcard)
    letI : Nonempty ↥U := hU.to_subtype
    have hm : mean (fun a : ↥U ↦ potential (k+1) (next k s a.val)) ≤ potential k s := by
      dsimp only [potential]
      rw [mean_sum]
      apply Finset.sum_le_sum
      intro z hz
      let c := t*load s z+((m : ℝ)-(k+1))*b z-t*R z
      have hpoint (a : ↥U) :
          Real.exp (t*load (next k s a.val) z+((m : ℝ)-(k+1 : ℕ))*b z-t*R z) ≤
            Real.exp c*Real.exp (t*(if a.val∈hit k s z then (1 : ℝ) else 0)) := by
        rw [←Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left (hload k hk s hs a.val a.property z hz) ht.le
        dsimp only [c]
        push_cast
        linarith
      have hh := mean_mono _ _ hpoint
      rw [mean_const_mul] at hh
      have hmgf := restricted_hit_mgf U (hit k s z) hU q (K z) t (b z)
        hq hcard (hhit k hk s hs z hz) (hrate z hz)
      apply (hh.trans (mul_le_mul_of_nonneg_left hmgf (Real.exp_pos c).le)).trans_eq
      rw [←Real.exp_add]
      congr 1
      dsimp only [c]
      ring
    obtain ⟨a,ha⟩ := exists_lt_of_mean_lt _ 1 (hm.trans_lt hpot)
    exact ⟨next k s a.val,hnext k hk s hs a.val a.property,ha⟩
  have hex : ∀ k, k ≤ m → ∃ s, Inv k s ∧ potential k s<1 := by
    intro k
    induction k with
    | zero => intro _; exact ⟨s₀,h₀,hstart⟩
    | succ k ih =>
      intro hk
      obtain ⟨s,hs,hp⟩ := ih (by omega)
      exact hstep k (by omega) s hs hp
  obtain ⟨s,hs,hp⟩ := hex m le_rfl
  refine ⟨s,hs,?_⟩
  intro z hz
  have hterm : Real.exp (t*load s z-t*R z) ≤ potential m s := by
    have hh := Finset.single_le_sum (f := fun z ↦ Real.exp (t*load s z+((m : ℝ)-m)*b z-t*R z))
      (fun z _ ↦ (Real.exp_pos _).le) hz
    simpa only [potential,sub_self,zero_mul,add_zero] using hh
  have he := Real.exp_lt_one_iff.mp (hterm.trans_lt hp)
  nlinarith

end Erdos66AdaptiveHitSelection
