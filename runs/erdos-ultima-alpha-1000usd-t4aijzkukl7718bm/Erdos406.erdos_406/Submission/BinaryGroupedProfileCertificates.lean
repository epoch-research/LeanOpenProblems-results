import Submission.BinaryPartialProfileCertificates

/-! Soundness of grouped ternary construction with binary output profiles.
The strict numerical certificate remains an explicit unsupplied hypothesis. -/
namespace Erdos406BinaryGroupedProfile
open Erdos406GroupedCertificate
open Erdos406Tropical (Automaton Run)
open Erdos406BinaryAcceptingMinplus
variable {σ τ : Type*} [Fintype σ] [DecidableEq σ]

structure Construction (h : ℕ) (D : Automaton σ) (F : σ → Prop) (τ : Type*) where
  endpoints : τ → σ → Prop
  R : σ → τ → ℕ → Prop
  H : σ → τ → ℕ → σ → ℝ
  seed : ∀ c, c < 3^h → ∃ p, R D.start p c ∧ ∀ t, endpoints p t →
    ∃ v, Run D D.start (Nat.digits 2 c).reverse t v ∧ v ≤ H D.start p c t
  step : ∀ s p c d e cp, c < 3^h → d < 2 → e < 2 → cp < 3^h →
    3^h*d+cp = 2*c+e → R s p c → ∀ sp, sp ∈ D.next s d →
    ∃ pp, R sp pp cp ∧ ∀ tp, endpoints pp tp →
      ∃ t, endpoints p t ∧ tp ∈ D.next t e ∧
        H s p c t+D.weight t e tp-D.weight s d sp ≤ H sp pp cp tp
  finish : ∀ s p c, GoodBlock h c → R s p c → F s →
    ∃ t, endpoints p t ∧ F t ∧ H s p c t ≤ h

namespace Construction
variable {h : ℕ} {D : Automaton σ} {F : σ → Prop}
    (C : Construction h D F τ)
include C

lemma simulate (n c : ℕ) (hc : c < 3^h) {s v}
    (hin : Run D D.start (Nat.digits 2 n).reverse s v) :
    ∃ p, C.R s p c ∧ ∀ t, C.endpoints p t →
      ∃ u, Run D D.start (Nat.digits 2 (3^h*n+c)).reverse t u ∧
        u-v ≤ C.H s p c t := by
  induction n using Nat.strong_induction_on generalizing c s v with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp only [Nat.digits_zero,List.reverse_nil] at hin
      cases hin
      obtain ⟨p,hr,hp⟩ := C.seed c hc
      refine ⟨p,hr,?_⟩
      intro t ht
      obtain ⟨u,hu,hh⟩ := hp t ht
      exact ⟨u,by simpa using hu,by simpa using hh⟩
    · have hp : 0 < n := Nat.pos_of_ne_zero hn
      let d := n%2
      let cp := (3^h*d+c)/2
      let e := (3^h*d+c)%2
      have hd : d < 2 := Nat.mod_lt _ (by decide)
      have he : e < 2 := Nat.mod_lt _ (by decide)
      have hcp : cp < 3^h := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr
        have hmd : 3^h*d ≤ 3^h := by
          simpa using Nat.mul_le_mul_left (3^h) (show d≤1 by omega)
        omega
      have hid : 3^h*d+c = 2*cp+e := by dsimp [cp,e]; omega
      rw [Nat.digits_of_two_le_of_pos (by decide : 2≤2) hp,List.reverse_cons] at hin
      obtain ⟨s0,a,hs0,hs,hv⟩ := hin.split_last
      obtain ⟨p,hr,hp0⟩ := ih (n/2) (Nat.div_lt_self hp (by decide)) cp hcp hs0
      obtain ⟨pp,hr',hstep⟩ := C.step s0 p cp d e c hcp hd he hc hid hr s hs
      refine ⟨pp,hr',?_⟩
      intro t ht
      obtain ⟨q,hq,hqt,hw⟩ := hstep t ht
      obtain ⟨b,hb,hbound⟩ := hp0 q hq
      have hout : 0 < 3^h*n+c := by positivity
      obtain ⟨heq,hmod⟩ := affine_div_mod 2 (3^h) n c (by decide)
      refine ⟨b+D.weight q e t,?_,?_⟩
      · rw [Nat.digits_of_two_le_of_pos (by decide : 2≤2) hout,
          List.reverse_cons,heq,hmod]
        exact hb.snoc hqt
      · dsimp only [d] at hw
        linarith

lemma exists_good_run (hh : 0<h) (hstart : F D.start) (n : ℕ)
    (hg : Nat.digits 3 n ⊆ [0,1]) :
    ∃ t v, Run D D.start (Nat.digits 2 n).reverse t v ∧ F t ∧
      v ≤ (h:ℝ)*(Nat.digits (3^h) n).length := by
  have hm : 2 ≤ 3^h := by
    have := one_lt_pow₀ (by decide : 1<(3:ℕ)) (Nat.ne_of_gt hh)
    omega
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      exact ⟨D.start,0,by simpa using Run.nil D.start,hstart,by simp⟩
    have hp : 0<n := Nat.pos_of_ne_zero hn
    obtain ⟨s,v,hr,hF,hv⟩ := ih (n/(3^h)) (Nat.div_lt_self hp hm)
      (Erdos406SparseTriple.good_div_pow hg h)
    have hd : GoodBlock h (n%(3^h)) :=
      ⟨Nat.mod_lt _ (by positivity),Erdos406SparseTriple.good_mod_pow hg h⟩
    obtain ⟨p,hp',hprof⟩ := C.simulate (n/(3^h)) (n%(3^h)) hd.1 hr
    obtain ⟨t,ht,hFt,hH⟩ := C.finish s p (n%(3^h)) hd hp' hF
    obtain ⟨u,hu,hbound⟩ := hprof t ht
    have he : 3^h*(n/(3^h))+n%(3^h)=n := by
      simpa [Nat.add_comm] using Nat.mod_add_div n (3^h)
    rw [he] at hu
    refine ⟨t,u,hu,hFt,?_⟩
    rw [Nat.digits_of_two_le_of_pos hm hp,List.length_cons]
    push_cast
    nlinarith
end Construction

lemma grouped_power_length_log (h k : ℕ) (hh : 0<h) :
    (h:ℝ)*(Nat.digits (3^h) (2^k)).length*Real.log 3 ≤
      (k:ℝ)*Real.log 2+(h:ℝ)*Real.log 3 := by
  have hm : 1 < 3^h := one_lt_pow₀ (by decide : 1<(3:ℕ)) (Nat.ne_of_gt hh)
  have hh' := Nat.base_pow_length_digits_le (3^h) (2^k) hm (by positivity)
  have hp : ((3:ℝ)^h)^(Nat.digits (3^h) (2^k)).length ≤
      (3:ℝ)^h*(2:ℝ)^k := by exact_mod_cast hh'
  have hl := Real.log_le_log (by positivity) hp
  rw [Real.log_pow,Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow] at hl
  nlinarith

/-- A strict grouped certificate implies the original finiteness statement.
This theorem does not assert existence of such a certificate. -/
theorem grouped_profile_minplus_criterion {h : ℕ} {D : Automaton σ} {F : σ → Prop}
    (C : Construction h D F τ) (hh : 0<h) (hstart : F D.start)
    (P : PowerBound D F) (hcrit : Real.log 2 < P.a*Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hgap : 0 < P.a*Real.log 3-Real.log 2 := by linarith
  obtain ⟨M,hM⟩ := exists_nat_gt ((P.B+(h:ℝ))*Real.log 3/
    (P.a*Real.log 3-Real.log 2))
  have hlarge := (div_lt_iff₀ hgap).mp hM
  have hcut (k : ℕ) (hk : M≤k) : ¬ Nat.digits 3 (2^k) ⊆ [0,1] := by
    intro hg
    obtain ⟨t,v,hr,hF,hv⟩ := C.exists_good_run hh hstart (2^k) hg
    have hword : (Nat.digits 2 (2^k)).reverse = 1::List.replicate k 0 := by
      have hx := Nat.digits_base_pow_mul (b:=2) (k:=k) (m:=1) (by decide) (by decide)
      simpa using congrArg List.reverse hx
    have hp := P.power_run_lower k (hword ▸ hr) hF
    have hb := mul_le_mul_of_nonneg_right (hp.trans hv) hlog.le
    have hlen := grouped_power_length_log h k hh
    have hMk : (M:ℝ)≤k := by exact_mod_cast hk
    have hkm := mul_le_mul_of_nonneg_right hMk hgap.le
    nlinarith
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨2^M,?_⟩
  rintro n ⟨⟨k,rfl⟩,hg⟩
  by_cases hk : k<M
  · exact Nat.pow_le_pow_right (by decide) (by omega)
  · exact (hcut k (by omega) hg).elim

end Erdos406BinaryGroupedProfile
