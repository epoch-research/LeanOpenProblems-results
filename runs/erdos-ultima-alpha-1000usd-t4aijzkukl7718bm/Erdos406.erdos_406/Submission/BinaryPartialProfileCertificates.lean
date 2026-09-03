import Submission.BinaryEvenProfileCertificates

/-! Partial-acceptance profile certificates. Accepted runs for ternary-good
inputs follow from construction, so universal acceptance is unnecessary.
No strictly supercritical instance is asserted. -/
namespace Erdos406BinaryPartialProfile
open Erdos406Tropical (Automaton Run)
open Erdos406BinaryAcceptingMinplus
open Erdos406BinaryProfileMinplus
open Erdos406BinaryWeighted
open Erdos406AffineCertificate Erdos406GroupedCertificate

variable {σ τ : Type*} [Fintype σ] [DecidableEq σ]
variable {D : Automaton σ} {F : σ → Prop}

/-- Starting with the empty accepted run, ternary construction produces an
accepted run of cost at most the ternary length, only where it is needed. -/
lemma exists_good_run (C : Erdos406BinaryProfileMinplus.Construction D F τ)
    (hstart : F D.start) (n : ℕ) (hg : Nat.digits 3 n ⊆ [0,1]) :
    ∃ t v, Run D D.start (Nat.digits 2 n).reverse t v ∧ F t ∧
      v ≤ (Nat.digits 3 n).length := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      exact ⟨D.start,0,by simpa using Run.nil D.start,hstart,by simp⟩
    have hp : 0<n := Nat.pos_of_ne_zero hn
    obtain ⟨s,v,hr,hF,hv⟩ := ih (n/3) (Nat.div_lt_self hp (by decide)) (good_div_three hg)
    have hd : n%3<2 := by
      rcases good_unit_mod_three hp hg with hd | hd <;> omega
    obtain ⟨p,hp',hprof⟩ := C.simulate (n/3) (n%3) (by omega) hr
    obtain ⟨t,ht,hFt,hH⟩ := C.finish s p (n%3) hd hp' hF
    obtain ⟨u,hu,hbound⟩ := hprof t ht
    have he : 3*(n/3)+n%3=n := by omega
    rw [he] at hu
    refine ⟨t,u,hu,hFt,?_⟩
    rw [Nat.digits_of_two_le_of_pos (by decide : 2≤3) hp,List.length_cons]
    push_cast
    linarith

/-- Abstract partial-run criterion. It never assigns a value to an integer
without an accepted run, nor assumes every integer is accepted. -/
theorem accepted_run_criterion (C : Erdos406BinaryProfileMinplus.Construction D F τ)
    (hstart : F D.start) (a B : ℝ)
    (hpower : ∀ (k : ℕ) t v, Even k →
      Run D D.start (Nat.digits 2 (2^k)).reverse t v → F t → a*k-B ≤ v)
    (hcrit : Real.log 2 < a*Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hgap : 0 < a*Real.log 3-Real.log 2 := by linarith
  obtain ⟨M,hM⟩ := exists_nat_gt ((B+1)*Real.log 3/(a*Real.log 3-Real.log 2))
  have hlarge := (div_lt_iff₀ hgap).mp hM
  have hcut (k : ℕ) (hk : M≤k) : ¬ Nat.digits 3 (2^k) ⊆ [0,1] := by
    intro hg
    obtain ⟨t,v,hr,hF,hv⟩ := exists_good_run C hstart (2^k) hg
    have hp := hpower k t v (Erdos406BinaryEvenProfile.even_exponent hg) hr hF
    have hb := mul_le_mul_of_nonneg_right (hp.trans hv) hlog.le
    have hlen := ternary_power_length_log k
    have hMk : (M : ℝ)≤k := by exact_mod_cast hk
    have hkm := mul_le_mul_of_nonneg_right hMk hgap.le
    nlinarith
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨2^M,?_⟩
  rintro n ⟨⟨k,rfl⟩,hg⟩
  by_cases hk : k<M
  · exact Nat.pow_le_pow_right (by decide) (by omega)
  · exact (hcut k (by omega) hg).elim

/-- All-exponent lower tables can be used without universal acceptance. -/
theorem partial_profile_minplus_criterion
    (C : Erdos406BinaryProfileMinplus.Construction D F τ)
    (hstart : F D.start) (P : Erdos406BinaryAcceptingMinplus.PowerBound D F)
    (hcrit : Real.log 2 < P.a*Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  apply accepted_run_criterion C hstart P.a P.B _ hcrit
  intro k t v _ hr hF
  have hword : (Nat.digits 2 (2^k)).reverse = 1::List.replicate k 0 := by
    have hh := Nat.digits_base_pow_mul (b:=2) (k:=k) (m:=1) (by decide) (by decide)
    simpa using congrArg List.reverse hh
  exact P.power_run_lower k (hword ▸ hr) hF

/-- Parity-restricted lower tables likewise need accepted runs only for good
inputs; a strictly supercritical table is still an unsupplied hypothesis. -/
theorem partial_even_profile_minplus_criterion
    (C : Erdos406BinaryProfileMinplus.Construction D F τ)
    (hstart : F D.start) (P : Erdos406BinaryEvenProfile.PowerBound D F)
    (hcrit : Real.log 2 < P.a*Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  apply accepted_run_criterion C hstart P.a P.B _ hcrit
  intro k t v hk hr hF
  obtain ⟨m,rfl⟩ := hk
  have he : m+m=2*m := by omega
  rw [he] at hr ⊢
  have hword : (Nat.digits 2 (2^(2*m))).reverse = 1::List.replicate (2*m) 0 := by
    have hh := Nat.digits_base_pow_mul (b:=2) (k:=2*m) (m:=1) (by decide) (by decide)
    simpa using congrArg List.reverse hh
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using P.power_run_lower m (hword ▸ hr) hF

end Erdos406BinaryPartialProfile
