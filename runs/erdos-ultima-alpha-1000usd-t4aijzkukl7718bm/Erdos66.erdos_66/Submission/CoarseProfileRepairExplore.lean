import Submission.CoarseCountingExplore

/-! A fixed finite template can be amplified while adjoining it to any set
with a specified logarithmic representation envelope. The sufficiently-large
threshold depends on the fixed template and block width. -/
namespace Erdos66CoarseProfileRepair
open Filter AdditiveCombinatorics Erdos66CoarseCounting Erdos66TemplatePacket
  Erdos66LocalizedRepair
open scoped Topology Classical
set_option maxHeartbeats 1500000

lemma log_mono_shift {a b : ℕ} (h : a ≤ b) :
    Real.log ((a : ℝ)+2) ≤ Real.log ((b : ℝ)+2) := by
  apply Real.log_le_log (by positivity)
  exact_mod_cast Nat.add_le_add_right h 2

lemma log_shift_nonneg (n : ℕ) : 0 ≤ Real.log ((n : ℝ)+2) :=
  Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)

/-- Exact self and union counts at the coarse center imply that there are no
mixed representations there. The same error budget controls both components
off center. -/
lemma coarse_control (B : Set ℕ) (P : Finset ℕ) (q m : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : Disjoint B (P : Set ℕ))
    (hself : sumRep (P : Set ℕ) q=2*m)
    (hcenter : sumRep (B ∪ (P : Set ℕ)) q=sumRep B q+2*m)
    (hoff : ∀ z, z ≠ q → (sumRep (B ∪ (P : Set ℕ)) z : ℝ)-sumRep B z ≤
      δ*Real.log ((z : ℝ)+2)) (z : ℕ) :
    0 ≤ (sumRep (P : Set ℕ) z : ℝ)-(if z=q then 2*(m : ℝ) else 0) ∧
    (sumRep (P : Set ℕ) z : ℝ)-(if z=q then 2*(m : ℝ) else 0) ≤ δ*Real.log ((z : ℝ)+2) ∧
    2*(mixed B P z : ℝ) ≤ δ*Real.log ((z : ℝ)+2) := by
  have he := union_rep B P z hd
  have he' : (sumRep (B ∪ (P : Set ℕ)) z : ℝ) =
      sumRep B z+2*(mixed B P z : ℝ)+sumRep (P : Set ℕ) z := by exact_mod_cast he
  by_cases hz : z=q
  · subst z
    have hmixed : mixed B P q=0 := by omega
    rw [if_pos rfl, hself, hmixed]
    push_cast
    have hh := mul_nonneg hδ (log_shift_nonneg q)
    exact ⟨by ring_nf; rfl,by linarith,by simpa using hh⟩
  · rw [if_neg hz, sub_zero]
    have h := hoff z hz
    have h₁ := Nat.cast_nonneg (α := ℝ) (mixed B P z)
    have h₂ := Nat.cast_nonneg (α := ℝ) (sumRep (P : Set ℕ) z)
    exact ⟨h₂,by linarith,by linarith⟩

/-- Quantitative lifting estimate, with an explicit factor of three times the
low template's cardinality. -/
theorem tensor_repair_bound (A : Set ℕ) (M : ℕ) (hM : 0 < M) (P S : Finset ℕ)
    (hS : ∀ s∈S, s < M) (hSS : ∀ s∈S, ∀ t∈S, s+t < M)
    (q m : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : Disjoint (coarse A M) (P : Set ℕ))
    (hc : ∀ z, 0 ≤ (sumRep (P : Set ℕ) z : ℝ)-(if z=q then 2*(m : ℝ) else 0) ∧
      (sumRep (P : Set ℕ) z : ℝ)-(if z=q then 2*(m : ℝ) else 0) ≤ δ*Real.log ((z : ℝ)+2) ∧
      2*(mixed (coarse A M) P z : ℝ) ≤ δ*Real.log ((z : ℝ)+2)) (n : ℕ) :
    0 ≤ (sumRep (A ∪ (tensor M P S : Set ℕ)) n : ℝ)-sumRep A n-
      (if n/M=q then 2*(m : ℝ)*sumRep (S : Set ℕ) (n%M) else 0) ∧
    (sumRep (A ∪ (tensor M P S : Set ℕ)) n : ℝ)-sumRep A n-
      (if n/M=q then 2*(m : ℝ)*sumRep (S : Set ℕ) (n%M) else 0)
      ≤ (3*(S.card : ℝ)*δ)*Real.log ((n : ℝ)+2) := by
  let k := n/M
  let t := n%M
  let E : ℝ := (sumRep (P : Set ℕ) k : ℝ)-(if k=q then 2*(m : ℝ) else 0)
  have hk : k ≤ n := Nat.div_le_self _ _
  have hk' : k-1 ≤ n := (Nat.sub_le _ _).trans hk
  have hE : 0 ≤ E := (hc k).1
  have hElim : E ≤ δ*Real.log ((n : ℝ)+2) :=
    (hc k).2.1.trans (mul_le_mul_of_nonneg_left (log_mono_shift hk) hδ)
  have hmix₁ : 2*(mixed (coarse A M) P k : ℝ) ≤ δ*Real.log ((n : ℝ)+2) :=
    (hc k).2.2.trans (mul_le_mul_of_nonneg_left (log_mono_shift hk) hδ)
  have hmix₂ : 2*(mixed (coarse A M) P (k-1) : ℝ) ≤ δ*Real.log ((n : ℝ)+2) :=
    (hc (k-1)).2.2.trans (mul_le_mul_of_nonneg_left (log_mono_shift hk') hδ)
  have hmix : 2*(mixed A (tensor M P S) n : ℝ) ≤
      (2*(S.card : ℝ)*δ)*Real.log ((n : ℝ)+2) := by
    have hraw : (mixed A (tensor M P S) n : ℝ) ≤
        ((mixed (coarse A M) P k : ℝ)+mixed (coarse A M) P (k-1))*S.card := by
      exact_mod_cast tensor_mixed_le A M hM P S hS n
    have hh := mul_le_mul_of_nonneg_right (add_le_add hmix₁ hmix₂) (Nat.cast_nonneg (α := ℝ) S.card)
    nlinarith
  have hlow : (sumRep (S : Set ℕ) t : ℝ) ≤ S.card := by exact_mod_cast finite_rep_le_card S t
  have hlow0 := Nat.cast_nonneg (α := ℝ) (sumRep (S : Set ℕ) t)
  have hprod : E*sumRep (S : Set ℕ) t ≤ ((S.card : ℝ)*δ)*Real.log ((n : ℝ)+2) := by
    calc
      _ ≤ E*S.card := mul_le_mul_of_nonneg_left hlow hE
      _ ≤ (δ*Real.log ((n : ℝ)+2))*S.card :=
        mul_le_mul_of_nonneg_right hElim (Nat.cast_nonneg _)
      _ = _ := by ring
  have hself : (sumRep (tensor M P S : Set ℕ) n : ℝ)=
      (sumRep (P : Set ℕ) k : ℝ)*sumRep (S : Set ℕ) t := by
    have hh := tensor_rep M hM P S hS hSS k t (Nat.mod_lt n hM)
    have he : k*M+t=n := Nat.div_add_mod' _ _
    rw [he] at hh
    exact_mod_cast hh
  have hdis := tensor_disjoint A M hM P S hS hd
  have he : (sumRep (A ∪ (tensor M P S : Set ℕ)) n : ℝ) =
      sumRep A n+2*(mixed A (tensor M P S) n : ℝ)+sumRep (tensor M P S : Set ℕ) n := by
    exact_mod_cast union_rep A (tensor M P S) n hdis
  have herr : (sumRep (A ∪ (tensor M P S : Set ℕ)) n : ℝ)-sumRep A n-
      (if n/M=q then 2*(m : ℝ)*sumRep (S : Set ℕ) (n%M) else 0) =
        2*(mixed A (tensor M P S) n : ℝ)+E*sumRep (S : Set ℕ) t := by
    rw [he,hself]
    dsimp [E,k,t]
    split_ifs <;> ring
  rw [herr]
  constructor
  · exact add_nonneg (by positivity) (mul_nonneg hE hlow0)
  · nlinarith

/-- Universal repair for a fixed finite profile. The template and width are
fixed before taking the sufficiently large center. This does not assert a
near-scale repair for growing templates. -/
theorem eventually_fixed_profile_repair (M : ℕ) (hM : 0 < M) (S : Finset ℕ)
    (hS : ∀ s∈S, s < M) (hSS : ∀ s∈S, ∀ t∈S, s+t < M)
    (D ε K C : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∀ᶠ q : ℕ in atTop, ∀ A : Set ℕ,
      (∀ z, (sumRep A z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2)) →
      ∀ m : ℕ, (m : ℝ) ≤ D*Real.log q →
      ∃ F : Finset ℕ, F.card=2*m*S.card ∧ Disjoint A (F : Set ℕ) ∧
        (∀ a∈F, q*M ≤ 4*a ∧ 3*a ≤ (2*q+6)*M) ∧
        ∀ n : ℕ,
          0 ≤ (sumRep (A ∪ (F : Set ℕ)) n : ℝ)-sumRep A n-
            (if n/M=q then 2*(m : ℝ)*sumRep (S : Set ℕ) (n%M) else 0) ∧
          (sumRep (A ∪ (F : Set ℕ)) n : ℝ)-sumRep A n-
            (if n/M=q then 2*(m : ℝ)*sumRep (S : Set ℕ) (n%M) else 0)
            ≤ ε*Real.log ((n : ℝ)+2) := by
  let δ := ε/(3*(S.card : ℝ)+1)
  have hden : 0 < 3*(S.card : ℝ)+1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδε : 3*(S.card : ℝ)*δ ≤ ε := by
    have he : δ*(3*(S.card : ℝ)+1)=ε := div_mul_cancel₀ ε hden.ne'
    nlinarith
  let K' : ℝ := (2*M : ℕ)*(K+C*Real.log (2*(M : ℝ)))
  let C' : ℝ := (2*M : ℕ)*C
  have hlogM : 0 ≤ Real.log (2*(M : ℝ)) := by
    apply Real.log_nonneg
    have hh : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hK' : 0 ≤ K' := by dsimp [K']; positivity
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  filter_upwards [eventually_localized_repair D δ K' C' hD hδ hK' hC'] with q hq
  intro A hA m hm
  obtain ⟨P,hPc,hPd,hPb,hPself,hPcenter,hPoff⟩ :=
    hq (coarse A M) (coarse_log_bound A M hM K C hC hA) m hm
  refine ⟨tensor M P S,?_,tensor_disjoint A M hM P S hS hPd,?_,?_⟩
  · rw [tensor_card M hM P S hS,hPc]
  · intro a ha
    obtain ⟨ps,hps,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hp,hs⟩ := Finset.mem_product.mp hps
    have hpb := hPb ps.1 hp
    have hsb := hS ps.2 hs
    have h₁ := Nat.mul_le_mul_right M hpb.1
    have h₂ := Nat.mul_le_mul_right M hpb.2
    constructor <;> nlinarith
  · intro n
    have hc := coarse_control (coarse A M) P q m δ hδ.le hPd hPself hPcenter
      (fun z hz ↦ (hPoff z hz).2)
    have hh := tensor_repair_bound A M hM P S hS hSS q m δ hδ.le hPd hc n
    exact ⟨hh.1,hh.2.trans (mul_le_mul_of_nonneg_right hδε (log_shift_nonneg n))⟩

end Erdos66CoarseProfileRepair
