import Submission.FiniteSampling

/-! A finite L² almost-periodicity lemma proved by sampling and pigeonhole.
This is a quantitative analytic ingredient, not a settlement of Erdős 3. -/
namespace Erdos3CrootSisaskL2

open Finset Erdos3FiniteSampling
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 1000000

/-- The packing step of the Croot--Sisask argument, without an analytic hypothesis. -/
lemma common_translate_fiber {G I : Type*} [AddCommGroup G] [Fintype I]
    (A S : Finset G) (L : Finset (I → A)) (hS : S.Nonempty) (hL : L.Nonempty) :
    ∃ u : I → G, ∃ T : Finset G, T ⊆ S ∧
      L.card*S.card ≤ (A+S).card^(Fintype.card I)*T.card ∧
      ∀ s ∈ T, ∃ v ∈ L, ∀ i, (v i : G)+s = u i := by
  classical
  let D := ↥L × ↥S
  let P := I → ↥(A+S)
  let h : D → P := fun vs i ↦
    ⟨(vs.1.val i : G)+(vs.2 : G), add_mem_add (vs.1.val i).property vs.2.property⟩
  letI : Nonempty L := hL.to_subtype
  letI : Nonempty S := hS.to_subtype
  letI : Nonempty P := ⟨h (Classical.choice (inferInstance : Nonempty D))⟩
  obtain ⟨u, _, hu⟩ := exists_max_image (univ : Finset P)
    (fun u ↦ (univ.filter (fun vs : D ↦ h vs = u)).card) univ_nonempty
  let F := univ.filter (fun vs : D ↦ h vs = u)
  let T := F.image (fun vs ↦ (vs.2 : G))
  have hinj : Set.InjOn (fun vs : D ↦ (vs.2 : G)) (F : Set D) := by
    intro a ha b hb hs
    change (a.2 : G) = (b.2 : G) at hs
    apply Prod.ext _ (Subtype.ext hs)
    apply Subtype.ext
    funext i
    apply Subtype.ext
    have hh := congrArg (fun v : P ↦ (v i : G))
      ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
    change (a.1.val i : G)+(a.2 : G) = (b.1.val i : G)+(b.2 : G) at hh
    rw [hs] at hh
    exact add_right_cancel hh
  have hTc : T.card = F.card := card_image_of_injOn hinj
  have hcount : Fintype.card D ≤ Fintype.card P * F.card := by
    calc
      Fintype.card D = ∑ u : P, (univ.filter (fun vs : D ↦ h vs = u)).card :=
        card_eq_sum_card_fiberwise (f := h) (t := univ) (by intro x hx; simp)
      _ ≤ ∑ _u : P, F.card := sum_le_sum (fun u hu' ↦ hu u hu')
      _ = _ := by simp
  refine ⟨fun i ↦ (u i : G), T, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨vs, _, rfl⟩ := mem_image.mp hs
    exact vs.2.property
  · simpa only [D, P, Fintype.card_prod, Fintype.card_coe, Fintype.card_fun, ← hTc] using hcount
  · intro s hs
    obtain ⟨vs, hvs, rfl⟩ := mem_image.mp hs
    refine ⟨vs.1.val, vs.1.property, fun i ↦ ?_⟩
    exact congrArg (fun v : P ↦ (v i : G)) (mem_filter.mp hvs).2

section Analytic
variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def smooth (A : Finset G) (f : G → ℝ) (x : G) : ℝ :=
  𝔼 a : A, f (x+(a : G))

noncomputable def empirical {I : Type*} [Fintype I] (v : I → G) (f : G → ℝ) (x : G) : ℝ :=
  𝔼 i, f (x+v i)

def sqNorm (f : G → ℝ) : ℝ := ∑ x, (f x)^2

lemma sum_translate (f : G → ℝ) (s : G) : (∑ x, f (x+s)) = ∑ x, f x :=
  Fintype.sum_equiv (Equiv.addRight s) (fun x ↦ f (x+s)) f (fun _ ↦ rfl)

lemma sample_energy (A : Finset G) (hA : A.Nonempty) (f : G → ℝ) :
    (∑ x : G, 𝔼 a : A, (f (x+(a : G)))^2) = sqNorm f := by
  letI : Nonempty A := hA.to_subtype
  rw [← expect_sum_comm]
  have hs (a : A) : (∑ x : G, (f (x+(a : G)))^2) = sqNorm f :=
    sum_translate (fun x ↦ (f x)^2) a
  simp_rw [hs]
  exact Fintype.expect_const _

/-- L² almost-periodicity with an exact cardinality estimate.
The differences of elements of T are approximate periods of the average of f over A. -/
theorem exists_many_L2_almost_periods (A S : Finset G) (hA : A.Nonempty) (hS : S.Nonempty)
    (f : G → ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ T : Finset G, T ⊆ S ∧
      A.card^n*S.card ≤ 2*(A+S).card^n*T.card ∧
      ∀ s ∈ T, ∀ t ∈ T,
        sqNorm (fun x ↦ smooth A f (x+s) - smooth A f (x+t)) ≤
          (8 / (n : ℝ))*sqNorm f := by
  classical
  letI : Nonempty A := hA.to_subtype
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨L, hLc, hgood⟩ := many_good_samples (I := Fin n) (fun (a : A) (x : G) ↦ f (x+(a : G)))
  have hLc' : A.card^n ≤ 2*L.card := by simpa using hLc
  have hLn : L.Nonempty := by
    have hh : 0 < A.card^n := pow_pos (card_pos.mpr hA) _
    exact card_pos.mp (by omega)
  have hgood' (v : Fin n → A) (hv : v ∈ L) :
      sqNorm (fun x ↦ empirical (fun i ↦ (v i : G)) f x - smooth A f x) ≤
        (2/(n : ℝ))*sqNorm f := by
    simpa only [sqNorm, empirical, smooth, Fintype.card_fin, sample_energy A hA f] using hgood v hv
  obtain ⟨u,T,hTS,hTc,hrep⟩ := common_translate_fiber A S L hS hLn
  refine ⟨T, hTS, ?_, ?_⟩
  · calc
      A.card^n*S.card ≤ (2*L.card)*S.card := Nat.mul_le_mul_right _ hLc'
      _ = 2*(L.card*S.card) := by ring
      _ ≤ 2*((A+S).card^n*T.card) := Nat.mul_le_mul_left 2 (by simpa using hTc)
      _ = _ := by ring
  · intro s hs t ht
    obtain ⟨v,hv,hvs⟩ := hrep s hs
    obtain ⟨w,hw,hwt⟩ := hrep t ht
    have he (z : Fin n → A) (r : G) (hz : ∀ i, (z i : G)+r = u i) (x : G) :
        empirical (fun i ↦ (z i : G)) f (x+r) = empirical u f x := by
      apply expect_congr rfl
      intro i _
      congr 1
      rw [← hz i]
      abel
    have herr (z : Fin n → A) (r : G) (hz : ∀ i, (z i : G)+r = u i) :
        sqNorm (fun x ↦ empirical u f x - smooth A f (x+r)) =
          sqNorm (fun x ↦ empirical (fun i ↦ (z i : G)) f x - smooth A f x) := by
      calc
        _ = ∑ x : G, (empirical (fun i ↦ (z i : G)) f (x+r) - smooth A f (x+r))^2 := by
          simp_rw [he z r hz]
          rfl
        _ = _ := sum_translate (fun x ↦
          (empirical (fun i ↦ (z i : G)) f x - smooth A f x)^2) r
    have hes : sqNorm (fun x ↦ empirical u f x - smooth A f (x+s)) ≤
        (2/(n : ℝ))*sqNorm f := by rw [herr v s hvs]; exact hgood' v hv
    have het : sqNorm (fun x ↦ empirical u f x - smooth A f (x+t)) ≤
        (2/(n : ℝ))*sqNorm f := by rw [herr w t hwt]; exact hgood' w hw
    calc
      _ ≤ ∑ x : G, (2*(empirical u f x - smooth A f (x+s))^2 +
          2*(empirical u f x - smooth A f (x+t))^2) := by
        apply sum_le_sum
        intro x _
        nlinarith [sq_nonneg ((empirical u f x - smooth A f (x+s)) +
          (empirical u f x - smooth A f (x+t)))]
      _ = 2*sqNorm (fun x ↦ empirical u f x - smooth A f (x+s)) +
          2*sqNorm (fun x ↦ empirical u f x - smooth A f (x+t)) := by
        simp only [sqNorm, sum_add_distrib, mul_sum]
      _ ≤ 2*((2/(n : ℝ))*sqNorm f) + 2*((2/(n : ℝ))*sqNorm f) := by gcongr
      _ = _ := by ring

end Analytic
#print axioms common_translate_fiber
#print axioms exists_many_L2_almost_periods
end Erdos3CrootSisaskL2
