import Submission.LocalRootUpperBasic
import Submission.LocalSeedLifting

/-! Large primes lose only a small fraction of the nonsingular seeds. These
are congruence bounds, not fixed-positive-power bounds on exact counts. -/
namespace Erdos322Research.LocalSharpSeedDensity
noncomputable section
open Finset LocalPeakCounting LocalSeedDensity LocalSeedLifting LocalRootUpperBasic
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

/-- A power-sum fiber in s+1 variables has at most K times the tail volume. -/
theorem field_sum_fiber_bound (p s K : ℕ) [Fact p.Prime] (hK : 0 < K)
    (a : ZMod p) :
    Fintype.card {x : Fin (s+1) → ZMod p // ∑ i, x i^K=a} ≤ K*p^s := by
  let A := {x : Fin (s+1) → ZMod p // ∑ i, x i^K=a}
  let tail : A → (Fin s → ZMod p) := fun x j ↦ x.val j.succ
  have hf (t : Fin s → ZMod p) : Fintype.card {x : A // tail x=t} ≤ K := by
    let b := a-∑ j, t j^K
    let f : {x : A // tail x=t} → {z : ZMod p // z^K=b} := fun x ↦
      ⟨x.val.val 0, by
        have hs := x.val.property
        rw [Fin.sum_univ_succ] at hs
        have ht (j : Fin s) : x.val.val j.succ=t j := congrFun x.property j
        simp only [ht] at hs
        dsimp only [b]
        linear_combination hs⟩
    have hi : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact congrArg Subtype.val h
      · exact (congrFun x.property j).trans (congrFun y.property j).symm
    exact (Fintype.card_le_of_injective f hi).trans (field_power_fiber_bound p K hK b)
  have hh := finite_fiber_bound tail K hf
  simpa only [Fintype.card_fun,Fintype.card_fin,ZMod.card,mul_comm] using hh

/-- Discarding roots with first coordinate zero costs at most K*p^(K-2). -/
theorem root_count_le_first_seed_add (k p : ℕ) [Fact p.Prime] :
    rootCount (k+2) p ≤ firstSeedCount k p+(k+2)*p^k := by
  let T := {x : Fin (k+1) → ZMod p // ∑ i, x i^(k+2)=0}
  let f : FirstSeeds k p ⊕ T → RingRoots (k+2) (ZMod p) := fun x ↦ match x with
    | .inl s => ⟨s.val,s.property.1⟩
    | .inr t => ⟨Fin.cons 0 t.val,by
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero,Fin.cons_succ,
          zero_pow (by omega : k+2 ≠ 0),zero_add]
        exact t.property⟩
  have hf : Function.Surjective f := by
    intro x
    by_cases hx : x.val 0=0
    · let t : T := ⟨fun j ↦ x.val j.succ,by
        have hs := x.property
        rw [Fin.sum_univ_succ,hx,zero_pow (by omega : k+2 ≠ 0),zero_add] at hs
        exact hs⟩
      refine ⟨.inr t,?_⟩
      apply Subtype.ext
      funext i
      refine Fin.cases hx.symm (fun _ ↦ rfl) i
    · exact ⟨.inl ⟨x.val,x.property,hx⟩,rfl⟩
  have hc := Fintype.card_le_of_surjective f hf
  have ht := field_sum_fiber_bound p k (k+2) (by omega) 0
  have he := Fintype.card_congr (rootsEquiv (k+2) p)
  change Fintype.card T ≤ (k+2)*p^k at ht
  rw [Fintype.card_sum] at hc
  rw [rootCount,he,firstSeedCount]
  exact hc.trans (Nat.add_le_add_left ht (Fintype.card (FirstSeeds k p)))

/-- The seed-density loss tends to zero as the prime tends to infinity. -/
theorem nearly_full_first_seeds (k p M : ℕ) [Fact p.Prime]
    (hM : 1 ≤ M) (hp : M*(k+2) ≤ p)
    (hroot : p^(k+1) ≤ rootCount (k+2) p) :
    (M-1)*p^(k+1) ≤ M*firstSeedCount k p := by
  have h := hroot.trans (root_count_le_first_seed_add k p)
  have hm := Nat.mul_le_mul_left M h
  have hb := Nat.mul_le_mul_right (p^k) hp
  have he : p^(k+1)=p*p^k := by rw [pow_succ']
  rw [← he] at hb
  have hsub : M-1+1=M := by omega
  nlinarith

/-- At depth K the singular contribution adds a full unit of normalized
volume. The resulting density approaches two, uniformly in large primes. -/
theorem density_at_degree (k p M : ℕ) [Fact p.Prime]
    (hk : ¬p ∣ k+2) (hM : 1 ≤ M) (hp : M*(k+2) ≤ p)
    (hroot : p^(k+1) ≤ rootCount (k+2) p) :
    (2*M-1)*(p^(k+2))^(k+1) ≤ M*rootCount (k+2) (p^(k+2)) := by
  have hs := nearly_full_first_seeds k p M hM hp hroot
  have hstep := rootCount_seed_step p 0 k hk
  have hz : rootCount (k+2) 1=1 := by simp [rootCount,Roots]
  simp only [zero_add,pow_zero,hz,one_mul] at hstep
  have hm := Nat.mul_le_mul_left M hstep
  have hb := Nat.mul_le_mul_right (p^((k+1)*(k+1))) hs
  have he : p^(k+1)*p^((k+1)*(k+1))=p^((k+2)*(k+1)) := by
    rw [← pow_add]
    congr 1
    ring
  have hb' : (M-1)*p^((k+2)*(k+1)) ≤
      M*(firstSeedCount k p*p^((k+1)*(k+1))) := by
    simpa only [mul_assoc,he] using hb
  rw [← pow_mul]
  have hsub : M-1+1=M := by omega
  have hsub' : 2*M-1=M+(M-1) := by omega
  rw [hsub',add_mul]
  nlinarith

end
end Erdos322Research.LocalSharpSeedDensity
