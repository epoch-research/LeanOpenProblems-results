import Submission.LocalPeakCounting
import Submission.Spec

/-! Exact representation-count consequences of prime-power concentration.
These are logarithmic, not positive-power, lower bounds. -/
namespace Erdos322Research.LocalPowerPeaks
noncomputable section
open Finset LocalPeakCounting
set_option maxHeartbeats 0

private lemma tuple_sum_bound (k q : ℕ) (hk : 0 < k) (x : Fin k → Fin q) :
    ∑ i, (x i : ℕ)^k ≤ q*(k*q^(k-1)) := by
  calc
    ∑ i, (x i : ℕ)^k ≤ ∑ _i : Fin k, q^k := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.pow_le_pow_left (x i).isLt.le _
    _ = k*q^k := by simp
    _ = q*(k*q^(k-1)) := by
      conv_lhs => arg 2; rw [← Nat.sub_add_cancel (show 1 ≤ k by omega),pow_succ]
      ring

private def quotientTarget (k q : ℕ) (hk : 0 < k) (hq : 0 < q) (x : Roots k q) :
    Fin (k*q^(k-1)+1) :=
  ⟨(∑ i, (x.val i : ℕ)^k)/q,by
    have hh := Nat.div_le_div_right (c := q) (tuple_sum_bound k q hk x.val)
    rw [Nat.mul_div_cancel_left _ hq] at hh
    omega⟩

private lemma quotientTarget_sum (k q : ℕ) (hk : 0 < k) (hq : 0 < q) (x : Roots k q) :
    ∑ i, (x.val i : ℕ)^k=q*(quotientTarget k q hk hq x : ℕ) :=
  (Nat.mul_div_cancel' x.property).symm

private lemma fiber_card_le (k q : ℕ) (hk : 0 < k) (hq : 0 < q)
    (y : Fin (k*q^(k-1)+1)) :
    Fintype.card {x : Roots k q // quotientTarget k q hk hq x=y} ≤
      Erdos322.representationCount k (q*(y : ℕ)) := by
  classical
  let T := {x : Roots k q // quotientTarget k q hk hq x=y}
  let U := {b : Fin k → Fin (q*(y : ℕ)+1) // ∑ i, (b i : ℕ)^k=q*(y : ℕ)}
  have hs (x : T) : ∑ i, (x.val.val i : ℕ)^k=q*(y : ℕ) := by
    rw [quotientTarget_sum k q hk hq x.val,x.property]
  let f : T → U := fun x ↦ ⟨fun i ↦ ⟨(x.val.val i : ℕ),by
    have hle : (x.val.val i : ℕ) ≤ (x.val.val i : ℕ)^k := Nat.le_pow (by omega)
    have hh := Finset.single_le_sum (f := fun j : Fin k ↦ (x.val.val j : ℕ)^k)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    rw [hs x] at hh
    change (x.val.val i : ℕ)^k ≤ q*(y : ℕ) at hh
    omega⟩,hs x⟩
  have hf : Function.Injective f := by
    intro x z h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrArg (fun b : U ↦ (b.val i : ℕ)) h
  have hh := Fintype.card_le_of_injective f hf
  change Fintype.card T ≤ Fintype.card U at hh
  simpa only [T,U,Fintype.card_subtype,Erdos322.representationCount] using hh

/-- A modular count larger than the number of possible exact targets forces
an exact peak. No formula for the integer representations is assumed. -/
theorem peak_of_rootCount (k q M : ℕ) (hk : 0 < k) (hq : 0 < q) (hM : 1 ≤ M)
    (hsize : (k*q^(k-1)+1)*M < rootCount k q) :
    ∃ n : ℕ, 0 < n ∧ M < Erdos322.representationCount k n ∧ n ≤ k*q^k := by
  classical
  have hfsize : Fintype.card (Fin (k*q^(k-1)+1))*M < Fintype.card (Roots k q) := by
    simpa only [rootCount,Fintype.card_fin] using hsize
  obtain ⟨y,hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (quotientTarget k q hk hq) hfsize
  have hfiber := fiber_card_le k q hk hq y
  rw [Fintype.card_subtype] at hfiber
  have hycount := hy.trans_le hfiber
  refine ⟨q*(y : ℕ),?_,hycount,?_⟩
  · by_contra hn
    have hz : q*(y : ℕ)=0 := by omega
    rw [hz] at hycount
    have hzero : Erdos322.representationCount k 0=1 := by simp [Erdos322.representationCount,hk.ne']
    rw [hzero] at hycount
    omega
  · have hybound : (y : ℕ) ≤ k*q^(k-1) := Nat.le_of_lt_succ y.isLt
    calc
      q*(y : ℕ) ≤ q*(k*q^(k-1)) := Nat.mul_le_mul_left q hybound
      _ = k*q^k := by
        conv_rhs => arg 2; rw [← Nat.sub_add_cancel (show 1 ≤ k by omega),pow_succ]
        ring

/-- Congruence concentration produces exact counts exceeding any prescribed
integer, with an exponential upper bound on the required target. -/
theorem peak_from_good_prime (p k : ℕ) [Fact p.Prime]
    (hk : ¬p ∣ k+2) (a : ZMod p) (ha : a ≠ 0) (hseed : a^(k+2)+1=0) (M : ℕ) :
    ∃ n : ℕ, 0 < n ∧ M < Erdos322.representationCount (k+2) n ∧
      n ≤ (k+2)*p^((k+2)*((k+2)*(((k+2)*p^(k+1)+1)*(M+1))+1)) := by
  classical
  let D := (k+2)*p^(k+1)+1
  let d := D*(M+1)
  let q := p^((k+2)*d+1)
  let A := p^((k+2)*d*(k+1))
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hq : 0 < q := pow_pos hp _
  have hA : 0 < A := pow_pos hp _
  have hqpow : q^(k+1)=p^(k+1)*A := by
    dsimp only [q,A]
    rw [← pow_mul,show ((k+2)*d+1)*(k+1)=(k+1)+(k+2)*d*(k+1) by ring,pow_add]
  have hcount := rootCount_growth p k hk a ha hseed d
  change (d+1)*A ≤ rootCount (k+2) q at hcount
  have hsize : ((k+2)*q^(k+1)+1)*(M+1) < Fintype.card (Roots (k+2) q) := by
    change ((k+2)*q^(k+1)+1)*(M+1) < rootCount (k+2) q
    apply lt_of_lt_of_le _ hcount
    rw [hqpow]
    dsimp only [D,d]
    nlinarith
  have hfsize : Fintype.card (Fin ((k+2)*q^((k+2)-1)+1))*(M+1) <
      Fintype.card (Roots (k+2) q) := by simpa using hsize
  obtain ⟨y,hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card
    (quotientTarget (k+2) q (by omega) hq) hfsize
  have hfiber := fiber_card_le (k+2) q (by omega) hq y
  rw [Fintype.card_subtype] at hfiber
  have hycount := hy.trans_le hfiber
  refine ⟨q*(y : ℕ),?_,by omega,?_⟩
  · by_contra hn
    have hz : q*(y : ℕ)=0 := by omega
    rw [hz] at hycount
    have hzero : Erdos322.representationCount (k+2) 0=1 := by
      simp [Erdos322.representationCount]
    rw [hzero] at hycount
    omega
  · have hybound : (y : ℕ) ≤ (k+2)*q^(k+1) := by have := y.isLt; simpa using Nat.le_of_lt_succ this
    calc
      q*(y : ℕ) ≤ q*((k+2)*q^(k+1)) := Nat.mul_le_mul_left q hybound
      _ = (k+2)*q^(k+2) := by rw [pow_succ]; ring
      _ = _ := by dsimp only [q,d,D]; rw [← pow_mul]; congr 2; ring


private theorem exponential_peaks_of_good_prime (p k : ℕ) [Fact p.Prime]
    (hk : ¬p ∣ k+2) (a : ZMod p) (ha : a ≠ 0) (hseed : a^(k+2)+1=0) :
    ∃ B : ℕ, 1 < B ∧ ∀ M : ℕ, ∃ n : ℕ,
      0 < n ∧ M < Erdos322.representationCount (k+2) n ∧ n ≤ B^(M+1) := by
  let D := (k+2)*p^(k+1)+1
  let B := (k+2)*p^((k+2)*((k+2)*D+1))
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hB : 1 < B := by
    have hh : 1 ≤ p^((k+2)*((k+2)*D+1)) := one_le_pow₀ hp
    dsimp only [B]
    nlinarith
  refine ⟨B,hB,?_⟩
  intro M
  obtain ⟨n,hn,hcount,hbound⟩ := peak_from_good_prime p k hk a ha hseed M
  refine ⟨n,hn,hcount,hbound.trans ?_⟩
  change (k+2)*p^((k+2)*((k+2)*(D*(M+1))+1)) ≤ B^(M+1)
  dsimp only [B]
  rw [mul_pow,← pow_mul]
  apply Nat.mul_le_mul
  · exact Nat.le_pow (by omega)
  · apply Nat.pow_le_pow_right hp
    nlinarith [Nat.zero_le ((k+2)*M)]

/-- Every critical power sum has unbounded peaks at exponentially bounded targets.
This proof covers even and odd exponents uniformly. -/
theorem exponential_size_peaks (k : ℕ) (hk : 2 ≤ k) :
    ∃ B : ℕ, 1 < B ∧ ∀ M : ℕ, ∃ n : ℕ,
      0 < n ∧ M < Erdos322.representationCount k n ∧ n ≤ B^(M+1) := by
  obtain ⟨s,hs⟩ := Nat.exists_eq_add_of_le hk
  have hks : k=s+2 := by omega
  subst k
  obtain ⟨p,hp,hk,a,ha,hseed⟩ := exists_good_prime (s+2) (by omega)
  letI : Fact p.Prime := ⟨hp⟩
  simpa only [Nat.add_comm 2 s] using exponential_peaks_of_good_prime p s hk a ha hseed

/-- For every k at least two, some positive constant times log n is exceeded
by the full representation count infinitely often. This is weaker than the
positive-power peaks requested in Erdos 322. -/
theorem logarithmic_peaks (k : ℕ) (hk : 2 ≤ k) :
    ∃ c > (0 : ℝ),
      {n : ℕ | c*Real.log (n : ℝ) < Erdos322.representationCount k n}.Infinite := by
  obtain ⟨B,hB,h⟩ := exponential_size_peaks k hk
  have hlogB : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast hB)
  let c : ℝ := 1/(2*Real.log (B : ℝ))
  have hc : 0 < c := by dsimp only [c]; positivity
  have hpeak (M n : ℕ) (hn : 0 < n) (hcoun : M < Erdos322.representationCount k n)
      (hb : n ≤ B^(M+1)) : c*Real.log (n : ℝ) < Erdos322.representationCount k n := by
    have hlog : Real.log (n : ℝ) ≤ (M+1)*Real.log (B : ℝ) := by
      calc
        Real.log (n : ℝ) ≤ Real.log ((B : ℝ)^(M+1)) := by
          apply Real.log_le_log (by exact_mod_cast hn)
          exact_mod_cast hb
        _ = (M+1)*Real.log (B : ℝ) := by rw [Real.log_pow]; push_cast; rfl
    have hr : (M : ℝ)+1 ≤ Erdos322.representationCount k n := by exact_mod_cast hcoun
    have hrpos : (0 : ℝ) < Erdos322.representationCount k n := by
      have hm : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
      linarith
    dsimp only [c]
    rw [one_div_mul_eq_div]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2*Real.log (B : ℝ))).mpr
    nlinarith
  refine ⟨c,hc,?_⟩
  by_contra hfin
  have hf : {n : ℕ | c*Real.log (n : ℝ) < Erdos322.representationCount k n}.Finite :=
    Set.not_infinite.mp hfin
  obtain ⟨M,hM⟩ := (hf.image (Erdos322.representationCount k)).bddAbove
  obtain ⟨n,hn,hcount,hb⟩ := h M
  have hm : Erdos322.representationCount k n ≤ M :=
    hM ⟨n,hpeak M n hn hcount hb,rfl⟩
  omega

/-- In particular the full count is unbounded for every exponent at least two. -/
theorem count_unbounded (k : ℕ) (hk : 2 ≤ k) (M : ℕ) :
    ∃ n : ℕ, M < Erdos322.representationCount k n := by
  obtain ⟨B,hB,h⟩ := exponential_size_peaks k hk
  obtain ⟨n,_,hn,_⟩ := h M
  exact ⟨n,hn⟩

end
end Erdos322Research.LocalPowerPeaks
