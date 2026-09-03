import FormalConjecturesUtil
import Submission.SmoothDensity
import Submission.CofactorDensity

/-! Arithmetic constraints on reversing edges after removing small factors.
These are obstructions to raw edge-by-edge symmetry, not a proof or disproof
of Erdős 371. -/

namespace Erdos371CoreGraphReversal

/-- Two oppositely directed edges with the same core endpoints force each
core to divide a sum of the opposite edge's multipliers. -/
theorem opposite_edges_dvd {a b c d u v : ℕ}
    (h₁ : a*u+1=b*v) (h₂ : c*v+1=d*u) :
    u ∣ b+c ∧ v ∣ a+d := by
  have hu : u ∣ b*(c*v+1)-c*(a*u) := by
    rw [h₂]
    exact Nat.dvd_sub (dvd_mul_of_dvd_right (dvd_mul_left u d) b)
      (dvd_mul_of_dvd_right (dvd_mul_left u a) c)
  constructor
  · have he₁ : b*(c*v+1)=c*(a*u)+(b+c) := by
      nlinarith [congrArg (fun x => c*x) h₁]
    have he : b*(c*v+1)-c*(a*u)=b+c := by omega
    exact he ▸ hu
  · have hv' : v ∣ d*(a*u+1)-a*(c*v) := by
      rw [h₁]
      exact Nat.dvd_sub (dvd_mul_of_dvd_right (dvd_mul_left v b) d)
        (dvd_mul_of_dvd_right (dvd_mul_left v c) a)
    have he₂ : d*(a*u+1)=a*(c*v)+(a+d) := by
      nlinarith [congrArg (fun x => a*x) h₂]
    have he : d*(a*u+1)-a*(c*v)=a+d := by omega
    exact he ▸ hv'

/-- If all four multipliers are bounded by `T`, both original edge locations
are bounded by `2*T^2`. Thus large edges cannot be paired in reverse while
keeping all four multipliers small. -/
theorem opposite_edges_bounded {a b c d u v T : ℕ}
    (hb : 0<b) (haT : a≤T) (hbT : b≤T) (hcT : c≤T) (hdT : d≤T)
    (h₁ : a*u+1=b*v) (h₂ : c*v+1=d*u) :
    u≤2*T ∧ v≤2*T ∧ a*u≤2*T^2 ∧ c*v≤2*T^2 := by
  obtain ⟨hu, hv⟩ := opposite_edges_dvd h₁ h₂
  have hu' := Nat.le_of_dvd (by omega : 0<b+c) hu
  have hd : 0<d := by
    by_contra hh
    have hd0 : d=0 := by omega
    simp [hd0] at h₂
  have hv' := Nat.le_of_dvd (by omega : 0<a+d) hv
  have huT : u≤2*T := by omega
  have hvT : v≤2*T := by omega
  refine ⟨huT,hvT,?_,?_⟩
  · nlinarith [Nat.mul_le_mul haT huT]
  · nlinarith [Nat.mul_le_mul hcT hvT]

abbrev oddCore (n : ℕ) : ℕ := ordCompl[2] n

lemma oddCore_dvd (n : ℕ) : oddCore n ∣ n := Nat.ordCompl_dvd n 2
lemma oddCore_le (n : ℕ) : oddCore n ≤ n := Nat.ordCompl_le n 2
lemma oddCore_not_even {n : ℕ} (hn : n≠0) : ¬2∣oddCore n :=
  Nat.not_dvd_ordCompl Nat.prime_two hn

lemma oddCore_eq_of_odd {n : ℕ} (hn : ¬2∣n) : oddCore n=n :=
  (Nat.ordCompl_eq_self_iff_zero_or_not_dvd n Nat.prime_two).mpr (Or.inr hn)

/-- Each edge between odd cores has one of its endpoints equal to the
original odd integer; deleting powers of two does not move that endpoint. -/
lemma oddCore_edge_endpoint (n : ℕ) : oddCore n=n ∨ oddCore (n+1)=n+1 := by
  by_cases hn : 2∣n
  · right
    apply oddCore_eq_of_odd
    intro hh
    exact Nat.prime_two.not_dvd_one ((Nat.dvd_add_iff_right hn).mpr hh)
  · exact Or.inl (oddCore_eq_of_odd hn)


lemma oddCore_strict_increase_endpoint {n : ℕ} (hn : 0<n)
    (huv : oddCore n < oddCore (n+1)) : oddCore (n+1)=n+1 := by
  rcases oddCore_edge_endpoint n with h | h
  · have hle := oddCore_le (n+1)
    have he : oddCore (n+1)=n+1 := by omega
    have ho := oddCore_not_even hn.ne'
    have ho' := oddCore_not_even (show n+1≠0 by omega)
    rw [h] at ho
    rw [he] at ho'
    simp only [Nat.dvd_iff_mod_eq_zero] at ho ho'
    omega
  · exact h

lemma oddCore_strict_decrease_endpoint {n : ℕ}
    (huv : oddCore (n+1) < oddCore n) : oddCore n=n := by
  rcases oddCore_edge_endpoint n with h | h
  · exact h
  · have hh := oddCore_le n
    omega

/-- An increasing odd-core edge can only be reversed if its smaller core
is one. In particular the graph is not made nearly symmetric by simply
removing powers of two. -/
lemma oddCore_reverse_increasing {n m : ℕ} (hn : 0<n)
    (huv : oddCore n < oddCore (n+1))
    (h₁ : oddCore m=oddCore (n+1)) (h₂ : oddCore (m+1)=oddCore n) :
    oddCore n≤1 := by
  have hn' := oddCore_strict_increase_endpoint hn huv
  have hm' : oddCore m=m := oddCore_strict_decrease_endpoint (by omega)
  have he : m=n+1 := by omega
  have hd := oddCore_dvd n
  have hd' := oddCore_dvd (m+1)
  rw [h₂, he, Nat.add_assoc] at hd'
  have htwo : oddCore n∣2 := (Nat.dvd_add_iff_right hd).mpr hd'
  have hle := Nat.le_of_dvd (by omega : 0<2) htwo
  have hodd := oddCore_not_even hn.ne'
  by_contra h
  have heq : oddCore n=2 := by omega
  exact hodd (by rw [heq])

/-- No pair of opposite edges between odd cores greater than one exists,
regardless of how far away the proposed reverse edge is. -/
theorem no_oddCore_reverse_above_one {n m : ℕ} (hn : 0<n) (hm : 0 < m)
    (hu : 1<oddCore n) (hv : 1<oddCore (n+1)) :
    ¬(oddCore m=oddCore (n+1) ∧ oddCore (m+1)=oddCore n) := by
  rintro ⟨h₁,h₂⟩
  rcases lt_trichotomy (oddCore n) (oddCore (n+1)) with h | h | h
  · have hh := oddCore_reverse_increasing hn h h₁ h₂
    omega
  · have hd := oddCore_dvd n
    have hd' : oddCore n∣n+1 := h ▸ oddCore_dvd (n+1)
    have hh : oddCore n∣1 := (Nat.dvd_add_iff_right hd).mpr hd'
    have hh' := Nat.le_of_dvd (by omega : 0<1) hh
    omega
  · have hh := oddCore_reverse_increasing hm (by omega) h₂.symm h₁.symm
    omega

lemma maxPrimeFac_le_two_of_oddCore_le_one {n : ℕ} (h : oddCore n≤1) :
    Nat.maxPrimeFac n≤2 := by
  by_cases hn : n=0
  · simp [hn]
  have hc : oddCore n=1 := by
    have hh := Nat.ordCompl_pos 2 hn
    change 0 < oddCore n at hh
    omega
  have he : n=2^(n.factorization 2) := by
    have hh := Nat.ordProj_mul_ordCompl_eq_self n 2
    change 2^(n.factorization 2)*oddCore n=n at hh
    simpa [hc] using hh.symm
  by_cases hk : n.factorization 2=0
  · have hn1 : n=1 := by simpa only [hk, pow_zero] using he
    simp [hn1]
  · rw [he, Nat.maxPrimeFac_pow hk]
    decide +kernel

/-- Only a density-zero set of adjacent pairs of odd cores has any reverse
edge anywhere. This concerns odd cores, not the largest-prime comparisons. -/
theorem oddCore_reverse_hasDensity_zero :
    {n : ℕ | ∃ m : ℕ, 0 < m ∧ oddCore m=oddCore (n+1) ∧
      oddCore (m+1)=oddCore n}.HasDensity 0 := by
  let S : Set ℕ := {n | Nat.maxPrimeFac n≤2}
  have hS : S.HasDensity 0 := Erdos371Exploration.bounded_maxPrimeFac_hasDensity_zero 2
  have hS' : {n | n+1∈S}.HasDensity 0 :=
    Erdos371CofactorDensity.density_zero_shift hS
  apply Erdos371Exploration.density_zero_of_subset (T := S∪{n | n+1∈S}) _
    (Erdos371CofactorDensity.density_zero_union hS hS')
  intro n hn
  obtain ⟨m,hm,h₁,h₂⟩ := hn
  by_cases hn0 : n=0
  · left
    simp [S, hn0]
  by_cases hu : oddCore n≤1
  · exact Or.inl (maxPrimeFac_le_two_of_oddCore_le_one hu)
  by_cases hv : oddCore (n+1)≤1
  · exact Or.inr (maxPrimeFac_le_two_of_oddCore_le_one hv)
  exact False.elim ((no_oddCore_reverse_above_one (Nat.pos_of_ne_zero hn0) hm
    (by omega) (by omega)) ⟨h₁,h₂⟩)

end Erdos371CoreGraphReversal

#print axioms Erdos371CoreGraphReversal.opposite_edges_bounded
#print axioms Erdos371CoreGraphReversal.no_oddCore_reverse_above_one
#print axioms Erdos371CoreGraphReversal.oddCore_reverse_hasDensity_zero
