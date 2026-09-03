import Submission.PeriodicSieveComponents

/-!
Arbitrarily long finite prime paths with different starting points force an
admissible translation-limit ray, not an actual prime ray. Consequently,
exclusion by one ordinary finite sieve entails a uniform bound on all finite
prime-path lengths. This is stronger than mere finiteness of each prime
component.
-/
namespace Erdos952Investigation.FinitePrimeSegments
open FiniteSieveReduction
set_option maxHeartbeats 0

def HasPrimeSegment (C : ℤ) (L : ℕ) : Prop :=
  ∃ x : ℕ → GaussianInt, Set.InjOn x (Set.Iic L) ∧
    (∀ i ≤ L, Prime (x i)) ∧ ∀ i < L, (x (i+1)-x i).norm < C

lemma block_index_lt (e L : ℕ) (b : Fin (e+1)) (i : Fin (L+1)) :
    b.val*(L+1)+i.val < (e+1)*(L+1) := by
  calc
    _ < b.val*(L+1)+(L+1) := Nat.add_lt_add_left i.isLt _
    _ = (b.val+1)*(L+1) := by ring
    _ ≤ (e+1)*(L+1) := Nat.mul_le_mul_right _ (by omega)

/-- Among `|E|+1` disjoint blocks of an injective finite sequence, one block
avoids the finite exceptional set `E`. -/
lemma exists_block_avoiding {V : Type*} (E : Finset V) (L : ℕ) (x : ℕ → V)
    (hx : Set.InjOn x (Set.Iio ((E.card+1)*(L+1)))) :
    ∃ b : Fin (E.card+1), ∀ i : Fin (L+1), x (b.val*(L+1)+i.val) ∉ E := by
  classical
  by_contra! hn
  choose j hj using hn
  let f : Fin (E.card+1) → E := fun b => ⟨x (b.val*(L+1)+(j b).val),hj b⟩
  have hf : Function.Injective f := by
    intro b c he
    have hi := hx (block_index_lt E.card L b (j b))
      (block_index_lt E.card L c (j c)) (congrArg Subtype.val he)
    have hb : (b.val*(L+1)+(j b).val)/(L+1) = b.val := by
      rw [Nat.mul_comm b.val, Nat.mul_add_div (Nat.succ_pos L),
        Nat.div_eq_of_lt (j b).isLt,Nat.add_zero]
    have hc : (c.val*(L+1)+(j c).val)/(L+1) = c.val := by
      rw [Nat.mul_comm c.val, Nat.mul_add_div (Nat.succ_pos L),
        Nat.div_eq_of_lt (j c).isLt,Nat.add_zero]
    apply Fin.ext
    rw [← hb,← hc,hi]
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin,Fintype.card_coe] at hc
  omega

noncomputable def exceptionSet (N : ℕ) : Finset GaussianInt :=
  (norm_sublevel_finite ((N : ℤ)^2)).toFinset

lemma mem_exceptionSet (N : ℕ) (z : GaussianInt) :
    z ∈ exceptionSet N ↔ z.norm ≤ (N : ℤ)^2 := by
  simp [exceptionSet]

noncomputable def segmentBound (N L : ℕ) : ℕ :=
  ((exceptionSet N).card+1)*(L+1)

/-- A long finite prime path supplies an admissible finite prefix. The
starting prime can depend on the desired prefix length. -/
lemma admissible_prefix_of_long_segment (C : ℤ) (n : ℕ)
    (h : HasPrimeSegment C (segmentBound n n)) :
    Nonempty (AdmissibleRay.Prefix C n) := by
  classical
  obtain ⟨x,hx,hp,hs⟩ := h
  obtain ⟨b,hb⟩ := exists_block_avoiding (exceptionSet n) n x
    (fun _ hi _ hj he => hx (Set.mem_Iio.mp hi).le (Set.mem_Iio.mp hj).le he)
  let K := b.val*(n+1)
  have hidx (i : Fin (n+1)) : K+i.val < segmentBound n n :=
    block_index_lt (exceptionSet n).card n b i
  have hlarge (i : Fin (n+1)) : (n : ℤ)^2 < (x (K+i.val)).norm := by
    have hh := hb i
    rw [mem_exceptionSet] at hh
    exact lt_of_not_ge hh
  let f : Fin (n+1) → GaussianInt := fun i => x (K+i.val)-x K
  have hf0 : f 0 = 0 := by simp [f]
  have hfi : Function.Injective f := by
    intro i j he
    have hxij : x (K+i.val) = x (K+j.val) := by simpa [f] using he
    have hi := hx (hidx i).le (hidx j).le hxij
    exact Fin.ext (by omega)
  have hstep (i : Fin n) : (AdmissibleRay.latticeGraph C).Adj
      (f i.castSucc) (f i.succ) := by
    refine ⟨fun he => ?_,?_⟩
    · have hh := congrArg Fin.val (hfi he)
      simp only [Fin.val_castSucc,Fin.val_succ] at hh
      omega
    · have he : f i.succ-f i.castSucc = x (K+i.val+1)-x (K+i.val) := by
        simp [f,Nat.add_assoc]
      rw [he]
      exact hs _ (hidx i.castSucc)
  refine ⟨⟨⟨f,hf0,hfi,hstep⟩,?_⟩⟩
  intro p hpn hprime
  refine ⟨(x K).re,(x K).im,fun i => ?_⟩
  apply AdmissibleRay.good_of_large_prime (hp _ (hidx i).le) hprime
  have hpn' : (p : ℤ) ≤ n := by exact_mod_cast hpn
  have hp0 : (0 : ℤ) ≤ p := Int.natCast_nonneg p
  have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have hh := hlarge i
  nlinarith

/-- Arbitrarily long finite actual-prime paths imply only an admissible ray
by this compactness argument. No primality of the limiting ray is claimed. -/
theorem unbounded_prime_segments_yield_admissible (C : ℤ)
    (h : ∀ L, HasPrimeSegment C L) : HasAdmissibleRay C :=
  AdmissibleRay.ray_of_prefixes C (fun n =>
    admissible_prefix_of_long_segment C n (h (segmentBound n n)))

/-- For any cutoff, a sufficiently long prime segment contains a segment of
the desired length entirely in that ordinary sieve. -/
lemma sieve_prefix_of_long_segment (C : ℤ) (N L : ℕ)
    (h : HasPrimeSegment C (segmentBound N L)) :
    ∃ z, Nonempty (RayReduction.Prefix (sieveGraph C N) z L) := by
  classical
  obtain ⟨x,hx,hp,hs⟩ := h
  obtain ⟨b,hb⟩ := exists_block_avoiding (exceptionSet N) L x
    (fun _ hi _ hj he => hx (Set.mem_Iio.mp hi).le (Set.mem_Iio.mp hj).le he)
  let K := b.val*(L+1)
  have hidx (i : Fin (L+1)) : K+i.val < segmentBound N L :=
    block_index_lt (exceptionSet N).card L b i
  have hlarge (i : Fin (L+1)) : (N : ℤ)^2 < (x (K+i.val)).norm := by
    have hh := hb i
    rw [mem_exceptionSet] at hh
    exact lt_of_not_ge hh
  let f : Fin (L+1) → GaussianInt := fun i => x (K+i.val)
  have hfi : Function.Injective f := by
    intro i j he
    have hh := hx (hidx i).le (hidx j).le he
    exact Fin.ext (by omega)
  have ha (i : Fin (L+1)) : Allowed N (f i) := by
    intro p hpN hprime hdiv
    have hh := prime_norm_divisor_bound (hp _ (hidx i).le) hprime hdiv
    have hpN' : (p : ℤ) ≤ N := by exact_mod_cast hpN
    have hp0 : (0 : ℤ) ≤ p := Int.natCast_nonneg p
    have hn0 : (0 : ℤ) ≤ N := Int.natCast_nonneg N
    have hbig := hlarge i
    change (x (K+i.val)).norm ≤ (p : ℤ)^2 at hh
    nlinarith
  refine ⟨x K,⟨⟨f,by simp [f],hfi,?_⟩⟩⟩
  intro i
  refine ⟨ha i.castSucc,ha i.succ,?_,?_⟩
  · intro he
    have hh := congrArg Fin.val (hfi he)
    simp only [Fin.val_castSucc,Fin.val_succ] at hh
    omega
  · simpa only [f,Fin.val_castSucc,Fin.val_succ,Nat.add_assoc] using
      hs _ (hidx i.castSucc)

/-- An explicit uniform prime-path bound from one global rejecting cutoff. -/
theorem ordinary_cutoff_explicit_segment_bound (C : ℤ) (N : ℕ)
    (hN : ¬ HasSieveRay C N) :
    ¬ HasPrimeSegment C (segmentBound N (N.factorial^2)) := by
  intro h
  obtain ⟨z,hz⟩ := sieve_prefix_of_long_segment C N (N.factorial^2) h
  exact hN ((sieve_ray_iff_infinite_component C N).mpr
    ⟨z,(PeriodicSieveComponents.infinite_component_iff_long_prefix C N z).mpr hz⟩)

/-- A global ordinary-sieve obstruction is a uniform bound on finite prime
paths, regardless of their starting points. -/
theorem ordinary_cutoff_implies_uniform_segment_bound (C : ℤ) (N : ℕ)
    (hN : ¬ HasSieveRay C N) : ∃ L, ¬ HasPrimeSegment C L := by
  by_contra! h
  exact hN ((admissible_ray_iff_finite_sieve_rays C).mp
    (unbounded_prime_segments_yield_admissible C h) N)

#print axioms ordinary_cutoff_explicit_segment_bound
#print axioms exists_block_avoiding
#print axioms admissible_prefix_of_long_segment
#print axioms unbounded_prime_segments_yield_admissible
#print axioms ordinary_cutoff_implies_uniform_segment_bound
end Erdos952Investigation.FinitePrimeSegments
