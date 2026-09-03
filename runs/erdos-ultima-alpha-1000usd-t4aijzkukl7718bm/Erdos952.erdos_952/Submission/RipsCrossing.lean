import Submission.FiniteSieveReduction

/-! Intersecting short straight edges join Gaussian-integer Rips components.
This is a local metric lemma, not a global planar separation theorem or a
solution of the Gaussian moat problem. -/
namespace Erdos952Investigation
namespace RipsCrossing
set_option maxHeartbeats 0

lemma endpoint_near_segment_point {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (a b p : E) (hp : p ∈ segment ℝ a b) :
    ∃ u : E, (u = a ∨ u = b) ∧ dist u p ≤ dist a b/2 := by
  have hh := dist_add_dist_of_mem_segment hp
  by_cases ha : dist a p ≤ dist a b/2
  · exact ⟨a,Or.inl rfl,ha⟩
  · refine ⟨b,Or.inr rfl,?_⟩
    rw [dist_comm b p]
    linarith

/-- This metric fact works in any real normed space, not only the plane. -/
theorem intersecting_short_segments {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (a b c d : E) (R : ℝ)
    (hab : dist a b < R) (hcd : dist c d < R)
    (hcross : (segment ℝ a b ∩ segment ℝ c d).Nonempty) :
    ∃ u v : E, (u = a ∨ u = b) ∧ (v = c ∨ v = d) ∧ dist u v < R := by
  obtain ⟨p,hp,hq⟩ := hcross
  obtain ⟨u,hu,hup⟩ := endpoint_near_segment_point a b p hp
  obtain ⟨v,hv,hvp⟩ := endpoint_near_segment_point c d p hq
  refine ⟨u,v,hu,hv,?_⟩
  have ht := dist_triangle u p v
  rw [dist_comm p v] at ht
  linarith

lemma gaussian_dist_sq (a b : GaussianInt) :
    dist (a : ℂ) (b : ℂ)^2 = ((b-a).norm : ℝ) := by
  rw [dist_comm,dist_eq_norm,Complex.sq_norm]
  rw [GaussianInt.intCast_real_norm,GaussianInt.toComplex_sub]

lemma gaussian_short_iff (a b : GaussianInt) (C : ℤ) :
    (b-a).norm < C ↔ dist (a : ℂ) (b : ℂ) < Real.sqrt (C : ℝ) := by
  rw [Real.lt_sqrt (dist_nonneg),gaussian_dist_sq]
  exact Int.cast_lt.symm

theorem intersecting_gaussian_edges (a b c d : GaussianInt) (C : ℤ)
    (hab : (b-a).norm < C) (hcd : (d-c).norm < C)
    (hcross : (segment ℝ (a : ℂ) (b : ℂ) ∩ segment ℝ (c : ℂ) (d : ℂ)).Nonempty) :
    ∃ u v : GaussianInt, (u = a ∨ u = b) ∧ (v = c ∨ v = d) ∧ (v-u).norm < C := by
  obtain ⟨u,v,hu,hv,huv⟩ := intersecting_short_segments (a : ℂ) b c d (Real.sqrt (C : ℝ))
    ((gaussian_short_iff a b C).mp hab) ((gaussian_short_iff c d C).mp hcd) hcross
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact ⟨a,c,Or.inl rfl,Or.inl rfl,(gaussian_short_iff a c C).mpr huv⟩
  · exact ⟨a,d,Or.inl rfl,Or.inr rfl,(gaussian_short_iff a d C).mpr huv⟩
  · exact ⟨b,c,Or.inr rfl,Or.inl rfl,(gaussian_short_iff b c C).mpr huv⟩
  · exact ⟨b,d,Or.inr rfl,Or.inr rfl,(gaussian_short_iff b d C).mpr huv⟩

lemma join_crossing_edges (G : SimpleGraph GaussianInt) (C : ℤ)
    (a b c d : GaussianInt) (hab : G.Adj a b) (hcd : G.Adj c d)
    (habnorm : (b-a).norm < C) (hcdnorm : (d-c).norm < C)
    (hclose : ∀ u v : GaussianInt, (u = a ∨ u = b) → (v = c ∨ v = d) →
      u ≠ v → (v-u).norm < C → G.Adj u v)
    (hcross : (segment ℝ (a : ℂ) (b : ℂ) ∩ segment ℝ (c : ℂ) (d : ℂ)).Nonempty) :
    G.Reachable a c := by
  obtain ⟨u,v,hu,hv,hn⟩ := intersecting_gaussian_edges a b c d C habnorm hcdnorm hcross
  have hau : G.Reachable a u := by
    rcases hu with rfl | rfl
    · exact SimpleGraph.Reachable.refl _
    · exact hab.reachable
  have hcv : G.Reachable c v := by
    rcases hv with rfl | rfl
    · exact SimpleGraph.Reachable.refl _
    · exact hcd.reachable
  have huv : G.Reachable u v := by
    by_cases he : u = v
    · rw [he]
    · exact (hclose u v hu hv he hn).reachable
  exact (hau.trans huv).trans hcv.symm

theorem prime_crossing_edges_connected (C : ℤ) (a b c d : GaussianInt)
    (hab : (primeGraph C).Adj a b) (hcd : (primeGraph C).Adj c d)
    (hcross : (segment ℝ (a : ℂ) (b : ℂ) ∩ segment ℝ (c : ℂ) (d : ℂ)).Nonempty) :
    (primeGraph C).Reachable a c := by
  apply join_crossing_edges (primeGraph C) C a b c d hab hcd hab.2.2.2 hcd.2.2.2 _ hcross
  intro u v hu hv hne hn
  have hpu : Prime u := by rcases hu with rfl | rfl; exact hab.1; exact hab.2.1
  have hpv : Prime v := by rcases hv with rfl | rfl; exact hcd.1; exact hcd.2.1
  exact ⟨hpu,hpv,hne,hn⟩

theorem sieve_crossing_edges_connected (C : ℤ) (N : ℕ) (a b c d : GaussianInt)
    (hab : (FiniteSieveReduction.sieveGraph C N).Adj a b)
    (hcd : (FiniteSieveReduction.sieveGraph C N).Adj c d)
    (hcross : (segment ℝ (a : ℂ) (b : ℂ) ∩ segment ℝ (c : ℂ) (d : ℂ)).Nonempty) :
    (FiniteSieveReduction.sieveGraph C N).Reachable a c := by
  apply join_crossing_edges (FiniteSieveReduction.sieveGraph C N) C a b c d
    hab hcd hab.2.2.2 hcd.2.2.2 _ hcross
  intro u v hu hv hne hn
  have hau : FiniteSieveReduction.Allowed N u := by
    rcases hu with rfl | rfl; exact hab.1; exact hab.2.1
  have hav : FiniteSieveReduction.Allowed N v := by
    rcases hv with rfl | rfl; exact hcd.1; exact hcd.2.1
  exact ⟨hau,hav,hne,hn⟩

/-- The union of the closed straight segments representing the edges of a
component. Isolated vertices contribute no segment to this definition. -/
def Trace (G : SimpleGraph GaussianInt) (z : GaussianInt) : Set ℂ :=
  {p | ∃ a b : GaussianInt, G.Reachable z a ∧ G.Adj a b ∧
    p ∈ segment ℝ (a : ℂ) (b : ℂ)}

theorem prime_component_traces_disjoint (C : ℤ) (z w : GaussianInt)
    (hzw : ¬ (primeGraph C).Reachable z w) :
    Disjoint (Trace (primeGraph C) z) (Trace (primeGraph C) w) := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  obtain ⟨a,b,hza,hab,hp⟩ := hp
  obtain ⟨c,d,hwc,hcd,hq⟩ := hq
  have hac := prime_crossing_edges_connected C a b c d hab hcd ⟨p,hp,hq⟩
  exact hzw ((hza.trans hac).trans hwc.symm)

theorem sieve_component_traces_disjoint (C : ℤ) (N : ℕ) (z w : GaussianInt)
    (hzw : ¬ (FiniteSieveReduction.sieveGraph C N).Reachable z w) :
    Disjoint (Trace (FiniteSieveReduction.sieveGraph C N) z)
      (Trace (FiniteSieveReduction.sieveGraph C N) w) := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  obtain ⟨a,b,hza,hab,hp⟩ := hp
  obtain ⟨c,d,hwc,hcd,hq⟩ := hq
  have hac := sieve_crossing_edges_connected C N a b c d hab hcd ⟨p,hp,hq⟩
  exact hzw ((hza.trans hac).trans hwc.symm)

#print axioms intersecting_gaussian_edges
#print axioms prime_component_traces_disjoint
#print axioms sieve_component_traces_disjoint
end RipsCrossing
end Erdos952Investigation
