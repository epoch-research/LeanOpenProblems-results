import Submission.BlowupThinning

/-! A projection obstruction for a proposed polynomial-graph packing of seed
pair neighborhoods. This does not rule out arbitrary nonlinear seed lifts,
and does not settle Erdős714. -/
noncomputable section
open Classical Finset SimpleGraph
open Erdos714Packing
set_option maxHeartbeats 3000000
namespace Erdos714SeedPairProjection
variable {A B T : Type*} [Fintype A] [Fintype B] [Fintype T]

/-- Both orders of a distinct pair, plus the diagonal, give all ordered pairs. -/
lemma factorial_two_add (n : ℕ) : n.descFactorial 2+n=n^2 := by
  cases n with
  | zero => simp
  | succ n => simp [Nat.descFactorial_succ]; ring

/-- The exact second-moment bound, with no truncation in the edge count. -/
theorem c4_edge_square (S : A → Finset B)
    (hfree : (completeBipartiteGraph (Fin 2) (Fin 2)).Free (incidence S)) :
    (∑ a, (S a).card)^2 ≤ Fintype.card B *
      ((Fintype.card A)*(Fintype.card A-1)+∑ a, (S a).card) := by
  have hf : (completeBipartiteGraph (Fin 2) (Fin 2)).Free (incidence (dual S)) := by
    rw [free_iff_common_card _ (by decide)]
    exact (common_card_dual_iff S (by decide)).mp
      ((free_iff_common_card S (by decide)).mp hfree)
  have hs := Erdos714Unbalanced.star_bound (dual S) (by decide : 0<2) hf
  norm_num only [Nat.reduceSub,one_mul] at hs
  have hp := pow_sum_le_card_mul_sum_pow (s := (univ : Finset B))
    (f := fun b => (dual S b).card) (by intros; omega) 1
  norm_num only [Nat.add_one_sub_one,Nat.reduceAdd,pow_one,card_univ] at hp
  have hid : (∑ b, (dual S b).card^2) =
      (∑ b, (dual S b).card.descFactorial 2)+(∑ b, (dual S b).card) := by
    simp_rw [← factorial_two_add]
    rw [sum_add_distrib]
  rw [hid,Erdos714Blowup.sum_dual_card] at hp
  calc
    _ ≤ Fintype.card B*((∑ b, (dual S b).card.descFactorial 2)+∑ a, (S a).card) := hp
    _ ≤ Fintype.card B*((Fintype.card A).descFactorial 2+∑ a, (S a).card) := by gcongr
    _ = _ := by simp [Nat.descFactorial_succ,mul_comm]

/-- A nonempty regular row set inside a C4-free incidence graph. -/
theorem regular_card_bound (S : A → Finset B) (D : ℕ)
    (hdeg : ∀ a, (S a).card=D) (hpos : 0<Fintype.card A)
    (hfree : (completeBipartiteGraph (Fin 2) (Fin 2)).Free (incidence S)) :
    Fintype.card A*D^2 ≤ Fintype.card B*(Fintype.card A-1+D) := by
  have h := c4_edge_square S hfree
  simp_rw [hdeg] at h
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id] at h
  apply Nat.le_of_mul_le_mul_left (c := Fintype.card A) _ hpos
  convert h using 1 <;> ring

/-- `π` being injective on each two-column common neighborhood is the
transversal condition needed to treat those neighborhoods as graphs over π. -/
def TransversalPairs (S : A → Finset B) (π : A → T) : Prop :=
  ∀ b c : B, b ≠ c → Set.InjOn π {a | b ∈ S a ∧ c ∈ S a}

omit [Fintype A] [Fintype T] in
/-- A fiber of a transversal projection contains no C4. -/
theorem fiber_free (S : A → Finset B) (π : A → T) (hπ : TransversalPairs S π) (t : T) :
    (completeBipartiteGraph (Fin 2) (Fin 2)).Free
      (incidence (fun a : {a // π a=t} => S a.val)) := by
  rw [free_iff_common_card _ (by decide)]
  intro f
  have hc : (common (fun a : {a // π a=t} => S a.val) f).card ≤ 1 := by
    apply card_le_one.mpr
    intro b hb c hc
    by_contra hbc
    have hb' := (mem_common _ f b).mp hb
    have hc' := (mem_common _ f c).mp hc
    have he : (f 0).val=(f 1).val := hπ b c hbc ⟨hb' 0,hc' 0⟩ ⟨hb' 1,hc' 1⟩
      ((f 0).property.trans (f 1).property.symm)
    have hf := f.injective (Subtype.ext he)
    exact (by decide : (0 : Fin 2) ≠ 1) hf
  omega

omit [Fintype T] in
/-- At the ideal seed scale, every projection fiber has at most q+1 rows.
No K33-freeness or algebraicity of the seed is needed for this conclusion. -/
theorem fiber_card_bound (S : A → Finset B) (π : A → T) (hπ : TransversalPairs S π)
    (q : ℕ) (hq : 2≤q) (hB : Fintype.card B ≤ q^3)
    (hdeg : ∀ a, (S a).card=q^2) (t : T) :
    Fintype.card {a // π a=t} ≤ q+1 := by
  let U := {a // π a=t}
  let m := Fintype.card U
  by_cases hm : 0 < m
  · have h := regular_card_bound (fun a : U => S a.val) (q^2)
      (fun a => hdeg a.val) hm (fiber_free S π hπ t)
    have h' : (m*q)*q^3 ≤ (m-1+q^2)*q^3 := by
      calc
        (m*q)*q^3 = m*(q^2)^2 := by ring
        _ ≤ Fintype.card B*(m-1+q^2) := h
        _ ≤ q^3*(m-1+q^2) := Nat.mul_le_mul_right _ hB
        _ = _ := by ring
    have he := Nat.le_of_mul_le_mul_right h' (pow_pos (by omega) 3)
    have hs : m-1+1=m := Nat.sub_add_cancel hm
    have hq1 : q-1+1=q := Nat.sub_add_cancel (by omega)
    have hc : (q-1)*m ≤ (q-1)*(q+1) := by
      nlinarith [congrArg (fun n : ℕ => n*m) hq1,
        congrArg (fun n : ℕ => n*(q+1)) hq1]
    exact Nat.le_of_mul_le_mul_left hc (by omega)
  · change m ≤ q+1
    omega

/-- Any single transversal coordinate system needs on the order of q² values,
not q values. The fiber bound is summed over the ACTUAL projection fibers. -/
theorem projection_card_bound (S : A → Finset B) (π : A → T) (hπ : TransversalPairs S π)
    (q : ℕ) (hq : 2≤q) (hB : Fintype.card B ≤ q^3) (hdeg : ∀ a, (S a).card=q^2) :
    Fintype.card A ≤ Fintype.card T*(q+1) := by
  have hsum := Fintype.sum_fiberwise π (fun _ => (1 : ℕ))
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mul_one] at hsum
  calc
    Fintype.card A = ∑ t, Fintype.card {a // π a=t} := hsum.symm
    _ ≤ ∑ _t : T, (q+1) := sum_le_sum (fun t _ => fiber_card_bound S π hπ q hq hB hdeg t)
    _ = _ := by simp

/-- In particular, q³ rows of degree q² cannot have such a projection to at
most q coordinate values. This only excludes the stated global projection. -/
theorem not_transversal (S : A → Finset B) (π : A → T) (q : ℕ) (hq : 2≤q)
    (hA : q^3 ≤ Fintype.card A) (hB : Fintype.card B ≤ q^3)
    (hT : Fintype.card T ≤ q) (hdeg : ∀ a, (S a).card=q^2) :
    ¬ TransversalPairs S π := by
  intro hπ
  have h := hA.trans (projection_card_bound S π hπ q hq hB hdeg)
  have he : q^3 ≤ q*(q+1) := h.trans (Nat.mul_le_mul_right _ hT)
  have hp : q+1 < q^2 := by nlinarith
  nlinarith [Nat.mul_le_mul_left q (show q+2 ≤ q^2 by omega)]

omit [Fintype T] in
/-- The same obstruction with the actual degree q²-1 of a quadratic norm seed. -/
theorem norm_scale_fiber_bound (S : A → Finset B) (π : A → T) (hπ : TransversalPairs S π)
    (q : ℕ) (hq : 4≤q) (hB : Fintype.card B ≤ q^3)
    (hdeg : ∀ a, (S a).card=q^2-1) (t : T) :
    Fintype.card {a // π a=t} ≤ 2*q := by
  let U := {a // π a=t}
  let m := Fintype.card U
  let D := q^2-1
  have hD : D+1=q^2 := Nat.sub_add_cancel (by nlinarith)
  have hq1 : q-1+1=q := Nat.sub_add_cancel (by omega)
  have hq2 : q-2+2=q := Nat.sub_add_cancel (by omega)
  have hD2 : (q-1)*q^3 ≤ D^2 := by
    have he := congrArg (fun x : ℕ => x^2) hD
    have he' := congrArg (fun x : ℕ => x*q^3) hq1
    nlinarith [Nat.mul_le_mul_left (q^2) (show 2≤q by omega)]
  by_cases hm : 0 < m
  · have h := regular_card_bound (fun a : U => S a.val) D
      (fun a => hdeg a.val) hm (fiber_free S π hπ t)
    have h' : ((q-1)*m)*q^3 ≤ (m-1+D)*q^3 := by
      calc
        ((q-1)*m)*q^3 = m*((q-1)*q^3) := by ring
        _ ≤ m*D^2 := Nat.mul_le_mul_left _ hD2
        _ ≤ Fintype.card B*(m-1+D) := h
        _ ≤ q^3*(m-1+D) := Nat.mul_le_mul_right _ hB
        _ = _ := by ring
    have he := Nat.le_of_mul_le_mul_right h' (pow_pos (by omega) 3)
    have hs : m-1+1=m := Nat.sub_add_cancel hm
    have he' : (q-2)*m ≤ q^2 := by
      nlinarith [congrArg (fun x : ℕ => x*m) hq1,
        congrArg (fun x : ℕ => x*m) hq2]
    have hc : q^2 ≤ (q-2)*(2*q) := by
      nlinarith [congrArg (fun x : ℕ => x*(2*q)) hq2,
        Nat.mul_le_mul_left q hq]
    exact Nat.le_of_mul_le_mul_left (he'.trans hc) (by omega)
  · change m ≤ 2*q
    omega

/-- A genuine quadratic norm seed has q³-q² vertices per side and degree
q²-1. A common coordinate set of size q cannot make all its pair neighborhoods
transversal, even after arbitrary bijective relabeling of either part. -/
theorem norm_scale_not_transversal (S : A → Finset B) (π : A → T)
    (q : ℕ) (hq : 4≤q) (hA : q^3-q^2 ≤ Fintype.card A)
    (hB : Fintype.card B ≤ q^3) (hT : Fintype.card T ≤ q)
    (hdeg : ∀ a, (S a).card=q^2-1) : ¬ TransversalPairs S π := by
  intro hπ
  have hsum := Fintype.sum_fiberwise π (fun _ => (1 : ℕ))
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mul_one] at hsum
  have he : q^3-q^2 ≤ 2*q^2 := by
    calc
      q^3-q^2 ≤ Fintype.card A := hA
      _ = ∑ t, Fintype.card {a // π a=t} := hsum.symm
      _ ≤ ∑ _t : T, (2*q) := sum_le_sum
        (fun t _ => norm_scale_fiber_bound S π hπ q hq hB hdeg t)
      _ = Fintype.card T*(2*q) := by simp
      _ ≤ q*(2*q) := Nat.mul_le_mul_right _ hT
      _ = _ := by ring
  have hs : q^3-q^2+q^2=q^3 := Nat.sub_add_cancel (by
    nlinarith [Nat.mul_le_mul_left (q^2) (show 1≤q by omega)])
  nlinarith [Nat.mul_le_mul_left (q^2) hq]

/-- A convenient real version of the truncated C4 estimate. -/
theorem c4_edge_real (S : A → Finset B)
    (hfree : (completeBipartiteGraph (Fin 2) (Fin 2)).Free (incidence S)) :
    ((∑ a, (S a).card : ℕ) : ℝ) ≤
      Fintype.card A*Real.sqrt (Fintype.card B)+Fintype.card B := by
  have hf : (completeBipartiteGraph (Fin 2) (Fin 2)).Free (incidence (dual S)) := by
    rw [free_iff_common_card _ (by decide)]
    exact (common_card_dual_iff S (by decide)).mp
      ((free_iff_common_card S (by decide)).mp hfree)
  have hp := Erdos714Unbalanced.power_bound (dual S) (by decide : 1≤2) hf
  simp only [Nat.reduceSub,one_mul,pow_one,Erdos714Blowup.sum_dual_card] at hp
  let e := ∑ a, (S a).card
  let M := Fintype.card B
  let n := Fintype.card A
  have hp' : ((e-M : ℕ) : ℝ)^2 ≤ (M : ℝ)*(n : ℝ)^2 := by exact_mod_cast hp
  have hroot : ((e-M : ℕ) : ℝ) ≤ (n : ℝ)*Real.sqrt M := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    calc
      ((e-M : ℕ) : ℝ)^2 ≤ (M : ℝ)*(n : ℝ)^2 := hp'
      _ = ((n : ℝ)*Real.sqrt M)^2 := by
        rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
        ring
  have he : (e : ℝ) ≤ ((e-M : ℕ) : ℝ)+M := by
    exact_mod_cast (show e ≤ (e-M)+M by omega)
  change (e : ℝ) ≤ (n : ℝ)*Real.sqrt M+M
  exact he.trans (add_le_add hroot le_rfl)

/-- The projection obstruction also applies without regularity. In particular
it can be used for an arbitrary selected edge set that still has the stated
transversal-pair property; it is not an obstruction to all edge thinnings. -/
theorem projection_edge_square (S : A → Finset B) (π : A → T)
    (hπ : TransversalPairs S π) :
    (∑ a, (S a).card)^2 ≤
      2*Fintype.card B*(Fintype.card A)^2+2*(Fintype.card B)^2*(Fintype.card T)^2 := by
  let e (t : T) := ∑ a : {a // π a=t}, (S a.val).card
  let m (t : T) := Fintype.card {a // π a=t}
  let N := Fintype.card A
  let M := Fintype.card B
  let L := Fintype.card T
  let E := ∑ a, (S a).card
  have he : (E : ℝ) = ∑ t, (e t : ℝ) := by
    exact_mod_cast (Fintype.sum_fiberwise π (fun a => (S a).card)).symm
  have hm : (N : ℝ) = ∑ t, (m t : ℝ) := by
    have h := Fintype.sum_fiberwise π (fun _ => (1 : ℕ))
    simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mul_one] at h
    exact_mod_cast h.symm
  have hb (t : T) : (e t : ℝ) ≤ (m t : ℝ)*Real.sqrt M+M := by
    exact c4_edge_real (fun a : {a // π a=t} => S a.val) (fiber_free S π hπ t)
  have hE : (E : ℝ) ≤ (N : ℝ)*Real.sqrt M+(M : ℝ)*L := by
    calc
      (E : ℝ) = ∑ t, (e t : ℝ) := he
      _ ≤ ∑ t, ((m t : ℝ)*Real.sqrt M+M) := sum_le_sum (fun t _ => hb t)
      _ = _ := by
        rw [sum_add_distrib,← sum_mul,← hm]
        simp only [sum_const,card_univ,nsmul_eq_mul]
        ring
  have hs : (E : ℝ)^2 ≤ 2*(M : ℝ)*(N : ℝ)^2+2*(M : ℝ)^2*(L : ℝ)^2 := by
    calc
      (E : ℝ)^2 ≤ ((N : ℝ)*Real.sqrt M+(M : ℝ)*L)^2 :=
        (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mpr hE
      _ ≤ 2*((N : ℝ)*Real.sqrt M)^2+2*((M : ℝ)*L)^2 := by
        nlinarith only [sq_nonneg ((N : ℝ)*Real.sqrt M-(M : ℝ)*L)]
      _ = _ := by
        rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
        ring
  exact_mod_cast hs

/-- At seed scale, every such selected graph loses a square-root factor of q. -/
theorem seed_scale_edge_square (S : A → Finset B) (π : A → T)
    (hπ : TransversalPairs S π) (q : ℕ) (hq : 1≤q)
    (hA : Fintype.card A ≤ q^3) (hB : Fintype.card B ≤ q^3)
    (hT : Fintype.card T ≤ q) : (∑ a, (S a).card)^2 ≤ 4*q^9 := by
  calc
    _ ≤ 2*Fintype.card B*(Fintype.card A)^2+2*(Fintype.card B)^2*(Fintype.card T)^2 :=
      projection_edge_square S π hπ
    _ ≤ 2*q^3*(q^3)^2+2*(q^3)^2*q^2 := by gcongr
    _ = 2*q^9+2*q^8 := by ring
    _ ≤ 4*q^9 := by
      have h : q^8 ≤ q^9 := Nat.pow_le_pow_right hq (by omega)
      omega

/-- A fixed retained fraction of a degree-q² seed is therefore impossible
under the global projection property, even with arbitrary edge deletions. -/
theorem seed_scale_budget (S : A → Finset B) (π : A → T)
    (hπ : TransversalPairs S π) (q K : ℕ) (hq : 1≤q)
    (hA : Fintype.card A ≤ q^3) (hB : Fintype.card B ≤ q^3)
    (hT : Fintype.card T ≤ q) (hdense : q^5 ≤ K*∑ a, (S a).card) : q ≤ 4*K^2 := by
  have h := seed_scale_edge_square S π hπ q hq hA hB hT
  have hp := Nat.pow_le_pow_left hdense 2
  rw [mul_pow] at hp
  have he : q*q^9 ≤ (4*K^2)*q^9 := by
    calc
      q*q^9 = (q^5)^2 := by ring
      _ ≤ K^2*(∑ a, (S a).card)^2 := hp
      _ ≤ K^2*(4*q^9) := Nat.mul_le_mul_left _ h
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right he (pow_pos (by omega) _)

end Erdos714SeedPairProjection
#print axioms Erdos714SeedPairProjection.c4_edge_square
#print axioms Erdos714SeedPairProjection.regular_card_bound
#print axioms Erdos714SeedPairProjection.fiber_free
#print axioms Erdos714SeedPairProjection.fiber_card_bound
#print axioms Erdos714SeedPairProjection.projection_card_bound
#print axioms Erdos714SeedPairProjection.not_transversal
#print axioms Erdos714SeedPairProjection.norm_scale_fiber_bound
#print axioms Erdos714SeedPairProjection.norm_scale_not_transversal

#print axioms Erdos714SeedPairProjection.c4_edge_real
#print axioms Erdos714SeedPairProjection.projection_edge_square
#print axioms Erdos714SeedPairProjection.seed_scale_edge_square
#print axioms Erdos714SeedPairProjection.seed_scale_budget
