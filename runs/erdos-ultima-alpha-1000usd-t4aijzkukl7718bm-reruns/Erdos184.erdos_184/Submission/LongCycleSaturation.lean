import FormalConjecturesUtil

/-!
An algebraic saturation construction for finite circuit-vector systems.
This is an auxiliary theorem, not a proof of Erdős 184. In particular, no
identification of an arbitrary vector system with the circuits of a graph
is asserted here.
-/

open scoped BigOperators Classical
namespace Erdos184.LongCycleSaturation

variable {E I J : Type*} [Fintype E] [Fintype I] [Fintype J]

noncomputable def length (a : I → E → ℕ) (i : I) : ℕ := ∑ e, a i e

def IsPartition (a : I → E → ℕ) (x : E → ℕ) (d : I → ℕ) : Prop :=
  ∀ e, (∑ i, d i * a i e) = x e

noncomputable def deposit (i : I) (r : ℕ) : I → ℕ :=
  fun t => if t = i then r else 0

noncomputable def pack (f : J → I) (z : J → ℕ) : I → ℕ :=
  fun t => ∑ j, if f j = t then z j else 0

lemma sum_deposit (i : I) (r : ℕ) : (∑ t, deposit i r t) = r := by
  classical
  simp [deposit]

lemma mass_deposit (a : I → E → ℕ) (i : I) (r : ℕ) (e : E) :
    (∑ t, deposit i r t * a t e) = r * a i e := by
  classical
  simp [deposit, ite_mul]

lemma sum_pack (f : J → I) (z : J → ℕ) : (∑ t, pack f z t) = ∑ j, z j := by
  classical
  unfold pack
  rw [Finset.sum_comm]
  simp

lemma mass_pack (a : I → E → ℕ) (f : J → I) (z : J → ℕ) (e : E) :
    (∑ t, pack f z t * a t e) = ∑ j, z j * a (f j) e := by
  classical
  simp only [pack, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [ite_mul]

lemma partition_length (a : I → E → ℕ) (x : E → ℕ) (d : I → ℕ)
    (hd : IsPartition a x d) : (∑ i, d i * length a i) = ∑ e, x e := by
  simp only [length, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun e _ => hd e)

lemma partition_length_le (a : I → E → ℕ) (x : E → ℕ) (d : I → ℕ)
    (hd : IsPartition a x d) (L : ℕ) (hL : ∀ i, length a i ≤ L) :
    (∑ e, x e) ≤ L * ∑ i, d i := by
  rw [← partition_length a x d hd, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (d i) (hL i)

/-- If the required differences have integer representations in the longest
circuit vectors, one common positive offset turns every such representation
into an optimal extension. The maximum-length lower bound proves optimality.
The supplied integer relations are essential hypotheses. -/
theorem exists_all_optimal_state
    (a : I → E → ℕ) (L : ℕ) (hL : 3 ≤ L)
    (lo : ∀ i, 2 ≤ length a i) (hi : ∀ i, length a i ≤ L)
    (f : J → I) (hf : ∀ j, length a (f j) = L)
    (p q : I) (hp : length a p = 2) (hq : length a q = L - 1)
    (w : I → J → ℤ)
    (hw : ∀ i e, (∑ j, w i j * (a (f j) e : ℤ)) =
      (a p e : ℤ) - a i e - ((length a i - 2 : ℕ) : ℤ) * a q e) :
    ∃ (x : E → ℕ) (k : ℕ),
      (∑ e, x e) = L * (k - 1) + 2 ∧
      (∀ d : I → ℕ, IsPartition a x d → k ≤ ∑ i, d i) ∧
      (∀ i, ∃ d : I → ℕ, IsPartition a x d ∧ 0 < d i ∧ (∑ t, d t) = k) := by
  classical
  let delta : I → ℕ := fun i => length a i - 2
  have hdelta (i : I) : length a i = delta i + 2 := by
    dsimp [delta]
    have h := lo i
    omega
  have sum_w (i : I) : (∑ j, w i j) = -(delta i : ℤ) := by
    have h := Finset.sum_congr (s₁ := (Finset.univ : Finset E)) rfl (fun e _ => hw i e)
    have hleft : (∑ e, ∑ j, w i j * (a (f j) e : ℤ)) =
        (∑ j, w i j) * (L : ℤ) := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, ← Nat.cast_sum]
      change (∑ j, w i j * (length a (f j) : ℤ)) = _
      simp only [hf, Finset.sum_mul]
    rw [hleft] at h
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Nat.cast_sum] at h
    change (∑ j, w i j) * (L : ℤ) =
      (length a p : ℤ) - length a i - (delta i : ℤ) * length a q at h
    rw [hp, hq, hdelta i] at h
    have hLcast : ((L - 1 : ℕ) : ℤ) = (L : ℤ) - 1 := by omega
    rw [hLcast, Nat.cast_add] at h
    have hpos : (0 : ℤ) < L := by omega
    nlinarith
  let z : J → ℕ := fun j => 1 + ∑ i, (-w i j).toNat
  have hz (i : I) (j : J) : 0 ≤ (z j : ℤ) + w i j := by
    have hsum : (-w i j).toNat ≤ ∑ t, (-w t j).toNat :=
      Finset.single_le_sum (f := fun t => (-w t j).toNat)
        (fun t _ => Nat.zero_le _) (Finset.mem_univ i)
    have hsum' : (((-w i j).toNat : ℕ) : ℤ) ≤ (z j : ℤ) := by
      exact_mod_cast (show (-w i j).toNat ≤ z j by dsimp [z]; omega)
    omega
  let u : I → J → ℕ := fun i j => ((z j : ℤ) + w i j).toNat
  have hu (i : I) (j : J) : (u i j : ℤ) = (z j : ℤ) + w i j := by
    exact Int.toNat_of_nonneg (hz i j)
  have count_u (i : I) : delta i + ∑ j, u i j = ∑ j, z j := by
    have h : (delta i : ℤ) + ∑ j, (u i j : ℤ) = ∑ j, (z j : ℤ) := by
      simp only [hu, Finset.sum_add_distrib, sum_w]
      ring
    exact_mod_cast h
  let x : E → ℕ := fun e => a p e + ∑ j, z j * a (f j) e
  let k : ℕ := (∑ j, z j) + 1
  have hmass : (∑ e, x e) = L * (∑ j, z j) + 2 := by
    simp only [x, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    change length a p + (∑ j, z j * length a (f j)) = _
    simp only [hp, hf, ← Finset.sum_mul]
    ring
  refine ⟨x, k, ?_, ?_, ?_⟩
  · simpa [k] using hmass
  · intro d hd
    have hb := partition_length_le a x d hd L hi
    rw [hmass] at hb
    dsimp [k]
    by_contra! hn
    have hmul := Nat.mul_le_mul_left L (show (∑ i, d i) ≤ ∑ j, z j by omega)
    omega
  · intro i
    let d : I → ℕ := fun t => deposit i 1 t + deposit q (delta i) t + pack f (u i) t
    have hd : IsPartition a x d := by
      intro e
      simp only [d, Nat.add_mul, Finset.sum_add_distrib, mass_deposit, mass_pack,
        Nat.one_mul]
      change a i e + delta i * a q e + (∑ j, u i j * a (f j) e) =
        a p e + ∑ j, z j * a (f j) e
      have h : (a i e : ℤ) + delta i * a q e + (∑ j, (u i j : ℤ) * a (f j) e) =
          a p e + ∑ j, (z j : ℤ) * a (f j) e := by
        simp only [hu, add_mul, Finset.sum_add_distrib]
        rw [hw i e]
        change (a i e : ℤ) + delta i * a q e +
          ((∑ j, (z j : ℤ) * a (f j) e) +
            (a p e - a i e - (delta i : ℤ) * a q e)) = _
        ring
      exact_mod_cast h
    refine ⟨d, hd, ?_, ?_⟩
    · dsimp [d]
      simp [deposit]
    · simp only [d, Finset.sum_add_distrib, sum_deposit, sum_pack]
      dsimp [k]
      have h := count_u i
      omega

end Erdos184.LongCycleSaturation
