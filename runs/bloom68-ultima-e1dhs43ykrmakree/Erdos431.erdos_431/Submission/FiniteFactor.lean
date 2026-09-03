import FormalConjecturesUtil

/-!
# Finite nontrivial summands cannot cover the eventual primes

This is a partial result only: the target problem has two infinite summands.
The proof constructs one reduced residue class blocking every member of a
finite left summand, then applies Dirichlet's theorem.
-/

open scoped Pointwise

namespace FiniteFactorResearch

/-- A reduced residue class can force a prime divisor for each of finitely
many nonzero shifts. The divisor is bounded independently of the class member. -/
theorem finite_shift_crt (F : Finset ℕ) (v : ℕ → ℕ)
    (hne : ∀ u ∈ F, v u ≠ u) :
    ∃ m r K : ℕ, 0 < m ∧ r.Coprime m ∧
      ∀ u ∈ F, ∃ q : ℕ, q.Prime ∧ q ≤ K ∧
        ∀ n : ℕ, n ≡ r [MOD m] → n + v u ≡ u [MOD q] := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      exact ⟨1, 0, 0, by omega, by norm_num, by simp⟩
  | @insert u F hu ih =>
      obtain ⟨m, r, K, hm, hr, hF⟩ :=
        ih (fun a ha => hne a (Finset.mem_insert_of_mem ha))
      obtain ⟨q, hqbig, hq⟩ := Nat.exists_infinite_primes (m + u + v u + 1)
      have hqm : m < q := by omega
      have hquv : u + v u < q := by omega
      have hvu : v u ≠ u := hne u (Finset.mem_insert_self _ _)
      let z := if u < v u then q - (v u - u) else u - v u
      have hz0 : 0 < z := by dsimp [z]; split_ifs <;> omega
      have hzq : z < q := by dsimp [z]; split_ifs <;> omega
      have hzmod : z + v u ≡ u [MOD q] := by
        dsimp [z]
        split_ifs with h
        · have heq : q - (v u - u) + v u = q + u := by omega
          rw [heq]
          change (q + u) % q = u % q
          simp
        · have heq : u - v u + v u = u := by omega
          rw [heq]
      have hzcop : z.Coprime q :=
        (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hz0 hzq)).symm
      have hmq : m.Coprime q :=
        (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm hqm)).symm
      let t := Nat.chineseRemainder hmq r z
      have htm : (t : ℕ).Coprime m := by
        change Nat.gcd (t : ℕ) m = 1
        rw [t.property.1.gcd_eq]
        exact hr
      have htq : (t : ℕ).Coprime q := by
        change Nat.gcd (t : ℕ) q = 1
        rw [t.property.2.gcd_eq]
        exact hzcop
      refine ⟨m * q, t, max K q, Nat.mul_pos hm hq.pos, htm.mul_right htq, ?_⟩
      intro a ha
      rcases Finset.mem_insert.mp ha with hau | haF
      · subst a
        refine ⟨q, hq, le_max_right _ _, ?_⟩
        intro n hn
        have hnq : n ≡ (t : ℕ) [MOD q] :=
          Nat.ModEq.of_dvd (dvd_mul_left q m) hn
        exact ((hnq.trans t.property.2).add_right (v u)).trans hzmod
      · obtain ⟨p, hp, hpK, hpn⟩ := hF a haF
        refine ⟨p, hp, hpK.trans (le_max_left _ _), ?_⟩
        intro n hn
        have hnm : n ≡ (t : ℕ) [MOD m] :=
          Nat.ModEq.of_dvd (dvd_mul_right m q) hn
        exact hpn n (hnm.trans t.property.1)

/-- A finite left factor with two distinct elements cannot have a sumset
agreeing with all primes beyond one fixed cutoff. -/
theorem no_finite_nontrivial_left {A B : Set ℕ} {N x y : ℕ}
    (hfin : A.Finite) (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y)
    (hN : ∀ n : ℕ, N < n → (n ∈ A + B ↔ n.Prime)) : False := by
  classical
  let F := hfin.toFinset
  let v : ℕ → ℕ := fun a => if a = x then y else x
  have hvA (a : ℕ) : v a ∈ A := by
    dsimp [v]
    split_ifs <;> assumption
  have hvne (a : ℕ) : v a ≠ a := by
    dsimp [v]
    split_ifs <;> omega
  obtain ⟨m, r, K, hm, hr, hblock⟩ := finite_shift_crt F v (fun a _ => hvne a)
  obtain ⟨p, hplarge, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (N + F.sup id + K) (ne_of_gt hm) hr
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Set.mem_add.mp ((hN p (by omega)).mpr hp)
  have haF : a ∈ F := by simpa [F] using ha
  have haM : a ≤ F.sup id := Finset.le_sup (f := id) haF
  obtain ⟨q, hq, hqK, hqmod⟩ := hblock a haF
  have hcong := hqmod p hpmod
  have hshift : a + (v a + b) ≡ a + 0 [MOD q] := by
    convert hcong using 1
    omega
  have hdvd : q ∣ v a + b :=
    Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' a hshift)
  have hprime : (v a + b).Prime :=
    (hN (v a + b) (by omega)).mp (Set.add_mem_add (hvA a) hb)
  have heq : q = v a + b := (Nat.prime_dvd_prime_iff_eq hq hprime).mp hdvd
  omega

/-- Two distinct left elements force an infinite left factor. -/
theorem left_infinite_of_two_mem {A B : Set ℕ} {N x y : ℕ}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y)
    (hN : ∀ n : ℕ, N < n → (n ∈ A + B ↔ n.Prime)) : A.Infinite := by
  intro hfin
  exact no_finite_nontrivial_left hfin hx hy hxy hN

/-- The symmetric statement for the right factor. -/
theorem right_infinite_of_two_mem {A B : Set ℕ} {N x y : ℕ}
    (hx : x ∈ B) (hy : y ∈ B) (hxy : x ≠ y)
    (hN : ∀ n : ℕ, N < n → (n ∈ A + B ↔ n.Prime)) : B.Infinite := by
  apply left_infinite_of_two_mem (B := A) (N := N) hx hy hxy
  intro n hn
  simpa [add_comm] using hN n hn

end FiniteFactorResearch
