import Submission.ShiftedPrimeCounting
import Submission.PrimitiveTotientCollisions

/-!
# Rectangles in the prime-predecessor incidence graph

The purpose of this investigation is to distinguish many genuine primitive
collisions from an increase in the inverse-totient multiplicity exponent.
No settlement of Erdős 821 is asserted in this file.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821.PrimeRectangles

lemma sum_column_cards (A B : Finset ℕ) (E : Finset (ℕ × ℕ))
    (hE : E ⊆ A ×ˢ B) :
    ∑ b ∈ B, (A.filter (fun a => (a,b) ∈ E)).card = E.card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := E) (t := B) (f := Prod.snd)
    (fun ab hab => (Finset.mem_product.mp (hE hab)).2)
  rw [h]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.card_bij (fun a _ => (a,b))
  · intro a ha
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).2, rfl⟩
  · intro a ha c hc he
    exact congrArg Prod.fst he
  · intro ab hab
    obtain ⟨hab, he⟩ := Finset.mem_filter.mp hab
    refine ⟨ab.1, Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (hE hab)).1, ?_⟩, ?_⟩
    · rw [← he]
      exact hab
    · exact Prod.ext rfl he.symm

lemma sum_row_cards (A B : Finset ℕ) (E : Finset (ℕ × ℕ))
    (hE : E ⊆ A ×ˢ B) :
    ∑ a ∈ A, (B.filter (fun b => (a,b) ∈ E)).card = E.card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := E) (t := A) (f := Prod.fst)
    (fun ab hab => (Finset.mem_product.mp (hE hab)).1)
  rw [h]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.card_bij (fun b _ => (a,b))
  · intro b hb
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hb).2, rfl⟩
  · intro b hb c hc he
    exact congrArg Prod.snd he
  · intro ab hab
    obtain ⟨hab, he⟩ := Finset.mem_filter.mp hab
    refine ⟨ab.2, Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (hE hab)).2, ?_⟩, ?_⟩
    · rw [← he]
      exact hab
    · exact Prod.ext he.symm rfl

lemma sum_column_sq_eq_common (A B : Finset ℕ) (E : Finset (ℕ × ℕ)) :
    (∑ b ∈ B, (A.filter (fun a => (a,b) ∈ E)).card ^ 2) =
      ∑ a ∈ A, ∑ c ∈ A,
        (B.filter (fun b => (a,b) ∈ E ∧ (c,b) ∈ E)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp_all

/-- The elementary rectangle-free incidence bound. -/
lemma card_sq_le_of_no_rectangle (A B : Finset ℕ) (E : Finset (ℕ × ℕ))
    (hE : E ⊆ A ×ˢ B)
    (hfree : ∀ a ∈ A, ∀ c ∈ A, a ≠ c → ∀ b ∈ B, ∀ d ∈ B,
      (a,b) ∈ E → (c,b) ∈ E → (a,d) ∈ E → (c,d) ∈ E → b = d) :
    E.card ^ 2 ≤ B.card * (E.card + A.card ^ 2) := by
  have hcommon (a : ℕ) (ha : a ∈ A) (c : ℕ) (hc : c ∈ A) :
      (B.filter (fun b => (a,b) ∈ E ∧ (c,b) ∈ E)).card ≤
        (if a = c then (B.filter (fun b => (a,b) ∈ E)).card else 0) + 1 := by
    by_cases hac : a = c
    · subst c
      simp only [and_self, ite_true]
      omega
    · rw [if_neg hac, zero_add]
      apply Finset.card_le_one.mpr
      intro b hb d hd
      obtain ⟨hbB, hab, hcb⟩ := Finset.mem_filter.mp hb
      obtain ⟨hdB, had, hcd⟩ := Finset.mem_filter.mp hd
      exact hfree a ha c hc hac b hbB d hdB hab hcb had hcd
  have hbound : (∑ b ∈ B, (A.filter (fun a => (a,b) ∈ E)).card ^ 2) ≤
      E.card + A.card ^ 2 := by
    rw [sum_column_sq_eq_common]
    calc
      _ ≤ ∑ a ∈ A, ∑ c ∈ A,
          ((if a = c then (B.filter (fun b => (a,b) ∈ E)).card else 0) + 1) :=
        Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun c hc => hcommon a ha c hc))
      _ = E.card + A.card ^ 2 := by
        simp only [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq, Finset.sum_const, Nat.nsmul_eq_mul, mul_one]
        simp only [Finset.sum_congr rfl (fun a ha => if_pos ha)]
        rw [sum_row_cards A B E hE]
        simp [pow_two]
  have hcs := sq_sum_le_card_mul_sum_sq (s := B)
    (f := fun b => (A.filter (fun a => (a,b) ∈ E)).card)
  rw [sum_column_cards A B E hE] at hcs
  exact hcs.trans (Nat.mul_le_mul_left _ hbound)

lemma exists_rectangle_of_card (A B : Finset ℕ) (E : Finset (ℕ × ℕ))
    (hE : E ⊆ A ×ˢ B)
    (hcard : B.card * (E.card + A.card ^ 2) < E.card ^ 2) :
    ∃ a ∈ A, ∃ c ∈ A, a ≠ c ∧ ∃ b ∈ B, ∃ d ∈ B, b ≠ d ∧
      (a,b) ∈ E ∧ (c,b) ∈ E ∧ (a,d) ∈ E ∧ (c,d) ∈ E := by
  by_contra H
  push_neg at H
  have hfree : ∀ a ∈ A, ∀ c ∈ A, a ≠ c → ∀ b ∈ B, ∀ d ∈ B,
      (a,b) ∈ E → (c,b) ∈ E → (a,d) ∈ E → (c,d) ∈ E → b = d := by
    intro a ha c hc hac b hb d hd hab hcb had hcd
    by_contra hbd
    exact H a ha c hc hac b hb d hd hbd hab hcb had hcd
  exact (not_lt_of_ge (card_sq_le_of_no_rectangle A B E hE hfree)) hcard

set_option linter.style.existsImplication false in
lemma exists_canonical_edges (P : Finset ℕ) (Q B : ℕ)
    (hP : ∀ p ∈ P, ∃ a ∈ Finset.Icc 1 Q, ∃ b ∈ Finset.Icc 1 B, a*b+1=p) :
    ∃ E : Finset (ℕ × ℕ), E ⊆ Finset.Icc 1 Q ×ˢ Finset.Icc 1 B ∧
      E.card = P.card ∧ (∀ ab ∈ E, ab.1*ab.2+1 ∈ P) ∧
      Set.InjOn (fun ab : ℕ × ℕ => ab.1*ab.2+1) (E : Set (ℕ × ℕ)) := by
  have H : ∀ p : ℕ, ∃ ab : ℕ × ℕ, p ∈ P →
      ab ∈ Finset.Icc 1 Q ×ˢ Finset.Icc 1 B ∧ ab.1*ab.2+1=p := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨a, ha, b, hb, he⟩ := hP p hp
      exact ⟨(a,b), fun _ => ⟨Finset.mem_product.mpr ⟨ha,hb⟩, he⟩⟩
    · exact ⟨(0,0), fun h => (hp h).elim⟩
  choose f hf using H
  have hinj : Set.InjOn f (P : Set ℕ) := by
    intro p hp q hq he
    exact ((hf p hp).2.symm.trans (congrArg (fun ab : ℕ × ℕ => ab.1*ab.2+1) he)).trans
      (hf q hq).2
  refine ⟨P.image f, ?_, Finset.card_image_of_injOn hinj, ?_, ?_⟩
  · intro ab hab
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hab
    exact (hf p hp).1
  · intro ab hab
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hab
    rwa [(hf p hp).2]
  · intro ab hab cd hcd he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hab
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hcd
    have hpq : p = q := by
      dsimp only at he
      rwa [(hf p hp).2, (hf q hq).2] at he
    exact congrArg f hpq

/-- Injectively labelled prime edges yield a collision between two coprime
squarefree semiprimes. All four input primes can be required to be large. -/
lemma exists_primitive_semiprimes_of_edges (A B : Finset ℕ) (E : Finset (ℕ × ℕ))
    (L : ℕ) (hE : E ⊆ A ×ˢ B)
    (hcard : B.card * (E.card + A.card ^ 2) < E.card ^ 2)
    (hprime : ∀ ab ∈ E, (ab.1*ab.2+1).Prime ∧ L < ab.1*ab.2+1)
    (hinj : Set.InjOn (fun ab : ℕ × ℕ => ab.1*ab.2+1) (E : Set (ℕ × ℕ))) :
    ∃ u v : ℕ, L < u ∧ L < v ∧ u ≠ v ∧ Squarefree u ∧ Squarefree v ∧
      Nat.Coprime u v ∧ Nat.totient u = Nat.totient v ∧
      u.primeFactors.card = 2 ∧ v.primeFactors.card = 2 := by
  obtain ⟨a, ha, c, hc, hac, b, hb, d, hd, hbd, hab, hcb, had, hcd⟩ :=
    exists_rectangle_of_card A B E hE hcard
  let p := a*b+1
  let q := c*d+1
  let r := c*b+1
  let t := a*d+1
  have hp : p.Prime ∧ L < p := hprime (a,b) hab
  have hq : q.Prime ∧ L < q := hprime (c,d) hcd
  have hr : r.Prime ∧ L < r := hprime (c,b) hcb
  have ht : t.Prime ∧ L < t := hprime (a,d) had
  have hpq : p ≠ q := fun he => hac (congrArg Prod.fst (hinj hab hcd he))
  have hpr : p ≠ r := fun he => hac (congrArg Prod.fst (hinj hab hcb he))
  have hpt : p ≠ t := fun he => hbd (congrArg Prod.snd (hinj hab had he))
  have hqr : q ≠ r := fun he => hbd (congrArg Prod.snd (hinj hcb hcd he.symm))
  have hqt : q ≠ t := fun he => hac (congrArg Prod.fst (hinj had hcd he.symm))
  have hrt : r ≠ t := fun he => hac (congrArg Prod.fst (hinj had hcb he.symm))
  have hc_pq := (Nat.coprime_primes hp.1 hq.1).mpr hpq
  have hc_rt := (Nat.coprime_primes hr.1 ht.1).mpr hrt
  have hcop : Nat.Coprime (p*q) (r*t) := by
    rw [Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right,
      Nat.coprime_mul_iff_right]
    exact ⟨⟨(Nat.coprime_primes hp.1 hr.1).mpr hpr,
      (Nat.coprime_primes hp.1 ht.1).mpr hpt⟩,
      ⟨(Nat.coprime_primes hq.1 hr.1).mpr hqr,
      (Nat.coprime_primes hq.1 ht.1).mpr hqt⟩⟩
  have hφ : Nat.totient (p*q) = Nat.totient (r*t) := by
    rw [Nat.totient_mul hc_pq, Nat.totient_mul hc_rt,
      Nat.totient_prime hp.1, Nat.totient_prime hq.1,
      Nat.totient_prime hr.1, Nat.totient_prime ht.1]
    dsimp [p,q,r,t]
    ring
  have hsmall1 : L < p*q := hp.2.trans_le (Nat.le_mul_of_pos_right _ hq.1.pos)
  have hsmall2 : L < r*t := hr.2.trans_le (Nat.le_mul_of_pos_right _ ht.1.pos)
  have hne : p*q ≠ r*t := by
    intro he
    have h := hcop
    rw [← he, Nat.coprime_self] at h
    have hpq1 : 1 < p*q := hp.1.one_lt.trans_le (Nat.le_mul_of_pos_right _ hq.1.pos)
    omega
  refine ⟨p*q, r*t, hsmall1, hsmall2, hne,
    (Nat.squarefree_mul hc_pq).mpr ⟨hp.1.squarefree, hq.1.squarefree⟩,
    (Nat.squarefree_mul hc_rt).mpr ⟨hr.1.squarefree, ht.1.squarefree⟩,
    hcop, hφ, ?_, ?_⟩
  · have hprod : ∏ z ∈ ({p,q} : Finset ℕ), z = p*q := Finset.prod_pair hpq
    rw [← hprod, Nat.primeFactors_prod (by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hp.1
      · exact hq.1)]
    simp [hpq]
  · have hprod : ∏ z ∈ ({r,t} : Finset ℕ), z = r*t := Finset.prod_pair hrt
    rw [← hprod, Nat.primeFactors_prod (by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hr.1
      · exact ht.1)]
    simp [hrt]

open AnalyticSieve

lemma rectangle_prime_family_at_scale (L : ℕ) (hL : 1 ≤ L)
    (hsmall : 32768000000000000 * (L+1)^7 ≤ 2^L) :
    ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ 2^(63*L) < p ∧ p ≤ 2^(64*L)) ∧
      (∀ p ∈ P, ∃ a ∈ Finset.Icc 1 (2^(30*L)),
        ∃ b ∈ Finset.Icc 1 (2^(35*L)), a*b+1=p) ∧
      2^(63*L) ≤ P.card ∧ P.card ≤ 2^(64*L) := by
  let M := primeModuliBetween (progressionScaleD L L) (progressionScaleQ L L)
  let P := shiftedWitnessPrimes M (progressionScaleB L L) (progressionScaleN L)
  have hD : progressionScaleD L L = 2^(29*L) := by
    unfold progressionScaleD
    congr 1
    omega
  have hQ : progressionScaleQ L L = 2^(30*L) := by
    unfold progressionScaleQ
    congr 1
    omega
  have hB : progressionScaleB L L = 2^(63*L) := by
    unfold progressionScaleB
    congr 1
    omega
  have hN : progressionScaleN L = 2^(64*L) := rfl
  have hquot : progressionScaleN L / progressionScaleD L L = 2^(35*L) := by
    rw [progression_scale_cofactor (le_refl L)]
    congr 1
    omega
  have hcount := progression_scale_prime_count hL (le_refl L) hsmall
  change progressionScaleN L ≤ 8388608 * L^3 * P.card at hcount
  have hpoly : 8388608 * L^3 ≤ 2^L := by
    have hp : L^3 ≤ (L+1)^7 :=
      (Nat.pow_le_pow_left (Nat.le_succ L) 3).trans
        (Nat.pow_le_pow_right (by omega : 0 < L+1) (by norm_num : 3 ≤ 7))
    omega
  have hlow : 2^(63*L) ≤ P.card := by
    apply Nat.le_of_mul_le_mul_left (c := 2^L) _ (by positivity)
    have heq : 2^L * 2^(63*L) = progressionScaleN L := by
      rw [← pow_add, hN]
      congr 1
      omega
    rw [heq]
    exact hcount.trans (Nat.mul_le_mul_right P.card hpoly)
  have hup : P.card ≤ 2^(64*L) := by
    have hs : P ⊆ Finset.Icc 1 (progressionScaleN L) := Finset.filter_subset _ _
    simpa only [Nat.card_Icc, Nat.add_sub_cancel, hN] using Finset.card_le_card hs
  refine ⟨P, ?_, ?_, hlow, hup⟩
  · intro p hp
    obtain ⟨hpI, hpr, hBp, hw⟩ := Finset.mem_filter.mp hp
    exact ⟨hpr, hB ▸ hBp, hN ▸ (Finset.mem_Icc.mp hpI).2⟩
  · intro p hp
    obtain ⟨hpI, hpr, hBp, q, hq, hres⟩ := Finset.mem_filter.mp hp
    have hqd := (mem_primeModuliBetween.mp hq)
    have hdvd : (q : ℕ) ∣ p-1 := (residue_one_iff_dvd_pred hpr.pos).mp hres
    have hp1 : 0 < p-1 := Nat.sub_pos_of_lt hpr.one_lt
    have hb0 : 0 < (p-1)/(q : ℕ) := Nat.div_pos (Nat.le_of_dvd hp1 hdvd) q.pos
    have hbup : (p-1)/(q : ℕ) ≤ progressionScaleN L / progressionScaleD L L := by
      apply (Nat.le_div_iff_mul_le (by rw [hD]; positivity)).mpr
      calc
        _ ≤ ((p-1)/(q : ℕ))*(q : ℕ) := Nat.mul_le_mul_left _ hqd.2.1
        _ = p-1 := Nat.div_mul_cancel hdvd
        _ ≤ progressionScaleN L := by have := (Finset.mem_Icc.mp hpI).2; omega
    refine ⟨q, Finset.mem_Icc.mpr ⟨q.pos, hQ ▸ hqd.2.2⟩,
      (p-1)/(q : ℕ), Finset.mem_Icc.mpr ⟨hb0, hquot ▸ hbup⟩, ?_⟩
    rw [Nat.mul_div_cancel' hdvd]
    omega

lemma primitive_semiprime_collision_at_scale (L : ℕ) (hL : 1 ≤ L)
    (hsmall : 32768000000000000 * (L+1)^7 ≤ 2^L) :
    ∃ u v : ℕ, 2^(63*L) < u ∧ 2^(63*L) < v ∧ u ≠ v ∧
      Squarefree u ∧ Squarefree v ∧ Nat.Coprime u v ∧
      Nat.totient u = Nat.totient v ∧
      u.primeFactors.card = 2 ∧ v.primeFactors.card = 2 := by
  obtain ⟨P, hP, hfac, hlow, hup⟩ := rectangle_prime_family_at_scale L hL hsmall
  obtain ⟨E, hE, hEP, hprime, hinj⟩ := exists_canonical_edges P (2^(30*L)) (2^(35*L)) hfac
  apply exists_primitive_semiprimes_of_edges (Finset.Icc 1 (2^(30*L)))
    (Finset.Icc 1 (2^(35*L))) E (2^(63*L)) hE ?_ ?_ hinj
  · simp only [Nat.card_Icc, Nat.add_sub_cancel, hEP]
    have hQ2 : (2^(30*L))^2 ≤ 2^(64*L) := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have hsize : 2^(35*L) * (P.card + (2^(30*L))^2) ≤ 2^(99*L+1) := by
      calc
        _ ≤ 2^(35*L) * (2^(64*L) + 2^(64*L)) := by gcongr
        _ = 2^(99*L+1) := by
          rw [show (2 : ℕ)^(64*L) + 2^(64*L) = 2^(64*L+1) by
            rw [pow_succ]; omega, ← pow_add]
          congr 1
          omega
    have hstrict : 2^(99*L+1) < (2^(63*L))^2 := by
      rw [← pow_mul]
      apply Nat.pow_lt_pow_right (by decide)
      omega
    exact hsize.trans_lt (hstrict.trans_le (Nat.pow_le_pow_left hlow 2))
  · intro ab hab
    exact ⟨(hP _ (hprime ab hab)).1, (hP _ (hprime ab hab)).2.1⟩

/-- An unconditional supply of nontrivial primitive collisions with exactly
two prime factors on each side. This does not give polynomially large fibers. -/
theorem exists_large_primitive_semiprime_collision (K : ℕ) :
    ∃ u v : ℕ, K < u ∧ K < v ∧ u ≠ v ∧ Squarefree u ∧ Squarefree v ∧
      Nat.Coprime u v ∧ Nat.totient u = Nat.totient v ∧
      u.primeFactors.card = 2 ∧ v.primeFactors.card = 2 := by
  have H : ∀ᶠ L : ℕ in atTop,
      32768000000000000 * (L+1)^7 ≤ 2^L := by
    simpa only [one_mul] using eventually_nat_poly_le_two_pow 1 32768000000000000 7
  obtain ⟨T, hT⟩ := eventually_atTop.mp H
  let L := max T (K+1)
  have hL : 1 ≤ L := by dsimp [L]; omega
  obtain ⟨u, v, hu, hv, hrest⟩ :=
    primitive_semiprime_collision_at_scale L hL (hT L (le_max_left _ _))
  have hKL : K < L := by dsimp [L]; omega
  have hLP : L ≤ 2^(63*L) := by
    exact (Nat.lt_two_pow_self (n := L)).le.trans
      (Nat.pow_le_pow_right (by decide) (by omega))
  exact ⟨u, v, hKL.trans (hLP.trans_lt hu), hKL.trans (hLP.trans_lt hv), hrest⟩

/-- The common outputs themselves are unbounded, not only the two inputs. -/
theorem infinite_primitive_semiprime_outputs :
    {n : ℕ | ∃ u v : ℕ, u ≠ v ∧ Squarefree u ∧ Squarefree v ∧
      Nat.Coprime u v ∧ Nat.totient u = n ∧ Nat.totient v = n ∧
      u.primeFactors.card = 2 ∧ v.primeFactors.card = 2}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro K
  obtain ⟨u, v, hu, hv, hne, hsu, hsv, hcop, hφ, hcu, hcv⟩ :=
    exists_large_primitive_semiprime_collision (24*K^2)
  have hbound : u ≤ 24*(Nat.totient u)^2 := by
    simpa using input_pow_le_totient_pow u 1 (by decide)
  have hlarge : K < Nat.totient u := by
    by_contra H
    have hle := Nat.pow_le_pow_left (le_of_not_gt H) 2
    omega
  exact ⟨Nat.totient u, ⟨u, v, hne, hsu, hsv, hcop, rfl, hφ.symm, hcu, hcv⟩, hlarge⟩

end Erdos821.PrimeRectangles
