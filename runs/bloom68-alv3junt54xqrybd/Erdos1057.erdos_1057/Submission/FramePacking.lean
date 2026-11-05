import Submission.PrimePool
import Submission.Certificates

/-!
# Inverse-residue packet-deletion bounds for actual Carmichael frames

A product-one family can be counted by deleting packets whose labels are
injective: a remainder determines the deleted packet, and hence the original
set. No uniform distribution of prime residues is assumed. For rational-prime
packets, injectivity follows whenever their integer products lie in an interval
of width less than the modulus.

These are unconditional finite counting lemmas, not a density theorem or its
negation. No declaration from `Submission.Spec` is imported or used.
-/

open Finset

namespace ProductOnePacking

variable {α G : Type*} [CommMonoid G]

/-- A remainder of a product-one set uniquely determines the label of its
removed packet. Only a commutative monoid is needed: the remainder is a unit. -/
theorem packet_label_eq_of_remainder_eq [DecidableEq α]
    {S T U V : Finset α} {g : α → G}
    (hUS : U ⊆ S) (hVT : V ⊆ T)
    (hS : (∏ a ∈ S, g a) = 1) (hT : (∏ a ∈ T, g a) = 1)
    (hrem : S \ U = T \ V) :
    (∏ a ∈ U, g a) = ∏ a ∈ V, g a := by
  have hSU : (∏ a ∈ S \ U, g a) * (∏ a ∈ U, g a) = 1 := by
    rw [Finset.prod_sdiff hUS, hS]
  have hTV : (∏ a ∈ T \ V, g a) * (∏ a ∈ V, g a) = 1 := by
    rw [Finset.prod_sdiff hVT, hT]
  have hunit : IsUnit (∏ a ∈ S \ U, g a) :=
    IsUnit.of_mul_eq_one (∏ a ∈ U, g a) hSU
  apply hunit.mul_left_cancel
  rw [hSU, hrem, hTV]

/-- Packet/remainder encoding is injective, even when packet sizes vary. -/
theorem deletion_remainder_injOn [DecidableEq α]
    {F Q : Finset (Finset α)} {g : α → G}
    (hprod : ∀ S ∈ F, (∏ a ∈ S, g a) = 1)
    (hinj : Set.InjOn (fun U : Finset α => ∏ a ∈ U, g a) (Q : Set (Finset α))) :
    Set.InjOn (fun e : Sigma fun _ : Finset α => Finset α => e.1 \ e.2)
      (F.sigma (fun S => Q.filter (fun U => U ⊆ S)) :
        Set (Sigma fun _ : Finset α => Finset α)) := by
  classical
  intro e he d hd heq
  change e.1 \ e.2 = d.1 \ d.2 at heq
  obtain ⟨heF, heQ⟩ := Finset.mem_sigma.mp he
  obtain ⟨hdF, hdQ⟩ := Finset.mem_sigma.mp hd
  obtain ⟨heQ, heSub⟩ := Finset.mem_filter.mp heQ
  obtain ⟨hdQ, hdSub⟩ := Finset.mem_filter.mp hdQ
  have hpacket : e.2 = d.2 := hinj heQ hdQ
    (packet_label_eq_of_remainder_eq heSub hdSub
      (hprod e.1 heF) (hprod d.1 hdF) heq)
  have hset : e.1 = d.1 := by
    calc
      e.1 = e.2 ∪ (e.1 \ e.2) := (Finset.union_sdiff_of_subset heSub).symm
      _ = d.2 ∪ (d.1 \ d.2) := by rw [heq, hpacket]
      _ = d.1 := Finset.union_sdiff_of_subset hdSub
  cases e
  cases d
  simp_all

/-- General packet-deletion packing. Packet sizes may vary. If labels are
injective on the permitted packets, each permitted remainder comes from at
most one original-set/packet pair. -/
theorem packet_deletion_bound [DecidableEq α]
    {F Q R : Finset (Finset α)} {g : α → G}
    (hprod : ∀ S ∈ F, (∏ a ∈ S, g a) = 1)
    (hinj : Set.InjOn (fun U : Finset α => ∏ a ∈ U, g a) (Q : Set (Finset α)))
    (hrem : ∀ S ∈ F, ∀ U ∈ Q, U ⊆ S → S \ U ∈ R) :
    (∑ S ∈ F, (Q.filter (fun U => U ⊆ S)).card) ≤ R.card := by
  classical
  let E := F.sigma (fun S => Q.filter (fun U => U ⊆ S))
  let f : (Sigma fun _ : Finset α => Finset α) → Finset α :=
    fun e => e.1 \ e.2
  have hf : Set.InjOn f (E : Set (Sigma fun _ : Finset α => Finset α)) :=
    deletion_remainder_injOn hprod hinj
  have hsub : E.image f ⊆ R := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨heF, heQ⟩ := Finset.mem_sigma.mp he
    obtain ⟨heQ, heSub⟩ := Finset.mem_filter.mp heQ
    exact hrem e.1 heF e.2 heQ heSub
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hf] at hcard
  simpa only [E, Finset.card_sigma] using hcard

/-- Nonnegative weighted packet packing. Weights are attached to remainders,
so no equidistribution or cancellation estimate is hidden in the bound. -/
theorem weighted_packet_deletion_bound [DecidableEq α]
    {F Q R : Finset (Finset α)} {g : α → G} {w : Finset α → ℝ}
    (hprod : ∀ S ∈ F, (∏ a ∈ S, g a) = 1)
    (hinj : Set.InjOn (fun U : Finset α => ∏ a ∈ U, g a) (Q : Set (Finset α)))
    (hrem : ∀ S ∈ F, ∀ U ∈ Q, U ⊆ S → S \ U ∈ R)
    (hw : ∀ V ∈ R, 0 ≤ w V) :
    (∑ S ∈ F, ∑ U ∈ Q.filter (fun U => U ⊆ S), w (S \ U)) ≤ ∑ V ∈ R, w V := by
  classical
  let E := F.sigma (fun S => Q.filter (fun U => U ⊆ S))
  let f : (Sigma fun _ : Finset α => Finset α) → Finset α :=
    fun e => e.1 \ e.2
  have hf : Set.InjOn f (E : Set (Sigma fun _ : Finset α => Finset α)) :=
    deletion_remainder_injOn hprod hinj
  have hsub : E.image f ⊆ R := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨heF, heQ⟩ := Finset.mem_sigma.mp he
    obtain ⟨heQ, heSub⟩ := Finset.mem_filter.mp heQ
    exact hrem e.1 heF e.2 heQ heSub
  calc
    (∑ S ∈ F, ∑ U ∈ Q.filter (fun U => U ⊆ S), w (S \ U)) =
        ∑ e ∈ E, w (f e) := by rw [Finset.sum_sigma]
    _ = ∑ V ∈ E.image f, w V := (Finset.sum_image hf).symm
    _ ≤ ∑ V ∈ R, w V := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun V hV _ => hw V hV)


/-- Constant-cardinality form of packet packing, with no restriction on `j`.
The explicit hypothesis is injectivity of labels of `j`-element packets. -/
theorem card_mul_choose_le [DecidableEq α]
    {P : Finset α} {F : Finset (Finset α)} {g : α → G} {t j : ℕ}
    (hF : ∀ S ∈ F, S ⊆ P ∧ S.card = t ∧ (∏ a ∈ S, g a) = 1)
    (hinj : Set.InjOn (fun U : Finset α => ∏ a ∈ U, g a)
      (P.powersetCard j : Set (Finset α))) :
    F.card * Nat.choose t j ≤ Nat.choose P.card (t - j) := by
  classical
  have hcount : ∀ S ∈ F,
      ((P.powersetCard j).filter (fun U => U ⊆ S)).card = Nat.choose t j := by
    intro S hS
    have heq : (P.powersetCard j).filter (fun U => U ⊆ S) = S.powersetCard j := by
      ext U
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨_, hcard⟩, hUS⟩
        exact ⟨hUS, hcard⟩
      · rintro ⟨hUS, hcard⟩
        exact ⟨⟨hUS.trans (hF S hS).1, hcard⟩, hUS⟩
    rw [heq, Finset.card_powersetCard, (hF S hS).2.1]
  have hpack := packet_deletion_bound
    (F := F) (Q := P.powersetCard j) (R := P.powersetCard (t - j))
    (fun S hS => (hF S hS).2.2) hinj (by
      intro S hS U hU hUS
      have hUj := (Finset.mem_powersetCard.mp hU).2
      apply Finset.mem_powersetCard.mpr
      refine ⟨Finset.sdiff_subset.trans (hF S hS).1, ?_⟩
      rw [Finset.card_sdiff_of_subset hUS, (hF S hS).2.1, hUj])
  rw [Finset.sum_const_nat hcount, Finset.card_powersetCard] at hpack
  exact hpack

/-- Injectivity of single-element packet labels follows from injectivity of
individual labels. -/
theorem singleton_packets_injOn [DecidableEq α] {P : Finset α} {g : α → G}
    (hinj : Set.InjOn g (P : Set α)) :
    Set.InjOn (fun U : Finset α => ∏ a ∈ U, g a)
      (P.powersetCard 1 : Set (Finset α)) := by
  classical
  intro U hU V hV heq
  obtain ⟨hUP, hUcard⟩ := Finset.mem_powersetCard.mp hU
  obtain ⟨hVP, hVcard⟩ := Finset.mem_powersetCard.mp hV
  obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp hUcard
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hVcard
  have huv : u = v := hinj (hUP (by simp)) (hVP (by simp)) (by simpa using heq)
  rw [huv]

end ProductOnePacking

namespace Erdos1057.FramePacking

/-- Prime packets whose products lie in one half-open modulus-width interval. -/
def shortPackets (P : Finset ℕ) (L A j : ℕ) : Finset (Finset ℕ) :=
  (P.powersetCard j).filter (fun U => A ≤ (∏ p ∈ U, p) ∧ (∏ p ∈ U, p) < A + L)

/-- Possible remainders after deleting a packet of product at least `A`. -/
def heightRemainders (P : Finset ℕ) (X A k : ℕ) : Finset (Finset ℕ) :=
  (P.powersetCard k).filter (fun R => A * (∏ p ∈ R, p) ≤ X)

/-- Integer products of rational-prime packets in one modulus-width interval
have distinct residues. No prime-distribution input is used. -/
theorem shortPackets_labels_injOn {P : Finset ℕ} {L A j : ℕ}
    (hp : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun U : Finset ℕ => ∏ p ∈ U, (p : ZMod L))
      (shortPackets P L A j : Set (Finset ℕ)) := by
  intro U hU V hV heq
  obtain ⟨hUP, hUj⟩ := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hU).1
  obtain ⟨hVP, hVj⟩ := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hV).1
  obtain ⟨hUlo, hUhi⟩ := (Finset.mem_filter.mp hU).2
  obtain ⟨hVlo, hVhi⟩ := (Finset.mem_filter.mp hV).2
  have hmod : Nat.ModEq L (∏ p ∈ U, p) (∏ p ∈ V, p) := by
    apply (ZMod.natCast_eq_natCast_iff _ _ L).mp
    simpa only [Nat.cast_prod] using heq
  have heqNat : (∏ p ∈ U, p) = ∏ p ∈ V, p := by
    apply Nat.le_antisymm
    · exact hmod.le_of_lt_add (by omega)
    · exact hmod.symm.le_of_lt_add (by omega)
  exact PrimePool.prod_injOn_subsets hp hUP hVP heqNat

/-- Deleting a packet of height at least `A` gives the stated remainder
height. This arithmetic step does not require a congruence hypothesis. -/
theorem short_packet_remainder_mem {P S U : Finset ℕ} {L X A t j : ℕ}
    (hS : S ⊆ P ∧ S.card = t ∧ (∏ p ∈ S, p) ≤ X)
    (hU : U ∈ shortPackets P L A j) (hUS : U ⊆ S) :
    S \ U ∈ heightRemainders P X A (t - j) := by
  obtain ⟨_, hUj⟩ := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hU).1
  have hA : A ≤ ∏ p ∈ U, p := (Finset.mem_filter.mp hU).2.1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powersetCard.mpr
    ⟨Finset.sdiff_subset.trans hS.1, ?_⟩, ?_⟩
  · rw [Finset.card_sdiff_of_subset hUS, hS.2.1, hUj]
  · calc
      A * (∏ p ∈ S \ U, p) ≤ (∏ p ∈ U, p) * (∏ p ∈ S \ U, p) :=
        Nat.mul_le_mul_right _ hA
      _ = ∏ p ∈ S, p := by rw [mul_comm, Finset.prod_sdiff hUS]
      _ ≤ X := hS.2.2

/-- Height-sensitive packing for all product-one prime sets of size `t`.
The left side counts all admissible deletions, not just one witness per set. -/
theorem short_packet_deletion_bound {P : Finset ℕ} {F : Finset (Finset ℕ)}
    {L X A t j : ℕ} (hp : ∀ p ∈ P, p.Prime)
    (hF : ∀ S ∈ F, S ⊆ P ∧ S.card = t ∧
      (∏ p ∈ S, (p : ZMod L)) = 1 ∧ (∏ p ∈ S, p) ≤ X) :
    (∑ S ∈ F, ((shortPackets P L A j).filter (fun U => U ⊆ S)).card) ≤
      (heightRemainders P X A (t - j)).card := by
  exact ProductOnePacking.packet_deletion_bound
    (fun S hS => (hF S hS).2.2.1) (shortPackets_labels_injOn hp)
    (fun S hS U hU hUS => short_packet_remainder_mem
      ⟨(hF S hS).1, (hF S hS).2.1, (hF S hS).2.2.2⟩ hU hUS)

/-- A uniform-height corollary: every `j`-prime packet has height at most `L`,
so the full binomial packet family can be deleted injectively. -/
theorem card_mul_choose_le_of_prime_height {P : Finset ℕ} {F : Finset (Finset ℕ)}
    {L Y t j : ℕ} (hp : ∀ p ∈ P, p.Prime) (hY : ∀ p ∈ P, p ≤ Y)
    (hYj : Y ^ j ≤ L)
    (hF : ∀ S ∈ F, S ⊆ P ∧ S.card = t ∧ (∏ p ∈ S, (p : ZMod L)) = 1) :
    F.card * Nat.choose t j ≤ Nat.choose P.card (t - j) := by
  have hshort : ∀ U ∈ P.powersetCard j, U ∈ shortPackets P L 1 j := by
    intro U hU
    obtain ⟨hUP, hUj⟩ := Finset.mem_powersetCard.mp hU
    have hpos : 0 < ∏ p ∈ U, p := Finset.prod_pos (fun p hpU => (hp p (hUP hpU)).pos)
    have hbound : (∏ p ∈ U, p) ≤ Y ^ j := by
      simpa only [hUj] using Finset.prod_le_pow_card U id Y (fun p hpU => hY p (hUP hpU))
    exact Finset.mem_filter.mpr ⟨hU, by omega⟩
  exact ProductOnePacking.card_mul_choose_le hF
    (fun U hU V hV heq => shortPackets_labels_injOn hp (hshort U hU) (hshort V hV) heq)

/-- Exact binomial identity identifying the gain in uniform-height packing. -/
theorem packing_gain_identity {r t j : ℕ} (hj : j ≤ t) (ht : t ≤ r) :
    Nat.choose r (t - j) * Nat.choose (r - t + j) j =
      Nat.choose r t * Nat.choose t j := by
  have hmul := Nat.choose_mul (n := r) (k := t) (s := t - j) (Nat.sub_le t j)
  have hdiff : r - (t - j) = r - t + j := by omega
  have hjdiff : t - (t - j) = j := by omega
  simpa only [hdiff, hjdiff, Nat.choose_symm hj] using hmul.symm

/-- This particular packing gain is never more than `L` when it is justified
solely by a uniform prime height `Y` and `Y^j ≤ L`. This is a method-specific
limitation, not an upper or lower claim about the true Carmichael count. -/
theorem packing_gain_le_modulus {r t j Y L : ℕ}
    (hj : j ≤ t) (ht : t ≤ r) (hrY : r ≤ Y) (hYj : Y ^ j ≤ L) :
    Nat.choose (r - t + j) j ≤ L := by
  have harg : r - t + j ≤ r := by omega
  calc
    Nat.choose (r - t + j) j ≤ (r - t + j) ^ j := Nat.choose_le_pow _ _
    _ ≤ r ^ j := Nat.pow_le_pow_left harg j
    _ ≤ Y ^ j := Nat.pow_le_pow_left hrY j
    _ ≤ L := hYj

/-- The actual prime pool of a frame, including unit compatibility. -/
noncomputable def primePool (L : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (L + 2)).filter
    (fun p => p.Prime ∧ p - 1 ∣ L ∧ p.Coprime L)

/-- Exact lambda, actual primality, compositeness, height and product-one are
all retained in this family. Each integer is represented by its prime set. -/
noncomputable def frameSubsets (L X t : ℕ) : Finset (Finset ℕ) := by
  classical
  exact ((primePool L).powersetCard t).filter (fun S =>
    IsCarmichael (∏ p ∈ S, p) ∧
    ArithmeticFunction.Carmichael (∏ p ∈ S, p) = L ∧ (∏ p ∈ S, p) ≤ X)

/-- The corresponding set of standard Carmichael integers. -/
def frameNumbers (L X t : ℕ) : Set ℕ :=
  {n | IsCarmichael n ∧ ArithmeticFunction.Carmichael n = L ∧
    n ≤ X ∧ n.primeFactors.card = t}

theorem primePool_prime {L p : ℕ} (hp : p ∈ primePool L) : p.Prime := by
  classical
  exact (Finset.mem_filter.mp hp).2.1

theorem primePool_bound {L p : ℕ} (hp : p ∈ primePool L) : p ≤ L + 1 := by
  classical
  have := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
  omega

/-- Every prime factor of an exact-frame Carmichael number belongs to the
actual unit-compatible prime pool; no prime is replaced by a divisor shift. -/
theorem primeFactors_subset_primePool {n L : ℕ}
    (hn : IsCarmichael n) (hLambda : ArithmeticFunction.Carmichael n = L) :
    n.primeFactors ⊆ primePool L := by
  classical
  have hLpos : 0 < L := by
    rw [← hLambda]
    exact CarmichaelCertificates.carmichael_divisor_pos hn (dvd_refl n)
  have hunit : n.Coprime L := by
    rw [← hLambda]
    exact CarmichaelCertificates.divisor_coprime_carmichael hn (dvd_refl n)
  intro p hp
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hpn := Nat.dvd_of_mem_primeFactors hp
  have hshift : p - 1 ∣ L := by
    rw [← hLambda, ← CarmichaelKorselt.carmichael_prime hpPrime]
    exact ArithmeticFunction.carmichael_dvd hpn
  have hle : p - 1 ≤ L := Nat.le_of_dvd hLpos hshift
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr (by have := hpPrime.two_le; omega),
    hpPrime, hshift, hunit.of_dvd_left hpn⟩

theorem frameSubsets_properties {L X t : ℕ} {S : Finset ℕ}
    (hS : S ∈ frameSubsets L X t) :
    S ⊆ primePool L ∧ S.card = t ∧
      (∏ p ∈ S, (p : ZMod L)) = 1 ∧ (∏ p ∈ S, p) ≤ X := by
  classical
  obtain ⟨hSp, hn, hLambda, hX⟩ := Finset.mem_filter.mp hS
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hSp
  refine ⟨hsub, hcard, ?_, hX⟩
  have hmod := CarmichaelCertificates.divisor_modEq_one hn (dvd_refl (∏ p ∈ S, p))
  rw [hLambda] at hmod
  have hz := (ZMod.natCast_eq_natCast_iff _ _ L).mpr hmod
  simpa only [Nat.cast_prod, Nat.cast_one] using hz

/-- The set encoding is exact and introduces no witness multiplicity. -/
theorem frameSubsets_image_eq (L X t : ℕ) :
    ((frameSubsets L X t).image (fun S => ∏ p ∈ S, p) : Set ℕ) = frameNumbers L X t := by
  classical
  ext n
  simp only [Finset.mem_coe]
  constructor
  · intro hn
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hSp, hCarm, hLambda, hX⟩ := Finset.mem_filter.mp hS
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hSp
    refine ⟨hCarm, hLambda, hX, ?_⟩
    rw [Nat.primeFactors_prod (fun p hp => primePool_prime (hsub hp)), hcard]
  · rintro ⟨hn, hLambda, hX, ht⟩
    have hsq := (CarmichaelKorselt.isCarmichael_iff_korselt n).mp hn |>.2.1
    have hprod := Nat.prod_primeFactors_of_squarefree hsq
    apply Finset.mem_image.mpr
    refine ⟨n.primeFactors, Finset.mem_filter.mpr ⟨?_, ?_⟩, hprod⟩
    · exact Finset.mem_powersetCard.mpr
        ⟨primeFactors_subset_primePool hn hLambda, ht⟩
    · simpa only [hprod] using (show IsCarmichael n ∧
        ArithmeticFunction.Carmichael n = L ∧ n ≤ X from ⟨hn, hLambda, hX⟩)

theorem frameSubsets_card_eq_ncard (L X t : ℕ) :
    (frameSubsets L X t).card = (frameNumbers L X t).ncard := by
  classical
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p)
      (frameSubsets L X t : Set (Finset ℕ)) := by
    intro S hS T hT heq
    simp only [Finset.mem_coe] at hS hT
    exact PrimePool.prod_injOn_subsets (fun p hp => primePool_prime hp)
      (frameSubsets_properties hS).1 (frameSubsets_properties hT).1 heq
  calc
    (frameSubsets L X t).card =
        ((frameSubsets L X t).image (fun S => ∏ p ∈ S, p)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = (((frameSubsets L X t).image (fun S => ∏ p ∈ S, p) : Set ℕ)).ncard :=
      (Set.ncard_coe_finset _).symm
    _ = (frameNumbers L X t).ncard := by rw [frameSubsets_image_eq]

/-- Eligible rational primes have distinct residues modulo their frame.
Their entire interval `[2,L+1]` has width less than `L`. -/
theorem primePool_labels_injOn (L : ℕ) :
    Set.InjOn (fun p : ℕ => (p : ZMod L)) (primePool L : Set ℕ) := by
  intro p hp q hq heq
  have hmod := (ZMod.natCast_eq_natCast_iff p q L).mp heq
  have hpLe := primePool_bound hp
  have hqLe := primePool_bound hq
  have hpTwo := (primePool_prime hp).two_le
  have hqTwo := (primePool_prime hq).two_le
  apply Nat.le_antisymm
  · exact hmod.le_of_lt_add (by omega)
  · exact hmod.symm.le_of_lt_add (by omega)

/-- Unconditional inverse-prime-deletion upper bound for every exact frame.
It uses actual primes and product-one, rather than all shifted divisors. -/
theorem ncard_frame_mul_card_le_choose (L X t : ℕ) :
    (frameNumbers L X t).ncard * t ≤ Nat.choose (primePool L).card (t - 1) := by
  have hbound := ProductOnePacking.card_mul_choose_le
    (F := frameSubsets L X t) (P := primePool L)
    (g := fun p => (p : ZMod L)) (j := 1)
    (fun S hS => ⟨(frameSubsets_properties hS).1,
      (frameSubsets_properties hS).2.1, (frameSubsets_properties hS).2.2.1⟩)
    (ProductOnePacking.singleton_packets_injOn (primePool_labels_injOn L))
  simpa only [Nat.choose_one_right, frameSubsets_card_eq_ncard] using hbound

/-- Unconditional short-packet packing for all exact Carmichael frames.
No bound on branch support, branch loads or the maximum prime is required. -/
theorem frame_short_packet_deletion_bound (L X A t j : ℕ) :
    (∑ S ∈ frameSubsets L X t,
      ((shortPackets (primePool L) L A j).filter (fun U => U ⊆ S)).card) ≤
      (heightRemainders (primePool L) X A (t - j)).card := by
  exact short_packet_deletion_bound (fun p hp => primePool_prime hp)
    (fun S hS => frameSubsets_properties hS)

/-- Weighted short-packet packing on the exact, unit-compatible Carmichael
frame. Keeping the remainder weights permits height-sensitive Rankin bounds
without discarding the product-one constraint. -/
theorem weighted_frame_short_packet_deletion_bound
    (L X A t j : ℕ) (w : Finset ℕ → ℝ)
    (hw : ∀ R ∈ heightRemainders (primePool L) X A (t - j), 0 ≤ w R) :
    (∑ S ∈ frameSubsets L X t,
      ∑ U ∈ (shortPackets (primePool L) L A j).filter (fun U => U ⊆ S), w (S \ U)) ≤
      ∑ R ∈ heightRemainders (primePool L) X A (t - j), w R := by
  exact ProductOnePacking.weighted_packet_deletion_bound
    (fun S hS => (frameSubsets_properties hS).2.2.1)
    (shortPackets_labels_injOn (fun p hp => primePool_prime hp))
    (fun S hS U hU hUS => short_packet_remainder_mem
      ⟨(frameSubsets_properties hS).1, (frameSubsets_properties hS).2.1,
        (frameSubsets_properties hS).2.2.2⟩ hU hUS) hw

/-- Divisor packets in one interval of width exactly the integer's own lambda. -/
noncomputable def windowDivisors (n A : ℕ) : Finset ℕ := by
  classical
  exact n.divisors.filter (fun d => A ≤ d ∧ d < A + ArithmeticFunction.Carmichael n)

/-- The bounded standard Carmichael set with all exact lambda frames allowed. -/
noncomputable def boundedCarmichaels (X H : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter
    (fun n => IsCarmichael n ∧ ArithmeticFunction.Carmichael n ≤ H)

/-- Fixed-frame inverse completion is unique for a divisor product in a
modulus-width interval. The packet need not be a prime or have bounded size. -/
theorem inverse_window_completion_unique {n m d e A : ℕ}
    (hn : IsCarmichael n) (hm : IsCarmichael m)
    (hLambda : ArithmeticFunction.Carmichael n = ArithmeticFunction.Carmichael m)
    (hd : d ∈ windowDivisors n A) (he : e ∈ windowDivisors m A)
    (hcofactor : n / d = m / e) : n = m ∧ d = e := by
  classical
  obtain ⟨hdd, hdlo, hdhi⟩ := Finset.mem_filter.mp hd
  obtain ⟨hed, helo, hehi⟩ := Finset.mem_filter.mp he
  have hdvd := Nat.dvd_of_mem_divisors hdd
  have hevd := Nat.dvd_of_mem_divisors hed
  have hunit : (n / d).Coprime (ArithmeticFunction.Carmichael n) :=
    (CarmichaelCertificates.divisor_coprime_carmichael hn (dvd_refl n)).of_dvd_left
      (Nat.div_dvd_of_dvd hdvd)
  have hnfac : (n / d) * d = n := by
    rw [mul_comm]
    exact Nat.mul_div_cancel' hdvd
  have hmfac : (n / d) * e = m := by
    rw [hcofactor, mul_comm]
    exact Nat.mul_div_cancel' hevd
  have hnmod := CarmichaelCertificates.divisor_modEq_one hn (dvd_refl n)
  have hmmod := CarmichaelCertificates.divisor_modEq_one hm (dvd_refl m)
  rw [← hLambda] at hmmod hehi
  have hprod : Nat.ModEq (ArithmeticFunction.Carmichael n) ((n / d) * d) ((n / d) * e) := by
    rw [hnfac, hmfac]
    exact hnmod.trans hmmod.symm
  have hdeMod := Nat.ModEq.cancel_left_of_coprime hunit.symm hprod
  have hde : d = e := Nat.le_antisymm
    (hdeMod.le_of_lt_add (by omega)) (hdeMod.symm.le_of_lt_add (by omega))
  refine ⟨?_, hde⟩
  rw [← hnfac, ← hmfac, hde]

/-- Global all-frame packing with an independently chosen center for each
exact lambda frame. The center may depend on the frame, but not freely on the
integer within that frame. The inverse-residue argument saves a factor `L`
over counting every divisor in that frame's entire length-`L` window. -/
theorem sum_frameWindowDivisors_le {X H : ℕ} (A : ℕ → ℕ)
    (hA : ∀ L ∈ Finset.Icc 1 H, 0 < A L) :
    (∑ n ∈ boundedCarmichaels X H,
      (windowDivisors n (A (ArithmeticFunction.Carmichael n))).card) ≤
      ∑ L ∈ Finset.Icc 1 H, X / A L := by
  classical
  let E := (boundedCarmichaels X H).sigma
    (fun n => windowDivisors n (A (ArithmeticFunction.Carmichael n)))
  let f : (Sigma fun _ : ℕ => ℕ) → (Sigma fun _ : ℕ => ℕ) :=
    fun e => ⟨ArithmeticFunction.Carmichael e.1, e.1 / e.2⟩
  have hf : Set.InjOn f (E : Set (Sigma fun _ : ℕ => ℕ)) := by
    intro e he d hd heq
    obtain ⟨hen, hew⟩ := Finset.mem_sigma.mp he
    obtain ⟨hdn, hdw⟩ := Finset.mem_sigma.mp hd
    have hCarmE := (Finset.mem_filter.mp hen).2.1
    have hCarmD := (Finset.mem_filter.mp hdn).2.1
    have hLambda : ArithmeticFunction.Carmichael e.1 = ArithmeticFunction.Carmichael d.1 :=
      congrArg Sigma.fst heq
    have hcofactor : e.1 / e.2 = d.1 / d.2 := congrArg Sigma.snd heq
    have hdw' : d.2 ∈ windowDivisors d.1 (A (ArithmeticFunction.Carmichael e.1)) := by
      simpa only [hLambda] using hdw
    obtain ⟨hnEq, hwEq⟩ := inverse_window_completion_unique hCarmE hCarmD
      hLambda hew hdw' hcofactor
    cases e
    cases d
    simp_all
  have hsub : E.image f ⊆ (Finset.Icc 1 H).sigma (fun L => Finset.Icc 1 (X / A L)) := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hen, hew⟩ := Finset.mem_sigma.mp he
    obtain ⟨heIcc, hCarm, hLambda⟩ := Finset.mem_filter.mp hen
    obtain ⟨_, hnX⟩ := Finset.mem_Icc.mp heIcc
    obtain ⟨hed, hAlo, _⟩ := Finset.mem_filter.mp hew
    have hdvd := Nat.dvd_of_mem_divisors hed
    have hLpos : 1 ≤ ArithmeticFunction.Carmichael e.1 :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt
        (CarmichaelCertificates.carmichael_divisor_pos hCarm (dvd_refl e.1)))
    have hLmem : ArithmeticFunction.Carmichael e.1 ∈ Finset.Icc 1 H :=
      Finset.mem_Icc.mpr ⟨hLpos, hLambda⟩
    have hcpos : 1 ≤ e.1 / e.2 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt
      (CarmichaelCertificates.divisor_pos hCarm (Nat.div_dvd_of_dvd hdvd)))
    have hcX : e.1 / e.2 ≤ X / A (ArithmeticFunction.Carmichael e.1) := by
      apply (Nat.le_div_iff_mul_le (hA _ hLmem)).mpr
      calc
        e.1 / e.2 * A (ArithmeticFunction.Carmichael e.1) ≤ e.1 / e.2 * e.2 :=
          Nat.mul_le_mul_left _ hAlo
        _ = e.1 := by rw [mul_comm]; exact Nat.mul_div_cancel' hdvd
        _ ≤ X := hnX
    exact Finset.mem_sigma.mpr ⟨hLmem, Finset.mem_Icc.mpr ⟨hcpos, hcX⟩⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hf] at hcard
  simp only [Finset.card_sigma, Nat.card_Icc, Nat.add_sub_cancel] at hcard
  simpa only [E, Finset.card_sigma] using hcard

/-- Constant-center corollary. This numerical corollary also follows from
ordinary divisor-union counting and by itself is not a new Korselt gap. -/
theorem sum_windowDivisors_le {X H A : ℕ} (hA : 0 < A) :
    (∑ n ∈ boundedCarmichaels X H, (windowDivisors n A).card) ≤ H * (X / A) := by
  have hbound := sum_frameWindowDivisors_le (X := X) (H := H) (fun _ => A) (fun _ _ => hA)
  simpa using hbound

/-- The all-frame stratum with at least `b` divisor packets in the prescribed
lambda-width window. No statement that all Carmichael numbers are rich is made. -/
noncomputable def windowRichCarmichaels (X H A b : ℕ) : Finset ℕ := by
  classical
  exact (boundedCarmichaels X H).filter (fun n => b ≤ (windowDivisors n A).card)

/-- An evaluated global upper bound for the packet-rich stratum. No rarity of
eligible primes, branch concentration or frame-support restriction is assumed. -/
theorem card_windowRich_mul_le {X H A b : ℕ} (hA : 0 < A) :
    (windowRichCarmichaels X H A b).card * b ≤ H * (X / A) := by
  classical
  calc
    (windowRichCarmichaels X H A b).card * b =
        ∑ _ ∈ windowRichCarmichaels X H A b, b := by simp
    _ ≤ ∑ n ∈ windowRichCarmichaels X H A b, (windowDivisors n A).card :=
      Finset.sum_le_sum (fun n hn => (Finset.mem_filter.mp hn).2)
    _ ≤ ∑ n ∈ boundedCarmichaels X H, (windowDivisors n A).card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)
    _ ≤ H * (X / A) := sum_windowDivisors_le hA

end Erdos1057.FramePacking
