import Submission.BinaryQuadraticLocalSieve
import Submission.SquarefreeConicCharacterScore
import Submission.SelbergMassLower

/-!
Exact local sieve densities for the mixed primes of the explicit two-field
conic, together with a finite exceptional-parameter upper bound.
-/
namespace Erdos1206.ConicMixedLocalSieve
open Finset BinaryQuadraticLocalSieve SquarefreeConicFamily SquarefreeConicCharacterScore
open ConicPrimeCharacterScore PrimeBoxCRT PrimeBoxSelberg SelbergMassLower
open scoped Classical

private lemma cast_ne_zero {p n : ℕ} (hn : 0 < n) (hnp : n < p) : (n:ZMod p) ≠ 0 := by
  intro h
  have hh := (CharP.cast_eq_zero_iff (ZMod p) p n).mp h
  have := Nat.le_of_dvd hn hh
  omega

noncomputable def localSet (p : ℕ) : Finset (ZMod p × ZMod p) :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    letI : NeZero p := ⟨hp.ne_zero⟩
    if χ p=1 then
      lineSet (affineRoots 3419 1160 29 ∪ affineRoots 374777 19880 263)
    else lineSet (affineRoots 769417 41884 571 ∪ affineRoots 797983 43324 589)
  else ∅

private lemma first_card {p : ℕ} (hp : p.Prime) (hbig : 1000000000 < p) (hχ : χ p=1) :
    letI : Fact p.Prime := ⟨hp⟩
    letI : NeZero p := ⟨hp.ne_zero⟩
    (lineSet (affineRoots (3419:ZMod p) 1160 29 ∪ affineRoots 374777 19880 263)).card =
      1+4*(p-1) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have h2 : (2:ZMod p) ≠ 0 := cast_ne_zero (n := 2) (by norm_num) (by omega)
  have hA : (3419:ZMod p) ≠ 0 := cast_ne_zero (n := 3419) (by norm_num) (by omega)
  have hB : (374777:ZMod p) ≠ 0 := cast_ne_zero (n := 374777) (by norm_num) (by omega)
  have hD : ((948996:ℤ):ZMod p) ≠ 0 := by
    simpa only [Int.cast_ofNat,Nat.cast_ofNat] using cast_ne_zero (p := p) (n := 948996) (by norm_num) (by omega)
  have hleg : legendreSym p 948996=1 := by
    simpa only [χ,← jacobiSym.legendreSym.to_jacobiSym] using hχ
  have hDs := (legendreSym.eq_one_iff p hD).mp hleg
  have he₁ : (1160:ZMod p)^2-4*3419*29=(948996:ℤ) := by norm_num
  have he₂ : (19880:ZMod p)^2-4*374777*263=(948996:ℤ) := by norm_num
  have hno (x : ZMod p) : ¬ ((3419:ZMod p)*x^2+1160*x+29=0 ∧
      (374777:ZMod p)*x^2+19880*x+263=0) := by
    rintro ⟨h₁,h₂⟩
    have hz : (180366264:ZMod p)=0 := by
      linear_combination (146856367450*x+3798228173)*h₁+(-1339735150*x-418130231)*h₂
    exact cast_ne_zero (n := 180366264) (by norm_num) (by omega) hz
  have hh := pair_lineSet_card (3419:ZMod p) 1160 29 374777 19880 263 hA hB h2
    (he₁ ▸ hD) (he₁ ▸ hDs) (he₂ ▸ hD) (he₂ ▸ hDs) hno
  simpa only [ZMod.card] using hh

private lemma second_card {p : ℕ} (hp : p.Prime) (hbig : 1000000000 < p) (hψ : ψ p=1) :
    letI : Fact p.Prime := ⟨hp⟩
    letI : NeZero p := ⟨hp.ne_zero⟩
    (lineSet (affineRoots (769417:ZMod p) 41884 571 ∪ affineRoots 797983 43324 589)).card =
      1+4*(p-1) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have h2 : (2:ZMod p) ≠ 0 := cast_ne_zero (n := 2) (by norm_num) (by omega)
  have hA : (769417:ZMod p) ≠ 0 := cast_ne_zero (n := 769417) (by norm_num) (by omega)
  have hB : (797983:ZMod p) ≠ 0 := cast_ne_zero (n := 797983) (by norm_num) (by omega)
  have hD : ((-3078972:ℤ):ZMod p) ≠ 0 := by
    simpa only [Int.cast_neg,Int.cast_ofNat] using
      neg_ne_zero.mpr (cast_ne_zero (p := p) (n := 3078972) (by norm_num) (by omega))
  have hleg : legendreSym p (-3078972)=1 := by
    simpa only [ψ,← jacobiSym.legendreSym.to_jacobiSym] using hψ
  have hDs := (legendreSym.eq_one_iff p hD).mp hleg
  have he₁ : (41884:ZMod p)^2-4*769417*571=(-3078972:ℤ) := by norm_num
  have he₂ : (43324:ZMod p)^2-4*797983*589=(-3078972:ℤ) := by norm_num
  have hno (x : ZMod p) : ¬ ((769417:ZMod p)*x^2+41884*x+571=0 ∧
      (797983:ZMod p)*x^2+43324*x+589=0) := by
    rintro ⟨h₁,h₂⟩
    have hz : (13874328:ZMod p)=0 := by
      linear_combination (-75448494667*x-1997545586)*h₁+(72747607933*x+1936523606)*h₂
    exact cast_ne_zero (n := 13874328) (by norm_num) (by omega) hz
  have hh := pair_lineSet_card (769417:ZMod p) 41884 571 797983 43324 589 hA hB h2
    (he₁ ▸ hD) (he₁ ▸ hDs) (he₂ ▸ hD) (he₂ ▸ hDs) hno
  simpa only [ZMod.card] using hh

lemma localSet_card {p : ℕ} (hp : p.Prime) (hbig : 1000000000 < p) (hmix : χ p ≠ ψ p) :
    (localSet p).card+3=4*p := by
  have hcard : (localSet p).card=1+4*(p-1) := by
    obtain ⟨hχ,hψ⟩ := symbols hp hbig
    by_cases hc : χ p=1
    · simpa only [localSet,dif_pos hp,if_pos hc] using first_card hp hbig hc
    · have hψ1 : ψ p=1 := by rcases hχ with h | h <;> rcases hψ with h' | h' <;> omega
      simpa only [localSet,dif_pos hp,if_neg hc] using second_card hp hbig hψ1
  have hp0 := hp.pos
  omega

lemma localDensity_eq {p : ℕ} (hp : p.Prime) (hbig : 1000000000 < p) (hmix : χ p ≠ ψ p) :
    localDensity localSet p=(4*(p:ℝ)-3)/(p:ℝ)^2 := by
  have hc : ((localSet p).card:ℝ)+3=4*(p:ℝ) := by exact_mod_cast localSet_card hp hbig hmix
  dsimp only [localDensity]
  congr 1
  linarith

lemma localDensity_bounds {p : ℕ} (hp : p.Prime) (hbig : 1000000000 < p) (hmix : χ p ≠ ψ p) :
    0 < localDensity localSet p ∧ localDensity localSet p ≤ 1/2 := by
  rw [localDensity_eq hp hbig hmix]
  have hpR : (10:ℝ)<p := by exact_mod_cast (show 10<p by omega)
  have hp0 : (0:ℝ)<p := by linarith
  constructor
  · exact div_pos (by linarith) (sq_pos_of_pos hp0)
  · apply (div_le_iff₀ (sq_pos_of_pos hp0)).mpr
    nlinarith [sq_nonneg ((p:ℝ)-4)]

lemma localSet_divisor {p t u : ℕ} (hp : p.Prime)
    (hmem : ((t:ZMod p),(u:ZMod p)) ∈ localSet p) :
    p ∣ F 0 t u ∨ p ∣ F 1 t u ∨ p ∣ F 2 t u ∨ p ∣ F 3 t u := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  simp only [localSet,dif_pos hp] at hmem
  have hdiv (i : Fin 4) (hz : (c i:ZMod p)*(t:ZMod p)^2+(b i:ZMod p)*t*u+(a i:ZMod p)*u^2=0) :
      p ∣ F i t u := by
    apply (CharP.cast_eq_zero_iff (ZMod p) p (F i t u)).mp
    simpa only [F,QuadraticSquarefreeSieve.quad,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
      add_comm,add_left_comm,add_assoc,mul_comm,mul_left_comm,mul_assoc] using hz
  split_ifs at hmem with hc
  · rcases lineSet_pair_zero hmem with hz | hz
    · exact Or.inl (hdiv 0 (by simpa only [a,b,c,Matrix.cons_val_zero,Nat.cast_ofNat] using hz))
    · exact Or.inr (Or.inl (hdiv 1 (by simpa [a,b,c] using hz)))
  · rcases lineSet_pair_zero hmem with hz | hz
    · exact Or.inr (Or.inr (Or.inl (hdiv 2 (by simpa [a,b,c] using hz))))
    · exact Or.inr (Or.inr (Or.inr (hdiv 3 (by simpa [a,b,c] using hz))))

lemma hits_le_mixedMass (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ χ p ≠ ψ p) {t u : ℕ} (hu : 0 < u) :
    (hits P localSet (t,u)).card ≤ mixedMass P χ ψ (F 0 t u) (F 1 t u) (F 2 t u) (F 3 t u) := by
  have hfilter : P.filter (fun p => χ p ≠ ψ p)=P := filter_eq_self.mpr (fun p hp => (hP p hp).2)
  rw [mixedMass,hfilter]
  have hpos (i : Fin 4) : 0 < F i t u := by
    fin_cases i <;> dsimp [F,QuadraticSquarefreeSieve.quad,a,b,c] <;> positivity
  calc
    _ = ∑ _p ∈ hits P localSet (t,u), 1 := by simp
    _ ≤ ∑ p ∈ hits P localSet (t,u),
        ((F 0 t u).factorization p+(F 1 t u).factorization p+
          (F 2 t u).factorization p+(F 3 t u).factorization p) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpP,hpl⟩ := mem_filter.mp hp
      have hprime := (hP p hpP).1
      rcases localSet_divisor hprime hpl with h | h | h | h
      · have := hprime.factorization_pos_of_dvd (hpos 0).ne' h; omega
      · have := hprime.factorization_pos_of_dvd (hpos 1).ne' h; omega
      · have := hprime.factorization_pos_of_dvd (hpos 2).ne' h; omega
      · have := hprime.factorization_pos_of_dvd (hpos 3).ne' h; omega
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (hits_subset P localSet (t,u)) (by intros; omega)

/-- A finite exceptional-parameter bound for the actual conic. The prime
block and level must satisfy the displayed logarithmic moment condition.
No asymptotic prime estimate is hidden in this statement. -/
theorem small_mixedMass_count (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 1000000000 < p ∧ χ p ≠ ψ p)
    (N z k : ℕ) (hz : 1 < z) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hmoment : 2*(∑ p ∈ P, (q*((4*(p:ℝ)-3)/(p:ℝ)^2))*Real.log p) ≤ Real.log z) :
    (((((range N) ×ˢ (range N)).filter (fun x => 0 < x.2 ∧
        mixedMass P χ ψ (F 0 x.1 x.2) (F 1 x.1 x.2) (F 2 x.1 x.2) (F 3 x.1 x.2) ≤ k)).card:ℝ)*
          (1-q)^k) ≤
      2*(N:ℝ)^2*Real.exp (-(∑ p ∈ P, q*((4*(p:ℝ)-3)/(p:ℝ)^2)))+
        2*(N:ℝ)*(z:ℝ)^6+(z:ℝ)^8 := by
  have he (p : ℕ) (hp : p ∈ P) : localDensity localSet p=(4*(p:ℝ)-3)/(p:ℝ)^2 :=
    localDensity_eq (hP p hp).1 (hP p hp).2.1 (hP p hp).2.2
  have hm : 2*(∑ p ∈ P, (q*localDensity localSet p)*Real.log p) ≤ Real.log z := by
    convert hmoment using 1
    congr 1
    exact sum_congr rfl (fun p hp => by rw [he p hp])
  have hh := few_hits_exponential P (fun p hp => (hP p hp).1) localSet
    (fun p hp => localDensity_bounds (hP p hp).1 (hP p hp).2.1 (hP p hp).2.2)
    N z k hz hq0 hq1 hm
  have hsub : (((range N) ×ˢ (range N)).filter (fun x => 0 < x.2 ∧
      mixedMass P χ ψ (F 0 x.1 x.2) (F 1 x.1 x.2) (F 2 x.1 x.2) (F 3 x.1 x.2) ≤ k)) ⊆
      (((range N) ×ˢ (range N)).filter (fun x => (hits P localSet x).card ≤ k)) := by
    intro x hx
    obtain ⟨hxN,hxu,hxm⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨hxN,(hits_le_mixedMass P (fun p hp => ⟨(hP p hp).1,(hP p hp).2.2⟩) hxu).trans hxm⟩
  have hc := mul_le_mul_of_nonneg_right
    ((Nat.cast_le (α := ℝ)).mpr (card_le_card hsub))
    (pow_nonneg (sub_nonneg.mpr hq1) k)
  have hsum : (∑ p ∈ P, q*localDensity localSet p) = ∑ p ∈ P, q*((4*(p:ℝ)-3)/(p:ℝ)^2) :=
    sum_congr rfl (fun p hp => by rw [he p hp])
  rw [hsum] at hh
  exact hc.trans hh

#print axioms localSet_card
#print axioms localDensity_bounds
#print axioms localSet_divisor
#print axioms hits_le_mixedMass
#print axioms small_mixedMass_count
end Erdos1206.ConicMixedLocalSieve
