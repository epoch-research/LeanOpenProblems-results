import Submission.OddPrimeCharacterDensity

/-!
For a completely additive ZMod 4 character odd at every prime, a squarefree
monochromatic cube collision can be transported into any prescribed color
using fresh primes. Thus the one-Sidon-fiber condition is equivalent to the
proper four-coloring condition in this class. Neither condition is proved.
-/
namespace Erdos1206.OddPrimeCharacterTransport

private lemma fresh_prime (N : ℕ) (hN : 0 < N) :
    ∃ p : ℕ, p.Prime ∧ Nat.Coprime p N := by
  obtain ⟨p,hbig,hp⟩ := Nat.exists_infinite_primes (N+1)
  refine ⟨p,hp,hp.coprime_iff_not_dvd.mpr ?_⟩
  intro hd
  have := Nat.le_of_dvd hN hd
  omega

private def subsetColors (a b d : ZMod 4) : Fin 8 → ZMod 4 :=
  ![0,a,b,d,a+b,a+d,b+d,a+b+d]

private lemma subsetColors_surjective : ∀ a b d r : ZMod 4,
    2*a=2 → 2*b=2 → 2*d=2 → ∃ i : Fin 8, subsetColors a b d i=r := by
  decide +kernel

/-- Every color can be represented by a squarefree integer coprime to any
prescribed nonzero integer. -/
theorem exists_squarefree_coprime_color (c : ℕ → ZMod 4)
    (hmul : ∀ a b : ℕ, 0<a → 0<b → c (a*b)=c a+c b)
    (hodd : ∀ p : ℕ, p.Prime → 2*c p=2)
    (N : ℕ) (hN : 0<N) (s : ZMod 4) :
    ∃ m : ℕ, Squarefree m ∧ Nat.Coprime m N ∧ c m=s := by
  have h1 : c 1=0 := by
    have hh := hmul 1 1 (by omega) (by omega)
    exact add_left_cancel (show c 1+c 1=c 1+0 by simpa using hh.symm)
  obtain ⟨p,hp,hpN⟩ := fresh_prime N hN
  obtain ⟨q,hq,hqpN⟩ := fresh_prime (p*N) (Nat.mul_pos hp.pos hN)
  obtain ⟨t,ht,htpqN⟩ := fresh_prime (p*q*N)
    (Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hN)
  have hqp : Nat.Coprime q p := hqpN.of_dvd_right (dvd_mul_right p N)
  have hqN : Nat.Coprime q N := hqpN.of_dvd_right (dvd_mul_left N p)
  have htpq : Nat.Coprime t (p*q) := htpqN.of_dvd_right (dvd_mul_right (p*q) N)
  have htN : Nat.Coprime t N := htpqN.of_dvd_right (dvd_mul_left N (p*q))
  have htp : Nat.Coprime t p := htpq.of_dvd_right (dvd_mul_right p q)
  have htq : Nat.Coprime t q := htpq.of_dvd_right (dvd_mul_left q p)
  have hspq : Squarefree (p*q) := (Nat.squarefree_mul hqp.symm).mpr ⟨hp.squarefree,hq.squarefree⟩
  have hspt : Squarefree (p*t) := (Nat.squarefree_mul htp.symm).mpr ⟨hp.squarefree,ht.squarefree⟩
  have hsqt : Squarefree (q*t) := (Nat.squarefree_mul htq.symm).mpr ⟨hq.squarefree,ht.squarefree⟩
  have hspqt : Squarefree (p*q*t) := (Nat.squarefree_mul htpq.symm).mpr ⟨hspq,ht.squarefree⟩
  have hcpq := hmul p q hp.pos hq.pos
  have hcpt := hmul p t hp.pos ht.pos
  have hcqt := hmul q t hq.pos ht.pos
  have hcpqt : c (p*q*t)=c p+c q+c t := by
    rw [hmul (p*q) t (Nat.mul_pos hp.pos hq.pos) ht.pos,hcpq]
  obtain ⟨i,hi⟩ := subsetColors_surjective (c p) (c q) (c t) s
    (hodd p hp) (hodd q hq) (hodd t ht)
  fin_cases i
  · exact ⟨1,squarefree_one,by simp,h1.trans hi⟩
  · exact ⟨p,hp.squarefree,hpN,hi⟩
  · exact ⟨q,hq.squarefree,hqN,hi⟩
  · exact ⟨t,ht.squarefree,htN,hi⟩
  · exact ⟨p*q,hspq,hpN.mul_left hqN,hcpq.trans hi⟩
  · exact ⟨p*t,hspt,hpN.mul_left htN,hcpt.trans hi⟩
  · exact ⟨q*t,hsqt,hqN.mul_left htN,hcqt.trans hi⟩
  · exact ⟨p*q*t,hspqt,(hpN.mul_left hqN).mul_left htN,hcpqt.trans hi⟩

/-- If one squarefree color fiber is cube-Sidon, all four are cube-Sidon.
The multiplier may depend on the four roots; it is not a common global map. -/
theorem all_fibers_sidon_of_one (c : ℕ → ZMod 4)
    (hmul : ∀ a b : ℕ, 0<a → 0<b → c (a*b)=c a+c b)
    (hodd : ∀ p : ℕ, p.Prime → 2*c p=2) (r : ZMod 4)
    (hs : IsSidon ((fun n : ℕ => n^3) '' {n | Squarefree n ∧ c n=r})) :
    ∀ s : ZMod 4, IsSidon ((fun n : ℕ => n^3) '' {n | Squarefree n ∧ c n=s}) := by
  intro s
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ _ ⟨d,hd,rfl⟩ _ ⟨e,he,rfl⟩ heq
  have ha0 : 0<a := Nat.pos_of_ne_zero ha.1.ne_zero
  have hb0 : 0<b := Nat.pos_of_ne_zero hb.1.ne_zero
  have hd0 : 0<d := Nat.pos_of_ne_zero hd.1.ne_zero
  have he0 : 0<e := Nat.pos_of_ne_zero he.1.ne_zero
  obtain ⟨m,hms,hmN,hmcol⟩ := exists_squarefree_coprime_color c hmul hodd
    (a*b*d*e) (by positivity) (r-s)
  have hm0 : 0 < m := Nat.pos_of_ne_zero hms.ne_zero
  have hmem (n : ℕ) (hn : Squarefree n ∧ c n=s) (hdiv : n ∣ a*b*d*e) :
      Squarefree (m*n) ∧ c (m*n)=r := by
    refine ⟨(Nat.squarefree_mul (hmN.of_dvd_right hdiv)).mpr ⟨hms,hn.1⟩,?_⟩
    rw [hmul m n hm0 (Nat.pos_of_ne_zero hn.1.ne_zero),hmcol,hn.2]
    ring
  have hma := hmem a ha (by exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right a b) d) e)
  have hmb := hmem b hb (by exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left b a) d) e)
  have hmd := hmem d hd (dvd_mul_of_dvd_left (dvd_mul_left d (a*b)) e)
  have hme := hmem e he (dvd_mul_left e (a*b*d))
  have heq' : (m*a)^3+(m*d)^3=(m*b)^3+(m*e)^3 := by
    simpa only [mul_pow,←mul_add] using congrArg (fun n : ℕ => m^3*n) heq
  have hh := hs _ ⟨m*a,hma,rfl⟩ _ ⟨m*b,hmb,rfl⟩
    _ ⟨m*d,hmd,rfl⟩ _ ⟨m*e,hme,rfl⟩ heq'
  simp only [mul_pow] at hh
  have hmp : 0 < m^3 := pow_pos hm0 _
  rcases hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact Or.inl ⟨Nat.eq_of_mul_eq_mul_left hmp h₁,Nat.eq_of_mul_eq_mul_left hmp h₂⟩
  · exact Or.inr ⟨Nat.eq_of_mul_eq_mul_left hmp h₁,Nat.eq_of_mul_eq_mul_left hmp h₂⟩

/-- Under the odd-prime hypothesis, Sidonness is independent of the chosen
squarefree fiber. This equivalence asserts neither side. -/
theorem fiber_sidon_iff (c : ℕ → ZMod 4)
    (hmul : ∀ a b : ℕ, 0<a → 0<b → c (a*b)=c a+c b)
    (hodd : ∀ p : ℕ, p.Prime → 2*c p=2) (r s : ZMod 4) :
    IsSidon ((fun n : ℕ => n^3) '' {n | Squarefree n ∧ c n=r}) ↔
      IsSidon ((fun n : ℕ => n^3) '' {n | Squarefree n ∧ c n=s}) :=
  ⟨fun h => all_fibers_sidon_of_one c hmul hodd r h s,
   fun h => all_fibers_sidon_of_one c hmul hodd s h r⟩

#print axioms fiber_sidon_iff


#print axioms exists_squarefree_coprime_color
#print axioms all_fibers_sidon_of_one
end Erdos1206.OddPrimeCharacterTransport
