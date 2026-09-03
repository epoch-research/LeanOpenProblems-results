import FormalConjecturesUtil

/-!
A four-prime obstruction to coloring prime roots by their residue modulo 18.
This only rules out a restricted coloring construction; it does not settle
Erdős Problem 1206.
-/

namespace Erdos1206.PrimeResidueColorObstruction

private lemma prime_witnesses :
    Nat.Prime 13297 ∧ Nat.Prime 24907 ∧ Nat.Prime 47119 ∧ Nat.Prime 49009 := by
  norm_num

/-- One residue class of primes already contains a nontrivial cubic collision. -/
theorem prime_progression_not_sidon :
    ¬ IsSidon ((fun n : ℕ => n^3) '' {n : ℕ | n.Prime ∧ n % 18 = 13}) := by
  intro hs
  obtain ⟨ha,hb,hc,hd⟩ := prime_witnesses
  have hh := hs
    _ ⟨13297,⟨ha,by norm_num⟩,rfl⟩
    _ ⟨24907,⟨hb,by norm_num⟩,rfl⟩
    _ ⟨49009,⟨hd,by norm_num⟩,rfl⟩
    _ ⟨47119,⟨hc,by norm_num⟩,rfl⟩
    (by norm_num : (13297:ℕ)^3+49009^3=24907^3+47119^3)
  norm_num at hh

/-- No choice of colors on the residue classes modulo 18 can be extended
on the other roots to proper squarefree cube-Sidon fibers. Multiplicativity
is not assumed or needed for this obstruction. -/
theorem residue_prime_colors_obstruct {ι : Type*} (f : ℕ → ι) (c : ℕ → ι)
    (hprime : ∀ p : ℕ, p.Prime → c p = f (p % 18)) :
    ¬ (∀ i : ι, IsSidon ((fun n : ℕ => n^3) ''
      {n : ℕ | Squarefree n ∧ c n = i})) := by
  intro hs
  obtain ⟨ha,hb,hc,hd⟩ := prime_witnesses
  have hca : c 13297 = f 13 := by simpa using hprime 13297 ha
  have hcb : c 24907 = f 13 := by simpa using hprime 24907 hb
  have hcc : c 47119 = f 13 := by simpa using hprime 47119 hc
  have hcd : c 49009 = f 13 := by simpa using hprime 49009 hd
  have hh := hs (f 13)
    _ ⟨13297,⟨ha.squarefree,hca⟩,rfl⟩
    _ ⟨24907,⟨hb.squarefree,hcb⟩,rfl⟩
    _ ⟨49009,⟨hd.squarefree,hcd⟩,rfl⟩
    _ ⟨47119,⟨hc.squarefree,hcc⟩,rfl⟩
    (by norm_num : (13297:ℕ)^3+49009^3=24907^3+47119^3)
  norm_num at hh

/-- In particular, allowing odd ZMod 4 prime colors depending on the prime
modulo 9 does not produce a proper coloring. -/
theorem mod_nine_prime_colors_obstruct {ι : Type*} (f : ℕ → ι) (c : ℕ → ι)
    (hprime : ∀ p : ℕ, p.Prime → c p = f (p % 9)) :
    ¬ (∀ i : ι, IsSidon ((fun n : ℕ => n^3) ''
      {n : ℕ | Squarefree n ∧ c n = i})) := by
  apply residue_prime_colors_obstruct (fun r => f (r % 9)) c
  intro p hp
  simpa only [Nat.mod_mod_of_dvd p (by decide : 9 ∣ 18)] using hprime p hp

#print axioms prime_progression_not_sidon
#print axioms residue_prime_colors_obstruct
#print axioms mod_nine_prime_colors_obstruct

end Erdos1206.PrimeResidueColorObstruction
