import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000
set_option exponentiation.threshold 10000

private def powFuel (a m e : ℕ) : ℕ → ℕ
  | 0 => 1 % m
  | f+1 => ((if e % 2 = 1 then a else 1) * powFuel ((a * a) % m) m (e / 2) f) % m

private lemma sq_pow_mod_goal (x m e : ℕ) :
    ((x % m % m * (x % m % m)) % m) ^ e % m = (x ^ e) ^ 2 % m := by
  rw [← Nat.pow_mod ((x % m % m) * (x % m % m)) e m]
  rw [mul_pow]
  rw [pow_two]
  simp [Nat.pow_mod, Nat.mul_mod]

private lemma powFuel_eq (a m e f : ℕ) (hbound : e < 2 ^ f) :
    powFuel a m e f = a ^ e % m := by
  induction f generalizing a e with
  | zero =>
      have he : e = 0 := by omega
      subst e
      simp [powFuel]
  | succ f ih =>
      have hdivbound : e / 2 < 2 ^ f := by
        have h2 : 2 ^ (f + 1) = 2 * 2 ^ f := by rw [pow_succ']
        rw [h2] at hbound
        exact Nat.div_lt_of_lt_mul hbound
      simp [powFuel]
      rw [ih ((a * a) % m) (e / 2) hdivbound]
      have hmodlt : e % 2 = 0 ∨ e % 2 = 1 := by omega
      rcases hmodlt with h0 | h1
      · have heven : e = 2 * (e / 2) := by
          have h := Nat.div_add_mod e 2
          omega
        rw [heven]
        simp [h0, pow_mul, Nat.mul_mod, Nat.mul_comm]
        rw [sq_pow_mod_goal a m (e / 2)]
        rw [show (a ^ (e / 2)) ^ 2 = (a ^ 2) ^ (e / 2) by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      · have hodd : e = 1 + 2 * (e / 2) := by
          have h := Nat.div_add_mod e 2
          omega
        have hdiv : (1 + 2 * (e / 2)) / 2 = e / 2 := by omega
        rw [hodd]
        simp [h1, hdiv, pow_add, pow_mul, Nat.mul_mod, Nat.mul_comm]
        rw [sq_pow_mod_goal a m (e / 2)]
        rw [show (a ^ (e / 2)) ^ 2 = (a ^ 2) ^ (e / 2) by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]


open Nat Finset

/--
A234360: $a(n) = \left|\left\{0 < k < n: (k+1)^{\phi(n-k)} + k \text{ is prime}\right\}\right|$, where $\phi(\cdot)$ is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  (filter (fun k => Nat.Prime ((k + 1) ^ (Nat.totient (n - k)) + k)) (Ico 1 n)).card

private theorem no_prime_1408_84 (hp : Nat.Prime ((84 + 1) ^ (Nat.totient (1408 - 84) / 2) - 84)) : False := by
  let N : ℕ := 5107936453918163757264144602051577257414121185886005338395391607121227801932615294179583059492436369272615585485700794681486733768732418148359567759868140497460565021156428719460152120747316441094689398177803284079388294504357126230002821106889365117054425239570578079550126103401255444920911105667656243114006578714491673987093930455894878714681879683967051436970976905592751317445343012987618483177821599031675327689540003253284517855415011642264965149577583460510528304293793780954927846566860932121209418682519402982150232124776854821418043513580010322826212336285503607227260208698658649714187396373432648033485747873783111572265541
  have hN : ((84 + 1) ^ (Nat.totient (1408 - 84) / 2) - 84) = N := by decide
  rw [hN] at hp
  have hndvd : ¬ (N ∣ 2) := by decide
  have hc : Nat.Coprime 2 N := ((hp.coprime_iff_not_dvd).2 hndvd).symm
  have hfer := Nat.ModEq.pow_card_sub_one_eq_one hp hc
  have hbound : N - 1 < 2 ^ 2116 := by decide
  have hpow : powFuel 2 N (N - 1) 2116 = 3932055639753323355671058877877921197494848472601092735999170940757673330699711082307745545791403089499258643365073684779473655008168992507715828908508666984312991800881692031545346231163450247486537260148958206524423016670099538688432039948129062337164016329353138184828090077216640855205809373890737804803368281854062334497806605877398872752840441537462753303897598241394068724728275087318104422286086406713592882122718236947866787416847778500490896068699837574734370056696094141219125149795527281891247814877822745162862722039552907266994780828476195913977719542410088448652874073758653984585602355537488241849392278169434114548698878 := by decide
  have hmod : 2 ^ (N - 1) % N = 3932055639753323355671058877877921197494848472601092735999170940757673330699711082307745545791403089499258643365073684779473655008168992507715828908508666984312991800881692031545346231163450247486537260148958206524423016670099538688432039948129062337164016329353138184828090077216640855205809373890737804803368281854062334497806605877398872752840441537462753303897598241394068724728275087318104422286086406713592882122718236947866787416847778500490896068699837574734370056696094141219125149795527281891247814877822745162862722039552907266994780828476195913977719542410088448652874073758653984585602355537488241849392278169434114548698878 := by
    have h := powFuel_eq 2 N (N - 1) 2116 hbound
    rw [hpow] at h
    exact h.symm
  have hcalc : 2 ^ (N - 1) % N ≠ 1 % N := by
    rw [hmod]
    decide
  exact hcalc hfer

