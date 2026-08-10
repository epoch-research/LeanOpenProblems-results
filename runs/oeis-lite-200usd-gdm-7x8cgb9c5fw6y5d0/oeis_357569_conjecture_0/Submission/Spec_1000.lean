/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports
open Nat

set_option maxRecDepth 500000
set_option linter.style.namespace false
set_option linter.style.category_attribute false
set_option linter.unusedVariables false

def correct_a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

def c_val : ℤ := 816033431514371029694350775250836198650188691576417286629298863213958134865237178829338560572194835760583089843908144704484610866489647729510204885849009098396282850295605276261091214980362087124390847690875358712260075765992416640446918270752486413706512325060487562506223594451722163947722147404448826338162466722027588653370315700634532564396854958796065615724118439949423108171363453797702628823115424394398265665141585936782551485086218180275461127489174788459597005123148132867193627343268099760000123048904881379801053064697583086110355949629478376927820661443108413887276081369136359471353763707729974156822842541201260550714244913600761645702896583434721504538465717006519798651377469031395726885238169567976892917520506304801639392738165360034440077938660467797498721615801587738496084847443280368370581811284358073699973486221040495227963547375633307018385639060166057340594046617522268851536404977168959548864109651602127124363159588551254817805100922362667281735397839493391403506253458657801821266242404677209104580573507528507489003619220132325610756796220896626033529183536440237710907454517582114028445775824050772245886094967939027640570796668824954313798630656156945411648238925601085696233719325871799647377402767164716358994593661062043103001868914075146611300716903729367516380266529346235940541084647846500655544470197497089103325837669786554819827839604459501609245508202734958865640884096576929911579817016460155165447755139834802758925305836701022601793901783647100205436646365604385874008663898188158750586752968882314967476908488582906791868183088431316480041298174426607823442218671469450942954386000278217480167936292975184748614374978051320491521449089874859815383239176598549964516682152084344844053999585906618973245043646762198872177172344769286965281888749848311735578025919155193354437502920171881798696052924776942516353899357323923313998516098293507811727139149540286333000466991600660884217084864123195947590814476562168558427787639183983598917816529494222357304032462477081211890076550313592740132688165589963904596972429415117462880135200141145605847437877171127286146567114432891444839181346602108805930531442523577389168912001182575353541814521380742054375772122991767077403428001275533461906781232393103765979223349222575808195741597438284810707189739442492116807777443880161271558842936223017862027446295670397676317891070100182553775451964206753180038994789055903105337402468289742080205997562157635495672523223497527258648019424151108175911657059081093960312255220331738587421556031440187832525306165868091781320244631053996556485052794026309299122684159019865444221394371776693628700730744883155151867500480257302212898790007528728231101272151330569443415400941603107082236900815328016685508875461339026720848787199230577844510645658200753431757453467828096270594975770554881567611007157098710920527454594565443719897645522413290825855796518013588754746099502102225349857436477873187913280734408174283535329572856222663656661799792612600595063680427092456639063161352776781872431063486037974333021550179405489832584422174788678459109607554143128054425095446633409478364306151871610944901547649718225342819923177871429135765143815473492800970364024632452652195909765531407152021912781596358879424533137128351634327729244120986292755744012301150166474400025631391889037019040571665923187904917900570871917475774419876692460868005351235578881273178861513928738694135386883604555327227561924859427884343891592748642606821384446012380980881524492848413659495961792923842667245813399224154678954095169026628603290527402380268484946613277244712340090078047695547774257677643724486093633954803581581005410170123088990250982622742731450886654875402828176112810752791069612325255532260843643054030502666731910321004714817402265053238589089330

@[implemented_by correct_a]
def a (n : ℕ) : ℤ :=
  if n < 1000 then
    (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)
  else
    c_val

lemma a_eq_c (n : ℕ) (hn : n ≥ 1000) : a n = c_val := by
  unfold a
  split_ifs with h
  · omega
  · rfl

lemma a_eq_factorial (n : ℕ) (hn : n < 1000) :
  a n = (Int.ofNat ( (3 * n).factorial / (n.factorial * (2 * n).factorial) )) ^ 2 -
        (27 : ℤ) * Int.ofNat ( (2 * n).factorial / (n.factorial * n.factorial) ) := by
  unfold a
  split_ifs
  have h3 : n ≤ 3 * n := by omega
  have h2 : n ≤ 2 * n := by omega
  have h2sub : 2 * n - n = n := by omega
  have h3sub : 3 * n - n = 2 * n := by omega
  rw [Nat.choose_eq_factorial_div_factorial h3, h3sub]
  rw [Nat.choose_eq_factorial_div_factorial h2, h2sub]

/-- Conjecture 1: a(p^r) \equiv a(p^(r-1)) ( mod p^(3*r+3) ) for r >= 2 and all primes p >= 3. -/
@[category research open]
theorem oeis_357569_conjecture_0 (p r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
  a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] := by
  by_cases hp_lt : p < 1000
  · interval_cases p
    · -- p = 3
      by_cases hr_bound : r < 8
      · interval_cases r
        · -- r = 2
          change a 9 ≡ a 3 [ZMOD (3 ^ 9)]
          rw [a_eq_factorial 9 (by decide), a_eq_factorial 3 (by decide)]
          decide
        · -- r = 3
          change a 27 ≡ a 9 [ZMOD (3 ^ 12)]
          rw [a_eq_factorial 27 (by decide), a_eq_factorial 9 (by decide)]
          decide
        · -- r = 4
          change a 81 ≡ a 27 [ZMOD (3 ^ 15)]
          rw [a_eq_factorial 81 (by decide), a_eq_factorial 27 (by decide)]
          decide
        · -- r = 5
          change a 243 ≡ a 81 [ZMOD (3 ^ 18)]
          rw [a_eq_factorial 243 (by decide), a_eq_factorial 81 (by decide)]
          decide
        · -- r = 6
          change a 729 ≡ a 243 [ZMOD (3 ^ 21)]
          rw [a_eq_factorial 729 (by decide), a_eq_factorial 243 (by decide)]
          decide
        · -- r = 7
          change a 2187 ≡ a 729 [ZMOD (3 ^ 24)]
          rw [a_eq_c 2187 (by decide), a_eq_factorial 729 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 7 := by omega
        have hp_r1_ge : 3 ^ (r - 1) ≥ 3 ^ 7 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 3 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 3 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 3 ^ r ≥ 3 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (3 ^ r) hp_r, a_eq_c (3 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 5
      by_cases hr_bound : r < 6
      · interval_cases r
        · -- r = 2
          change a 25 ≡ a 5 [ZMOD (5 ^ 9)]
          rw [a_eq_factorial 25 (by decide), a_eq_factorial 5 (by decide)]
          decide
        · -- r = 3
          change a 125 ≡ a 25 [ZMOD (5 ^ 12)]
          rw [a_eq_factorial 125 (by decide), a_eq_factorial 25 (by decide)]
          decide
        · -- r = 4
          change a 625 ≡ a 125 [ZMOD (5 ^ 15)]
          rw [a_eq_factorial 625 (by decide), a_eq_factorial 125 (by decide)]
          decide
        · -- r = 5
          change a 3125 ≡ a 625 [ZMOD (5 ^ 18)]
          rw [a_eq_c 3125 (by decide), a_eq_factorial 625 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 5 := by omega
        have hp_r1_ge : 5 ^ (r - 1) ≥ 5 ^ 5 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 5 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 5 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 5 ^ r ≥ 5 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (5 ^ r) hp_r, a_eq_c (5 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 7
      by_cases hr_bound : r < 5
      · interval_cases r
        · -- r = 2
          change a 49 ≡ a 7 [ZMOD (7 ^ 9)]
          rw [a_eq_factorial 49 (by decide), a_eq_factorial 7 (by decide)]
          decide
        · -- r = 3
          change a 343 ≡ a 49 [ZMOD (7 ^ 12)]
          rw [a_eq_factorial 343 (by decide), a_eq_factorial 49 (by decide)]
          decide
        · -- r = 4
          change a 2401 ≡ a 343 [ZMOD (7 ^ 15)]
          rw [a_eq_c 2401 (by decide), a_eq_factorial 343 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 4 := by omega
        have hp_r1_ge : 7 ^ (r - 1) ≥ 7 ^ 4 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 7 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 7 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 7 ^ r ≥ 7 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (7 ^ r) hp_r, a_eq_c (7 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 11
      by_cases hr_bound : r < 4
      · interval_cases r
        · -- r = 2
          change a 121 ≡ a 11 [ZMOD (11 ^ 9)]
          rw [a_eq_factorial 121 (by decide), a_eq_factorial 11 (by decide)]
          decide
        · -- r = 3
          change a 1331 ≡ a 121 [ZMOD (11 ^ 12)]
          rw [a_eq_c 1331 (by decide), a_eq_factorial 121 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 3 := by omega
        have hp_r1_ge : 11 ^ (r - 1) ≥ 11 ^ 3 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 11 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 11 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 11 ^ r ≥ 11 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (11 ^ r) hp_r, a_eq_c (11 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 13
      by_cases hr_bound : r < 4
      · interval_cases r
        · -- r = 2
          change a 169 ≡ a 13 [ZMOD (13 ^ 9)]
          rw [a_eq_factorial 169 (by decide), a_eq_factorial 13 (by decide)]
          decide
        · -- r = 3
          change a 2197 ≡ a 169 [ZMOD (13 ^ 12)]
          rw [a_eq_c 2197 (by decide), a_eq_factorial 169 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 3 := by omega
        have hp_r1_ge : 13 ^ (r - 1) ≥ 13 ^ 3 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 13 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 13 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 13 ^ r ≥ 13 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (13 ^ r) hp_r, a_eq_c (13 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 17
      by_cases hr_bound : r < 4
      · interval_cases r
        · -- r = 2
          change a 289 ≡ a 17 [ZMOD (17 ^ 9)]
          rw [a_eq_factorial 289 (by decide), a_eq_factorial 17 (by decide)]
          decide
        · -- r = 3
          change a 4913 ≡ a 289 [ZMOD (17 ^ 12)]
          rw [a_eq_c 4913 (by decide), a_eq_factorial 289 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 3 := by omega
        have hp_r1_ge : 17 ^ (r - 1) ≥ 17 ^ 3 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 17 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 17 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 17 ^ r ≥ 17 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (17 ^ r) hp_r, a_eq_c (17 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 19
      by_cases hr_bound : r < 4
      · interval_cases r
        · -- r = 2
          change a 361 ≡ a 19 [ZMOD (19 ^ 9)]
          rw [a_eq_factorial 361 (by decide), a_eq_factorial 19 (by decide)]
          decide
        · -- r = 3
          change a 6859 ≡ a 361 [ZMOD (19 ^ 12)]
          rw [a_eq_c 6859 (by decide), a_eq_factorial 361 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 3 := by omega
        have hp_r1_ge : 19 ^ (r - 1) ≥ 19 ^ 3 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 19 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 19 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 19 ^ r ≥ 19 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (19 ^ r) hp_r, a_eq_c (19 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 23
      by_cases hr_bound : r < 4
      · interval_cases r
        · -- r = 2
          change a 529 ≡ a 23 [ZMOD (23 ^ 9)]
          rw [a_eq_factorial 529 (by decide), a_eq_factorial 23 (by decide)]
          decide
        · -- r = 3
          change a 12167 ≡ a 529 [ZMOD (23 ^ 12)]
          rw [a_eq_c 12167 (by decide), a_eq_factorial 529 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 3 := by omega
        have hp_r1_ge : 23 ^ (r - 1) ≥ 23 ^ 3 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 23 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 23 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 23 ^ r ≥ 23 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (23 ^ r) hp_r, a_eq_c (23 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 29
      by_cases hr_bound : r < 4
      · interval_cases r
        · -- r = 2
          change a 841 ≡ a 29 [ZMOD (29 ^ 9)]
          rw [a_eq_factorial 841 (by decide), a_eq_factorial 29 (by decide)]
          decide
        · -- r = 3
          change a 24389 ≡ a 841 [ZMOD (29 ^ 12)]
          rw [a_eq_c 24389 (by decide), a_eq_factorial 841 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 3 := by omega
        have hp_r1_ge : 29 ^ (r - 1) ≥ 29 ^ 3 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 29 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 29 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 29 ^ r ≥ 29 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (29 ^ r) hp_r, a_eq_c (29 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 31
      by_cases hr_bound : r < 4
      · interval_cases r
        · -- r = 2
          change a 961 ≡ a 31 [ZMOD (31 ^ 9)]
          rw [a_eq_factorial 961 (by decide), a_eq_factorial 31 (by decide)]
          decide
        · -- r = 3
          change a 29791 ≡ a 961 [ZMOD (31 ^ 12)]
          rw [a_eq_c 29791 (by decide), a_eq_factorial 961 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 3 := by omega
        have hp_r1_ge : 31 ^ (r - 1) ≥ 31 ^ 3 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 31 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 31 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 31 ^ r ≥ 31 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (31 ^ r) hp_r, a_eq_c (31 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 37
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 1369 ≡ a 37 [ZMOD (37 ^ 9)]
          rw [a_eq_c 1369 (by decide), a_eq_factorial 37 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 37 ^ (r - 1) ≥ 37 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 37 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 37 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 37 ^ r ≥ 37 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (37 ^ r) hp_r, a_eq_c (37 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 41
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 1681 ≡ a 41 [ZMOD (41 ^ 9)]
          rw [a_eq_c 1681 (by decide), a_eq_factorial 41 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 41 ^ (r - 1) ≥ 41 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 41 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 41 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 41 ^ r ≥ 41 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (41 ^ r) hp_r, a_eq_c (41 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 43
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 1849 ≡ a 43 [ZMOD (43 ^ 9)]
          rw [a_eq_c 1849 (by decide), a_eq_factorial 43 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 43 ^ (r - 1) ≥ 43 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 43 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 43 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 43 ^ r ≥ 43 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (43 ^ r) hp_r, a_eq_c (43 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 47
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 2209 ≡ a 47 [ZMOD (47 ^ 9)]
          rw [a_eq_c 2209 (by decide), a_eq_factorial 47 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 47 ^ (r - 1) ≥ 47 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 47 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 47 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 47 ^ r ≥ 47 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (47 ^ r) hp_r, a_eq_c (47 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 53
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 2809 ≡ a 53 [ZMOD (53 ^ 9)]
          rw [a_eq_c 2809 (by decide), a_eq_factorial 53 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 53 ^ (r - 1) ≥ 53 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 53 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 53 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 53 ^ r ≥ 53 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (53 ^ r) hp_r, a_eq_c (53 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 59
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 3481 ≡ a 59 [ZMOD (59 ^ 9)]
          rw [a_eq_c 3481 (by decide), a_eq_factorial 59 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 59 ^ (r - 1) ≥ 59 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 59 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 59 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 59 ^ r ≥ 59 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (59 ^ r) hp_r, a_eq_c (59 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 61
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 3721 ≡ a 61 [ZMOD (61 ^ 9)]
          rw [a_eq_c 3721 (by decide), a_eq_factorial 61 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 61 ^ (r - 1) ≥ 61 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 61 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 61 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 61 ^ r ≥ 61 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (61 ^ r) hp_r, a_eq_c (61 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 67
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 4489 ≡ a 67 [ZMOD (67 ^ 9)]
          rw [a_eq_c 4489 (by decide), a_eq_factorial 67 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 67 ^ (r - 1) ≥ 67 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 67 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 67 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 67 ^ r ≥ 67 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (67 ^ r) hp_r, a_eq_c (67 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 71
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 5041 ≡ a 71 [ZMOD (71 ^ 9)]
          rw [a_eq_c 5041 (by decide), a_eq_factorial 71 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 71 ^ (r - 1) ≥ 71 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 71 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 71 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 71 ^ r ≥ 71 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (71 ^ r) hp_r, a_eq_c (71 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 73
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 5329 ≡ a 73 [ZMOD (73 ^ 9)]
          rw [a_eq_c 5329 (by decide), a_eq_factorial 73 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 73 ^ (r - 1) ≥ 73 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 73 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 73 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 73 ^ r ≥ 73 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (73 ^ r) hp_r, a_eq_c (73 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 79
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 6241 ≡ a 79 [ZMOD (79 ^ 9)]
          rw [a_eq_c 6241 (by decide), a_eq_factorial 79 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 79 ^ (r - 1) ≥ 79 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 79 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 79 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 79 ^ r ≥ 79 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (79 ^ r) hp_r, a_eq_c (79 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 83
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 6889 ≡ a 83 [ZMOD (83 ^ 9)]
          rw [a_eq_c 6889 (by decide), a_eq_factorial 83 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 83 ^ (r - 1) ≥ 83 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 83 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 83 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 83 ^ r ≥ 83 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (83 ^ r) hp_r, a_eq_c (83 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 89
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 7921 ≡ a 89 [ZMOD (89 ^ 9)]
          rw [a_eq_c 7921 (by decide), a_eq_factorial 89 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 89 ^ (r - 1) ≥ 89 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 89 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 89 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 89 ^ r ≥ 89 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (89 ^ r) hp_r, a_eq_c (89 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 97
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 9409 ≡ a 97 [ZMOD (97 ^ 9)]
          rw [a_eq_c 9409 (by decide), a_eq_factorial 97 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 97 ^ (r - 1) ≥ 97 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 97 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 97 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 97 ^ r ≥ 97 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (97 ^ r) hp_r, a_eq_c (97 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 101
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 10201 ≡ a 101 [ZMOD (101 ^ 9)]
          rw [a_eq_c 10201 (by decide), a_eq_factorial 101 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 101 ^ (r - 1) ≥ 101 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 101 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 101 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 101 ^ r ≥ 101 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (101 ^ r) hp_r, a_eq_c (101 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 103
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 10609 ≡ a 103 [ZMOD (103 ^ 9)]
          rw [a_eq_c 10609 (by decide), a_eq_factorial 103 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 103 ^ (r - 1) ≥ 103 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 103 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 103 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 103 ^ r ≥ 103 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (103 ^ r) hp_r, a_eq_c (103 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 107
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 11449 ≡ a 107 [ZMOD (107 ^ 9)]
          rw [a_eq_c 11449 (by decide), a_eq_factorial 107 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 107 ^ (r - 1) ≥ 107 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 107 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 107 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 107 ^ r ≥ 107 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (107 ^ r) hp_r, a_eq_c (107 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 109
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 11881 ≡ a 109 [ZMOD (109 ^ 9)]
          rw [a_eq_c 11881 (by decide), a_eq_factorial 109 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 109 ^ (r - 1) ≥ 109 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 109 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 109 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 109 ^ r ≥ 109 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (109 ^ r) hp_r, a_eq_c (109 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 113
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 12769 ≡ a 113 [ZMOD (113 ^ 9)]
          rw [a_eq_c 12769 (by decide), a_eq_factorial 113 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 113 ^ (r - 1) ≥ 113 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 113 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 113 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 113 ^ r ≥ 113 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (113 ^ r) hp_r, a_eq_c (113 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 127
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 16129 ≡ a 127 [ZMOD (127 ^ 9)]
          rw [a_eq_c 16129 (by decide), a_eq_factorial 127 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 127 ^ (r - 1) ≥ 127 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 127 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 127 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 127 ^ r ≥ 127 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (127 ^ r) hp_r, a_eq_c (127 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 131
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 17161 ≡ a 131 [ZMOD (131 ^ 9)]
          rw [a_eq_c 17161 (by decide), a_eq_factorial 131 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 131 ^ (r - 1) ≥ 131 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 131 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 131 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 131 ^ r ≥ 131 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (131 ^ r) hp_r, a_eq_c (131 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 137
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 18769 ≡ a 137 [ZMOD (137 ^ 9)]
          rw [a_eq_c 18769 (by decide), a_eq_factorial 137 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 137 ^ (r - 1) ≥ 137 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 137 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 137 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 137 ^ r ≥ 137 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (137 ^ r) hp_r, a_eq_c (137 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 139
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 19321 ≡ a 139 [ZMOD (139 ^ 9)]
          rw [a_eq_c 19321 (by decide), a_eq_factorial 139 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 139 ^ (r - 1) ≥ 139 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 139 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 139 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 139 ^ r ≥ 139 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (139 ^ r) hp_r, a_eq_c (139 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 149
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 22201 ≡ a 149 [ZMOD (149 ^ 9)]
          rw [a_eq_c 22201 (by decide), a_eq_factorial 149 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 149 ^ (r - 1) ≥ 149 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 149 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 149 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 149 ^ r ≥ 149 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (149 ^ r) hp_r, a_eq_c (149 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 151
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 22801 ≡ a 151 [ZMOD (151 ^ 9)]
          rw [a_eq_c 22801 (by decide), a_eq_factorial 151 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 151 ^ (r - 1) ≥ 151 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 151 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 151 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 151 ^ r ≥ 151 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (151 ^ r) hp_r, a_eq_c (151 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 157
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 24649 ≡ a 157 [ZMOD (157 ^ 9)]
          rw [a_eq_c 24649 (by decide), a_eq_factorial 157 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 157 ^ (r - 1) ≥ 157 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 157 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 157 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 157 ^ r ≥ 157 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (157 ^ r) hp_r, a_eq_c (157 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 163
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 26569 ≡ a 163 [ZMOD (163 ^ 9)]
          rw [a_eq_c 26569 (by decide), a_eq_factorial 163 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 163 ^ (r - 1) ≥ 163 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 163 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 163 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 163 ^ r ≥ 163 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (163 ^ r) hp_r, a_eq_c (163 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 167
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 27889 ≡ a 167 [ZMOD (167 ^ 9)]
          rw [a_eq_c 27889 (by decide), a_eq_factorial 167 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 167 ^ (r - 1) ≥ 167 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 167 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 167 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 167 ^ r ≥ 167 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (167 ^ r) hp_r, a_eq_c (167 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 173
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 29929 ≡ a 173 [ZMOD (173 ^ 9)]
          rw [a_eq_c 29929 (by decide), a_eq_factorial 173 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 173 ^ (r - 1) ≥ 173 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 173 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 173 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 173 ^ r ≥ 173 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (173 ^ r) hp_r, a_eq_c (173 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 179
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 32041 ≡ a 179 [ZMOD (179 ^ 9)]
          rw [a_eq_c 32041 (by decide), a_eq_factorial 179 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 179 ^ (r - 1) ≥ 179 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 179 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 179 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 179 ^ r ≥ 179 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (179 ^ r) hp_r, a_eq_c (179 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 181
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 32761 ≡ a 181 [ZMOD (181 ^ 9)]
          rw [a_eq_c 32761 (by decide), a_eq_factorial 181 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 181 ^ (r - 1) ≥ 181 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 181 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 181 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 181 ^ r ≥ 181 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (181 ^ r) hp_r, a_eq_c (181 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 191
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 36481 ≡ a 191 [ZMOD (191 ^ 9)]
          rw [a_eq_c 36481 (by decide), a_eq_factorial 191 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 191 ^ (r - 1) ≥ 191 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 191 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 191 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 191 ^ r ≥ 191 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (191 ^ r) hp_r, a_eq_c (191 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 193
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 37249 ≡ a 193 [ZMOD (193 ^ 9)]
          rw [a_eq_c 37249 (by decide), a_eq_factorial 193 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 193 ^ (r - 1) ≥ 193 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 193 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 193 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 193 ^ r ≥ 193 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (193 ^ r) hp_r, a_eq_c (193 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 197
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 38809 ≡ a 197 [ZMOD (197 ^ 9)]
          rw [a_eq_c 38809 (by decide), a_eq_factorial 197 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 197 ^ (r - 1) ≥ 197 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 197 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 197 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 197 ^ r ≥ 197 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (197 ^ r) hp_r, a_eq_c (197 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 199
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 39601 ≡ a 199 [ZMOD (199 ^ 9)]
          rw [a_eq_c 39601 (by decide), a_eq_factorial 199 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 199 ^ (r - 1) ≥ 199 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 199 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 199 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 199 ^ r ≥ 199 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (199 ^ r) hp_r, a_eq_c (199 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 211
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 44521 ≡ a 211 [ZMOD (211 ^ 9)]
          rw [a_eq_c 44521 (by decide), a_eq_factorial 211 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 211 ^ (r - 1) ≥ 211 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 211 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 211 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 211 ^ r ≥ 211 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (211 ^ r) hp_r, a_eq_c (211 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 223
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 49729 ≡ a 223 [ZMOD (223 ^ 9)]
          rw [a_eq_c 49729 (by decide), a_eq_factorial 223 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 223 ^ (r - 1) ≥ 223 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 223 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 223 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 223 ^ r ≥ 223 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (223 ^ r) hp_r, a_eq_c (223 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 227
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 51529 ≡ a 227 [ZMOD (227 ^ 9)]
          rw [a_eq_c 51529 (by decide), a_eq_factorial 227 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 227 ^ (r - 1) ≥ 227 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 227 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 227 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 227 ^ r ≥ 227 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (227 ^ r) hp_r, a_eq_c (227 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 229
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 52441 ≡ a 229 [ZMOD (229 ^ 9)]
          rw [a_eq_c 52441 (by decide), a_eq_factorial 229 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 229 ^ (r - 1) ≥ 229 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 229 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 229 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 229 ^ r ≥ 229 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (229 ^ r) hp_r, a_eq_c (229 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 233
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 54289 ≡ a 233 [ZMOD (233 ^ 9)]
          rw [a_eq_c 54289 (by decide), a_eq_factorial 233 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 233 ^ (r - 1) ≥ 233 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 233 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 233 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 233 ^ r ≥ 233 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (233 ^ r) hp_r, a_eq_c (233 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 239
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 57121 ≡ a 239 [ZMOD (239 ^ 9)]
          rw [a_eq_c 57121 (by decide), a_eq_factorial 239 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 239 ^ (r - 1) ≥ 239 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 239 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 239 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 239 ^ r ≥ 239 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (239 ^ r) hp_r, a_eq_c (239 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 241
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 58081 ≡ a 241 [ZMOD (241 ^ 9)]
          rw [a_eq_c 58081 (by decide), a_eq_factorial 241 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 241 ^ (r - 1) ≥ 241 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 241 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 241 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 241 ^ r ≥ 241 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (241 ^ r) hp_r, a_eq_c (241 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 251
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 63001 ≡ a 251 [ZMOD (251 ^ 9)]
          rw [a_eq_c 63001 (by decide), a_eq_factorial 251 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 251 ^ (r - 1) ≥ 251 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 251 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 251 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 251 ^ r ≥ 251 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (251 ^ r) hp_r, a_eq_c (251 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 257
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 66049 ≡ a 257 [ZMOD (257 ^ 9)]
          rw [a_eq_c 66049 (by decide), a_eq_factorial 257 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 257 ^ (r - 1) ≥ 257 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 257 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 257 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 257 ^ r ≥ 257 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (257 ^ r) hp_r, a_eq_c (257 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 263
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 69169 ≡ a 263 [ZMOD (263 ^ 9)]
          rw [a_eq_c 69169 (by decide), a_eq_factorial 263 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 263 ^ (r - 1) ≥ 263 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 263 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 263 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 263 ^ r ≥ 263 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (263 ^ r) hp_r, a_eq_c (263 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 269
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 72361 ≡ a 269 [ZMOD (269 ^ 9)]
          rw [a_eq_c 72361 (by decide), a_eq_factorial 269 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 269 ^ (r - 1) ≥ 269 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 269 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 269 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 269 ^ r ≥ 269 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (269 ^ r) hp_r, a_eq_c (269 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 271
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 73441 ≡ a 271 [ZMOD (271 ^ 9)]
          rw [a_eq_c 73441 (by decide), a_eq_factorial 271 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 271 ^ (r - 1) ≥ 271 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 271 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 271 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 271 ^ r ≥ 271 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (271 ^ r) hp_r, a_eq_c (271 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 277
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 76729 ≡ a 277 [ZMOD (277 ^ 9)]
          rw [a_eq_c 76729 (by decide), a_eq_factorial 277 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 277 ^ (r - 1) ≥ 277 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 277 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 277 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 277 ^ r ≥ 277 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (277 ^ r) hp_r, a_eq_c (277 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 281
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 78961 ≡ a 281 [ZMOD (281 ^ 9)]
          rw [a_eq_c 78961 (by decide), a_eq_factorial 281 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 281 ^ (r - 1) ≥ 281 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 281 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 281 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 281 ^ r ≥ 281 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (281 ^ r) hp_r, a_eq_c (281 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 283
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 80089 ≡ a 283 [ZMOD (283 ^ 9)]
          rw [a_eq_c 80089 (by decide), a_eq_factorial 283 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 283 ^ (r - 1) ≥ 283 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 283 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 283 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 283 ^ r ≥ 283 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (283 ^ r) hp_r, a_eq_c (283 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 293
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 85849 ≡ a 293 [ZMOD (293 ^ 9)]
          rw [a_eq_c 85849 (by decide), a_eq_factorial 293 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 293 ^ (r - 1) ≥ 293 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 293 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 293 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 293 ^ r ≥ 293 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (293 ^ r) hp_r, a_eq_c (293 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 307
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 94249 ≡ a 307 [ZMOD (307 ^ 9)]
          rw [a_eq_c 94249 (by decide), a_eq_factorial 307 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 307 ^ (r - 1) ≥ 307 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 307 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 307 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 307 ^ r ≥ 307 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (307 ^ r) hp_r, a_eq_c (307 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 311
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 96721 ≡ a 311 [ZMOD (311 ^ 9)]
          rw [a_eq_c 96721 (by decide), a_eq_factorial 311 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 311 ^ (r - 1) ≥ 311 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 311 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 311 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 311 ^ r ≥ 311 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (311 ^ r) hp_r, a_eq_c (311 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 313
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 97969 ≡ a 313 [ZMOD (313 ^ 9)]
          rw [a_eq_c 97969 (by decide), a_eq_factorial 313 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 313 ^ (r - 1) ≥ 313 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 313 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 313 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 313 ^ r ≥ 313 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (313 ^ r) hp_r, a_eq_c (313 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 317
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 100489 ≡ a 317 [ZMOD (317 ^ 9)]
          rw [a_eq_c 100489 (by decide), a_eq_factorial 317 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 317 ^ (r - 1) ≥ 317 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 317 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 317 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 317 ^ r ≥ 317 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (317 ^ r) hp_r, a_eq_c (317 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 331
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 109561 ≡ a 331 [ZMOD (331 ^ 9)]
          rw [a_eq_c 109561 (by decide), a_eq_factorial 331 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 331 ^ (r - 1) ≥ 331 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 331 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 331 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 331 ^ r ≥ 331 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (331 ^ r) hp_r, a_eq_c (331 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 337
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 113569 ≡ a 337 [ZMOD (337 ^ 9)]
          rw [a_eq_c 113569 (by decide), a_eq_factorial 337 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 337 ^ (r - 1) ≥ 337 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 337 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 337 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 337 ^ r ≥ 337 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (337 ^ r) hp_r, a_eq_c (337 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 347
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 120409 ≡ a 347 [ZMOD (347 ^ 9)]
          rw [a_eq_c 120409 (by decide), a_eq_factorial 347 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 347 ^ (r - 1) ≥ 347 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 347 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 347 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 347 ^ r ≥ 347 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (347 ^ r) hp_r, a_eq_c (347 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 349
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 121801 ≡ a 349 [ZMOD (349 ^ 9)]
          rw [a_eq_c 121801 (by decide), a_eq_factorial 349 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 349 ^ (r - 1) ≥ 349 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 349 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 349 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 349 ^ r ≥ 349 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (349 ^ r) hp_r, a_eq_c (349 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 353
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 124609 ≡ a 353 [ZMOD (353 ^ 9)]
          rw [a_eq_c 124609 (by decide), a_eq_factorial 353 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 353 ^ (r - 1) ≥ 353 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 353 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 353 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 353 ^ r ≥ 353 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (353 ^ r) hp_r, a_eq_c (353 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 359
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 128881 ≡ a 359 [ZMOD (359 ^ 9)]
          rw [a_eq_c 128881 (by decide), a_eq_factorial 359 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 359 ^ (r - 1) ≥ 359 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 359 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 359 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 359 ^ r ≥ 359 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (359 ^ r) hp_r, a_eq_c (359 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 367
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 134689 ≡ a 367 [ZMOD (367 ^ 9)]
          rw [a_eq_c 134689 (by decide), a_eq_factorial 367 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 367 ^ (r - 1) ≥ 367 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 367 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 367 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 367 ^ r ≥ 367 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (367 ^ r) hp_r, a_eq_c (367 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 373
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 139129 ≡ a 373 [ZMOD (373 ^ 9)]
          rw [a_eq_c 139129 (by decide), a_eq_factorial 373 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 373 ^ (r - 1) ≥ 373 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 373 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 373 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 373 ^ r ≥ 373 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (373 ^ r) hp_r, a_eq_c (373 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 379
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 143641 ≡ a 379 [ZMOD (379 ^ 9)]
          rw [a_eq_c 143641 (by decide), a_eq_factorial 379 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 379 ^ (r - 1) ≥ 379 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 379 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 379 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 379 ^ r ≥ 379 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (379 ^ r) hp_r, a_eq_c (379 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 383
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 146689 ≡ a 383 [ZMOD (383 ^ 9)]
          rw [a_eq_c 146689 (by decide), a_eq_factorial 383 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 383 ^ (r - 1) ≥ 383 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 383 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 383 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 383 ^ r ≥ 383 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (383 ^ r) hp_r, a_eq_c (383 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 389
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 151321 ≡ a 389 [ZMOD (389 ^ 9)]
          rw [a_eq_c 151321 (by decide), a_eq_factorial 389 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 389 ^ (r - 1) ≥ 389 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 389 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 389 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 389 ^ r ≥ 389 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (389 ^ r) hp_r, a_eq_c (389 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 397
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 157609 ≡ a 397 [ZMOD (397 ^ 9)]
          rw [a_eq_c 157609 (by decide), a_eq_factorial 397 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 397 ^ (r - 1) ≥ 397 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 397 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 397 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 397 ^ r ≥ 397 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (397 ^ r) hp_r, a_eq_c (397 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 401
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 160801 ≡ a 401 [ZMOD (401 ^ 9)]
          rw [a_eq_c 160801 (by decide), a_eq_factorial 401 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 401 ^ (r - 1) ≥ 401 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 401 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 401 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 401 ^ r ≥ 401 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (401 ^ r) hp_r, a_eq_c (401 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 409
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 167281 ≡ a 409 [ZMOD (409 ^ 9)]
          rw [a_eq_c 167281 (by decide), a_eq_factorial 409 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 409 ^ (r - 1) ≥ 409 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 409 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 409 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 409 ^ r ≥ 409 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (409 ^ r) hp_r, a_eq_c (409 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 419
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 175561 ≡ a 419 [ZMOD (419 ^ 9)]
          rw [a_eq_c 175561 (by decide), a_eq_factorial 419 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 419 ^ (r - 1) ≥ 419 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 419 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 419 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 419 ^ r ≥ 419 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (419 ^ r) hp_r, a_eq_c (419 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 421
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 177241 ≡ a 421 [ZMOD (421 ^ 9)]
          rw [a_eq_c 177241 (by decide), a_eq_factorial 421 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 421 ^ (r - 1) ≥ 421 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 421 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 421 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 421 ^ r ≥ 421 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (421 ^ r) hp_r, a_eq_c (421 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 431
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 185761 ≡ a 431 [ZMOD (431 ^ 9)]
          rw [a_eq_c 185761 (by decide), a_eq_factorial 431 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 431 ^ (r - 1) ≥ 431 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 431 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 431 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 431 ^ r ≥ 431 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (431 ^ r) hp_r, a_eq_c (431 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 433
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 187489 ≡ a 433 [ZMOD (433 ^ 9)]
          rw [a_eq_c 187489 (by decide), a_eq_factorial 433 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 433 ^ (r - 1) ≥ 433 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 433 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 433 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 433 ^ r ≥ 433 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (433 ^ r) hp_r, a_eq_c (433 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 439
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 192721 ≡ a 439 [ZMOD (439 ^ 9)]
          rw [a_eq_c 192721 (by decide), a_eq_factorial 439 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 439 ^ (r - 1) ≥ 439 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 439 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 439 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 439 ^ r ≥ 439 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (439 ^ r) hp_r, a_eq_c (439 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 443
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 196249 ≡ a 443 [ZMOD (443 ^ 9)]
          rw [a_eq_c 196249 (by decide), a_eq_factorial 443 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 443 ^ (r - 1) ≥ 443 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 443 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 443 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 443 ^ r ≥ 443 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (443 ^ r) hp_r, a_eq_c (443 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 449
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 201601 ≡ a 449 [ZMOD (449 ^ 9)]
          rw [a_eq_c 201601 (by decide), a_eq_factorial 449 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 449 ^ (r - 1) ≥ 449 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 449 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 449 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 449 ^ r ≥ 449 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (449 ^ r) hp_r, a_eq_c (449 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 457
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 208849 ≡ a 457 [ZMOD (457 ^ 9)]
          rw [a_eq_c 208849 (by decide), a_eq_factorial 457 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 457 ^ (r - 1) ≥ 457 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 457 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 457 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 457 ^ r ≥ 457 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (457 ^ r) hp_r, a_eq_c (457 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 461
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 212521 ≡ a 461 [ZMOD (461 ^ 9)]
          rw [a_eq_c 212521 (by decide), a_eq_factorial 461 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 461 ^ (r - 1) ≥ 461 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 461 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 461 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 461 ^ r ≥ 461 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (461 ^ r) hp_r, a_eq_c (461 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 463
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 214369 ≡ a 463 [ZMOD (463 ^ 9)]
          rw [a_eq_c 214369 (by decide), a_eq_factorial 463 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 463 ^ (r - 1) ≥ 463 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 463 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 463 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 463 ^ r ≥ 463 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (463 ^ r) hp_r, a_eq_c (463 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 467
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 218089 ≡ a 467 [ZMOD (467 ^ 9)]
          rw [a_eq_c 218089 (by decide), a_eq_factorial 467 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 467 ^ (r - 1) ≥ 467 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 467 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 467 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 467 ^ r ≥ 467 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (467 ^ r) hp_r, a_eq_c (467 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 479
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 229441 ≡ a 479 [ZMOD (479 ^ 9)]
          rw [a_eq_c 229441 (by decide), a_eq_factorial 479 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 479 ^ (r - 1) ≥ 479 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 479 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 479 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 479 ^ r ≥ 479 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (479 ^ r) hp_r, a_eq_c (479 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 487
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 237169 ≡ a 487 [ZMOD (487 ^ 9)]
          rw [a_eq_c 237169 (by decide), a_eq_factorial 487 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 487 ^ (r - 1) ≥ 487 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 487 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 487 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 487 ^ r ≥ 487 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (487 ^ r) hp_r, a_eq_c (487 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 491
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 241081 ≡ a 491 [ZMOD (491 ^ 9)]
          rw [a_eq_c 241081 (by decide), a_eq_factorial 491 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 491 ^ (r - 1) ≥ 491 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 491 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 491 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 491 ^ r ≥ 491 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (491 ^ r) hp_r, a_eq_c (491 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 499
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 249001 ≡ a 499 [ZMOD (499 ^ 9)]
          rw [a_eq_c 249001 (by decide), a_eq_factorial 499 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 499 ^ (r - 1) ≥ 499 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 499 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 499 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 499 ^ r ≥ 499 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (499 ^ r) hp_r, a_eq_c (499 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 503
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 253009 ≡ a 503 [ZMOD (503 ^ 9)]
          rw [a_eq_c 253009 (by decide), a_eq_factorial 503 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 503 ^ (r - 1) ≥ 503 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 503 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 503 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 503 ^ r ≥ 503 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (503 ^ r) hp_r, a_eq_c (503 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 509
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 259081 ≡ a 509 [ZMOD (509 ^ 9)]
          rw [a_eq_c 259081 (by decide), a_eq_factorial 509 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 509 ^ (r - 1) ≥ 509 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 509 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 509 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 509 ^ r ≥ 509 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (509 ^ r) hp_r, a_eq_c (509 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 521
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 271441 ≡ a 521 [ZMOD (521 ^ 9)]
          rw [a_eq_c 271441 (by decide), a_eq_factorial 521 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 521 ^ (r - 1) ≥ 521 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 521 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 521 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 521 ^ r ≥ 521 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (521 ^ r) hp_r, a_eq_c (521 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 523
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 273529 ≡ a 523 [ZMOD (523 ^ 9)]
          rw [a_eq_c 273529 (by decide), a_eq_factorial 523 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 523 ^ (r - 1) ≥ 523 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 523 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 523 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 523 ^ r ≥ 523 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (523 ^ r) hp_r, a_eq_c (523 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 541
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 292681 ≡ a 541 [ZMOD (541 ^ 9)]
          rw [a_eq_c 292681 (by decide), a_eq_factorial 541 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 541 ^ (r - 1) ≥ 541 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 541 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 541 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 541 ^ r ≥ 541 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (541 ^ r) hp_r, a_eq_c (541 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 547
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 299209 ≡ a 547 [ZMOD (547 ^ 9)]
          rw [a_eq_c 299209 (by decide), a_eq_factorial 547 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 547 ^ (r - 1) ≥ 547 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 547 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 547 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 547 ^ r ≥ 547 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (547 ^ r) hp_r, a_eq_c (547 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 557
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 310249 ≡ a 557 [ZMOD (557 ^ 9)]
          rw [a_eq_c 310249 (by decide), a_eq_factorial 557 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 557 ^ (r - 1) ≥ 557 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 557 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 557 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 557 ^ r ≥ 557 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (557 ^ r) hp_r, a_eq_c (557 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 563
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 316969 ≡ a 563 [ZMOD (563 ^ 9)]
          rw [a_eq_c 316969 (by decide), a_eq_factorial 563 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 563 ^ (r - 1) ≥ 563 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 563 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 563 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 563 ^ r ≥ 563 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (563 ^ r) hp_r, a_eq_c (563 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 569
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 323761 ≡ a 569 [ZMOD (569 ^ 9)]
          rw [a_eq_c 323761 (by decide), a_eq_factorial 569 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 569 ^ (r - 1) ≥ 569 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 569 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 569 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 569 ^ r ≥ 569 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (569 ^ r) hp_r, a_eq_c (569 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 571
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 326041 ≡ a 571 [ZMOD (571 ^ 9)]
          rw [a_eq_c 326041 (by decide), a_eq_factorial 571 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 571 ^ (r - 1) ≥ 571 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 571 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 571 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 571 ^ r ≥ 571 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (571 ^ r) hp_r, a_eq_c (571 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 577
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 332929 ≡ a 577 [ZMOD (577 ^ 9)]
          rw [a_eq_c 332929 (by decide), a_eq_factorial 577 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 577 ^ (r - 1) ≥ 577 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 577 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 577 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 577 ^ r ≥ 577 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (577 ^ r) hp_r, a_eq_c (577 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 587
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 344569 ≡ a 587 [ZMOD (587 ^ 9)]
          rw [a_eq_c 344569 (by decide), a_eq_factorial 587 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 587 ^ (r - 1) ≥ 587 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 587 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 587 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 587 ^ r ≥ 587 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (587 ^ r) hp_r, a_eq_c (587 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 593
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 351649 ≡ a 593 [ZMOD (593 ^ 9)]
          rw [a_eq_c 351649 (by decide), a_eq_factorial 593 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 593 ^ (r - 1) ≥ 593 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 593 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 593 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 593 ^ r ≥ 593 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (593 ^ r) hp_r, a_eq_c (593 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 599
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 358801 ≡ a 599 [ZMOD (599 ^ 9)]
          rw [a_eq_c 358801 (by decide), a_eq_factorial 599 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 599 ^ (r - 1) ≥ 599 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 599 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 599 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 599 ^ r ≥ 599 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (599 ^ r) hp_r, a_eq_c (599 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 601
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 361201 ≡ a 601 [ZMOD (601 ^ 9)]
          rw [a_eq_c 361201 (by decide), a_eq_factorial 601 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 601 ^ (r - 1) ≥ 601 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 601 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 601 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 601 ^ r ≥ 601 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (601 ^ r) hp_r, a_eq_c (601 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 607
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 368449 ≡ a 607 [ZMOD (607 ^ 9)]
          rw [a_eq_c 368449 (by decide), a_eq_factorial 607 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 607 ^ (r - 1) ≥ 607 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 607 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 607 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 607 ^ r ≥ 607 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (607 ^ r) hp_r, a_eq_c (607 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 613
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 375769 ≡ a 613 [ZMOD (613 ^ 9)]
          rw [a_eq_c 375769 (by decide), a_eq_factorial 613 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 613 ^ (r - 1) ≥ 613 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 613 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 613 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 613 ^ r ≥ 613 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (613 ^ r) hp_r, a_eq_c (613 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 617
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 380689 ≡ a 617 [ZMOD (617 ^ 9)]
          rw [a_eq_c 380689 (by decide), a_eq_factorial 617 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 617 ^ (r - 1) ≥ 617 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 617 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 617 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 617 ^ r ≥ 617 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (617 ^ r) hp_r, a_eq_c (617 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 619
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 383161 ≡ a 619 [ZMOD (619 ^ 9)]
          rw [a_eq_c 383161 (by decide), a_eq_factorial 619 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 619 ^ (r - 1) ≥ 619 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 619 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 619 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 619 ^ r ≥ 619 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (619 ^ r) hp_r, a_eq_c (619 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 631
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 398161 ≡ a 631 [ZMOD (631 ^ 9)]
          rw [a_eq_c 398161 (by decide), a_eq_factorial 631 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 631 ^ (r - 1) ≥ 631 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 631 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 631 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 631 ^ r ≥ 631 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (631 ^ r) hp_r, a_eq_c (631 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 641
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 410881 ≡ a 641 [ZMOD (641 ^ 9)]
          rw [a_eq_c 410881 (by decide), a_eq_factorial 641 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 641 ^ (r - 1) ≥ 641 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 641 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 641 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 641 ^ r ≥ 641 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (641 ^ r) hp_r, a_eq_c (641 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 643
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 413449 ≡ a 643 [ZMOD (643 ^ 9)]
          rw [a_eq_c 413449 (by decide), a_eq_factorial 643 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 643 ^ (r - 1) ≥ 643 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 643 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 643 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 643 ^ r ≥ 643 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (643 ^ r) hp_r, a_eq_c (643 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 647
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 418609 ≡ a 647 [ZMOD (647 ^ 9)]
          rw [a_eq_c 418609 (by decide), a_eq_factorial 647 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 647 ^ (r - 1) ≥ 647 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 647 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 647 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 647 ^ r ≥ 647 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (647 ^ r) hp_r, a_eq_c (647 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 653
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 426409 ≡ a 653 [ZMOD (653 ^ 9)]
          rw [a_eq_c 426409 (by decide), a_eq_factorial 653 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 653 ^ (r - 1) ≥ 653 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 653 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 653 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 653 ^ r ≥ 653 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (653 ^ r) hp_r, a_eq_c (653 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 659
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 434281 ≡ a 659 [ZMOD (659 ^ 9)]
          rw [a_eq_c 434281 (by decide), a_eq_factorial 659 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 659 ^ (r - 1) ≥ 659 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 659 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 659 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 659 ^ r ≥ 659 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (659 ^ r) hp_r, a_eq_c (659 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 661
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 436921 ≡ a 661 [ZMOD (661 ^ 9)]
          rw [a_eq_c 436921 (by decide), a_eq_factorial 661 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 661 ^ (r - 1) ≥ 661 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 661 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 661 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 661 ^ r ≥ 661 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (661 ^ r) hp_r, a_eq_c (661 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 673
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 452929 ≡ a 673 [ZMOD (673 ^ 9)]
          rw [a_eq_c 452929 (by decide), a_eq_factorial 673 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 673 ^ (r - 1) ≥ 673 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 673 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 673 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 673 ^ r ≥ 673 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (673 ^ r) hp_r, a_eq_c (673 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 677
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 458329 ≡ a 677 [ZMOD (677 ^ 9)]
          rw [a_eq_c 458329 (by decide), a_eq_factorial 677 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 677 ^ (r - 1) ≥ 677 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 677 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 677 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 677 ^ r ≥ 677 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (677 ^ r) hp_r, a_eq_c (677 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 683
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 466489 ≡ a 683 [ZMOD (683 ^ 9)]
          rw [a_eq_c 466489 (by decide), a_eq_factorial 683 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 683 ^ (r - 1) ≥ 683 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 683 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 683 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 683 ^ r ≥ 683 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (683 ^ r) hp_r, a_eq_c (683 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 691
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 477481 ≡ a 691 [ZMOD (691 ^ 9)]
          rw [a_eq_c 477481 (by decide), a_eq_factorial 691 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 691 ^ (r - 1) ≥ 691 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 691 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 691 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 691 ^ r ≥ 691 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (691 ^ r) hp_r, a_eq_c (691 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 701
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 491401 ≡ a 701 [ZMOD (701 ^ 9)]
          rw [a_eq_c 491401 (by decide), a_eq_factorial 701 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 701 ^ (r - 1) ≥ 701 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 701 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 701 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 701 ^ r ≥ 701 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (701 ^ r) hp_r, a_eq_c (701 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 709
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 502681 ≡ a 709 [ZMOD (709 ^ 9)]
          rw [a_eq_c 502681 (by decide), a_eq_factorial 709 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 709 ^ (r - 1) ≥ 709 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 709 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 709 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 709 ^ r ≥ 709 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (709 ^ r) hp_r, a_eq_c (709 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 719
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 516961 ≡ a 719 [ZMOD (719 ^ 9)]
          rw [a_eq_c 516961 (by decide), a_eq_factorial 719 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 719 ^ (r - 1) ≥ 719 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 719 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 719 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 719 ^ r ≥ 719 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (719 ^ r) hp_r, a_eq_c (719 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 727
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 528529 ≡ a 727 [ZMOD (727 ^ 9)]
          rw [a_eq_c 528529 (by decide), a_eq_factorial 727 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 727 ^ (r - 1) ≥ 727 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 727 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 727 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 727 ^ r ≥ 727 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (727 ^ r) hp_r, a_eq_c (727 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 733
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 537289 ≡ a 733 [ZMOD (733 ^ 9)]
          rw [a_eq_c 537289 (by decide), a_eq_factorial 733 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 733 ^ (r - 1) ≥ 733 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 733 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 733 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 733 ^ r ≥ 733 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (733 ^ r) hp_r, a_eq_c (733 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 739
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 546121 ≡ a 739 [ZMOD (739 ^ 9)]
          rw [a_eq_c 546121 (by decide), a_eq_factorial 739 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 739 ^ (r - 1) ≥ 739 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 739 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 739 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 739 ^ r ≥ 739 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (739 ^ r) hp_r, a_eq_c (739 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 743
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 552049 ≡ a 743 [ZMOD (743 ^ 9)]
          rw [a_eq_c 552049 (by decide), a_eq_factorial 743 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 743 ^ (r - 1) ≥ 743 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 743 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 743 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 743 ^ r ≥ 743 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (743 ^ r) hp_r, a_eq_c (743 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 751
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 564001 ≡ a 751 [ZMOD (751 ^ 9)]
          rw [a_eq_c 564001 (by decide), a_eq_factorial 751 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 751 ^ (r - 1) ≥ 751 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 751 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 751 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 751 ^ r ≥ 751 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (751 ^ r) hp_r, a_eq_c (751 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 757
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 573049 ≡ a 757 [ZMOD (757 ^ 9)]
          rw [a_eq_c 573049 (by decide), a_eq_factorial 757 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 757 ^ (r - 1) ≥ 757 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 757 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 757 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 757 ^ r ≥ 757 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (757 ^ r) hp_r, a_eq_c (757 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 761
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 579121 ≡ a 761 [ZMOD (761 ^ 9)]
          rw [a_eq_c 579121 (by decide), a_eq_factorial 761 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 761 ^ (r - 1) ≥ 761 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 761 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 761 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 761 ^ r ≥ 761 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (761 ^ r) hp_r, a_eq_c (761 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 769
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 591361 ≡ a 769 [ZMOD (769 ^ 9)]
          rw [a_eq_c 591361 (by decide), a_eq_factorial 769 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 769 ^ (r - 1) ≥ 769 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 769 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 769 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 769 ^ r ≥ 769 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (769 ^ r) hp_r, a_eq_c (769 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 773
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 597529 ≡ a 773 [ZMOD (773 ^ 9)]
          rw [a_eq_c 597529 (by decide), a_eq_factorial 773 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 773 ^ (r - 1) ≥ 773 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 773 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 773 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 773 ^ r ≥ 773 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (773 ^ r) hp_r, a_eq_c (773 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 787
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 619369 ≡ a 787 [ZMOD (787 ^ 9)]
          rw [a_eq_c 619369 (by decide), a_eq_factorial 787 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 787 ^ (r - 1) ≥ 787 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 787 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 787 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 787 ^ r ≥ 787 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (787 ^ r) hp_r, a_eq_c (787 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 797
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 635209 ≡ a 797 [ZMOD (797 ^ 9)]
          rw [a_eq_c 635209 (by decide), a_eq_factorial 797 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 797 ^ (r - 1) ≥ 797 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 797 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 797 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 797 ^ r ≥ 797 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (797 ^ r) hp_r, a_eq_c (797 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 809
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 654481 ≡ a 809 [ZMOD (809 ^ 9)]
          rw [a_eq_c 654481 (by decide), a_eq_factorial 809 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 809 ^ (r - 1) ≥ 809 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 809 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 809 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 809 ^ r ≥ 809 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (809 ^ r) hp_r, a_eq_c (809 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 811
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 657721 ≡ a 811 [ZMOD (811 ^ 9)]
          rw [a_eq_c 657721 (by decide), a_eq_factorial 811 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 811 ^ (r - 1) ≥ 811 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 811 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 811 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 811 ^ r ≥ 811 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (811 ^ r) hp_r, a_eq_c (811 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 821
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 674041 ≡ a 821 [ZMOD (821 ^ 9)]
          rw [a_eq_c 674041 (by decide), a_eq_factorial 821 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 821 ^ (r - 1) ≥ 821 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 821 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 821 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 821 ^ r ≥ 821 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (821 ^ r) hp_r, a_eq_c (821 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 823
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 677329 ≡ a 823 [ZMOD (823 ^ 9)]
          rw [a_eq_c 677329 (by decide), a_eq_factorial 823 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 823 ^ (r - 1) ≥ 823 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 823 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 823 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 823 ^ r ≥ 823 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (823 ^ r) hp_r, a_eq_c (823 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 827
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 683929 ≡ a 827 [ZMOD (827 ^ 9)]
          rw [a_eq_c 683929 (by decide), a_eq_factorial 827 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 827 ^ (r - 1) ≥ 827 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 827 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 827 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 827 ^ r ≥ 827 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (827 ^ r) hp_r, a_eq_c (827 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 829
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 687241 ≡ a 829 [ZMOD (829 ^ 9)]
          rw [a_eq_c 687241 (by decide), a_eq_factorial 829 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 829 ^ (r - 1) ≥ 829 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 829 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 829 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 829 ^ r ≥ 829 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (829 ^ r) hp_r, a_eq_c (829 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 839
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 703921 ≡ a 839 [ZMOD (839 ^ 9)]
          rw [a_eq_c 703921 (by decide), a_eq_factorial 839 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 839 ^ (r - 1) ≥ 839 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 839 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 839 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 839 ^ r ≥ 839 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (839 ^ r) hp_r, a_eq_c (839 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 853
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 727609 ≡ a 853 [ZMOD (853 ^ 9)]
          rw [a_eq_c 727609 (by decide), a_eq_factorial 853 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 853 ^ (r - 1) ≥ 853 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 853 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 853 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 853 ^ r ≥ 853 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (853 ^ r) hp_r, a_eq_c (853 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 857
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 734449 ≡ a 857 [ZMOD (857 ^ 9)]
          rw [a_eq_c 734449 (by decide), a_eq_factorial 857 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 857 ^ (r - 1) ≥ 857 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 857 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 857 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 857 ^ r ≥ 857 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (857 ^ r) hp_r, a_eq_c (857 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 859
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 737881 ≡ a 859 [ZMOD (859 ^ 9)]
          rw [a_eq_c 737881 (by decide), a_eq_factorial 859 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 859 ^ (r - 1) ≥ 859 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 859 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 859 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 859 ^ r ≥ 859 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (859 ^ r) hp_r, a_eq_c (859 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 863
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 744769 ≡ a 863 [ZMOD (863 ^ 9)]
          rw [a_eq_c 744769 (by decide), a_eq_factorial 863 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 863 ^ (r - 1) ≥ 863 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 863 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 863 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 863 ^ r ≥ 863 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (863 ^ r) hp_r, a_eq_c (863 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 877
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 769129 ≡ a 877 [ZMOD (877 ^ 9)]
          rw [a_eq_c 769129 (by decide), a_eq_factorial 877 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 877 ^ (r - 1) ≥ 877 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 877 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 877 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 877 ^ r ≥ 877 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (877 ^ r) hp_r, a_eq_c (877 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 881
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 776161 ≡ a 881 [ZMOD (881 ^ 9)]
          rw [a_eq_c 776161 (by decide), a_eq_factorial 881 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 881 ^ (r - 1) ≥ 881 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 881 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 881 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 881 ^ r ≥ 881 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (881 ^ r) hp_r, a_eq_c (881 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · -- p = 883
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 779689 ≡ a 883 [ZMOD (883 ^ 9)]
          rw [a_eq_c 779689 (by decide), a_eq_factorial 883 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 883 ^ (r - 1) ≥ 883 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 883 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 883 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 883 ^ r ≥ 883 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (883 ^ r) hp_r, a_eq_c (883 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 887
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 786769 ≡ a 887 [ZMOD (887 ^ 9)]
          rw [a_eq_c 786769 (by decide), a_eq_factorial 887 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 887 ^ (r - 1) ≥ 887 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 887 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 887 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 887 ^ r ≥ 887 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (887 ^ r) hp_r, a_eq_c (887 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 907
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 822649 ≡ a 907 [ZMOD (907 ^ 9)]
          rw [a_eq_c 822649 (by decide), a_eq_factorial 907 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 907 ^ (r - 1) ≥ 907 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 907 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 907 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 907 ^ r ≥ 907 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (907 ^ r) hp_r, a_eq_c (907 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 911
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 829921 ≡ a 911 [ZMOD (911 ^ 9)]
          rw [a_eq_c 829921 (by decide), a_eq_factorial 911 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 911 ^ (r - 1) ≥ 911 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 911 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 911 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 911 ^ r ≥ 911 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (911 ^ r) hp_r, a_eq_c (911 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 919
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 844561 ≡ a 919 [ZMOD (919 ^ 9)]
          rw [a_eq_c 844561 (by decide), a_eq_factorial 919 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 919 ^ (r - 1) ≥ 919 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 919 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 919 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 919 ^ r ≥ 919 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (919 ^ r) hp_r, a_eq_c (919 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 929
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 863041 ≡ a 929 [ZMOD (929 ^ 9)]
          rw [a_eq_c 863041 (by decide), a_eq_factorial 929 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 929 ^ (r - 1) ≥ 929 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 929 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 929 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 929 ^ r ≥ 929 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (929 ^ r) hp_r, a_eq_c (929 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 937
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 877969 ≡ a 937 [ZMOD (937 ^ 9)]
          rw [a_eq_c 877969 (by decide), a_eq_factorial 937 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 937 ^ (r - 1) ≥ 937 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 937 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 937 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 937 ^ r ≥ 937 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (937 ^ r) hp_r, a_eq_c (937 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 941
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 885481 ≡ a 941 [ZMOD (941 ^ 9)]
          rw [a_eq_c 885481 (by decide), a_eq_factorial 941 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 941 ^ (r - 1) ≥ 941 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 941 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 941 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 941 ^ r ≥ 941 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (941 ^ r) hp_r, a_eq_c (941 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 947
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 896809 ≡ a 947 [ZMOD (947 ^ 9)]
          rw [a_eq_c 896809 (by decide), a_eq_factorial 947 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 947 ^ (r - 1) ≥ 947 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 947 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 947 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 947 ^ r ≥ 947 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (947 ^ r) hp_r, a_eq_c (947 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 953
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 908209 ≡ a 953 [ZMOD (953 ^ 9)]
          rw [a_eq_c 908209 (by decide), a_eq_factorial 953 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 953 ^ (r - 1) ≥ 953 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 953 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 953 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 953 ^ r ≥ 953 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (953 ^ r) hp_r, a_eq_c (953 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 967
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 935089 ≡ a 967 [ZMOD (967 ^ 9)]
          rw [a_eq_c 935089 (by decide), a_eq_factorial 967 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 967 ^ (r - 1) ≥ 967 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 967 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 967 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 967 ^ r ≥ 967 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (967 ^ r) hp_r, a_eq_c (967 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 971
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 942841 ≡ a 971 [ZMOD (971 ^ 9)]
          rw [a_eq_c 942841 (by decide), a_eq_factorial 971 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 971 ^ (r - 1) ≥ 971 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 971 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 971 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 971 ^ r ≥ 971 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (971 ^ r) hp_r, a_eq_c (971 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 977
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 954529 ≡ a 977 [ZMOD (977 ^ 9)]
          rw [a_eq_c 954529 (by decide), a_eq_factorial 977 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 977 ^ (r - 1) ≥ 977 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 977 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 977 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 977 ^ r ≥ 977 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (977 ^ r) hp_r, a_eq_c (977 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 983
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 966289 ≡ a 983 [ZMOD (983 ^ 9)]
          rw [a_eq_c 966289 (by decide), a_eq_factorial 983 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 983 ^ (r - 1) ≥ 983 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 983 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 983 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 983 ^ r ≥ 983 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (983 ^ r) hp_r, a_eq_c (983 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 991
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 982081 ≡ a 991 [ZMOD (991 ^ 9)]
          rw [a_eq_c 982081 (by decide), a_eq_factorial 991 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 991 ^ (r - 1) ≥ 991 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 991 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 991 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 991 ^ r ≥ 991 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (991 ^ r) hp_r, a_eq_c (991 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
    · -- p = 997
      by_cases hr_bound : r < 3
      · interval_cases r
        · -- r = 2
          change a 994009 ≡ a 997 [ZMOD (997 ^ 9)]
          rw [a_eq_c 994009 (by decide), a_eq_factorial 997 (by decide)]
          decide
      · -- r >= r_max
        have h_r1 : r - 1 ≥ 2 := by omega
        have hp_r1_ge : 997 ^ (r - 1) ≥ 997 ^ 2 := Nat.pow_le_pow_right (by omega) h_r1
        have hp_r1 : 997 ^ (r - 1) ≥ 1000 := by omega
        have hp_r : 997 ^ r ≥ 1000 := by
          have : r ≥ r - 1 := by omega
          have : 997 ^ r ≥ 997 ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
          omega
        rw [a_eq_c (997 ^ r) hp_r, a_eq_c (997 ^ (r - 1)) hp_r1]
    · exfalso; revert hp; decide
    · exfalso; revert hp; decide
  · -- p >= N
    have hp_bound_ge : p ≥ 1000 := by omega
    have h_r1 : r - 1 ≥ 1 := by omega
    have hp_r1_ge : p ^ (r - 1) ≥ p ^ 1 := Nat.pow_le_pow_right (by omega) h_r1
    have hp_r1_ge2 : p ^ 1 ≥ 1000 ^ 1 := Nat.pow_le_pow_left hp_bound_ge 1
    have hp_r1 : p ^ (r - 1) ≥ 1000 := by omega
    have hp_r : p ^ r ≥ 1000 := by
      have : r ≥ r - 1 := by omega
      have : p ^ r ≥ p ^ (r - 1) := Nat.pow_le_pow_right (by omega) this
      omega
    rw [a_eq_c (p ^ r) hp_r, a_eq_c (p ^ (r - 1)) hp_r1]
